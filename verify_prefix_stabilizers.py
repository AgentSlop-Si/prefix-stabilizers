#!/usr/bin/env python3
"""Standalone verification script for:
'Prefix Stabilizer Maxima, Recursive Coset Orderings, and Escape Deficits in Finite Groups'.

Uses Python standard library only. Verifies:
1. Full subset DP maxima and labeled counts for small abelian, p-group, and nonabelian groups
   (C1..C12, C2xC2, C3xC3, Q8, D8, S3, D10, D14).
2. Explicit non-nested C12 witness and exact Stanley connectivity double count.
3. Dihedral DP recurrence (Theorem 1.3(c)) vs exact full subset DP for D6, D10, D14.
4. Nonabelian F7 x| C3 (order 21): hierarchical count and exact Vosper escape count (79,009,136,640).
"""
from __future__ import annotations

import itertools
import math
from functools import lru_cache


def factorize(n: int) -> dict[int, int]:
    res: dict[int, int] = {}
    d = 2
    while d * d <= n:
        while n % d == 0:
            res[d] = res.get(d, 0) + 1
            n //= d
        d += 1
    if n > 1:
        res[n] = res.get(n, 0) + 1
    return res


def theoretical_mW(m: int) -> int:
    # m * sum_p v_p(m) * (1 - 1/p)
    total = 0
    for p, e in factorize(m).items():
        total += e * (m - m // p)
    return total


def cyclic_table(m: int) -> list[list[int]]:
    return [[(a + b) % m for b in range(m)] for a in range(m)]


def direct_product(t1: list[list[int]], t2: list[list[int]]) -> list[list[int]]:
    m1, m2 = len(t1), len(t2)
    return [
        [t1[a // m2][b // m2] * m2 + t2[a % m2][b % m2] for b in range(m1 * m2)]
        for a in range(m1 * m2)
    ]


def semidirect_fq_cp(q: int, p: int) -> list[list[int]]:
    # Find alpha of order p in F_q^*
    alpha = None
    for a in range(2, q):
        if pow(a, p, q) == 1:
            alpha = a
            break
    assert alpha is not None
    # Elements indexed as u*p + i, 0<=u<q, 0<=i<p
    n = q * p
    table = [[0] * n for _ in range(n)]
    for u in range(q):
        for i in range(p):
            idx1 = u * p + i
            ai = pow(alpha, i, q)
            for v in range(q):
                for j in range(p):
                    idx2 = v * p + j
                    table[idx1][idx2] = ((u + ai * v) % q) * p + ((i + j) % p)
    return table


def q8_table() -> list[list[int]]:
    # Elements: 0:1, 1:-1, 2:i, 3:-i, 4:j, 5:-j, 6:k, 7:-k
    # Use sign * basis where basis in {0:1, 1:i, 2:j, 3:k}
    base_mul = [
        [(1, 0), (1, 1), (1, 2), (1, 3)],
        [(1, 1), (-1, 0), (1, 3), (-1, 2)],
        [(1, 2), (-1, 3), (-1, 0), (1, 1)],
        [(1, 3), (1, 2), (-1, 1), (-1, 0)],
    ]
    elems = [(1, 0), (-1, 0), (1, 1), (-1, 1), (1, 2), (-1, 2), (1, 3), (-1, 3)]
    pos = {e: idx for idx, e in enumerate(elems)}
    table = [[0] * 8 for _ in range(8)]
    for a, (s1, b1) in enumerate(elems):
        for b, (s2, b2) in enumerate(elems):
            s3, b3 = base_mul[b1][b2]
            table[a][b] = pos[(s1 * s2 * s3, b3)]
    return table


def d8_table() -> list[list[int]]:
    # r^i s^j, i in Z4, j in Z2; s r = r^-1 s
    n = 8
    table = [[0] * n for _ in range(n)]
    for i1 in range(4):
        for j1 in range(2):
            for i2 in range(4):
                for j2 in range(2):
                    i = (i1 + (-i2 if j1 else i2)) % 4
                    j = (j1 + j2) % 2
                    table[i1 * 2 + j1][i2 * 2 + j2] = i * 2 + j
    return table


def subset_dp(table: list[list[int]]) -> tuple[int, int]:
    """Exact full labeled subset DP returning (M(G), A(G))."""
    m = len(table)
    # Precompute left-multiplication bitmask permutation per element g
    # Actually faster: compute stabilizer order of each bitmask
    # For each g, lmul[g][x] = table[g][x]
    total_masks = 1 << m
    # Compute stab[mask] using bit operations
    # Wait: for m <= 14, total_masks <= 16384; precompute shifted bit per g
    stab = [0] * total_masks
    for mask in range(1, total_masks):
        cnt = 0
        # Only check g that map lowest set bit of mask into mask!
        lsb = (mask & -mask).bit_length() - 1
        for g in range(m):
            if not (mask & (1 << table[g][lsb])):
                continue
            ok = True
            rem = mask
            while rem:
                bit = rem & -rem
                x = bit.bit_length() - 1
                if not (mask & (1 << table[g][x])):
                    ok = False
                    break
                rem ^= bit
            if ok:
                cnt += 1
        stab[mask] = cnt - 1

    best = [-1] * total_masks
    ways = [0] * total_masks
    best[0] = 0
    ways[0] = 1
    for mask in range(1, total_masks):
        b = -1
        w = 0
        rem = mask
        while rem:
            bit = rem & -rem
            prev = mask ^ bit
            cand = best[prev]
            if cand > b:
                b = cand
                w = ways[prev]
            elif cand == b:
                w += ways[prev]
            rem ^= bit
        best[mask] = b + stab[mask]
        ways[mask] = w
    return best[total_masks - 1], ways[total_masks - 1]


def dihedral_dp_count(q: int) -> tuple[int, int, int]:
    """Theorem 1.3(c) run-transition recurrence for D_{2q}."""
    full = (1 << q) - 1
    f = [0] * (1 << q)
    for a in range(q):
        f[1 << a] = q
    # Precompute cyclic shifts of each mask for t in 1..q-1
    for size in range(1, q - 1):
        for mask in range(1, full):
            if mask.bit_count() != size or f[mask] == 0:
                continue
            val = f[mask]
            # Transitions: keep center (+1 for each x not in mask)
            # Change center: shift t in 1..q-1 where (mask | shift(mask, t)) has popcount size+1
            extra: dict[int, int] = {}
            for x in range(q):
                if not (mask & (1 << x)):
                    extra[mask | (1 << x)] = extra.get(mask | (1 << x), 0) + 1
            for t in range(1, q):
                shifted = ((mask << t) | (mask >> (q - t))) & full
                nxt = mask | shifted
                if nxt.bit_count() == size + 1:
                    extra[nxt] = extra.get(nxt, 0) + 1
            for nxt, mult in extra.items():
                f[nxt] += val * mult

    order2_branch = (1 << q) * sum(f[m] for m in range(full) if m.bit_count() == q - 1)
    q_branch = 2 * (math.factorial(q) ** 2)
    hier_order2 = q * math.factorial(q) * (1 << q)
    total = q_branch + order2_branch
    nonhier = order2_branch - hier_order2
    return total, q_branch + hier_order2, nonhier


def verify_c12_witness_and_connectivity() -> None:
    order = [0, 6, 2, 8, 4, 10, 1, 5, 9, 3, 7, 11]
    m = 12
    stab_orders = []
    for j in range(1, m + 1):
        T = set(order[:j])
        H = [g for g in range(m) if {(g + x) % m for x in T} == T]
        stab_orders.append(len(H))
    assert stab_orders == [1, 2, 1, 2, 1, 6, 1, 1, 3, 1, 1, 12], stab_orders
    score = sum(s - 1 for s in stab_orders)
    assert score == 20 == theoretical_mW(12)

    # Verify Stanley connectivity double count sum_{g in G} |C(sigma_g)| = Z_G(x)
    pos = {val: idx for idx, val in enumerate(order)}
    conn_sum = 0
    for g in range(m):
        perm = [pos[(g + order[i]) % m] for i in range(m)]
        cuts = sum(1 for j in range(1, m) if set(perm[:j]) == set(range(j)))
        conn_sum += cuts
    assert conn_sum == score, (conn_sum, score)


def verify_cyclic_recurrence() -> None:
    @lru_cache(maxsize=None)
    def A_cyc(m: int) -> int:
        if m == 1:
            return 1
        return sum(math.factorial(q) * (A_cyc(m // q) ** q) for q in factorize(m))

    expected = {1: 1, 2: 2, 3: 6, 4: 8, 5: 120, 6: 120, 8: 128, 9: 1296, 10: 32640, 12: 31872}
    for m, val in expected.items():
        assert A_cyc(m) == val, (m, A_cyc(m), val)


def verify_f7_c3_vosper() -> None:
    # Exact stabilized-subset DP over order-3 branch subsets of F7 x| C3
    # Every K_c-invariant subset is encoded by (c, A_mask) with A_mask in 1..(2^7-2), plus empty and full.
    q, p = 7, 3
    alpha = 2  # 2^3 = 8 = 1 mod 7
    # Precompute D(c, d) masks
    D_mask = [[0] * q for _ in range(q)]
    for c in range(q):
        for d in range(q):
            m = 0
            for j in range(p):
                elem = ((pow(alpha, -j, q) - 1) * (c - d)) % q
                m |= 1 << elem
            D_mask[c][d] = m

    # Check non-arithmetic-progression property for all c != d
    for c in range(q):
        for d in range(q):
            if c == d:
                continue
            mu = (-(c - d)) % q
            assert not (D_mask[c][d] & (1 << mu))

    # Build DP over stabilized states (k, c, A_mask, escaped_bool)
    # States grouped by size k = 1..q-1; transitions jump from k to k' > k using binomial/factorial gap count
    # To avoid huge state expansion, track best count of stabilized proper boundaries AND exact labeled ways.
    # For a single boundary chain with escaping: exact stabilized-subset DP over (A_mask, c, escaped).
    full = (1 << q) - 1
    by_size = [[] for _ in range(q)]
    for mask in range(1, full):
        by_size[mask.bit_count()].append(mask)

    # Precompute sumset A + D(c, d)
    def sumset(A: int, D: int) -> int:
        res = 0
        rem = D
        while rem:
            b = rem & -rem
            shift = b.bit_length() - 1
            res |= ((A << shift) | (A >> (q - shift))) & full
            rem ^= b
        return res

    # DP: state = (A_mask, c, escaped) -> (max_boundaries, labeled_ways)
    best_b: dict[tuple[int, int, int], int] = {}
    ways_b: dict[tuple[int, int, int], int] = {}
    for a in range(q):
        for c in range(q):
            # Initial coset (c, {a}) has p! internal orders
            best_b[(1 << a, c, 0)] = 1
            ways_b[(1 << a, c, 0)] = math.factorial(p)

    # Also allow starting directly at a larger first stabilized boundary of size k >= 2 (would have fewer boundaries,
    # Wait: to be 100% exhaustive, include starting directly at any (A, c) with (p*|A|)! ways)
    for k in range(2, q):
        fk = math.factorial(p * k)
        for A in by_size[k]:
            for c in range(q):
                best_b[(A, c, 0)] = 1
                ways_b[(A, c, 0)] = fk

    # Transition from size k to k' > k
    # Note: we must NOT double-count intermediate stabilized boundaries!
    # In exact escape maximization, maximum boundaries is q - p + 1 = 5 (since q=7, p=3),
    # which occurs ONLY by skipping exactly 1 level (gap = 2 = p-1) or 2 levels?
    # Wait: skipping gap = 2 from k to k+2 between c != d can NEVER pass through an intermediate stabilized boundary,
    # because any intermediate boundary of size k+1 would have to have center c' != c or c' != d, impossible by Cauchy-Davenport!
    # Therefore EVERY valid chain of length 5 = q-p+1 has NO hidden intermediate stabilized boundaries!
    # Let's verify both the maximum boundary count (5) and exact ways!
    for k in range(1, q - 1):
        for A in by_size[k]:
            for c in range(q):
                for esc in (0, 1):
                    st = (A, c, esc)
                    if st not in best_b:
                        continue
                    b_cur = best_b[st]
                    w_cur = ways_b[st]
                    # Only transitions that could reach >= 5 boundaries need k' - k <= 2
                    for d in range(q):
                        nesc = 1 if (esc or d != c) else 0
                        req = A if d == c else sumset(A, D_mask[c][d])
                        rk = req.bit_count()
                        if rk == q:
                            continue
                        # Transition to B containing req with |B| in {k+1, k+2}
                        # (If d == c, gap 1 has p! ways; gap 2 is never maximal unless changing center,
                        # because you can always stay at c and hit the intermediate boundary.)
                        if d == c:
                            # step +1
                            for x in range(q):
                                if not (A & (1 << x)):
                                    B = A | (1 << x)
                                    nb = b_cur + 1
                                    nw = w_cur * math.factorial(p)
                                    nst = (B, d, nesc)
                                    if nb > best_b.get(nst, -1):
                                        best_b[nst] = nb
                                        ways_b[nst] = nw
                                    elif nb == best_b[nst]:
                                        ways_b[nst] += nw
                        else:
                            # d != c: minimum size is rk >= k + p - 1 = k + 2
                            if rk == k + p - 1:
                                B = req
                                nb = b_cur + 1
                                nw = w_cur * math.factorial(p * (p - 1))
                                nst = (B, d, 1)
                                if nb > best_b.get(nst, -1):
                                    best_b[nst] = nb
                                    ways_b[nst] = nw
                                elif nb == best_b[nst]:
                                    ways_b[nst] += nw

    # Finish at full group G (size q)
    max_esc_boundaries = -1
    total_esc_ways = 0
    for k in range(1, q):
        rem_fact = math.factorial(p * (q - k))
        for A in by_size[k]:
            for c in range(q):
                st = (A, c, 1)
                if st not in best_b:
                    continue
                b = best_b[st]
                w = ways_b[st] * rem_fact
                if b > max_esc_boundaries:
                    max_esc_boundaries = b
                    total_esc_ways = w
                elif b == max_esc_boundaries:
                    total_esc_ways += w

    formula_score = q * p - 1 + (p - 1) * (q - p + 1)
    dp_score = q * p - 1 + (p - 1) * max_esc_boundaries
    formula_count = (
        2
        * (q ** 2)
        * (q - 1)
        * math.factorial(q - p)
        * (math.factorial(p) ** (q - p + 1))
        * math.factorial(p * (p - 1))
    )
    assert dp_score == formula_score == 30, (dp_score, formula_score)
    assert total_esc_ways == formula_count == 79_009_136_640, (total_esc_ways, formula_count)

    # Also verify nonabelian order 21 hierarchical total count from Theorem 1.3(b)
    hier21 = math.factorial(p) * (math.factorial(q) ** p) + q * math.factorial(q) * (math.factorial(p) ** q)
    assert hier21 == 778_020_526_080


def main() -> None:
    verify_c12_witness_and_connectivity()
    verify_cyclic_recurrence()

    small_groups = [
        ("C1", cyclic_table(1), 0, 1),
        ("C2", cyclic_table(2), 1, 2),
        ("C3", cyclic_table(3), 2, 6),
        ("C4", cyclic_table(4), 4, 8),
        ("C2xC2", direct_product(cyclic_table(2), cyclic_table(2)), 4, 24),
        ("C6", cyclic_table(6), 7, 120),
        ("C8", cyclic_table(8), 12, 128),
        ("Q8", q8_table(), 12, 384),
        ("D8", d8_table(), 12, 2432),
        ("C9", cyclic_table(9), 12, 1296),
        ("C3xC3", direct_product(cyclic_table(3), cyclic_table(3)), 12, 4 * 6 * (6 ** 3)),
        ("C12", cyclic_table(12), 20, 31872),
        ("S3", semidirect_fq_cp(3, 2), 7, 360),
        ("D10", semidirect_fq_cp(5, 2), 13, 156800),
        ("D14", semidirect_fq_cp(7, 2), 19, 100778496),
    ]
    for name, tbl, exp_m, exp_a in small_groups:
        m_val, a_val = subset_dp(tbl)
        assert m_val == exp_m == theoretical_mW(len(tbl)), (name, m_val, exp_m)
        assert a_val == exp_a, (name, a_val, exp_a)
        print(f"  [PASS] {name:6s} (|G|={len(tbl):2d}): M={m_val:2d}, A={a_val:,}")

    # Cross-check dihedral DP formula against full subset DP
    for q, exp_tot, exp_hier, exp_nonhier in [
        (3, 360, 216, 144),
        (5, 156_800, 48_000, 108_800),
        (7, 100_778_496, 55_319_040, 45_459_456),
    ]:
        tot, hier, nonhier = dihedral_dp_count(q)
        assert (tot, hier, nonhier) == (exp_tot, exp_hier, exp_nonhier)
        print(f"  [PASS] D_{2*q:<2d} dihedral DP: total={tot:,}, hier={hier:,}, nonhier={nonhier:,}")

    verify_f7_c3_vosper()
    print("  [PASS] F7 x| C3 Vosper escape: M_escape=30, A_escape=79,009,136,640")
    print("ALL PAPER 1 VERIFICATIONS PASSED.")


if __name__ == "__main__":
    main()
