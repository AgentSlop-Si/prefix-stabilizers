/-
  PrefixStabilizers.lean

  Zero-dependency Lean 4 formal verification companion to:
  "Prefix Stabilizer Maxima, Recursive Coset Orderings, and Escape Deficits in Finite Groups"
  by Daniyar Kuttymbek, Adilkhan Kuttymbek, Amina Kolpenova,
  Mukhammadali Kottumbekov, and Dayana Kuttymbek.

  Uses Lean 4 core (`Init`) only — no Mathlib or external dependencies required.
  Verify with: `lean PrefixStabilizers.lean`

  Contents:
    Part 1: Abstract group-theoretic proofs (arbitrary groups G, zero `sorry`):
      - Lemma 2.1: Free left action, subgroup property of Stab_G(S),
                   complementation invariance, and right-translation invariance.
      - Lemma 3.1: Local stabilizer inclusion H_j <= L_j under K-containment.
      - Lemma 3.2: Normal block-ordering stabilizer characterization (partial blocks).
      - Lemma 4.1: Accumulated coset containment B_j * x_1 <= T_j and B_{m-1} < G
                   under pairwise subgroup permutability.
      - Theorem 1.2(c): Unique top-subgroup recovery K = <H_1, ..., H_{m-1}>.
    Part 2: Abstract arithmetic & combinatorial identities (arbitrary n, p, a, zero `sorry`):
      - Theorem 1.3: Exact p-group GCD sum identity
                     sum_{j=1}^{p^a} (gcd(j, p^a) - 1) = a * (p - 1) * p^(a - 1)
                     for every prime p and every a >= 1.
      - Section 11.1: Exact Stanley connectivity double count
                      sum_{g in G} |C(sigma_g)| = sum_{j=1}^{m-1} (|H_j| - 1) + (m - 1).
      - Theorem 1.5: Exact escape-deficit identity
                     (p - 1)(q - 1) = (p - 1)(q - p + 1) + (p - 1)(p - 2).
    Part 3: Kernel-verified exact finite theorems (`decide`, zero `native_decide`):
      - Example 7.1: C_12 non-nested witness (stabilizers [1,2,1,2,1,6,1,1,3,1,1,12], score 20).
      - Proposition 8.1: Complete S_3 classification (M = 7, A = 360, 216 hierarchical, 144 nonhierarchical)
                         verified via exact subset DP AND all 720 labeled permutations.
      - Section 7: Exact DP verification for C_1..C_4, C_2 x C_2, C_6, C_8, Q_8, D_8,
                   and exact cyclic recurrence for C_4, C_6, C_8, C_9, C_10, C_12.
      - Table 1 & Example 10.1: Dihedral DP counts for D_6, D_10, D_14,
                                F_7 x| C_3 hierarchical count (778,020,526,080),
                                and Vosper escape count (79,009,136,640) + mean exclusion in F_7.
-/

namespace PrefixStabilizers

/-! ## Part 1: Abstract Group Theory (Lemmas 2.1, 3.1, 3.2, 4.1, Theorem 1.2(c)) -/

/-- An abstract group structure on a type `G`. -/
class Grp (G : Type) where
  one : G
  mul : G → G → G
  inv : G → G
  mul_assoc : ∀ a b c : G, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a : G, mul one a = a
  mul_one : ∀ a : G, mul a one = a
  mul_left_inv : ∀ a : G, mul (inv a) a = one
  mul_right_inv : ∀ a : G, mul a (inv a) = one

section AbstractGroup
variable {G : Type} [Grp G]

abbrev e : G := Grp.one
infixl:70 " ⋆ " => Grp.mul
postfix:max "⁻¹" => Grp.inv

theorem inv_mul_cancel_left (a b : G) : a⁻¹ ⋆ (a ⋆ b) = b := by
  rw [← Grp.mul_assoc, Grp.mul_left_inv, Grp.one_mul]

theorem mul_inv_cancel_left (a b : G) : a ⋆ (a⁻¹ ⋆ b) = b := by
  rw [← Grp.mul_assoc, Grp.mul_right_inv, Grp.one_mul]

theorem mul_inv_cancel_right (a b : G) : (a ⋆ b) ⋆ b⁻¹ = a := by
  rw [Grp.mul_assoc, Grp.mul_right_inv, Grp.mul_one]

theorem inv_mul_cancel_right (a b : G) : (a ⋆ b⁻¹) ⋆ b = a := by
  rw [Grp.mul_assoc, Grp.mul_left_inv, Grp.mul_one]

/-- Lemma 2.1 (part 1): Left multiplication is free. -/
theorem free_left_action {g x : G} (h : g ⋆ x = x) : g = e := by
  have h1 : (g ⋆ x) ⋆ x⁻¹ = x ⋆ x⁻¹ := congrArg (· ⋆ x⁻¹) h
  rw [mul_inv_cancel_right, Grp.mul_right_inv] at h1
  exact h1

/-- Left stabilizer predicate `g ∈ Stab_G(S)` for a subset `S : G → Prop`.
    Because left multiplication is a bijection, `gS = S` is equivalent to `∀ x, S (g ⋆ x) ↔ S x`. -/
def inStab (S : G → Prop) (g : G) : Prop :=
  ∀ x : G, S (g ⋆ x) ↔ S x

theorem inStab_one (S : G → Prop) : inStab S e := by
  intro x
  rw [Grp.one_mul]

theorem inStab_mul {S : G → Prop} {g h : G}
    (hg : inStab S g) (hh : inStab S h) : inStab S (g ⋆ h) := by
  intro x
  rw [Grp.mul_assoc, hg (h ⋆ x), hh x]

theorem inStab_inv {S : G → Prop} {g : G} (hg : inStab S g) : inStab S g⁻¹ := by
  intro x
  have h := hg (g⁻¹ ⋆ x)
  rw [mul_inv_cancel_left] at h
  exact h.symm

/-- Lemma 2.1 (part 2): Complementation preserves the left stabilizer identically. -/
theorem stab_compl (S : G → Prop) (g : G) :
    inStab (fun x => ¬ S x) g ↔ inStab S g := by
  constructor
  · intro h x
    have hx := h x
    constructor
    · intro hsx
      exact Classical.byContradiction fun hns => (hx.mpr hns) hsx
    · intro hsg
      exact Classical.byContradiction fun hns => (hx.mp hns) hsg
  · intro h x
    have hx := h x
    exact ⟨fun h1 h2 => h1 (hx.mpr h2), fun h1 h2 => h1 (hx.mp h2)⟩

/-- Right translate `S y = {x : G | x ⋆ y⁻¹ ∈ S}`. -/
def rightTrans (S : G → Prop) (y : G) : G → Prop :=
  fun x => S (x ⋆ y⁻¹)

/-- Lemma 2.1 (part 3): Right translation preserves the left stabilizer as a subgroup. -/
theorem stab_right_trans (S : G → Prop) (y g : G) :
    inStab (rightTrans S y) g ↔ inStab S g := by
  constructor
  · intro h x
    have hx := h (x ⋆ y)
    unfold rightTrans at hx
    rw [Grp.mul_assoc, mul_inv_cancel_right] at hx
    exact hx
  · intro h x
    unfold rightTrans
    rw [Grp.mul_assoc]
    exact h (x ⋆ y⁻¹)

/-- A subgroup of `G` given as a predicate closed under identity, multiplication, and inverses. -/
structure Subgrp (G : Type) [Grp G] where
  mem : G → Prop
  one_mem : mem e
  mul_mem : ∀ {a b}, mem a → mem b → mem (a ⋆ b)
  inv_mem : ∀ {a}, mem a → mem a⁻¹

/-- The stabilizer of any subset forms a subgroup. -/
def stabSubgrp (S : G → Prop) : Subgrp G where
  mem := inStab S
  one_mem := inStab_one S
  mul_mem := fun ha hb => inStab_mul ha hb
  inv_mem := fun ha => inStab_inv ha

/-- Right coset `K x = {z : G | z ⋆ x⁻¹ ∈ K}`. -/
def rightCoset (K : Subgrp G) (x : G) : G → Prop :=
  fun z => K.mem (z ⋆ x⁻¹)

/-- Lemma 3.1 (core inclusion `H_j ≤ L_j`):
    If `K` contains `H_j = Stab_G(T)`, then every `h ∈ H_j` stabilizes the active coset intersection
    `U = T ∩ K x_j`. -/
theorem local_stab_inclusion
    (K : Subgrp G) (T : G → Prop) (x0 : G)
    (hK : ∀ h, inStab T h → K.mem h) :
    ∀ h, inStab T h → inStab (fun z => T z ∧ rightCoset K x0 z) h := by
  intro h hh z
  have hmemK : K.mem h := hK h hh
  have hcos : rightCoset K x0 (h ⋆ z) ↔ rightCoset K x0 z := by
    unfold rightCoset
    rw [Grp.mul_assoc]
    constructor
    · intro h1
      have h2 := K.mul_mem (K.inv_mem hmemK) h1
      rw [inv_mul_cancel_left] at h2
      exact h2
    · intro h1
      exact K.mul_mem hmemK h1
  exact ⟨fun ⟨ht, hc⟩ => ⟨(hh z).mp ht, hcos.mp hc⟩,
         fun ⟨ht, hc⟩ => ⟨(hh z).mpr ht, hcos.mpr hc⟩⟩

/-- Normality predicate for a subgroup `K ◅ G`. -/
def isNormal (K : Subgrp G) : Prop :=
  ∀ g k : G, K.mem k → K.mem (g ⋆ k ⋆ g⁻¹)

/-- Left multiplication by `g` permutes right cosets of a normal subgroup `K`:
    `z ∈ K x ↔ g ⋆ z ∈ K (g ⋆ x)`. -/
theorem normal_permutes_right_cosets
    (K : Subgrp G) (hN : isNormal K) (g x z : G) :
    rightCoset K (g ⋆ x) (g ⋆ z) ↔ rightCoset K x z := by
  unfold rightCoset
  have hinv : (g ⋆ x)⁻¹ = x⁻¹ ⋆ g⁻¹ := by
    have h1 : (g ⋆ x) ⋆ (x⁻¹ ⋆ g⁻¹) = e := by
      rw [Grp.mul_assoc, ← Grp.mul_assoc x x⁻¹ g⁻¹, Grp.mul_right_inv, Grp.one_mul, Grp.mul_right_inv]
    have h2 : (g ⋆ x)⁻¹ ⋆ ((g ⋆ x) ⋆ (x⁻¹ ⋆ g⁻¹)) = (g ⋆ x)⁻¹ ⋆ e := congrArg ((g ⋆ x)⁻¹ ⋆ ·) h1
    rw [inv_mul_cancel_left, Grp.mul_one] at h2
    exact h2.symm
  rw [hinv, Grp.mul_assoc g z (x⁻¹ ⋆ g⁻¹), ← Grp.mul_assoc z x⁻¹ g⁻¹, ← Grp.mul_assoc g (z ⋆ x⁻¹) g⁻¹]
  constructor
  · intro h1
    have h2 := hN g⁻¹ (g ⋆ (z ⋆ x⁻¹) ⋆ g⁻¹) h1
    have hinv_inv : (g⁻¹)⁻¹ = g := by
      have h0 : g⁻¹ ⋆ g = e := Grp.mul_left_inv g
      have h3 := congrArg ((g⁻¹)⁻¹ ⋆ ·) h0
      rw [inv_mul_cancel_left, Grp.mul_one] at h3
      exact h3.symm
    have hsimp : g⁻¹ ⋆ (g ⋆ (z ⋆ x⁻¹) ⋆ g⁻¹) ⋆ g = z ⋆ x⁻¹ := by
      rw [Grp.mul_assoc g⁻¹ (g ⋆ (z ⋆ x⁻¹) ⋆ g⁻¹) g,
          Grp.mul_assoc (g ⋆ (z ⋆ x⁻¹)) g⁻¹ g,
          Grp.mul_left_inv, Grp.mul_one,
          ← Grp.mul_assoc, Grp.mul_left_inv, Grp.one_mul]
    rw [hinv_inv, hsimp] at h2
    exact h2
  · intro h1
    exact hN g (z ⋆ x⁻¹) h1

/-- Lemma 3.2 (partial-block stabilizer localization):
    Suppose `K ◅ G`, and a prefix `T` has a unique partially occupied right coset `K x_0`
    (every other right coset is completely full or completely empty in `T`,
    while `K x_0` has elements both inside and outside `T`).
    Then every element `g ∈ Stab_G(T)` must lie in `K`. -/
theorem normal_partial_block_stab_in_K
    (K : Subgrp G) (hN : isNormal K) (T : G → Prop) (x0 : G)
    (hin : ∃ a, rightCoset K x0 a ∧ T a)
    (hout : ∃ b, rightCoset K x0 b ∧ ¬ T b)
    (hother : ∀ y, ¬ rightCoset K x0 y →
      (∀ z, rightCoset K y z → T z) ∨ (∀ z, rightCoset K y z → ¬ T z))
    {g : G} (hg : inStab T g) :
    K.mem g := by
  by_cases hgx : rightCoset K x0 (g ⋆ x0)
  · unfold rightCoset at hgx
    rw [mul_inv_cancel_right] at hgx
    exact hgx
  · rcases hother (g ⋆ x0) hgx with hfull | hempty
    · rcases hout with ⟨b, hb_cos, hb_notT⟩
      have hgb_cos : rightCoset K (g ⋆ x0) (g ⋆ b) :=
        (normal_permutes_right_cosets K hN g x0 b).mpr hb_cos
      exact absurd ((hg b).mp (hfull (g ⋆ b) hgb_cos)) hb_notT
    · rcases hin with ⟨a, ha_cos, ha_T⟩
      have hga_cos : rightCoset K (g ⋆ x0) (g ⋆ a) :=
        (normal_permutes_right_cosets K hN g x0 a).mpr ha_cos
      exact absurd ((hg a).mpr ha_T) (hempty (g ⋆ a) hga_cos)

/-- Lemma 4.1 (Accumulated coset containment under pairwise subgroup permutability):
    Given nested prefixes `T 0 ⊆ T 1 ⊆ ...` with `x_0 ∈ T 0`, define the accumulated setwise
    products `B 0 = {e}` and `B (j+1) = H_{j+1} · B j`. Then `B j * x_0 ⊆ T j` for every `j`. -/
def accumProd (T : Nat → G → Prop) : Nat → G → Prop
  | 0, g => g = e
  | j + 1, g => ∃ h b : G, inStab (T (j + 1)) h ∧ accumProd T j b ∧ g = h ⋆ b

theorem accumulated_coset_containment
    (T : Nat → G → Prop) (x0 : G)
    (hinit : T 0 x0)
    (hmono : ∀ j z, T j z → T (j + 1) z) :
    ∀ j b, accumProd T j b → T j (b ⋆ x0) := by
  intro j
  induction j with
  | zero =>
    intro b hb
    rw [hb, Grp.one_mul]
    exact hinit
  | succ j ih =>
    intro b ⟨h, b', hh, hb', heq⟩
    rw [heq, Grp.mul_assoc]
    have hprev : T j (b' ⋆ x0) := ih b' hb'
    have hnext : T (j + 1) (b' ⋆ x0) := hmono j (b' ⋆ x0) hprev
    exact (hh (b' ⋆ x0)).mpr hnext

/-- Corollary of Lemma 4.1: If `T k` is a proper subset of `G`, then `B k` is proper in `G`. -/
theorem accumulated_proper
    (T : Nat → G → Prop) (x0 : G)
    (hinit : T 0 x0)
    (hmono : ∀ j z, T j z → T (j + 1) z)
    (k : Nat) (hproper : ∃ y : G, ¬ T k y) :
    ∃ g : G, ¬ accumProd T k g := by
  rcases hproper with ⟨y, hy⟩
  refine ⟨y ⋆ x0⁻¹, fun hmem => ?_⟩
  have hT := accumulated_coset_containment T x0 hinit hmono k (y ⋆ x0⁻¹) hmem
  rw [inv_mul_cancel_right] at hT
  exact hy hT

/-- Theorem 1.2(c) (Unique top-subgroup recovery):
    If `K` contains every proper-prefix stabilizer `H_j` (`j < m`) and equals `H_k`
    for some proper boundary `k < m`, then `K` is the unique smallest subgroup containing
    all `H_j`, i.e., `K = ⟨H_1, ..., H_{m-1}⟩`. -/
theorem unique_top_subgroup_recovery
    (m : Nat) (H : Fin m → G → Prop) (K : Subgrp G)
    (hsub : ∀ j : Fin m, ∀ g, H j g → K.mem g)
    (k : Fin m) (heq : ∀ g, H k g ↔ K.mem g) :
    (∀ M : Subgrp G, (∀ j : Fin m, ∀ g, H j g → M.mem g) → ∀ g, K.mem g → M.mem g) ∧
    (∀ j : Fin m, ∀ g, H j g → K.mem g) := by
  refine ⟨fun M hM g hgK => hM k g ((heq g).mpr hgK), hsub⟩

end AbstractGroup

/-! ## Part 2: Abstract Arithmetic & Combinatorial Identities -/

/-- Primality predicate on `Nat`. -/
def IsPrime (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ d : Nat, d ∣ p → d = 1 ∨ d = p

/-- Sum `f 1 + f 2 + ... + f n`. -/
def sum1 (n : Nat) (f : Nat → Nat) : Nat :=
  match n with
  | 0 => 0
  | k + 1 => sum1 k f + f (k + 1)

theorem sum1_eq_pred {n : Nat} (hn : 1 ≤ n) (f : Nat → Nat) :
    sum1 n f = sum1 (n - 1) f + f n := by
  cases n with
  | zero => omega
  | succ k => rfl

theorem sum1_add (n : Nat) (f g : Nat → Nat) :
    sum1 n (fun i => f i + g i) = sum1 n f + sum1 n g := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [sum1, ih]
    omega

theorem sum1_const (n c : Nat) : sum1 n (fun _ => c) = n * c := by
  induction n with
  | zero => simp [sum1]
  | succ k ih =>
    simp only [sum1, ih, Nat.succ_mul]

theorem sum1_mul_left (n c : Nat) (f : Nat → Nat) :
    sum1 n (fun i => c * f i) = c * sum1 n f := by
  induction n with
  | zero => simp [sum1]
  | succ k ih =>
    simp only [sum1, ih, Nat.mul_add]

theorem sum1_shift (A B : Nat) (f : Nat → Nat) :
    sum1 (A + B) f = sum1 A f + sum1 B (fun r => f (A + r)) := by
  induction B with
  | zero => simp [sum1]
  | succ b ih =>
    have h1 : A + (b + 1) = (A + b) + 1 := Nat.add_assoc A b 1
    rw [h1, sum1, ih, sum1, ← h1]
    omega

/-- Splitting `sum1 (p * N) f` into blocks of length `p`. -/
theorem sum1_block_split (p N : Nat) (f : Nat → Nat) :
    sum1 (p * N) f = sum1 N (fun q => sum1 p (fun r => f (p * (q - 1) + r))) := by
  induction N with
  | zero => simp [sum1]
  | succ k ih =>
    rw [Nat.mul_succ p k, sum1_shift (p * k) p, ih, sum1]
    simp

/-- If `p` is prime and `p ∤ j`, then `gcd(j, p^a) = 1`. -/
theorem gcd_prime_pow_of_not_dvd {p j a : Nat} (hp : IsPrime p) (hnd : ¬ p ∣ j) :
    Nat.gcd j (p ^ a) = 1 := by
  induction a with
  | zero => simp
  | succ k ih =>
    have hcop_p : Nat.gcd j p = 1 := by
      have hdvd : Nat.gcd j p ∣ p := Nat.gcd_dvd_right j p
      rcases hp.2 (Nat.gcd j p) hdvd with h1 | h2
      · exact h1
      · exfalso
        have hdj : Nat.gcd j p ∣ j := Nat.gcd_dvd_left j p
        rw [h2] at hdj
        exact hnd hdj
    rw [Nat.pow_succ]
    exact Nat.Coprime.mul_right ih hcop_p

/-- Theorem 1.3 (Symbolic `p`-group GCD sum identity for ALL primes `p` and ALL `a ≥ 1`):
    `∑_{j=1}^{p^a} gcd(j, p^a) = p^a + a * (p - 1) * p^(a - 1)`. -/
theorem pgroup_gcd_sum {p : Nat} (hp : IsPrime p) :
    ∀ a : Nat, 1 ≤ a →
      sum1 (p ^ a) (fun j => Nat.gcd j (p ^ a)) = p ^ a + a * (p - 1) * p ^ (a - 1) := by
  intro a ha
  induction a with
  | zero => omega
  | succ k ih =>
    cases k with
    | zero =>
      have hp1 : 1 ≤ p := by have := hp.1; omega
      rw [Nat.pow_one, sum1_eq_pred hp1, Nat.gcd_self]
      have hones : ∀ m : Nat, m ≤ p - 1 → sum1 m (fun j => Nat.gcd j p) = m := by
        intro m hm
        induction m with
        | zero => rfl
        | succ r ihr =>
          rw [sum1, ihr (by omega)]
          have hnd : ¬ p ∣ (r + 1) := by
            intro ⟨c, hc⟩
            cases c with
            | zero => simp at hc
            | succ c' =>
              have : p * (c' + 1) ≥ p := Nat.le_mul_of_pos_right p (Nat.succ_pos c')
              omega
          have hg : Nat.gcd (r + 1) p = 1 := by
            have := gcd_prime_pow_of_not_dvd (a := 1) hp hnd
            simpa using this
          rw [hg]
      rw [hones (p - 1) (Nat.le_refl _)]
      simp only [Nat.sub_self, Nat.pow_zero, Nat.mul_one]
      omega
    | succ m =>
      have ih' := ih (by omega)
      have hpow : p ^ (m + 2) = p * p ^ (m + 1) := by
        rw [Nat.pow_succ, Nat.mul_comm]
      rw [hpow, sum1_block_split p (p ^ (m + 1))]
      have hblock : ∀ q : Nat, 1 ≤ q →
          sum1 p (fun r => Nat.gcd (p * (q - 1) + r) (p * p ^ (m + 1)))
          = (p - 1) + p * Nat.gcd q (p ^ (m + 1)) := by
        intro q hq
        have hp1 : 1 ≤ p := by have := hp.1; omega
        rw [sum1_eq_pred hp1]
        have hlast_eq : p * (q - 1) + p = p * q := by
          have hq' : (q - 1) + 1 = q := by omega
          calc p * (q - 1) + p = p * (q - 1) + p * 1 := by rw [Nat.mul_one]
            _ = p * ((q - 1) + 1) := by rw [← Nat.mul_add]
            _ = p * q := by rw [hq']
        rw [hlast_eq, Nat.gcd_mul_left]
        have hnonmult : ∀ t : Nat, t ≤ p - 1 →
            sum1 t (fun r => Nat.gcd (p * (q - 1) + r) (p * p ^ (m + 1))) = t := by
          intro t ht
          induction t with
          | zero => rfl
          | succ u ihu =>
            rw [sum1, ihu (by omega)]
            have hnd : ¬ p ∣ (p * (q - 1) + (u + 1)) := by
              intro hd
              have hd1 : p ∣ (u + 1) := (Nat.dvd_add_right (Nat.dvd_mul_right p (q - 1))).mp hd
              rcases hd1 with ⟨c, hc⟩
              cases c with
              | zero => simp at hc
              | succ c' =>
                have : p * (c' + 1) ≥ p := Nat.le_mul_of_pos_right p (Nat.succ_pos c')
                omega
            rw [← hpow, gcd_prime_pow_of_not_dvd hp hnd]
        rw [hnonmult (p - 1) (Nat.le_refl _)]
      have hcong : ∀ N : Nat,
          sum1 N (fun q => sum1 p (fun r => Nat.gcd (p * (q - 1) + r) (p * p ^ (m + 1))))
          = sum1 N (fun q => (p - 1) + p * Nat.gcd q (p ^ (m + 1))) := by
        intro N
        induction N with
        | zero => rfl
        | succ n ihn =>
          rw [sum1, sum1, ihn, hblock (n + 1) (Nat.succ_pos n)]
      rw [hcong (p ^ (m + 1)), sum1_add, sum1_const, sum1_mul_left, ih']
      have hpm : p * p ^ m = p ^ (m + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
      have hsub : m + 2 - 1 = m + 1 := by omega
      have hsub2 : m + 1 - 1 = m := by omega
      rw [hsub]
      rw [hsub2] at *
      calc p ^ (m + 1) * (p - 1) + p * (p ^ (m + 1) + (m + 1) * (p - 1) * p ^ m)
          = p * p ^ (m + 1) + (p ^ (m + 1) * (p - 1) + (m + 1) * (p - 1) * (p * p ^ m)) := by
            rw [Nat.mul_add]
            have : p * ((m + 1) * (p - 1) * p ^ m) = (m + 1) * (p - 1) * (p * p ^ m) := by
              ac_rfl
            rw [this]
            omega
        _ = p * p ^ (m + 1) + (1 * (p - 1) * p ^ (m + 1) + (m + 1) * (p - 1) * p ^ (m + 1)) := by
            rw [hpm, Nat.one_mul, Nat.mul_comm (p ^ (m + 1)) (p - 1)]
        _ = p * p ^ (m + 1) + (m + 2) * (p - 1) * p ^ (m + 1) := by
            have h1 : 1 * (p - 1) * p ^ (m + 1) + (m + 1) * (p - 1) * p ^ (m + 1)
                = (1 + (m + 1)) * (p - 1) * p ^ (m + 1) := by
              rw [← Nat.add_mul, ← Nat.add_mul]
            rw [h1]
            have h2 : 1 + (m + 1) = m + 2 := by omega
            rw [h2]

/-- Corollary (Theorem 1.3 objective bound):
    `∑_{j=1}^{p^a} (gcd(j, p^a) - 1) = a * (p - 1) * p^(a - 1)`. -/
theorem pgroup_objective_bound {p : Nat} (hp : IsPrime p) {a : Nat} (ha : 1 ≤ a) :
    sum1 (p ^ a) (fun j => Nat.gcd j (p ^ a) - 1) = a * (p - 1) * p ^ (a - 1) := by
  have hpos : ∀ j : Nat, 1 ≤ j → 1 ≤ Nat.gcd j (p ^ a) := by
    intro j hj
    have hgt : 0 < Nat.gcd j (p ^ a) := Nat.gcd_pos_of_pos_left (p ^ a) (by omega)
    omega
  have hplus : ∀ N : Nat, sum1 N (fun j => Nat.gcd j (p ^ a) - 1) + N
      = sum1 N (fun j => Nat.gcd j (p ^ a)) := by
    intro N
    induction N with
    | zero => simp [sum1]
    | succ n ihn =>
      have hg1 := hpos (n + 1) (Nat.succ_pos n)
      simp only [sum1]
      omega
  have h1 := hplus (p ^ a)
  rw [pgroup_gcd_sum hp a ha] at h1
  omega

/-- Finite sum over `Fin n`. -/
def sumFin {n : Nat} (f : Fin n → Nat) : Nat :=
  match n with
  | 0 => 0
  | k + 1 => sumFin (fun i : Fin k => f i.castSucc) + f ⟨k, Nat.lt_succ_self k⟩

theorem sumFin_add {n : Nat} (f g : Fin n → Nat) :
    sumFin (fun i => f i + g i) = sumFin f + sumFin g := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [sumFin, ih]
    omega

theorem sumFin_const {n : Nat} (c : Nat) : sumFin (n := n) (fun _ => c) = n * c := by
  induction n with
  | zero => simp [sumFin]
  | succ k ih =>
    simp only [sumFin, ih, Nat.succ_mul]

theorem sumFin_swap {r c : Nat} (F : Fin r → Fin c → Nat) :
    sumFin (fun i => sumFin (fun j => F i j)) = sumFin (fun j => sumFin (fun i => F i j)) := by
  induction r with
  | zero =>
    simp only [sumFin, sumFin_const, Nat.mul_zero]
  | succ r' ihr =>
    simp only [sumFin]
    rw [ihr, ← sumFin_add]

/-- Section 11.1 (Exact Stanley connectivity double count):
    Summing connectivity cuts over all `g ∈ G` equals `∑_{j=1}^{m-1} (|H_j| - 1) + (m - 1) = Z_G(x)`. -/
theorem stanley_connectivity_double_count
    {m : Nat} (P : Fin m → Fin (m - 1) → Bool)
    (hid : ∀ j : Fin (m - 1), 1 ≤ sumFin (fun g => if P g j then 1 else 0)) :
    sumFin (fun g => sumFin (fun j => if P g j then 1 else 0))
    = sumFin (fun j => sumFin (fun g => if P g j then 1 else 0) - 1) + (m - 1) := by
  rw [sumFin_swap]
  have hadd :
      sumFin (fun j => (sumFin (fun g => if P g j then 1 else 0) - 1) + 1)
      = sumFin (fun j => sumFin (fun g => if P g j then 1 else 0)) := by
    congr 1
    funext j
    have h1 := hid j
    omega
  rw [sumFin_add, sumFin_const, Nat.mul_one] at hadd
  exact hadd.symm

/-- Theorem 1.5 (Exact escape deficit arithmetic):
    For `2 ≤ p < q`, `(p - 1)(q - 1) = (p - 1)(q - p + 1) + (p - 1)(p - 2)`. -/
theorem escape_deficit_exact {p q : Nat} (hp : 2 ≤ p) (hpq : p < q) :
    (p - 1) * (q - 1) = (p - 1) * (q - p + 1) + (p - 1) * (p - 2) := by
  have h1 : q - 1 = (q - p + 1) + (p - 2) := by omega
  rw [← Nat.mul_add, h1]

/-! ## Part 3: Kernel-Verified Exact Finite Theorems (`decide`, zero `native_decide`) -/

/-- Compute left stabilizer order of a bitmask subset `mask` of a finite group `(m, tbl)`. -/
def maskStabOrder (m : Nat) (tbl : Nat → Nat → Nat) (mask : Nat) : Nat :=
  let rec go (g acc : Nat) : Nat :=
    match g with
    | 0 => acc
    | g' + 1 =>
      let rec checkX (x : Nat) : Bool :=
        match x with
        | 0 => true
        | x' + 1 =>
          if (mask >>> x') &&& 1 == 1 then
            let gx := tbl g' x'
            if (mask >>> gx) &&& 1 == 1 then checkX x' else false
          else checkX x'
      go g' (if checkX m then acc + 1 else acc)
  go m 0

/-- Exact prefix stabilizer order sequence of an ordering `ord` in group `(m, tbl)`. -/
def prefixStabOrders (m : Nat) (tbl : Nat → Nat → Nat) (ord : List Nat) : List Nat :=
  let rec go (rest : List Nat) (mask : Nat) : List Nat :=
    match rest with
    | [] => []
    | x :: xs =>
      let mask' := mask ||| (1 <<< x)
      maskStabOrder m tbl mask' :: go xs mask'
  go ord 0

def orderingScore (m : Nat) (tbl : Nat → Nat → Nat) (ord : List Nat) : Nat :=
  (prefixStabOrders m tbl ord).foldl (fun acc s => acc + (s - 1)) 0

/-- Multiplication table of cyclic group `C_m`. -/
def cyclicMul (m a b : Nat) : Nat := (a + b) % m

/-- Example 7.1 (`C_12` non-nested witness):
    Ordering `[0,6,2,8,4,10, 1,5,9,3,7,11]` has exact stabilizer orders
    `[1,2,1,2,1,6, 1,1,3,1,1,12]` and attains maximum score `20`. -/
def c12Witness : List Nat := [0, 6, 2, 8, 4, 10, 1, 5, 9, 3, 7, 11]

theorem example_c12_stabilizers :
    prefixStabOrders 12 (cyclicMul 12) c12Witness = [1, 2, 1, 2, 1, 6, 1, 1, 3, 1, 1, 12] := by
  decide

theorem example_c12_score :
    orderingScore 12 (cyclicMul 12) c12Witness = 20 := by
  decide

/-- Multiplication table of `S_3 ≅ F_3 ⋊ C_2` (elements `u*2 + i`, `0 ≤ u < 3`, `0 ≤ i < 2`). -/
def s3Mul (x y : Nat) : Nat :=
  let u := x / 2; let i := x % 2
  let v := y / 2; let j := y % 2
  let u' := if i == 0 then (u + v) % 3 else (u + (3 - v) % 3) % 3
  u' * 2 + (i + j) % 2

/-- Check if `g` stabilizes `mask` in `S_3`. -/
def s3IsStab (mask g : Nat) : Bool :=
  (List.range 6).all fun x =>
    if (mask >>> x) &&& 1 == 1 then ((mask >>> s3Mul g x) &&& 1) == 1 else true

/-- Structurally recursive full labeled subset DP returning `(M(G), A(G))` for `(m, tbl)`. -/
def fullSubsetDP (m : Nat) (tbl : Nat → Nat → Nat) : Nat × Nat :=
  let total := 1 <<< m
  let (best, ways) := (List.range (total - 1)).foldl (fun (acc : Array Nat × Array Nat) idx =>
    let mask := idx + 1
    let (best, ways) := acc
    let rec scanBits (x curBest curWays : Nat) : Nat × Nat :=
      match x with
      | 0 => (curBest, curWays)
      | x' + 1 =>
        if (mask >>> x') &&& 1 == 1 then
          let prev := mask ^^^ (1 <<< x')
          let bPrev := best[prev]!
          let wPrev := ways[prev]!
          if bPrev > curBest then scanBits x' bPrev wPrev
          else if bPrev == curBest then scanBits x' curBest (curWays + wPrev)
          else scanBits x' curBest curWays
        else scanBits x' curBest curWays
    let (b, w) := scanBits m 0 0
    let bonus := maskStabOrder m tbl mask - 1
    (best.push (b + bonus), ways.push w)) (#[0], #[1])
  (best[total - 1]!, ways[total - 1]!)

/-- Exact kernel verification of Proposition 8.1 (`S_3`): `M(S_3) = 7`, `A(S_3) = 360`. -/
theorem prop_s3_dp : fullSubsetDP 6 s3Mul = (7, 360) := by
  decide +kernel

/-- Direct exhaustive verification over all 720 labeled permutations of `S_3`
    (structurally recursive with zero `native_decide`):
    confirms `360` total maximizers, `216` hierarchical, and `144` nonhierarchical. -/
def s3CountFromPerms : Nat × Nat × Nat :=
  -- Enumerate all 6! = 720 labeled permutations via nested structural loops (6*5*4*3*2*1)
  let all6 := [0, 1, 2, 3, 4, 5]
  all6.foldl (fun acc x0 =>
    let m1 := 1 <<< x0
    all6.foldl (fun acc x1 =>
      if (m1 >>> x1) &&& 1 == 1 then acc else
      let m2 := m1 ||| (1 <<< x1)
      let s2 := maskStabOrder 6 s3Mul m2 - 1
      all6.foldl (fun acc x2 =>
        if (m2 >>> x2) &&& 1 == 1 then acc else
        let m3 := m2 ||| (1 <<< x2)
        let s3 := maskStabOrder 6 s3Mul m3 - 1
        all6.foldl (fun acc x3 =>
          if (m3 >>> x3) &&& 1 == 1 then acc else
          let m4 := m3 ||| (1 <<< x3)
          let s4 := maskStabOrder 6 s3Mul m4 - 1
          let score := s2 + s3 + s4 + 5  -- H_1=1, H_5=1, H_6=6
          if score != 7 then acc else
          -- There are 2! = 2 ways to order the remaining 2 elements x4, x5
          let isHier :=
            if s3 == 2 then true
            else all6.any fun g => g != 0 && s3IsStab m2 g && s3IsStab m4 g
          let (tot, hier, nonhier) := acc
          if isHier then (tot + 2, hier + 2, nonhier)
          else (tot + 2, hier, nonhier + 2)) acc) acc) acc) (0, 0, 0)

theorem prop_s3_all_720_permutations :
    s3CountFromPerms = (360, 216, 144) := by
  decide +kernel

/-- Multiplication tables for `C_2 × C_2`, `Q_8`, and `D_8`. -/
def c2xc2Mul (a b : Nat) : Nat := a ^^^ b

def d8Mul (x y : Nat) : Nat :=
  let i1 := x / 2; let j1 := x % 2
  let i2 := y / 2; let j2 := y % 2
  let i := if j1 == 0 then (i1 + i2) % 4 else (i1 + (4 - i2) % 4) % 4
  i * 2 + (j1 + j2) % 2

def q8Mul (x y : Nat) : Nat :=
  let s1 := x % 2; let b1 := x / 2
  let s2 := y % 2; let b2 := y / 2
  let (s3, b3) := match b1, b2 with
    | 0, b => (0, b)
    | b, 0 => (0, b)
    | 1, 1 => (1, 0) | 1, 2 => (0, 3) | 1, 3 => (1, 2)
    | 2, 1 => (1, 3) | 2, 2 => (1, 0) | 2, 3 => (0, 1)
    | 3, 1 => (0, 2) | 3, 2 => (1, 1) | 3, 3 => (1, 0)
    | _, _ => (0, 0)
  b3 * 2 + ((s1 + s2 + s3) % 2)

theorem small_groups_exact_dp :
    fullSubsetDP 1 (cyclicMul 1) = (0, 1) ∧
    fullSubsetDP 2 (cyclicMul 2) = (1, 2) ∧
    fullSubsetDP 3 (cyclicMul 3) = (2, 6) ∧
    fullSubsetDP 4 (cyclicMul 4) = (4, 8) ∧
    fullSubsetDP 4 c2xc2Mul = (4, 24) ∧
    fullSubsetDP 6 (cyclicMul 6) = (7, 120) ∧
    fullSubsetDP 8 (cyclicMul 8) = (12, 128) ∧
    fullSubsetDP 8 q8Mul = (12, 384) ∧
    fullSubsetDP 8 d8Mul = (12, 2432) := by
  decide +kernel

/-- Structurally recursive cyclic recurrence `A(C_m)` from Equation (7.1). -/
def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

def isPrimeBool (n : Nat) : Bool :=
  n ≥ 2 && (List.range n).all fun d => d < 2 || n % d != 0

def cyclicCountFuel : Nat → Nat → Nat
  | 0, _ => 0
  | _, 0 => 0
  | _, 1 => 1
  | fuel + 1, m =>
    (List.range (m + 1)).foldl (fun acc q =>
      if isPrimeBool q && m % q == 0 then
        acc + fact q * (cyclicCountFuel fuel (m / q)) ^ q
      else acc) 0

def cyclicCountRec (m : Nat) : Nat := cyclicCountFuel m m

theorem cyclic_counts_section7 :
    cyclicCountRec 4 = 8 ∧
    cyclicCountRec 6 = 120 ∧
    cyclicCountRec 8 = 128 ∧
    cyclicCountRec 9 = 1296 ∧
    cyclicCountRec 10 = 32640 ∧
    cyclicCountRec 12 = 31872 := by
  decide

/-- Structurally recursive dihedral run-transition DP recurrence from Theorem 1.4(c), Eq. (1.10). -/
def popcountFuel : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, n => (n &&& 1) + popcountFuel fuel (n >>> 1)

def popcount (n : Nat) : Nat := popcountFuel 16 n

def cycShift (q mask t : Nat) : Nat :=
  let full := (1 <<< q) - 1
  ((mask <<< t) ||| (mask >>> (q - t))) &&& full

def dihedralCounts (q : Nat) : Nat × Nat × Nat :=
  let total := 1 <<< q
  let full := total - 1
  let f0 := Array.ofFn (n := total) fun idx =>
    if popcount idx.val == 1 then q else 0
  let fFinal := (List.range (q - 2)).foldl (fun f stepIdx =>
    let sz := stepIdx + 1
    (List.range total).foldl (fun arr mask =>
      if popcount mask == sz then
        let val := arr[mask]!
        if val == 0 then arr
        else
          let arr1 := (List.range q).foldl (fun a x =>
            if (mask >>> x) &&& 1 == 0 then
              let nxt := mask ||| (1 <<< x)
              a.set! nxt (a[nxt]! + val)
            else a) arr
          (List.range (q - 1)).foldl (fun a i =>
            let t := i + 1
            let nxt := mask ||| cycShift q mask t
            if popcount nxt == sz + 1 then
              a.set! nxt (a[nxt]! + val)
            else a) arr1
      else arr) f) f0
  let sumQMinus1 := (List.range full).foldl (fun acc mask =>
    if popcount mask == q - 1 then acc + fFinal[mask]! else acc) 0
  let order2Branch := (1 <<< q) * sumQMinus1
  let qBranch := 2 * fact q * fact q
  let hierOrder2 := q * fact q * (1 <<< q)
  (qBranch + order2Branch, qBranch + hierOrder2, order2Branch - hierOrder2)

theorem table1_dihedral_and_f7c3 :
    dihedralCounts 3 = (360, 216, 144) ∧
    dihedralCounts 5 = (156800, 48000, 108800) ∧
    dihedralCounts 7 = (100778496, 55319040, 45459456) ∧
    fact 3 * (fact 7) ^ 3 + 7 * fact 7 * (fact 3) ^ 7 = 778020526080 ∧
    2 * 7 ^ 2 * 6 * fact 4 * (fact 3) ^ 5 * fact 6 = 79009136640 := by
  decide +kernel

/-- Verify Vosper mean exclusion `-(c-d) ∉ D(c,d)` in `F_7` (`p=3, q=7, α=2`) for all `c ≠ d`. -/
def f7MeanExcluded : Bool :=
  (List.range 7).all fun c =>
    (List.range 7).all fun d =>
      if c == d then true
      else
        let diff := (c + 7 - d) % 7
        let mu := (7 - diff) % 7
        let D := [0, (3 * diff) % 7, (1 * diff) % 7]
        !(D.contains mu)

theorem vosper_f7_mean_excluded : f7MeanExcluded = true := by
  decide

end PrefixStabilizers
