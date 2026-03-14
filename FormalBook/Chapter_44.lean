/-
Copyright 2022 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/
import Mathlib.Tactic
import Mathlib.Analysis.Matrix.Spectrum
import Archive.Wiedijk100Theorems.FriendshipGraphs

/-!
# Of friends and politicians — The Friendship Theorem via ℝ eigenvalue analysis

## Proof outline (following "Proofs from THE BOOK", Chapter 44)

The proof proceeds in two steps:

**(1) Combinatorial step:** If no vertex is adjacent to all others, then the graph must be
*k*-regular for some `k`, with `n = k² - k + 1` vertices. (This part is imported from
`Archive.Wiedijk100Theorems.FriendshipGraphs`.)

**(2) Linear algebra step (the contradiction for k ≥ 3):**
We analyze the eigenvalues of the adjacency matrix `A` using the relation `A² = (k-1)I + J`,
where `J` is the all-ones matrix.

Following the book's approach:
- **J's eigenvalues:** The all-ones matrix `J` has eigenvalue `n` (multiplicity 1, eigenvector
  the all-ones vector) and eigenvalue `0` (multiplicity `n-1`, on the orthogonal complement).
- **A²'s eigenvalues:** Since `A² = (k-1)I + J`, the eigenvalues of `A²` are
  `k-1+n = k²` (multiplicity 1) and `k-1` (multiplicity `n-1`).
- **A's eigenvalues:** Since `A` is symmetric (hence diagonalizable), the eigenvalues of `A`
  are `k` (multiplicity 1) and `±√(k-1)` (multiplicities `r` and `s`, with `r+s = n-1`).
- **Trace argument:** `tr(A) = 0` gives `k + r√(k-1) - s√(k-1) = 0`, so
  `√(k-1) = k/(s-r)` is rational.

**Dedekind's lemma (1858)** then forces `√(k-1)` to be an integer `h`, giving
`k = h² + 1` and `h | h² + 1`, hence `h | 1`, so `k = 2` — contradiction.

### Dedekind's lemma: book proof vs. formalization

The book presents Dedekind's 1858 proof by *infinite descent*: let `n₀` be the smallest
natural number with `n₀√m ∈ ℕ`. If `√m ∉ ℕ`, pick `ℓ ∈ ℕ` with `0 < √m - ℓ < 1`, then
`n₁ := n₀(√m - ℓ) < n₀` also satisfies `n₁√m ∈ ℕ`, contradicting minimality.

Our formalization uses the equivalent *coprime representation*: if `p² = m·q²` with
`gcd(p,q) = 1`, then `q² | p²` and coprimality forces `q² | 1`, hence `q = 1`. This is
the same argument in different clothing — "smallest denominator" ↔ "coprime fraction" ↔
"reduced form" — and both establish that `√m` rational implies `√m` integer.
-/

set_option maxHeartbeats 6400000

namespace chapter44

open scoped Classical
open Finset SimpleGraph Theorems100 Matrix

variable {V : Type*} [Fintype V] [Nonempty V]
variable {G : SimpleGraph V} {d : ℕ}

/-! ### Dedekind's lemma (1858): √m rational ⟹ √m integer

The book's proof uses infinite descent on the smallest `n₀` with `n₀√m ∈ ℕ`.
We formalize the equivalent coprime-fraction version: `p² = m·q²` with `gcd(p,q) = 1`
forces `q = 1`. Both arguments establish that `√m ∈ ℚ ⟹ √m ∈ ℤ`. -/

/-- **Dedekind's lemma (1858).** If `p² = m * q²` with `gcd(p,q) = 1`, then `q = 1`.

This is the coprime-fraction formulation of: if `√m` is rational, it is an integer.
The book's "smallest natural number" argument is equivalent — reducing a fraction to
lowest terms is the same as choosing the minimal denominator. -/
lemma Nat.sqrt_rational_is_integer (m p q : ℕ) (hq : 0 < q)
    (hcop : Nat.Coprime p q) (hsq : p ^ 2 = m * q ^ 2) : q = 1 := by
  have h1 : q ^ 2 ∣ p ^ 2 := ⟨m, by linarith⟩
  have h3 : q ^ 2 ∣ 1 := by
    have h4 : q ^ 2 ∣ Nat.gcd (q ^ 2) (p ^ 2) := Nat.dvd_gcd dvd_rfl h1
    rwa [Nat.coprime_comm.mp (hcop.pow 2 2)] at h4
  nlinarith [Nat.le_of_dvd Nat.one_pos h3, sq_nonneg q]

/-! ### Number-theoretic endgame: `k²(d-1) = d²` and `d ≥ 3` yield contradiction

From the trace equation we obtain `k²(d-1) = d²`. Dedekind's lemma forces `√(d-1)`
to be an integer `h`. Then `d = h²+1`, so `h | h²+1` and `h | h²`, giving `h | 1`,
hence `d ∈ {1,2}` — contradicting `d ≥ 3`. -/

private lemma false_of_sq_mul_pred_eq_sq (d k : ℕ) (hd : 3 ≤ d) (hk : 0 < k)
    (heq : k ^ 2 * (d - 1) = d ^ 2) : False := by
  -- Reduce d/k to coprime pair (a, b) with d = a*g, k = b*g
  obtain ⟨a, b, g, hg, had, hbk, hcop⟩ :
      ∃ a b g : ℕ, 0 < g ∧ d = a * g ∧ k = b * g ∧ Nat.Coprime a b := by
    refine ⟨d / Nat.gcd d k, k / Nat.gcd d k, Nat.gcd d k, ?_, ?_, ?_, ?_⟩
    · exact Nat.pos_of_ne_zero (by intro h; simp [Nat.gcd_eq_zero_iff.mp h] at hk)
    · exact (Nat.div_mul_cancel (Nat.gcd_dvd_left d k)).symm
    · exact (Nat.div_mul_cancel (Nat.gcd_dvd_right d k)).symm
    · exact Nat.coprime_div_gcd_div_gcd
        (Nat.pos_of_ne_zero (by intro h; simp [Nat.gcd_eq_zero_iff.mp h] at hk))
  have ha_pos : 0 < a := by
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · rw [zero_mul] at had; omega
    · exact ha
  have hb_pos : 0 < b := by
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · rw [zero_mul] at hbk; omega
    · exact hb
  -- Cancel g² to get b²(d-1) = a²
  have heq2 : b ^ 2 * (d - 1) = a ^ 2 := by
    have h2 : g ^ 2 * (b ^ 2 * (d - 1)) = g ^ 2 * a ^ 2 := by
      have : (b * g) ^ 2 * (d - 1) = (a * g) ^ 2 := by rw [← had, ← hbk]; exact heq
      nlinarith
    exact mul_left_cancel₀ (by positivity : (g : ℕ) ^ 2 ≠ 0) h2
  -- Apply Dedekind's lemma: a² = (d-1)·b² with gcd(a,b) = 1 gives b = 1
  have hb1 : b = 1 := Nat.sqrt_rational_is_integer (d - 1) a b hb_pos hcop (by linarith)
  subst hb1; rw [one_mul] at hbk; subst hbk
  simp only [one_pow, one_mul] at heq2
  -- Now d - 1 = a², so d = a² + 1 = a·k, hence a·k = a² + 1
  have hak : a * k = a ^ 2 + 1 := by omega
  -- h | h²+1 and h | h² imply h | 1 (book's final step)
  have ha1 : a ∣ 1 := by
    have h : a ∣ a * k := dvd_mul_right a k
    rw [hak] at h
    exact (Nat.dvd_add_right (dvd_pow_self a two_ne_zero)).mp h
  have : a ≤ 1 := Nat.le_of_dvd Nat.one_pos ha1
  interval_cases a; all_goals omega

/-! ### Auxiliary lemmas for the eigenvalue analysis -/

/-- If each `f i` satisfies `f i ^ 2 = c` over a finset, then `(∑ f)² = c * k²` for some `k`.
This captures the fact that a sum of values `±√c` squares to a multiple of `c`. -/
private lemma sq_sum_eq_sq_mul {ι : Type*} (S : Finset ι) (f : ι → ℝ) (c : ℕ)
    (hc : 0 < c) (hf : ∀ i ∈ S, f i ^ 2 = (c : ℝ)) :
    ∃ k : ℕ, (∑ i ∈ S, f i) ^ 2 = ↑c * (k : ℝ) ^ 2 := by
  have hcr : (0 : ℝ) < c := Nat.cast_pos.mpr hc
  set g := fun i => f i / Real.sqrt c
  have hg_pm : ∀ i ∈ S, g i = 1 ∨ g i = -1 := by
    intro i hi
    have hg1 : g i ^ 2 = 1 := by
      simp only [g, div_pow]; rw [hf i hi, Real.sq_sqrt (by positivity), div_self (by positivity)]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp (show g i ^ 2 = 1 ^ 2 by rw [hg1, one_pow]) with h | h
    · left; exact h
    · right; linarith
  set gi : ι → ℤ := fun i => if g i = 1 then 1 else -1
  have hsum_eq : (∑ i ∈ S, g i) = ((∑ i ∈ S, gi i : ℤ) : ℝ) := by
    rw [Int.cast_sum]; apply Finset.sum_congr rfl; intro i hi
    rcases hg_pm i hi with h | h
    · simp [gi, h]
    · simp [gi, h, show ¬((-1 : ℝ) = 1) from by norm_num]
  have hsq : (∑ i ∈ S, f i) ^ 2 = (∑ i ∈ S, g i) ^ 2 * c := by
    have : ∑ i ∈ S, f i = (∑ i ∈ S, g i) * Real.sqrt c := by
      rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro i _
      exact (div_mul_cancel₀ _ (Real.sqrt_ne_zero'.mpr hcr)).symm
    rw [this, mul_pow, Real.sq_sqrt (by positivity)]
  rw [hsq, hsum_eq]
  set s := (∑ i ∈ S, gi i)
  use s.natAbs
  rw [show (s.natAbs : ℝ) ^ 2 = (s : ℝ) ^ 2 from by
    rw [show (s.natAbs : ℝ) = ((s.natAbs : ℤ) : ℝ) from by simp]
    exact_mod_cast Int.natAbs_sq s]
  ring

private lemma trace_unitary_conj {n : Type*} [Fintype n] [DecidableEq n]
    (U : ↥(unitaryGroup n ℝ)) (M : Matrix n n ℝ) :
    ((Unitary.conjStarAlgAut ℝ (Matrix n n ℝ)) U M).trace = M.trace := by
  simp only [Unitary.conjStarAlgAut_apply]
  rw [trace_mul_cycle, Unitary.star_mul_self_of_mem U.prop, one_mul]

/-! ### Main contradiction: a k-regular friendship graph with k ≥ 3 cannot exist

The proof follows the book's eigenvalue analysis:

**Step 1.** `A² = (k-1)I + J` (from the friendship + regularity conditions).

**Step 2. J's eigenvalues.** `J` has eigenvalue `n` (multiplicity 1) and `0` (multiplicity `n-1`).
The all-ones vector `𝟏` is an eigenvector for eigenvalue `n`, and any vector orthogonal to `𝟏`
is in the kernel of `J`.

**Step 3. A²'s eigenvalues.** From `A² = (k-1)I + J`:
- Eigenvalue `k-1+n = k²` with multiplicity 1 (on `span{𝟏}`)
- Eigenvalue `k-1` with multiplicity `n-1` (on `𝟏⊥`)

**Step 4. A's eigenvalues.** Since `A` is real symmetric, it is diagonalizable. Its eigenvalues
must square to eigenvalues of `A²`, so they are `±k` and `±√(k-1)`. The all-ones vector gives
eigenvalue `+k` (multiplicity 1). The remaining `n-1` eigenvalues are `±√(k-1)`.

**Step 5. Trace.** `tr(A) = 0` gives `k + r√(k-1) - s√(k-1) = 0`, making `√(k-1)` rational.
Dedekind's lemma forces `√(k-1) ∈ ℤ`, leading to `k = 2` — contradiction.

In the formalization, Steps 2–4 are captured via the annihilating polynomial
`(A² - (k-1)I)(A² - k²I) = 0`, which is equivalent to analyzing J's eigenvalues and lifting
through `A² = (k-1)I + J`. The polynomial factors correspond exactly to the two eigenspaces
of J (the `𝟏`-direction and its complement). -/

theorem false_of_three_le_degree_real (hG : Friendship G) (hd : G.IsRegularOfDegree d)
    (h3 : 3 ≤ d) : False := by
  classical
  -- A is symmetric (the adjacency matrix of an undirected graph)
  have hAH : (G.adjMatrix ℝ).IsHermitian := by
    ext i j; simp only [conjTranspose_apply, star_trivial, adjMatrix_apply, G.adj_comm j i]
  let ev := hAH.eigenvalues
  let eb := hAH.eigenvectorBasis
  let n := Fintype.card V
  let J : Matrix V V ℝ := of fun (_ _ : V) => (1 : ℝ)
  -- ── Combinatorial setup from part (1) ──
  have hcard : d + (n - 1) = d * d := Friendship.card_of_regular hG hd
  have hn_pos : 0 < n := Fintype.card_pos
  have hn_eq : (n : ℝ) = (d : ℝ) ^ 2 - (d : ℝ) + 1 := by
    have : n + d = d * d + 1 := by omega
    have : (↑n + ↑d : ℝ) = ↑d * ↑d + 1 := by exact_mod_cast this
    nlinarith
  -- ── Step 1: A² = (k-1)I + J ──
  have hAsq : (G.adjMatrix ℝ) ^ 2 = ((d : ℝ) - 1) • (1 : Matrix V V ℝ) + J := by
    have h := Friendship.adjMatrix_sq_of_regular (R := ℝ) hG hd
    ext i j
    have : ((G.adjMatrix ℝ) ^ 2) i j = if i = j then (d : ℝ) else 1 := by
      rw [h]; simp [of_apply]
    simp only [this, smul_apply, smul_eq_mul, add_apply, one_apply, of_apply, J]
    split_ifs <;> ring
  -- ── Step 2: J² = n·J (J has eigenvalue n on 𝟏, eigenvalue 0 on 𝟏⊥) ──
  have hJsq : J * J = (n : ℝ) • J := by
    show J * J = (Fintype.card V : ℝ) • J
    ext i j; simp [J, mul_apply, of_apply, sum_const, Finset.card_univ, nsmul_eq_mul, smul_apply,
      smul_eq_mul]
  -- ── Step 4 (trace): ∑ eigenvalues = tr(A) = 0 ──
  have hsum0 : ∑ i : V, ev i = 0 := by
    have h1 := hAH.trace_eq_sum_eigenvalues
    simp only [RCLike.ofReal_real_eq_id, id] at h1
    rw [trace_adjMatrix ℝ G] at h1; linarith
  -- ── Steps 2–3 via annihilating polynomial: (A²-(k-1)I)(A²-k²I) = 0 ──
  -- This is equivalent to: J·(J - nI) = 0, which encodes J's eigenvalues {n, 0}.
  -- Substituting A² = (k-1)I + J transforms J's eigenvalue equation into A²'s.
  have hpoly : ((G.adjMatrix ℝ) ^ 2 - ((d : ℝ) - 1) • 1) *
      ((G.adjMatrix ℝ) ^ 2 - (d : ℝ) ^ 2 • 1) = 0 := by
    have hJ : (G.adjMatrix ℝ) ^ 2 - ((d : ℝ) - 1) • 1 = J := by rw [hAsq]; abel
    have hJn : (G.adjMatrix ℝ) ^ 2 - (d : ℝ) ^ 2 • 1 = J - (n : ℝ) • 1 := by
      rw [hAsq, hn_eq]; ext i j
      simp only [sub_apply, smul_apply, smul_eq_mul, one_apply, add_apply, of_apply, J]; ring
    rw [hJ, hJn, mul_sub, mul_smul_comm, hJsq, mul_one, sub_self]
  -- ── Step 3: each eigenvalue λ satisfies λ² ∈ {k-1, k²} ──
  -- (These are A²'s eigenvalues, coming from J's eigenvalues {0, n} shifted by k-1)
  have hev_sq : ∀ j : V, ev j ^ 2 = (d : ℝ) - 1 ∨ ev j ^ 2 = (d : ℝ) ^ 2 := by
    intro j
    have hv := hAH.mulVec_eigenvectorBasis j
    set v := (eb j).ofLp
    have hA2v : (G.adjMatrix ℝ) ^ 2 *ᵥ v = ev j ^ 2 • v := by
      show _ = hAH.eigenvalues j ^ 2 • v
      rw [sq (G.adjMatrix ℝ), ← mulVec_mulVec, hv, mulVec_smul, hv, smul_smul, sq]
    have h1 : ((G.adjMatrix ℝ) ^ 2 - ((d : ℝ) - 1) • 1) *ᵥ v =
        (ev j ^ 2 - ((d : ℝ) - 1)) • v := by
      simp only [sub_mulVec, smul_mulVec, one_mulVec, hA2v, sub_smul]
    have h2 : ((G.adjMatrix ℝ) ^ 2 - (d : ℝ) ^ 2 • 1) *ᵥ v =
        (ev j ^ 2 - (d : ℝ) ^ 2) • v := by
      simp only [sub_mulVec, smul_mulVec, one_mulVec, hA2v, sub_smul]
    have h3 : ((ev j ^ 2 - ((d : ℝ) - 1)) * (ev j ^ 2 - (d : ℝ) ^ 2)) • v = 0 := by
      calc ((ev j ^ 2 - ((d : ℝ) - 1)) * (ev j ^ 2 - (d : ℝ) ^ 2)) • v
          = ((G.adjMatrix ℝ) ^ 2 - ((d : ℝ) - 1) • 1) *ᵥ
            ((ev j ^ 2 - (d : ℝ) ^ 2) • v) := by
            rw [mulVec_smul, h1, smul_smul]; ring_nf
        _ = ((G.adjMatrix ℝ) ^ 2 - ((d : ℝ) - 1) • 1) *ᵥ
            (((G.adjMatrix ℝ) ^ 2 - (d : ℝ) ^ 2 • 1) *ᵥ v) := by rw [h2]
        _ = (((G.adjMatrix ℝ) ^ 2 - ((d : ℝ) - 1) • 1) *
            ((G.adjMatrix ℝ) ^ 2 - (d : ℝ) ^ 2 • 1)) *ᵥ v := mulVec_mulVec ..
        _ = 0 := by rw [hpoly, zero_mulVec]
    have hv_ne : v ≠ 0 := by
      intro habs
      exact absurd (eb.orthonormal.1 j) (by
        have : (eb j : EuclideanSpace ℝ V) = 0 := by ext i; exact congr_fun habs i
        simp [this])
    rcases mul_eq_zero.mp (smul_eq_zero.mp h3 |>.resolve_right hv_ne) with h | h
    · left; linarith
    · right; linarith
  -- ── ∑ ev² = n·d (from tr(A²)) ──
  have hsum_sq : ∑ j : V, ev j ^ 2 = (n : ℝ) * (d : ℝ) := by
    have htr : ∑ j : V, ev j ^ 2 = ((G.adjMatrix ℝ) ^ 2).trace := by
      show ∑ j, hAH.eigenvalues j ^ 2 = _
      conv_rhs => rw [hAH.spectral_theorem]
      rw [← map_pow, trace_unitary_conj]
      simp [trace_diagonal, sq, diagonal_mul_diagonal]
    have htrval : ((G.adjMatrix ℝ) ^ 2).trace = (n : ℝ) * d := by
      rw [hAsq]
      simp only [Matrix.trace, Matrix.diag, smul_apply, smul_eq_mul, add_apply, one_apply,
        of_apply, J]
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      push_cast; ring
    linarith
  -- ── Step 4–5: Partition eigenvalues into "big" (λ²=k²) and "small" (λ²=k-1) ──
  -- The "big" eigenvalue corresponds to the 𝟏-direction (J's eigenvalue n),
  -- the "small" eigenvalues correspond to 𝟏⊥ (J's eigenvalue 0).
  let big := Finset.univ.filter (fun j : V => ev j ^ 2 = (d : ℝ) ^ 2)
  let small := Finset.univ.filter (fun j : V => ev j ^ 2 = (d : ℝ) - 1)
  have hpart : big ∪ small = Finset.univ := by
    ext j; constructor
    · intro _; exact Finset.mem_univ _
    · intro _
      simp only [big, small, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      exact (hev_sq j).symm
  have hdisj : Disjoint big small := by
    rw [Finset.disjoint_filter]
    intro j _ h1 h2; nlinarith
  have hcard_sum : big.card + small.card = Fintype.card V := by
    rw [← Finset.card_union_of_disjoint hdisj, hpart, Finset.card_univ]
  -- |big| = 1: the eigenvalue k² has multiplicity 1 (matching J's eigenvalue n)
  have hbig1 : big.card = 1 := by
    have hbs : ∑ j ∈ big, ev j ^ 2 + ∑ j ∈ small, ev j ^ 2 = (n : ℝ) * d := by
      rw [← Finset.sum_union hdisj, hpart]; exact hsum_sq
    have hbig_s : ∀ j ∈ big, ev j ^ 2 = (d : ℝ) ^ 2 := fun j hj => by
      simp only [big, Finset.mem_filter, Finset.mem_univ, true_and] at hj; exact hj
    have hsmall_s : ∀ j ∈ small, ev j ^ 2 = ((d : ℝ) - 1) := fun j hj => by
      simp only [small, Finset.mem_filter, Finset.mem_univ, true_and] at hj; exact hj
    rw [Finset.sum_congr rfl hbig_s, Finset.sum_congr rfl hsmall_s,
        Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul] at hbs
    have h2 : (big.card : ℝ) + (small.card : ℝ) = (n : ℝ) := by exact_mod_cast hcard_sum
    have hmul : (big.card : ℝ) * ((d : ℝ) ^ 2 - (d : ℝ) + 1) = (n : ℝ) := by nlinarith
    rw [hn_eq] at hmul
    have hpos : (0 : ℝ) < (d : ℝ) ^ 2 - (d : ℝ) + 1 := by nlinarith
    have : (big.card : ℝ) = 1 := by
      nlinarith [mul_comm (big.card : ℝ) ((d : ℝ) ^ 2 - (d : ℝ) + 1)]
    exact_mod_cast this
  -- ── Step 5: Trace equation → √(k-1) is rational ──
  -- The n-1 "small" eigenvalues are ±√(k-1). Their sum plus the single "big"
  -- eigenvalue (±k) equals 0. This makes √(k-1) = k/(s-r) rational.
  have hsmall_ev_sq : (∑ j ∈ small, ev j) ^ 2 = (d : ℝ) ^ 2 := by
    have hev_split : ∑ j ∈ big, ev j + ∑ j ∈ small, ev j = 0 := by
      rw [← Finset.sum_union hdisj, hpart]; exact hsum0
    obtain ⟨j₀, hj₀⟩ := Finset.card_eq_one.mp hbig1
    have hbig_sq : (∑ j ∈ big, ev j) ^ 2 = (d : ℝ) ^ 2 := by
      rw [hj₀, Finset.sum_singleton]
      have : j₀ ∈ big := by rw [hj₀]; exact Finset.mem_singleton_self _
      simp only [big, Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact this
    have : ∑ j ∈ small, ev j = -(∑ j ∈ big, ev j) := by linarith
    rw [this, neg_sq]; exact hbig_sq
  -- Each "small" eigenvalue satisfies ev² = (d-1 : ℕ)
  have hsmall_ev : ∀ j ∈ small, ev j ^ 2 = ((d - 1 : ℕ) : ℝ) := by
    intro j hj; simp only [small, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    have : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ d)]; simp
    rw [this]; exact hj
  -- ── Apply Dedekind's lemma to reach contradiction ──
  rcases Nat.eq_zero_or_pos (d - 1) with hd0 | hd1
  · omega  -- d-1 = 0 means d = 1, contradicts d ≥ 3
  · -- √(k-1) is rational: (∑ small ev)² = (d-1)·k² for some k
    obtain ⟨k, hk_eq⟩ := sq_sum_eq_sq_mul small ev (d - 1) hd1 hsmall_ev
    -- Combined with (∑ small ev)² = d²: (d-1)·k² = d²
    have hdk : (d - 1 : ℕ) * k ^ 2 = d ^ 2 := by
      have : ((d - 1 : ℕ) : ℝ) * (k : ℝ) ^ 2 = (d : ℝ) ^ 2 := by
        rw [← hk_eq]; exact hsmall_ev_sq
      have h1 : ((d - 1 : ℕ) * k ^ 2 : ℕ) = (d ^ 2 : ℕ) := by exact_mod_cast this
      exact h1
    have hk_pos : 0 < k := by
      rcases Nat.eq_zero_or_pos k with rfl | hkp
      · simp at hdk; nlinarith
      · exact hkp
    -- Dedekind's lemma + divisibility endgame
    exact false_of_sq_mul_pred_eq_sq d k h3 hk_pos (by linarith)

theorem friendship_theorem
    (h : ∀ ⦃v w : V⦄, v ≠ w → Fintype.card (G.commonNeighbors v w) = 1) :
    ∃ v : V, ∀ w : V, v ≠ w → G.Adj v w := by
  have hG : Friendship G := h
  by_contra npG
  rcases hG.isRegularOf_not_existsPolitician npG with ⟨d, dreg⟩
  rcases lt_or_ge d 3 with hlt | hge
  · exact npG (hG.existsPolitician_of_degree_le_two dreg (Nat.lt_succ_iff.mp hlt))
  · exact false_of_three_le_degree_real hG dreg hge

end chapter44
