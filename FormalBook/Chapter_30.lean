/-
Copyright 2022 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching, Yachiyo (OpenClaw)
-/
import Mathlib

/-!
# Three famous theorems on finite sets

## Katona's cyclic permutation proof of Erdős–Ko–Rado

  - [x] Theorem 1 (Sperner)
  - [x] Theorem 2 (Erdős–Ko–Rado) — Katona's cyclic permutation proof
  - [x] Theorem 3 (Hall's marriage theorem)

## References

* Aigner, M. and Ziegler, G.M., "Proofs from THE BOOK", Chapter 30
* Katona, G.O.H., "A simple proof of the Erdős–Ko–Rado theorem", 1972
-/

namespace chapter30

/-! ## Theorem 1: Sperner's theorem -/

/-- **Sperner's theorem.** -/
theorem sperner {α : Type*} [Fintype α] [DecidableEq α]
    (𝒜 : Finset (Finset α)) (h𝒜 : IsAntichain (· ⊆ ·) (SetLike.coe 𝒜)) :
    𝒜.card ≤ (Fintype.card α).choose (Fintype.card α / 2) :=
  h𝒜.sperner

/-! ## Theorem 2: Erdős–Ko–Rado (Katona's cyclic permutation proof) -/

section ErdosKoRado

/-- A circular arc of length `k` starting at `s` on a circle of `n` points.
    `circularArc n k s = {s, s+1, …, s+k-1} mod n` as a `Finset (Fin n)`. -/
def circularArc {n : ℕ} (k : ℕ) (s : Fin n) : Finset (Fin n) :=
  (Finset.range k).image fun j => s + ⟨j % n, Nat.mod_lt j (Fin.pos s)⟩

/-- The image of a circular arc under a permutation. -/
def permArc {n : ℕ} (k : ℕ) (σ : Equiv.Perm (Fin n)) (s : Fin n) : Finset (Fin n) :=
  (circularArc k s).image σ

/-- **Arc Lemma.** On a circle of `n ≥ 2k` points, at most `k` arcs of length `k`
can be pairwise intersecting.

**Proof:** Define a map Ψ from starting points to `{0, …, k-1}` by
  `Ψ(s) = (s - i₀).val` if forward offset `< k`, else `(s - i₀).val - (n - k)`.
This is injective because any "collision" between forward and backward offsets
would force distance exactly `k`, contradicting pairwise intersection `< k`. -/

private lemma fin_add_sub_cancel' {n : ℕ} (s j : Fin n) : (s + j - s) = j := by
  ext; simp only [Fin.sub_def, Fin.add_def, Fin.val_mk]
  rcases Nat.lt_or_ge (s.val + j.val) n with h | h
  · rw [Nat.mod_eq_of_lt h, show n - s.val + (s.val + j.val) = n + j.val from by omega,
        Nat.add_mod_left, Nat.mod_eq_of_lt j.isLt]
  · rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega : s.val + j.val - n < n),
        show n - s.val + (s.val + j.val - n) = j.val from by omega, Nat.mod_eq_of_lt j.isLt]

private lemma circularArc_sub_val_lt' {n k : ℕ} (hkn : k ≤ n) {s x : Fin n}
    (hx : x ∈ circularArc k s) : (x - s).val < k := by
  simp only [circularArc, Finset.mem_image, Finset.mem_range] at hx
  obtain ⟨j, hjk, rfl⟩ := hx
  rw [fin_add_sub_cancel']; simp [Nat.mod_eq_of_lt (by omega : j < n)]; exact hjk

private lemma mod_close' {n k a b c : ℕ} (ha : a < n) (hb : b < n) (hc : c < n)
    (h1 : (n - a + c) % n < k) (h2 : (n - b + c) % n < k) :
    (n - b + a) % n < k ∨ (n - a + b) % n < k := by
  have aux : ∀ x y : ℕ, x < n → y < n → x ≤ y → (n - x + y) % n = y - x :=
    fun x y hx hy hxy => by
      rw [Nat.mod_eq_sub_mod (by omega), show n - x + y - n = y - x from by omega,
          Nat.mod_eq_of_lt (by omega)]
  have aux2 : ∀ x y : ℕ, x < n → y < n → y < x → (n - x + y) % n = n - x + y :=
    fun x y hx _ hxy => Nat.mod_eq_of_lt (by omega)
  rcases le_or_gt a c with hac | hac <;> rcases le_or_gt b c with hbc | hbc
  · rw [aux a c ha hc hac] at h1; rw [aux b c hb hc hbc] at h2
    rcases le_or_gt a b with hab | hab
    · right; rw [aux a b ha hb hab]; omega
    · left; rw [aux b a hb ha (le_of_lt hab)]; omega
  · rw [aux a c ha hc hac] at h1; rw [aux2 b c hb hc hbc] at h2
    left; rw [aux2 b a hb ha (by omega)]; omega
  · rw [aux2 a c ha hc hac] at h1; rw [aux b c hb hc hbc] at h2
    right; rw [aux2 a b ha hb (by omega)]; omega
  · rw [aux2 a c ha hc hac] at h1; rw [aux2 b c hb hc hbc] at h2
    rcases le_or_gt a b with hab | hab
    · right; rcases eq_or_lt_of_le hab with rfl | hab'
      · rw [show n - a + a = n from by omega, Nat.mod_self]; omega
      · rw [aux a b ha hb hab]; omega
    · left; rw [aux b a hb ha (le_of_lt hab)]; omega

private lemma arc_inter_close' {n k : ℕ} (hkn : k ≤ n) (i j : Fin n)
    (h : (circularArc k i ∩ circularArc k j).Nonempty) :
    (i - j).val < k ∨ (j - i).val < k := by
  obtain ⟨x, hx⟩ := h; rw [Finset.mem_inter] at hx
  simp only [Fin.sub_def, Fin.val_mk] at *
  exact mod_close' i.isLt j.isLt x.isLt
    (circularArc_sub_val_lt' hkn hx.1) (circularArc_sub_val_lt' hkn hx.2)

private lemma fin_sub_add_sub {n : ℕ} (a b : Fin n) (hab : a ≠ b) :
    (a - b).val + (b - a).val = n := by
  simp only [Fin.sub_def, Fin.val_mk]
  have ha := a.isLt; have hb := b.isLt
  have hne : a.val ≠ b.val := fun h => hab (Fin.ext h)
  rcases Nat.lt_or_ge a.val b.val with h | h
  · rw [Nat.mod_eq_of_lt (by omega : n - b.val + a.val < n),
        Nat.mod_eq_sub_mod (by omega : n ≤ n - a.val + b.val),
        show n - a.val + b.val - n = b.val - a.val from by omega,
        Nat.mod_eq_of_lt (by omega : b.val - a.val < n)]
    omega
  · have : b.val < a.val := lt_of_le_of_ne h (Ne.symm hne)
    rw [Nat.mod_eq_sub_mod (by omega : n ≤ n - b.val + a.val),
        show n - b.val + a.val - n = a.val - b.val from by omega,
        Nat.mod_eq_of_lt (by omega : a.val - b.val < n),
        Nat.mod_eq_of_lt (by omega : n - a.val + b.val < n)]
    omega

lemma arc_lemma {n k : ℕ} (h2k : 2 * k ≤ n) (S : Finset (Fin n))
    (hS : ∀ i ∈ S, ∀ j ∈ S, (circularArc k i ∩ circularArc k j).Nonempty) :
    S.card ≤ k := by
  rcases S.eq_empty_or_nonempty with rfl | hne; · simp
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · obtain ⟨i₀, hi₀⟩ := hne; exact absurd (hS i₀ hi₀ i₀ hi₀) (by simp [circularArc])
  have hkn : k ≤ n := by omega
  obtain ⟨i₀, hi₀⟩ := hne
  haveI : NeZero n := ⟨by omega⟩
  let f : Fin n → ℕ := fun s =>
    let d := (s - i₀).val
    if d < k then d else d - (n - k)
  have hrange : ∀ s ∈ S, (s - i₀).val < k ∨ n - (s - i₀).val < k := by
    intro s hs
    have h := arc_inter_close' hkn s i₀ (hS s hs i₀ hi₀)
    rcases eq_or_ne s i₀ with rfl | hne
    · left; simp; exact hk
    · have hsum := fin_sub_add_sub s i₀ hne
      rcases h with h | h
      · left; exact h
      · right; omega
  have hf_lt : ∀ s ∈ S, f s < k := by
    intro s hs; simp only [f]
    split_ifs with h; · exact h
    have hd := arc_inter_close' hkn s i₀ (hS s hs i₀ hi₀)
    rcases hd with h' | h'
    · exact absurd h' h
    · have hne : s ≠ i₀ := by intro heq; subst heq; simp at h; omega
      have := fin_sub_add_sub s i₀ hne; omega
  have hf_inj : ∀ s₁ ∈ S, ∀ s₂ ∈ S, f s₁ = f s₂ → s₁ = s₂ := by
    intro s₁ hs₁ s₂ hs₂ heq
    simp only [f] at heq
    set d₁ := (s₁ - i₀).val
    set d₂ := (s₂ - i₀).val
    have hpair := arc_inter_close' hkn s₁ s₂ (hS s₁ hs₁ s₂ hs₂)
    rw [show s₁ - s₂ = (s₁ - i₀) - (s₂ - i₀) from by abel,
        show s₂ - s₁ = (s₂ - i₀) - (s₁ - i₀) from by abel] at hpair
    split_ifs at heq with h₁ _ h₁
    · have : s₁ - i₀ = s₂ - i₀ := Fin.ext heq
      have := congr_arg (· + i₀) this; simp at this; exact this
    · exfalso
      have hd₂_ge : n - d₂ < k := (hrange s₂ hs₂).resolve_left (by omega)
      have h12 : ((s₁ - i₀) - (s₂ - i₀)).val = k := by
        show ((n - (s₂ - i₀).val + (s₁ - i₀).val) % n) = k
        rw [show (n - (s₂ - i₀).val + (s₁ - i₀).val) = n - d₂ + d₁ from rfl,
            Nat.mod_eq_of_lt (by omega : n - d₂ + d₁ < n)]; omega
      have h21 : ((s₂ - i₀) - (s₁ - i₀)).val = n - k := by
        have := fin_sub_add_sub (s₁ - i₀) (s₂ - i₀)
          (by intro h; have := congr_arg Fin.val h; omega); omega
      rw [h12, h21] at hpair; rcases hpair with hp | hp <;> omega
    · exfalso
      have hd₁_ge : n - d₁ < k := (hrange s₁ hs₁).resolve_left (by omega)
      have h21 : ((s₂ - i₀) - (s₁ - i₀)).val = k := by
        show ((n - (s₁ - i₀).val + (s₂ - i₀).val) % n) = k
        rw [show (n - (s₁ - i₀).val + (s₂ - i₀).val) = n - d₁ + d₂ from rfl,
            Nat.mod_eq_of_lt (by omega : n - d₁ + d₂ < n)]; omega
      have h12 : ((s₁ - i₀) - (s₂ - i₀)).val = n - k := by
        have := fin_sub_add_sub (s₂ - i₀) (s₁ - i₀)
          (by intro h; have := congr_arg Fin.val h; omega); omega
      rw [h12, h21] at hpair; rcases hpair with hp | hp <;> omega
    · have hd₁r : n - d₁ < k := by
        have := hrange s₁ hs₁; simp only [d₁] at this ⊢; omega
      have hd₂r : n - d₂ < k := by
        have := hrange s₂ hs₂; simp only [d₂] at this ⊢; omega
      have : s₁ - i₀ = s₂ - i₀ := Fin.ext (by omega)
      have := congr_arg (· + i₀) this; simp at this; exact this
  calc S.card
      = (S.image f).card := by
          rw [Finset.card_image_of_injOn (fun a ha b hb => hf_inj a ha b hb)]
    _ ≤ (Finset.range k).card := Finset.card_le_card (by
          intro x hx; rw [Finset.mem_image] at hx; obtain ⟨s, hs, rfl⟩ := hx
          exact Finset.mem_range.mpr (hf_lt s hs))
    _ = k := Finset.card_range k

/-- Permutations preserve arc intersection. -/
lemma permArc_inter {n k : ℕ} (σ : Equiv.Perm (Fin n)) (i j : Fin n)
    (h : (circularArc k i ∩ circularArc k j).Nonempty) :
    (permArc k σ i ∩ permArc k σ j).Nonempty := by
  obtain ⟨x, hx⟩ := h
  rw [Finset.mem_inter] at hx
  refine ⟨σ x, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
  · exact Finset.mem_image_of_mem σ hx.1
  · exact Finset.mem_image_of_mem σ hx.2

/-- For a fixed permutation and intersecting family, at most k arcs are in 𝒜. -/
lemma perm_arcs_le_k {n k : ℕ} (h2k : 2 * k ≤ n)
    (𝒜 : Finset (Finset (Fin n)))
    (h𝒜 : (𝒜 : Set (Finset (Fin n))).Intersecting)
    (σ : Equiv.Perm (Fin n)) :
    (Finset.univ.filter (fun s : Fin n => permArc k σ s ∈ 𝒜)).card ≤ k := by
  set T := Finset.univ.filter (fun s : Fin n => permArc k σ s ∈ 𝒜)
  -- T is pairwise intersecting in arc-space, so arc_lemma applies
  suffices hT : ∀ i ∈ T, ∀ j ∈ T,
      (circularArc k i ∩ circularArc k j).Nonempty from
    arc_lemma h2k T hT
  intro i hi j hj
  have hi' : permArc k σ i ∈ 𝒜 := (Finset.mem_filter.mp hi).2
  have hj' : permArc k σ j ∈ 𝒜 := (Finset.mem_filter.mp hj).2
  -- 𝒜 is intersecting, so permArc σ i and permArc σ j are not disjoint
  have hint := h𝒜 hi' hj'
  -- ¬Disjoint means there is a common element
  simp only [Finset.not_disjoint_iff] at hint
  obtain ⟨x, hxi, hxj⟩ := hint
  -- x is in both permArcs, so σ⁻¹ x is in both circular arcs
  simp only [permArc, Finset.mem_image] at hxi hxj
  obtain ⟨a, hai, rfl⟩ := hxi
  obtain ⟨b, hbj, hσ⟩ := hxj
  have hab : a = b := σ.injective hσ.symm
  subst hab
  exact ⟨a, Finset.mem_inter.mpr ⟨hai, hbj⟩⟩

/-- **Upper bound**: summing `perm_arcs_le_k` over all permutations gives
`∑_σ #{i | permArc σ i ∈ 𝒜} ≤ k · n!`. -/
private lemma upper_bound_sum {n k : ℕ} (h2k : 2 * k ≤ n)
    (𝒜 : Finset (Finset (Fin n)))
    (h𝒜 : (𝒜 : Set (Finset (Fin n))).Intersecting) :
    ∑ σ : Equiv.Perm (Fin n),
      (Finset.univ.filter (fun s : Fin n => permArc k σ s ∈ 𝒜)).card
      ≤ k * n.factorial := by
  calc ∑ σ : Equiv.Perm (Fin n),
        (Finset.univ.filter (fun s : Fin n => permArc k σ s ∈ 𝒜)).card
      ≤ ∑ _ : Equiv.Perm (Fin n), k :=
        Finset.sum_le_sum fun σ _ => perm_arcs_le_k h2k 𝒜 h𝒜 σ
    _ = k * n.factorial := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_perm,
          Fintype.card_fin, mul_comm]

/-- The cardinality of a circular arc. -/
private lemma circularArc_card {n k : ℕ} (hk : k ≤ n) (_hn : 0 < n) (i : Fin n) :
    (circularArc k i).card = k := by
  unfold circularArc
  rw [Finset.card_image_of_injOn]
  · exact Finset.card_range k
  · intro j₁ hj₁ j₂ hj₂ heq
    simp only [Finset.coe_range, Set.mem_Iio] at hj₁ hj₂
    have := add_left_cancel heq
    simp only [Fin.mk.injEq] at this
    rw [Nat.mod_eq_of_lt (by omega : j₁ < n), Nat.mod_eq_of_lt (by omega : j₂ < n)] at this
    exact this

/-- For each fixed starting point `i` and target set `A` with `|A| = k`,
    the number of permutations mapping the circular arc at `i` to `A`
    is `k! * (n-k)!`. -/
private lemma count_perms_fixing_arc {n k : ℕ} (_hk : k ≤ n) (i : Fin n) (A : Finset (Fin n))
    (hA : A.card = k) (hcirc : (circularArc k i).card = k) :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => permArc k σ i = A)).card =
      k.factorial * (n - k).factorial := by
  set arc := circularArc k i
  have hAc : arcᶜ.card = n - k := by rw [Finset.card_compl, hcirc, Fintype.card_fin]
  have hAc' : Aᶜ.card = n - k := by rw [Finset.card_compl, hA, Fintype.card_fin]
  -- permArc k σ i = arc.image σ
  have key : ∀ σ : Equiv.Perm (Fin n), permArc k σ i = A ↔ arc.image σ = A := by
    intro σ; rfl
  simp_rw [key]
  have fwd_mem (σ : Equiv.Perm (Fin n)) (hσ : arc.image σ = A) (x : Fin n) :
      x ∈ arc ↔ σ x ∈ A := by
    rw [← hσ]; exact ⟨Finset.mem_image_of_mem σ,
      fun h => let ⟨_, hy, hyx⟩ := Finset.mem_image.mp h; σ.injective hyx ▸ hy⟩
  rw [← Fintype.card_subtype]
  have htmp : Fintype.card {σ : Equiv.Perm (Fin n) | arc.image σ = A} =
      Fintype.card (↥(arc : Finset _) ≃ ↥(A : Finset _)) *
      Fintype.card (↥(arcᶜ : Finset _) ≃ ↥(Aᶜ : Finset _)) := by
    rw [← Fintype.card_prod]
    exact Fintype.card_congr {
      toFun := fun ⟨σ, hσ⟩ =>
        (⟨fun ⟨x, hx⟩ => ⟨σ x, (fwd_mem σ hσ x).mp hx⟩,
          fun ⟨y, hy⟩ => ⟨σ⁻¹ y, (fwd_mem σ hσ _).mpr (by simp [hy])⟩,
          fun _ => Subtype.ext (by simp), fun _ => Subtype.ext (by simp)⟩,
         ⟨fun ⟨x, hx⟩ => ⟨σ x, Finset.mem_compl.mpr (((fwd_mem σ hσ x).not).mp (Finset.mem_compl.mp hx))⟩,
          fun ⟨y, hy⟩ => ⟨σ⁻¹ y, Finset.mem_compl.mpr (((fwd_mem σ hσ _).not).mpr (by simp [Finset.mem_compl.mp hy]))⟩,
          fun _ => Subtype.ext (by simp), fun _ => Subtype.ext (by simp)⟩)
      invFun := fun ⟨f, g⟩ =>
        ⟨⟨fun x => if hx : x ∈ arc then (f ⟨x, hx⟩).val
                   else (g ⟨x, Finset.mem_compl.mpr hx⟩).val,
          fun y => if hy : y ∈ A then (f.symm ⟨y, hy⟩).val
                   else (g.symm ⟨y, Finset.mem_compl.mpr hy⟩).val,
          fun x => by
            by_cases hx : x ∈ arc
            · simp [hx, (f ⟨x, hx⟩).prop]
            · simp [hx]
              have hgx := (g ⟨x, Finset.mem_compl.mpr hx⟩).prop
              rw [Finset.mem_compl] at hgx
              simp [hgx],
          fun y => by
            by_cases hy : y ∈ A
            · simp [hy, (f.symm ⟨y, hy⟩).prop]
            · simp [hy]
              have hgy := (g.symm ⟨y, Finset.mem_compl.mpr hy⟩).prop
              rw [Finset.mem_compl] at hgy
              simp [hgy]⟩,
        by ext y; simp only [Finset.mem_image]; constructor
           · rintro ⟨x, hx, rfl⟩; simp [hx, (f ⟨x, hx⟩).prop]
           · intro hy; exact ⟨(f.symm ⟨y, hy⟩).val, (f.symm ⟨y, hy⟩).prop, by simp⟩⟩
      left_inv := fun ⟨σ, hσ⟩ => by
        ext x; simp only
        by_cases hx : x ∈ arc
        · simp []
        · simp []
      right_inv := fun ⟨f, g⟩ => by
        ext ⟨x, hx⟩
        · simp []
        · simp only [Finset.mem_compl] at hx
          simp [hx]
    }
  calc Fintype.card {σ : Equiv.Perm (Fin n) | arc.image σ = A}
      = Fintype.card (↥(arc : Finset _) ≃ ↥(A : Finset _)) *
        Fintype.card (↥(arcᶜ : Finset _) ≃ ↥(Aᶜ : Finset _)) := htmp
    _ = k.factorial * (n - k).factorial := by
        congr 1
        · have e := (arc.equivFin.trans (finCongr hcirc)).trans (A.equivFin.trans (finCongr hA)).symm
          rw [Fintype.card_equiv e, Fintype.card_coe, hcirc]
        · have e := (arcᶜ.equivFin.trans (finCongr hAc)).trans (Aᶜ.equivFin.trans (finCongr hAc')).symm
          rw [Fintype.card_equiv e, Fintype.card_coe, hAc]

/-- **Lower bound (double counting identity)**: each member of `𝒜` is produced
by `permArc k σ i` for at least `n · k! · (n-k)!` pairs `(σ, i)`.

The proof swaps the order of summation:
  `∑_σ #{i | permArc σ i ∈ 𝒜} = ∑_i #{σ | permArc σ i ∈ 𝒜}`
then for each `i`, bounds `#{σ | permArc σ i ∈ 𝒜} ≥ |𝒜| · k! · (n-k)!`
by noting that for each `A ∈ 𝒜`, there are `k! · (n-k)!` permutations `σ`
with `permArc σ i = A`, and these sets are disjoint for different `A`. -/
private lemma lower_bound_sum {n k : ℕ} (_h2k : 2 * k ≤ n)
    (𝒜 : Finset (Finset (Fin n)))
    (_h𝒜 : (𝒜 : Set (Finset (Fin n))).Intersecting)
    (hSized : (𝒜 : Set (Finset (Fin n))).Sized k) :
    𝒜.card * (n * k.factorial * (n - k).factorial) ≤
      ∑ σ : Equiv.Perm (Fin n),
        (Finset.univ.filter (fun s : Fin n => permArc k σ s ∈ 𝒜)).card := by
  by_cases hn : n = 0
  · subst hn; simp
  have hn' : 0 < n := Nat.pos_of_ne_zero hn
  have hk : k ≤ n := by omega
  -- Step 1: Rewrite filter card as sum of indicator
  simp_rw [Finset.card_filter]
  -- Step 2: Swap the summation order
  rw [Finset.sum_comm]
  -- Now goal is: 𝒜.card * (n * k! * (n-k)!) ≤ ∑ i, ∑ σ, if permArc k σ i ∈ 𝒜 then 1 else 0
  -- Step 3: LHS = ∑_{i : Fin n} (𝒜.card * k! * (n-k)!)
  rw [show 𝒜.card * (n * k.factorial * (n - k).factorial) =
    ∑ _i : Fin n, 𝒜.card * (k.factorial * (n - k).factorial) by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring]
  -- Step 4: Suffices to show pointwise bound for each i
  apply Finset.sum_le_sum
  intro i _
  -- Need: 𝒜.card * (k! * (n-k)!) ≤ ∑ σ, if permArc k σ i ∈ 𝒜 then 1 else 0
  -- RHS = (univ.filter (fun σ => permArc k σ i ∈ 𝒜)).card
  rw [← Finset.card_filter]
  -- For each A ∈ 𝒜, {σ | permArc k σ i = A} ⊆ {σ | permArc k σ i ∈ 𝒜} and these are disjoint
  -- So #{σ | permArc k σ i ∈ 𝒜} ≥ ∑_{A ∈ 𝒜} #{σ | permArc k σ i = A} = |𝒜| * k! * (n-k)!
  calc 𝒜.card * (k.factorial * (n - k).factorial)
      = ∑ _A ∈ 𝒜, k.factorial * (n - k).factorial := by
        rw [Finset.sum_const]; simp
    _ = ∑ A ∈ 𝒜,
        (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => permArc k σ i = A)).card := by
        apply Finset.sum_congr rfl
        intro A hA
        rw [count_perms_fixing_arc hk i A (hSized hA) (circularArc_card hk hn' i)]
    _ ≤ (Finset.univ.filter (fun σ => permArc k σ i ∈ 𝒜)).card := by
        -- The sets {σ | permArc k σ i = A} for A ∈ 𝒜 are disjoint subsets
        rw [← Finset.card_biUnion]
        · apply Finset.card_le_card
          intro σ hσ
          rw [Finset.mem_biUnion] at hσ
          obtain ⟨A, hA, hσA⟩ := hσ
          rw [Finset.mem_filter] at hσA ⊢
          exact ⟨hσA.1, hσA.2 ▸ hA⟩
        · intro A hA B hB hAB
          simp only [Finset.disjoint_left]
          intro σ hσA hσB
          rw [Finset.mem_filter] at hσA hσB
          exact hAB (hσA.2 ▸ hσB.2)

/-- **Double counting inequality.**
`|𝒜| · n · k! · (n-k)! ≤ k · n!`.

This follows from two facts:
1. `∑_σ #{i | permArc σ i ∈ 𝒜} ≤ k · n!` (from perm_arcs_le_k)
2. `|𝒜| · n · k! · (n-k)! ≤ ∑_σ #{i | permArc σ i ∈ 𝒜}` (double counting identity) -/
lemma double_counting_ineq {n k : ℕ} (h2k : 2 * k ≤ n)
    (𝒜 : Finset (Finset (Fin n)))
    (h𝒜 : (𝒜 : Set (Finset (Fin n))).Intersecting)
    (hSized : (𝒜 : Set (Finset (Fin n))).Sized k) :
    𝒜.card * (n * k.factorial * (n - k).factorial) ≤ k * n.factorial :=
  le_trans (lower_bound_sum h2k 𝒜 h𝒜 hSized) (upper_bound_sum h2k 𝒜 h𝒜)

/-- **Factorial identity**: `C(n-1, k-1) · n · k! · (n-k)! = k · n!`. -/
lemma choose_factorial_identity {n k : ℕ} (h1k : 1 ≤ k) (hkn : k ≤ n) :
    (n - 1).choose (k - 1) * (n * k.factorial * (n - k).factorial) = k * n.factorial := by
  have hk1 : k - 1 ≤ n - 1 := by omega
  -- Use choose_symm_diff and choose_mul_factorial_mul_factorial
  have h := Nat.choose_mul_factorial_mul_factorial hk1
  -- h : (n-1).choose (k-1) * (k-1)! * (n-1-(k-1))! = (n-1)!
  have hnk : n - 1 - (k - 1) = n - k := by omega
  rw [hnk] at h
  -- k! = k * (k-1)!
  have hk_fac : k.factorial = k * (k - 1).factorial := by
    cases k with | zero => omega | succ m => simp [Nat.factorial_succ]
  -- n! = n * (n-1)!
  have hn_fac : n.factorial = n * (n - 1).factorial := by
    cases n with | zero => omega | succ m => simp [Nat.factorial_succ]
  rw [hk_fac, hn_fac]
  -- Goal: C * (n * (k * (k-1)!) * (n-k)!) = k * (n * (n-1)!)
  -- From h: C * (k-1)! * (n-k)! = (n-1)!
  -- So: C * (n * (k * (k-1)!) * (n-k)!) = n * k * (C * (k-1)! * (n-k)!) = n * k * (n-1)!
  -- And: k * (n * (n-1)!) = k * n * (n-1)!
  -- These are equal.
  have : (n - 1).choose (k - 1) * (n * (k * (k - 1).factorial) * (n - k).factorial) =
      n * k * ((n - 1).choose (k - 1) * (k - 1).factorial * (n - k).factorial) := by ring
  rw [this, h]
  ring

/-- **Erdős–Ko–Rado theorem** (Katona's cyclic permutation proof).
If `n ≥ 2k`, then the maximum size of an intersecting k-uniform family
of subsets of `Fin n` is `C(n-1, k-1)`.

The double counting gives `|𝒜| · n · k! · (n-k)! ≤ k · n!`.
Since `C(n-1, k-1) · n · k! · (n-k)! = k · n!`, we get `|𝒜| ≤ C(n-1, k-1)`. -/
theorem erdos_ko_rado {n : ℕ} {𝒜 : Finset (Finset (Fin n))} {k : ℕ}
    (h𝒜 : (𝒜 : Set (Finset (Fin n))).Intersecting)
    (hSized : (𝒜 : Set (Finset (Fin n))).Sized k)
    (hk : k ≤ n / 2) :
    𝒜.card ≤ (n - 1).choose (k - 1) := by
  -- Trivial case k = 0
  rcases Nat.eq_zero_or_pos k with rfl | h1k
  · convert Nat.zero_le _
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    exact fun A hA ↦ h𝒜 hA hA
      (by rw [Finset.disjoint_self_iff_empty, ← Finset.card_eq_zero]; exact hSized hA)
  have hkn : k ≤ n := le_trans hk (Nat.div_le_self n 2)
  have h2k : 2 * k ≤ n := by omega
  -- Use the double counting inequality and factorial identity
  have hdc := double_counting_ineq h2k 𝒜 h𝒜 hSized
  have hid := choose_factorial_identity h1k hkn
  have hpos : 0 < n * k.factorial * (n - k).factorial := by
    apply Nat.mul_pos (Nat.mul_pos (by omega) (Nat.factorial_pos k)) (Nat.factorial_pos (n - k))
  -- |𝒜| * denom ≤ k * n! = C(n-1,k-1) * denom
  rw [← hid] at hdc
  exact Nat.le_of_mul_le_mul_right hdc hpos

end ErdosKoRado

/-! ## Theorem 3: Hall's marriage theorem

The proof follows the book's inductive argument on `|ι|`, with two cases:

**Case 1 (Strict):** If the Hall condition holds *strictly* for every proper nonempty
subset (`|⋃_{i∈S} A_i| ≥ |S| + 1`), pick any representative for an arbitrary element,
remove it from the remaining sets, and apply the induction hypothesis.
(Formalized as `HallMarriageTheorem.hall_hard_inductive_step_A`.)

**Case 2 (Tight):** If some proper nonempty subset `S` satisfies `|⋃_{i∈S} A_i| = |S|`,
solve `S` and `Sᶜ` independently (removing the representatives of `S` from the sets
indexed by `Sᶜ`), then combine.
(Formalized as `HallMarriageTheorem.hall_hard_inductive_step_B`.)

The finite case (`HallMarriageTheorem.hall_hard_inductive`) is then lifted to
arbitrary index types via a compactness argument
(`Finset.all_card_le_biUnion_card_iff_existsInjective`).
-/

/-- **Hall's marriage theorem.** -/
theorem hall_marriage {ι : Type*} {α : Type*} [DecidableEq α]
    (t : ι → Finset α) :
    (∀ s : Finset ι, s.card ≤ (s.biUnion t).card) ↔
      ∃ f : ι → α, Function.Injective f ∧ ∀ x, f x ∈ t x :=
  Finset.all_card_le_biUnion_card_iff_exists_injective t

end chapter30
