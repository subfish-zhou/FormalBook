/-
Copyright 2022 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/
import Mathlib
import FormalBook.Mathlib.EdgeFinset
import Archive.Wiedijk100Theorems.AscendingDescendingSequences

/-!
# Pigeon-hole and double counting

## TODO
  - [x] statement (pigeon_hole_principle)
  - 1. Numbers
    - [x] Claim 1 (coprime pair)
    - [x] Claim 2 (divisibility)
  - 2. Sequences
    - [x] Claim 3 (Erdős–Szekeres) — via ErdosSzekeres (merged)
  - 3. Sums
    - [x] Claim 4 (contiguous sum divisible by n)
  - [x] Double Counting
  - 4. Numbers again
    - [x] sum_divisor_count (proved)
  - 5. Graphs
    - [x] sum_choose_deg_le_choose_card (proved)
    - [x] c4_free_edge_bound (proved)
  - 6. Sperner's Lemma
    - [x] sperner_lemma (proved — abstract parity version)
    - [x] sperner_lemma_exists (proved — corollary)
    - [x] brouwer_fixed_point_2d (proved — via covering space / no-retraction argument)
-/

/-! ## Erdős–Szekeres theorem

Uses the proof by Bhavik Mehta from Mathlib's Archive:
`Archive.Wiedijk100Theorems.AscendingDescendingSequences`.

**Faithfulness note:** The book assigns each element a single label tᵢ (length of
the longest increasing subsequence starting at aᵢ) and applies pigeonhole to get
n+1 elements with the same label, then argues they must be decreasing. The Mathlib
Archive proof uses a dual-label strategy (maxInc, maxDec) and applies pigeonhole to
the product {1,…,m} × {1,…,n}. The two strategies are mathematically equivalent —
the dual-label approach is a natural generalization that avoids the separate
"same-label implies decreasing" argument.
-/

namespace ErdosSzekeres

/-- Corollary: Any injective sequence of `m*n+1` elements has an increasing subsequence
of length `m+1` or a decreasing subsequence of length `n+1`. -/
theorem erdos_szekeres_fin (m n : ℕ) (f : Fin (m * n + 1) → ℝ) (hf : Function.Injective f) :
    (∃ t : Finset (Fin (m * n + 1)), m < t.card ∧ StrictMonoOn f t) ∨
    (∃ t : Finset (Fin (m * n + 1)), n < t.card ∧ StrictAntiOn f t) := by
  apply Theorems100.erdos_szekeres _ hf
  simp [Fintype.card_fin]

end ErdosSzekeres

/-! ## Brouwer Fixed Point Theorem (merged from Brouwer.lean) -/

noncomputable section BrouwerProof

open Metric Set unitInterval Topology Complex Real

private abbrev acBase : AddCircle (1 : ℝ) := QuotientAddGroup.mk 0

private def acLoop : Path acBase acBase where
  toFun t := QuotientAddGroup.mk (t : ℝ)
  continuous_toFun := continuous_quotient_mk'.comp continuous_subtype_val
  source' := rfl
  target' := by
    show QuotientAddGroup.mk (1 : ℝ) = QuotientAddGroup.mk 0
    rw [QuotientAddGroup.eq]; simp

private def acCov : IsCoveringMap (QuotientAddGroup.mk : ℝ → AddCircle (1 : ℝ)) :=
  AddCircle.isCoveringMap_coe 1

private theorem acLoop_lift_eq :
    (⟨fun t => (t : ℝ), continuous_subtype_val⟩ : C(I, ℝ)) =
    acCov.liftPath acLoop.toContinuousMap 0 rfl := by
  rw [IsCoveringMap.eq_liftPath_iff']
  exact ⟨by ext; simp [acLoop], by simp⟩

private theorem not_sc_addCircle : ¬ SimplyConnectedSpace (AddCircle (1 : ℝ)) := by
  intro hsc
  have hom := SimplyConnectedSpace.paths_homotopic acLoop (Path.refl acBase)
  have key := acCov.liftPath_apply_one_eq_of_homotopicRel hom 0 rfl rfl
  have h1 : (acCov.liftPath acLoop.toContinuousMap 0 rfl) 1 = (1 : ℝ) := by
    rw [← acLoop_lift_eq]; simp
  have h2 : (acCov.liftPath (Path.refl acBase).toContinuousMap 0 rfl) 1 = (0 : ℝ) := by
    have : (ContinuousMap.const I (0 : ℝ)) =
        acCov.liftPath (Path.refl acBase).toContinuousMap 0 rfl := by
      rw [IsCoveringMap.eq_liftPath_iff']
      exact ⟨by ext; simp only [ContinuousMap.const_zero, ContinuousMap.coe_zero,
        Function.comp_apply, Pi.zero_apply, QuotientAddGroup.mk_zero, Path.coe_toContinuousMap,
        Path.refl_apply], by simp only [ContinuousMap.const_zero, ContinuousMap.zero_apply]⟩
    rw [← this]; simp
  rw [h1, h2] at key; exact one_ne_zero key

private theorem sc_of_retract {X A : Type*}
    [TopologicalSpace X] [TopologicalSpace A] [SimplyConnectedSpace X]
    (i : C(A, X)) (r : C(X, A)) (hri : ∀ a, r (i a) = a) :
    SimplyConnectedSpace A := by
  rw [simply_connected_iff_paths_homotopic']
  have hX := (simply_connected_iff_paths_homotopic' (Y := X)).mp inferInstance
  refine ⟨⟨⟨r (Classical.arbitrary X)⟩, fun a b => ?_⟩, fun p₁ p₂ => ?_⟩
  · obtain ⟨p⟩ := hX.1.joined (i a) (i b)
    exact ⟨(p.map r.continuous).cast (hri a).symm (hri b).symm⟩
  · let q₁ := p₁.map i.continuous
    let q₂ := p₂.map i.continuous
    obtain ⟨H⟩ := hX.2 q₁ q₂
    have hH := H.map r
    have h₀ : q₁.map r.continuous = p₁.cast (hri _) (hri _) := by
      ext t; show r (i (p₁ t)) = p₁ t; exact hri (p₁ t)
    have h₁ : q₂.map r.continuous = p₂.cast (hri _) (hri _) := by
      ext t; show r (i (p₂ t)) = p₂ t; exact hri (p₂ t)
    rw [h₀, h₁] at hH
    exact ⟨hH⟩

private theorem sc_of_homeomorph {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) [hsc : SimplyConnectedSpace X] : SimplyConnectedSpace Y :=
  sc_of_retract ⟨e.symm, e.symm.continuous⟩ ⟨e, e.continuous⟩ (fun y => e.apply_symm_apply y)

private theorem not_sc_of_homeomorph {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (h : ¬ SimplyConnectedSpace X) : ¬ SimplyConnectedSpace Y := by
  intro hY
  apply h
  let _ : SimplyConnectedSpace Y := hY
  exact sc_of_homeomorph e.symm

private noncomputable def circleSphereHomeomorph : Circle ≃ₜ sphere (0 : ℂ) 1 where
  toFun z := ⟨z.1, z.2⟩
  invFun z := ⟨z.1, z.2⟩
  left_inv z := by ext; rfl
  right_inv z := by ext; rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

private theorem not_sc_sphere : ¬ SimplyConnectedSpace (sphere (0 : ℂ) 1) := by
  have h1 := not_sc_addCircle
  have h2 : ¬ SimplyConnectedSpace Circle :=
    not_sc_of_homeomorph (AddCircle.homeomorphCircle one_ne_zero) h1
  exact not_sc_of_homeomorph circleSphereHomeomorph h2

private instance : ContractibleSpace (closedBall (0 : ℂ) 1) :=
  Convex.contractibleSpace (convex_closedBall (0:ℂ) 1)
    ⟨(0 : ℂ), mem_closedBall_self one_pos.le⟩

private instance : SimplyConnectedSpace (closedBall (0 : ℂ) 1) :=
  SimplyConnectedSpace.ofContractible _

private theorem no_retraction_complex :
    ¬ ∃ (r : C(closedBall (0 : ℂ) 1, sphere (0 : ℂ) 1)),
      ∀ (x : sphere (0 : ℂ) 1), r ⟨x.1, sphere_subset_closedBall x.2⟩ = x := by
  rintro ⟨r, hr⟩
  exact not_sc_sphere (sc_of_retract
    ⟨fun x => ⟨x.1, sphere_subset_closedBall x.2⟩, continuous_inclusion sphere_subset_closedBall⟩
    r hr)

private def nsq (z : ℂ) : ℝ := ‖z‖ ^ 2

private lemma nsq_eq (z : ℂ) : nsq z = Complex.normSq z :=
  (Complex.normSq_eq_norm_sq z).symm

private def rA (f : ℂ → ℂ) (x : ℂ) : ℝ := nsq (x - f x)
private def rB (f : ℂ → ℂ) (x : ℂ) : ℝ := @inner ℝ ℂ _ (f x) (x - f x)
private def rC (f : ℂ → ℂ) (x : ℂ) : ℝ := nsq (f x) - 1
private def rDisc (f : ℂ → ℂ) (x : ℂ) : ℝ := rB f x ^ 2 - rA f x * rC f x
private def rS (f : ℂ → ℂ) (x : ℂ) : ℝ := (-rB f x + Real.sqrt (rDisc f x)) / rA f x
private def rR (f : ℂ → ℂ) (x : ℂ) : ℂ := f x + (rS f x : ℂ) * (x - f x)

private lemma rA_pos {f : ℂ → ℂ} {x : ℂ}
    (hfp : ∀ x, ‖x‖ ≤ 1 → f x ≠ x) (hx : ‖x‖ ≤ 1) : 0 < rA f x := by
  simp only [rA, nsq]; exact pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr (hfp x hx).symm)) 2

private lemma rC_nonpos {f : ℂ → ℂ} {x : ℂ}
    (hfB : ∀ x, ‖x‖ ≤ 1 → ‖f x‖ ≤ 1) (hx : ‖x‖ ≤ 1) : rC f x ≤ 0 := by
  simp only [rC, nsq]
  have h := hfB x hx
  have h_sq : ‖f x‖ ^ 2 ≤ 1 := by
    rw [pow_two, ← one_mul (1 : ℝ)]
    exact mul_self_le_mul_self (norm_nonneg _) h
  linarith [h_sq]

private lemma rDisc_nonneg {f : ℂ → ℂ} {x : ℂ}
    (hfB : ∀ x, ‖x‖ ≤ 1 → ‖f x‖ ≤ 1) (hfp : ∀ x, ‖x‖ ≤ 1 → f x ≠ x)
    (hx : ‖x‖ ≤ 1) : 0 ≤ rDisc f x := by
  simp only [rDisc]
  nlinarith [sq_nonneg (rB f x), (rA_pos hfp hx).le, rC_nonpos hfB hx]

private lemma quad_at_one (f : ℂ → ℂ) (x : ℂ) :
    rA f x + 2 * rB f x + rC f x = nsq x - 1 := by
  simp only [rA, rB, rC, nsq]
  have h : ‖f x + (x - f x)‖ ^ 2 = ‖x‖ ^ 2 := by congr 1; abel_nf
  rw [norm_add_sq_real] at h
  linarith

private lemma rS_root {f : ℂ → ℂ} {x : ℂ}
    (hfB : ∀ x, ‖x‖ ≤ 1 → ‖f x‖ ≤ 1) (hfp : ∀ x, ‖x‖ ≤ 1 → f x ≠ x)
    (hx : ‖x‖ ≤ 1) :
    rA f x * rS f x ^ 2 + 2 * rB f x * rS f x + rC f x = 0 := by
  have hA := rA_pos hfp hx
  have hΔ := rDisc_nonneg hfB hfp hx
  set B := rB f x; set C := rC f x; set A := rA f x
  set sqΔ := Real.sqrt (rDisc f x)
  have hΔeq : sqΔ ^ 2 = B ^ 2 - A * C := by
    simp only [sqΔ, rDisc]; exact Real.sq_sqrt hΔ
  have hS : rS f x = (-B + sqΔ) / A := rfl
  rw [hS]
  field_simp
  nlinarith [sq_nonneg sqΔ, hΔeq, sq_nonneg B, hA.le]

private lemma rR_norm_sq_expand (f : ℂ → ℂ) (x : ℂ) :
    nsq (rR f x) = rA f x * rS f x ^ 2 + 2 * rB f x * rS f x + rC f x + 1 := by
  simp only [rR, rA, rB, rC, nsq]
  set s := rS f x
  set a := f x
  set b := x - f x
  have hsm : (↑s : ℂ) • b = (s : ℝ) • b := Complex.coe_smul s b
  rw [show (↑s : ℂ) * b = (↑s : ℂ) • b from (smul_eq_mul ..).symm]
  rw [hsm, norm_add_sq_real a ((s : ℝ) • b), real_inner_smul_right, norm_smul,
      Real.norm_eq_abs, mul_pow, sq_abs]
  ring

private lemma rR_on_sphere {f : ℂ → ℂ} {x : ℂ}
    (hfB : ∀ x, ‖x‖ ≤ 1 → ‖f x‖ ≤ 1) (hfp : ∀ x, ‖x‖ ≤ 1 → f x ≠ x)
    (hx : ‖x‖ ≤ 1) : ‖rR f x‖ = 1 := by
  have h : nsq (rR f x) = 1 := by rw [rR_norm_sq_expand, rS_root hfB hfp hx]; ring
  simp only [nsq] at h
  have hnn := norm_nonneg (rR f x)
  nlinarith [sq_abs ‖rR f x‖]

private lemma rS_eq_one {f : ℂ → ℂ} {x : ℂ}
    (hfB : ∀ x, ‖x‖ ≤ 1 → ‖f x‖ ≤ 1) (hfp : ∀ x, ‖x‖ ≤ 1 → f x ≠ x)
    (hx : ‖x‖ ≤ 1) (hx1 : ‖x‖ = 1) : rS f x = 1 := by
  have hA := rA_pos hfp hx
  have hC := rC_nonpos hfB hx
  have hquad : rA f x + 2 * rB f x + rC f x = 0 := by
    rw [quad_at_one]; simp [nsq, hx1]
  have hBval : rB f x = -(rA f x + rC f x) / 2 := by linarith
  have hDiscEq : rDisc f x = ((rA f x - rC f x) / 2) ^ 2 := by
    simp only [rDisc, hBval]; ring
  have hAC : 0 ≤ (rA f x - rC f x) / 2 := by linarith
  simp only [rS, hBval, hDiscEq, Real.sqrt_sq hAC]
  field_simp; ring

private lemma rR_eq_on_sphere {f : ℂ → ℂ} {x : ℂ}
    (hfB : ∀ x, ‖x‖ ≤ 1 → ‖f x‖ ≤ 1) (hfp : ∀ x, ‖x‖ ≤ 1 → f x ≠ x)
    (hx : ‖x‖ ≤ 1) (hx1 : ‖x‖ = 1) : rR f x = x := by
  have h1 := rS_eq_one hfB hfp hx hx1
  simp only [rR, h1]; push_cast; ring

private lemma rR_continuousOn {f : ℂ → ℂ}
    (hfc : Continuous f) (hfp : ∀ x, ‖x‖ ≤ 1 → f x ≠ x) :
    ContinuousOn (rR f) (closedBall 0 1) := by
  have hfco : ContinuousOn f (closedBall 0 1) := hfc.continuousOn
  have hA_cont : ContinuousOn (rA f) (closedBall 0 1) :=
    (continuous_norm.comp_continuousOn (continuousOn_id.sub hfco)).pow 2
  have hB_cont : ContinuousOn (rB f) (closedBall (0 : ℂ) 1) := by
    unfold rB
    have hfco' : ContinuousOn (fun x => (f x, x - f x)) (closedBall 0 1) :=
      fun x hx => ContinuousWithinAt.prodMk (hfco x hx) ((continuousOn_id.sub hfco) x hx)
    exact continuous_inner.comp_continuousOn hfco'
  have hC_cont : ContinuousOn (rC f) (closedBall 0 1) :=
    ((continuous_norm.comp_continuousOn hfco).pow 2).sub continuousOn_const
  have hDisc_cont : ContinuousOn (rDisc f) (closedBall 0 1) := by
    unfold rDisc
    exact (hB_cont.pow 2).sub (hA_cont.mul hC_cont)
  have hSqrt_cont : ContinuousOn (fun x => Real.sqrt (rDisc f x)) (closedBall 0 1) :=
    continuous_sqrt.comp_continuousOn hDisc_cont
  have hA_ne : ∀ x ∈ closedBall (0 : ℂ) 1, rA f x ≠ 0 := fun x hx =>
    ne_of_gt (rA_pos hfp (mem_closedBall_zero_iff.mp hx))
  have hS_cont : ContinuousOn (rS f) (closedBall 0 1) := by
    unfold rS
    exact (hB_cont.neg.add hSqrt_cont).div hA_cont hA_ne
  unfold rR
  exact hfco.add ((continuous_ofReal.comp_continuousOn hS_cont).mul (continuousOn_id.sub hfco))

private theorem retraction_from_fp_free {f : ℂ → ℂ}
    (hfc : Continuous f) (hfB : ∀ x, ‖x‖ ≤ 1 → ‖f x‖ ≤ 1)
    (hfp : ∀ x, ‖x‖ ≤ 1 → f x ≠ x) :
    ∃ (r : C(closedBall (0 : ℂ) 1, sphere (0 : ℂ) 1)),
      ∀ (x : sphere (0 : ℂ) 1), r ⟨x.1, sphere_subset_closedBall x.2⟩ = x := by
  refine ⟨⟨fun x => ⟨rR f x.1, mem_sphere_zero_iff_norm.mpr
    (rR_on_sphere hfB hfp (mem_closedBall_zero_iff.mp x.2))⟩,
    (rR_continuousOn hfc hfp).comp_continuous continuous_subtype_val (fun x => x.2) |>.subtype_mk _⟩,
    fun x => ?_⟩
  ext; exact congr_arg Subtype.val (by
    simp only [ContinuousMap.coe_mk]
    congr 1; exact rR_eq_on_sphere hfB hfp
      (mem_closedBall_zero_iff.mp (sphere_subset_closedBall x.2))
      (mem_sphere_zero_iff_norm.mp x.2))

private theorem brouwer_complex
    (f : ℂ → ℂ) (hf : Continuous f) (hB : ∀ x, ‖x‖ ≤ 1 → ‖f x‖ ≤ 1) :
    ∃ x, ‖x‖ ≤ 1 ∧ f x = x := by
  by_contra h; push_neg at h
  have hfp : ∀ x, ‖x‖ ≤ 1 → f x ≠ x := fun x hx hfx => (h x hx hfx).elim
  exact no_retraction_complex (retraction_from_fp_free hf hB hfp)

theorem brouwer_fixed_point_2d_from_complex
    (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (hf : Continuous f) (hB : ∀ x, ‖x‖ ≤ 1 → ‖f x‖ ≤ 1) :
    ∃ x, ‖x‖ ≤ 1 ∧ f x = x := by
  set e := Complex.orthonormalBasisOneI.repr with he
  set g : ℂ → ℂ := fun z => e.symm (f (e z)) with hg
  have hgc : Continuous g := e.symm.continuous.comp (hf.comp e.continuous)
  have hgB : ∀ x, ‖x‖ ≤ 1 → ‖g x‖ ≤ 1 := fun x hx => by
    simp only [hg]; rw [LinearIsometryEquiv.norm_map]
    exact hB _ (by rwa [LinearIsometryEquiv.norm_map])
  obtain ⟨z, hz1, hz2⟩ := brouwer_complex g hgc hgB
  exact ⟨e z, by rwa [LinearIsometryEquiv.norm_map], by
    have := congr_arg e hz2; simp [hg] at this; exact this⟩

end BrouwerProof

namespace chapter28

theorem pigeon_hole_principle (n r : ℕ) (h : r < n) (object_to_boxes : Fin n → Fin r) :
  ∃ box : Fin r, ∃ object₁ object₂ : Fin n,
  object₁ ≠ object₂ ∧
  object_to_boxes object₁ = box ∧
  object_to_boxes object₂ = box := by
  have ⟨object₁, object₂, h_object⟩ :=
      Fintype.exists_ne_map_eq_of_card_lt object_to_boxes (by convert h <;> simp)
  use object_to_boxes object₁
  use object₁
  use object₂
  tauto



variable {α : Type*} [Fintype α] [DecidableEq α]
variable {G : SimpleGraph α} [DecidableRel G.Adj]

local prefix:100 "#" => Finset.card
local notation "E" => G.edgeFinset
local notation "d(" v ")" => G.degree v
local notation "I(" v ")" => G.incidenceFinset v

/-- **Handshaking lemma**: The sum of vertex degrees equals twice the number of edges.

This is also available in Mathlib as `SimpleGraph.sum_degrees_eq_twice_card_edges`,
which uses darts (oriented edges) as the intermediate counting object. Our proof
follows the book's double-counting argument more faithfully: we count incidence
pairs (v, e) with v ∈ e, swap the summation order via
`Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow`, then observe each edge
contributes exactly 2. -/
lemma handshaking : ∑ v, d(v) = 2 * #E := by
  calc  ∑ v, d(v)
    _ = ∑ v, #I(v)             := by simp [G.card_incidenceFinset_eq_degree]
    _ = ∑ v, #{e ∈ E | v ∈ e}  := by simp [G.incidenceFinset_eq_filter]
    _ = ∑ e ∈ E, #{v | v ∈ e}  := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow _
    -- FIXME: was (G.card_filter_mem_of_mem_edgeFinset e he)) but is commented out currently in Mathlib.EdgeFinset
    _ = ∑ e ∈ E, 2             := Finset.sum_congr rfl (λ e he ↦ by
      obtain ⟨x, y, hne, rfl⟩ := Sym2.not_isDiag_iff_exists.mp
        (SimpleGraph.not_isDiag_of_mem_edgeSet _ (SimpleGraph.mem_edgeFinset.mp he))
      have : #{v | v ∈ s(x, y)} = (s(x, y) : Finset α).card := by
        congr 1; ext v; simp
      rw [this, Sym2.card_toFinset_mk_of_ne hne])
    _ = 2 * ∑ e ∈ E, 1         := (Finset.mul_sum E (λ _ ↦ 1) 2).symm
    _ = 2 * #E                 := by rw [Finset.card_eq_sum_ones E]

section claims

/-- **Claim 1 (Coprime pair):** From any n+1 numbers in {0,...,2n-1} (representing {1,...,2n}),
two must be coprime (as values +1). -/
theorem claim1_coprime (n : ℕ)
    (S : Finset (Fin (2 * n))) (hS : n < S.card) :
    ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ Nat.Coprime (a.val + 1) (b.val + 1) := by
  let box : Fin (2 * n) → Fin n := fun x => ⟨x.val / 2, by omega⟩
  obtain ⟨a, ha, b, hb, hab, hbox⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (f := box) (by simpa using hS) (fun x _ => Finset.mem_univ _)
  refine ⟨a, ha, b, hb, hab, ?_⟩
  have hq : a.val / 2 = b.val / 2 := by
    have := congr_arg Fin.val hbox; simpa using this
  -- Same box ⇒ consecutive values ⇒ coprime
  rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hab) with hlt | hlt
  · have hcons : b.val = a.val + 1 := by omega
    rw [hcons]
    exact Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)
  · have hcons : a.val = b.val + 1 := by omega
    rw [hcons]
    exact (Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)).symm

/-- Claim 2: From {1, 2, ..., 2n}, any n+1 chosen numbers contain two where one divides the other. -/
theorem claim2_divisible (n : ℕ) (hn : 0 < n) (S : Finset ℕ)
    (hS_sub : ∀ x ∈ S, 1 ≤ x ∧ x ≤ 2 * n)
    (hS_card : S.card = n + 1) :
    ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ a ∣ b := by
  -- Map each element to its odd part (x / 2^(x.factorization 2)) then to (oddPart-1)/2.
  -- n+1 elements into n boxes → two share a box → same odd part → one divides the other.
  let op : ℕ → ℕ := fun x => x / 2 ^ (x.factorization 2)
  have hmap : ∀ x ∈ S, (op x - 1) / 2 ∈ Finset.range n := by
    intro x hx; simp [op]; have := hS_sub x hx
    exact Nat.div_lt_of_lt_mul (by have := Nat.div_le_self x (2 ^ x.factorization 2); omega)
  have hlt : (Finset.range n).card < S.card := by simp; omega
  obtain ⟨a, ha, b, hb, hne, hbox⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt hmap
  have ha_odd : ¬ 2 ∣ op a := Nat.not_dvd_ordCompl (by norm_num) (by have := hS_sub a ha; omega)
  have hb_odd : ¬ 2 ∣ op b := Nat.not_dvd_ordCompl (by norm_num) (by have := hS_sub b hb; omega)
  have ha_pos : 0 < op a :=
    Nat.div_pos (Nat.ordProj_le 2 (by have := hS_sub a ha; omega)) (by positivity)
  have hb_pos : 0 < op b :=
    Nat.div_pos (Nat.ordProj_le 2 (by have := hS_sub b hb; omega)) (by positivity)
  have hop_eq : op a = op b := by omega
  have hdvd : a ∣ b ∨ b ∣ a := by
    set ja := a.factorization 2; set jb := b.factorization 2
    have ha' : a = 2 ^ ja * (op a) := (Nat.ordProj_mul_ordCompl_eq_self a 2).symm
    have hb' : b = 2 ^ jb * (op b) := (Nat.ordProj_mul_ordCompl_eq_self b 2).symm
    rw [← hop_eq] at hb'
    rcases le_or_gt ja jb with hle | hlt
    · left; rw [ha', hb']; exact mul_dvd_mul_right (Nat.pow_dvd_pow 2 hle) _
    · right; rw [ha', hb']; exact mul_dvd_mul_right (Nat.pow_dvd_pow 2 hlt.le) _
  rcases hdvd with h | h
  · exact ⟨a, ha, b, hb, hne, h⟩
  · exact ⟨b, hb, a, ha, Ne.symm hne, h⟩

/-- **Claim 3 (Erdős–Szekeres):** Any injective sequence of mn+1 distinct reals has an
increasing subsequence of length m+1 or a decreasing subsequence of length n+1. -/
theorem claim3_erdos_szekeres (m n : ℕ) (f : Fin (m * n + 1) → ℝ) (hf : Function.Injective f) :
    (∃ t : Finset (Fin (m * n + 1)), m < t.card ∧ StrictMonoOn f t) ∨
    (∃ t : Finset (Fin (m * n + 1)), n < t.card ∧ StrictAntiOn f t) :=
  ErdosSzekeres.erdos_szekeres_fin m n f hf

/-- **Claim 4 (Contiguous sum divisible by n):** Given n integers, there exists a nonempty
contiguous subsequence whose sum is divisible by n. -/
theorem claim4_contiguous_sum (n : ℕ) (hn : 0 < n) (a : Fin n → ℤ) :
    ∃ (l r : Fin n), l ≤ r ∧ (n : ℤ) ∣ ∑ i ∈ Finset.Icc l r, a i := by
  set s : Fin (n + 1) → ℤ :=
    fun i => ∑ j : Fin n, if j.val < i.val then a j else 0 with hs_def
  have hnn : (0 : ℤ) < ↑n := by omega
  let f : Fin (n+1) → Fin n := fun i =>
    ⟨(s i % ↑n).toNat, by
      have h1 := Int.emod_nonneg (s i) (ne_of_gt hnn)
      have h2 := Int.emod_lt_of_pos (s i) hnn
      omega⟩
  obtain ⟨i, j, hij, hfij⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by simp)
  have hmod : s i % ↑n = s j % ↑n := by
    have h0 := congr_arg Fin.val hfij
    simp [f] at h0
    have := Int.emod_nonneg (s i) (ne_of_gt hnn)
    have := Int.emod_nonneg (s j) (ne_of_gt hnn)
    omega
  obtain ⟨i', j', hi'j', hmod'⟩ : ∃ i' j' : Fin (n+1), i' < j' ∧ s i' % ↑n = s j' % ↑n := by
    rcases lt_or_gt_of_ne hij with h | h
    · exact ⟨i, j, h, hmod⟩
    · exact ⟨j, i, h, hmod.symm⟩
  have hdvd : (n : ℤ) ∣ s j' - s i' := by
    rw [Int.dvd_iff_emod_eq_zero, ← Int.emod_eq_emod_iff_emod_sub_eq_zero]
    exact hmod'.symm
  have hi'_lt_n : i'.val < n := by omega
  suffices hsuff : s j' - s i' =
      ∑ k ∈ Finset.Icc (⟨i'.val, hi'_lt_n⟩ : Fin n) ⟨j'.val - 1, by omega⟩, a k by
    exact ⟨⟨i'.val, hi'_lt_n⟩, ⟨j'.val - 1, by omega⟩, by simp [Fin.le_def]; omega, hsuff ▸ hdvd⟩
  simp only [s, ← Finset.sum_sub_distrib]
  trans ∑ k : Fin n, if i'.val ≤ k.val ∧ k.val < j'.val then a k else 0
  · congr 1; ext ⟨k, hk⟩
    by_cases h1 : k < j'.val
    all_goals by_cases h2 : k < i'.val
    all_goals simp_all
    all_goals omega
  · rw [← Finset.sum_filter]; congr 1; ext ⟨k, hk⟩
    simp [Finset.mem_filter, Finset.mem_Icc, Fin.le_def]; omega


end claims

/-! ## Double Counting -/

/-- Double counting: the sum over rows of the number of related columns equals
the sum over columns of the number of related rows. This is a direct wrapper
around Mathlib's `Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow`. -/
theorem double_counting {α β : Type*}
    (R : Finset α) (C : Finset β) (r : α → β → Prop) [∀ a b, Decidable (r a b)] :
    (∑ p ∈ R, (Finset.bipartiteAbove r C p).card) =
    (∑ q ∈ C, (Finset.bipartiteBelow r R q).card) :=
  Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow r

/-! ## 5. Graphs — C₄-free edge bound -/

/-- In a C₄-free graph, the sum of C(d(v), 2) over all vertices is at most C(n, 2).

This is the key combinatorial inequality: each pair of vertices can have at most one
common neighbor (otherwise they'd form a 4-cycle), so the number of "cherries"
(paths of length 2) is at most the number of vertex pairs. -/
theorem sum_choose_deg_le_choose_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hC4 : ∀ (a b c d : V), a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      ¬(G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) :
    ∑ v : V, (G.degree v).choose 2 ≤ (Fintype.card V).choose 2 := by
  -- Each C(d(v),2) counts 2-element subsets of neighbors
  have key : ∀ v : V, (G.degree v).choose 2 = #((G.neighborFinset v).powersetCard 2) := by
    intro v; rw [Finset.card_powersetCard, SimpleGraph.card_neighborFinset_eq_degree]
  simp_rw [key]
  -- LHS = #(Σ v, (neighborFinset v).powersetCard 2)
  -- RHS = #(univ.powersetCard 2)
  calc ∑ v : V, #((G.neighborFinset v).powersetCard 2)
      = #(Finset.univ.sigma (fun v => (G.neighborFinset v).powersetCard 2)) := by
          rw [Finset.card_sigma]
    _ ≤ #((Finset.univ : Finset V).powersetCard 2) := ?_
    _ = (Fintype.card V).choose 2 := by rw [Finset.card_powersetCard, Finset.card_univ]
  -- Injection from sigma to powersetCard 2 univ
  apply Finset.card_le_card_of_injOn Sigma.snd
  · -- maps into target
    intro ⟨v, p⟩ hx
    simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe, Finset.mem_powersetCard] at hx ⊢
    exact ⟨hx.2.1.trans (Finset.subset_univ _), hx.2.2⟩
  · -- injective (C₄-free condition)
    intro ⟨v₁, p₁⟩ hx₁ ⟨v₂, p₂⟩ hx₂ (hfx : p₁ = p₂)
    subst hfx
    simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe, Finset.mem_powersetCard] at hx₁ hx₂
    have hp₁ := hx₁.2
    have hp₂ := hx₂.2
    suffices v₁ = v₂ by subst this; rfl
    by_contra hne
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 hp₁.2
    have ha₁ : G.Adj v₁ a := by
      rw [← SimpleGraph.mem_neighborFinset]; exact hp₁.1 (Finset.mem_insert_self a {b})
    have hb₁ : G.Adj v₁ b := by
      rw [← SimpleGraph.mem_neighborFinset]; exact hp₁.1 (Finset.mem_insert.2 (Or.inr (Finset.mem_singleton_self b)))
    have ha₂ : G.Adj v₂ a := by
      rw [← SimpleGraph.mem_neighborFinset]; exact hp₂.1 (Finset.mem_insert_self a {b})
    have hb₂ : G.Adj v₂ b := by
      rw [← SimpleGraph.mem_neighborFinset]; exact hp₂.1 (Finset.mem_insert.2 (Or.inr (Finset.mem_singleton_self b)))
    have hv₁a : v₁ ≠ a := G.ne_of_adj ha₁
    have hv₁b : v₁ ≠ b := G.ne_of_adj hb₁
    have hv₂a : v₂ ≠ a := G.ne_of_adj ha₂
    have hv₂b : v₂ ≠ b := G.ne_of_adj hb₂
    exact hC4 v₁ a v₂ b hv₁a hne hv₁b (Ne.symm hv₂a) hab hv₂b
      ⟨ha₁, ha₂.symm, hb₂, hb₁.symm⟩

/-- If a simple graph on n vertices contains no 4-cycle (C₄), then
|E| ≤ ⌊n/4 · (1 + √(4n − 3))⌋.

The proof uses `sum_choose_deg_le_choose_card` together with the handshaking lemma
and Cauchy–Schwarz / Jensen. -/
theorem c4_free_edge_bound
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hC4 : ∀ (a b c d : V), a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      ¬(G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (n : ℕ) (hn : Fintype.card V = n) :
    G.edgeFinset.card ≤ ⌊(n : ℝ) / 4 * (1 + Real.sqrt (4 * n - 3))⌋₊ := by
  -- Let e = G.edgeFinset.card
  set e := G.edgeFinset.card with he_def
  -- Step 0: Get the key inequality from C₄-free condition
  have hchoose := sum_choose_deg_le_choose_card G hC4
  -- Step 1: Cast everything to ℝ
  -- We need: (e : ℝ) ≤ n/4 * (1 + √(4n-3))
  -- Then Nat.floor gives us the result
  suffices h : (e : ℝ) ≤ (n : ℝ) / 4 * (1 + Real.sqrt (4 * (n : ℝ) - 3)) by
    exact Nat.le_floor h
  -- Step 2: From sum_choose to sum_sq bound (in ℝ)
  -- ∑ C(d(v), 2) ≤ C(n, 2) means ∑ d(v)*(d(v)-1) ≤ n*(n-1)
  -- i.e., ∑ d(v)² - ∑ d(v) ≤ n*(n-1)
  -- i.e., ∑ d(v)² ≤ n*(n-1) + 2*e  (using handshaking)
  have hhand : ∑ v : V, G.degree v = 2 * e := handshaking
  have sum_sq_bound : ∑ v : V, ((G.degree v : ℝ) ^ 2) ≤ (n : ℝ) * ((n : ℝ) - 1) + 2 * (e : ℝ) := by
    have h_real : (∑ v : V, (G.degree v : ℝ) * ((G.degree v : ℝ) - 1)) ≤ (n : ℝ) * ((n : ℝ) - 1) := by
      have h1 : ∀ k : ℕ, (k : ℝ) * ((k : ℝ) - 1) = 2 * (k.choose 2 : ℝ) := by
        intro k; rw [Nat.cast_choose_two (K := ℝ)]; ring
      have hc : (∑ v : V, (G.degree v).choose 2 : ℝ) ≤ ((n.choose 2 : ℕ) : ℝ) := by
        exact_mod_cast (hn ▸ hchoose)
      calc ∑ v : V, (G.degree v : ℝ) * ((G.degree v : ℝ) - 1)
          = ∑ v : V, 2 * ((G.degree v).choose 2 : ℝ) := by simp_rw [h1]
        _ = 2 * ∑ v : V, ((G.degree v).choose 2 : ℝ) := by rw [Finset.mul_sum]
        _ ≤ 2 * ((n.choose 2 : ℕ) : ℝ) := by linarith
        _ = (n : ℝ) * ((n : ℝ) - 1) := by rw [← h1]
    -- d*(d-1) = d² - d
    have h_eq : ∀ v : V, (G.degree v : ℝ) * ((G.degree v : ℝ) - 1) =
        (G.degree v : ℝ) ^ 2 - (G.degree v : ℝ) := by intro v; ring
    simp_rw [h_eq] at h_real
    -- h_real: ∑ (d² - d) ≤ n*(n-1)
    -- i.e., ∑ d² - ∑ d ≤ n*(n-1)
    have h_sub : ∑ v : V, ((G.degree v : ℝ) ^ 2 - (G.degree v : ℝ)) =
        (∑ v : V, (G.degree v : ℝ) ^ 2) - (∑ v : V, (G.degree v : ℝ)) := by
      rw [← Finset.sum_sub_distrib]
    rw [h_sub] at h_real
    have h5 : (∑ v : V, (G.degree v : ℝ)) = 2 * (e : ℝ) := by exact_mod_cast hhand
    linarith
  -- Step 3: Cauchy-Schwarz: (∑ d(v))² ≤ n * ∑ d(v)²
  have n_eq : Fintype.card V = n := hn
  have cauchy : (∑ v : V, (G.degree v : ℝ)) ^ 2 ≤
      (Fintype.card V : ℝ) * ∑ v : V, (G.degree v : ℝ) ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun v : V => (G.degree v : ℝ))
    rwa [Finset.card_univ] at h
  rw [n_eq] at cauchy
  -- Step 4: Combine: (2e)² ≤ n * (n(n-1) + 2e)
  have sum_deg_real : (∑ v : V, (G.degree v : ℝ)) = 2 * (e : ℝ) := by
    exact_mod_cast hhand
  rw [sum_deg_real] at cauchy
  -- cauchy: (2*e)² ≤ n * ∑ d(v)²
  -- sum_sq_bound: ∑ d(v)² ≤ n*(n-1) + 2*e
  -- So: 4*e² ≤ n * (n*(n-1) + 2*e) = n²*(n-1) + 2*n*e
  have key : 4 * (e : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 * ((n : ℝ) - 1) + 2 * (n : ℝ) * (e : ℝ) := by
    have h1 : (2 * (e : ℝ)) ^ 2 = 4 * (e : ℝ) ^ 2 := by ring
    rw [h1] at cauchy
    calc 4 * (e : ℝ) ^ 2
        ≤ (n : ℝ) * ∑ v : V, (G.degree v : ℝ) ^ 2 := cauchy
      _ ≤ (n : ℝ) * ((n : ℝ) * ((n : ℝ) - 1) + 2 * (e : ℝ)) := by
            apply mul_le_mul_of_nonneg_left sum_sq_bound (Nat.cast_nonneg n)
      _ = (n : ℝ) ^ 2 * ((n : ℝ) - 1) + 2 * (n : ℝ) * (e : ℝ) := by ring
  -- Step 5: Solve quadratic: 4e² - 2ne - n²(n-1) ≤ 0
  -- e ≤ (2n + √(4n² + 16n²(n-1))) / 8 = (2n + 2n√(4n-3)) / 8 = n/4 * (1 + √(4n-3))
  -- Equivalently: e ≤ n/4 * (1 + √(4n-3))
  -- This means: 4e ≤ n * (1 + √(4n-3))
  -- i.e., 4e - n ≤ n * √(4n-3)
  -- Squaring (if 4e - n ≤ 0, done; otherwise): (4e - n)² ≤ n² * (4n - 3)
  -- (4e-n)² = 16e² - 8ne + n² ≤ 4n²(n-1) + 8ne - 8ne + n² = 4n³ - 4n² + n² = 4n³ - 3n²
  -- = n²(4n-3) ✓
  by_cases hn0 : n = 0
  · subst hn0
    have hcard : Fintype.card V = 0 := hn
    have he0 : e = 0 := by
      rw [he_def]
      have h := SimpleGraph.card_edgeFinset_le_card_choose_two (G := G)
      rw [hcard] at h
      have : Nat.choose 0 2 = 0 := by decide
      rw [this] at h; omega
    simp [he0]
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)
  -- We want: e ≤ n/4 * (1 + √(4n-3))
  -- Suffices: 4*e ≤ n + n * √(4n-3)
  suffices h4e : 4 * (e : ℝ) ≤ (n : ℝ) + (n : ℝ) * Real.sqrt (4 * (n : ℝ) - 3) by
    linarith [mul_comm ((n : ℝ) / 4) (1 + Real.sqrt (4 * (n : ℝ) - 3)),
              show (n : ℝ) / 4 * (1 + Real.sqrt (4 * (n : ℝ) - 3)) =
                ((n : ℝ) + (n : ℝ) * Real.sqrt (4 * (n : ℝ) - 3)) / 4 by ring]
  -- If 4e ≤ n, done since n * √(4n-3) ≥ 0
  by_cases h4e_le : 4 * (e : ℝ) ≤ (n : ℝ)
  · linarith [mul_nonneg (Nat.cast_nonneg n) (Real.sqrt_nonneg (4 * (n : ℝ) - 3))]
  push_neg at h4e_le
  -- Otherwise 4e > n, so 4e - n > 0. We square both sides.
  rw [show 4 * (e : ℝ) ≤ (n : ℝ) + (n : ℝ) * Real.sqrt (4 * (n : ℝ) - 3) ↔
      4 * (e : ℝ) - (n : ℝ) ≤ (n : ℝ) * Real.sqrt (4 * (n : ℝ) - 3) by constructor <;> intro h <;> linarith]
  -- Need: 4n - 3 ≥ 0 for sqrt to be meaningful
  have h4n3 : (0 : ℝ) ≤ 4 * (n : ℝ) - 3 := by
    have : 1 ≤ n := Nat.pos_of_ne_zero hn0
    linarith [show (1 : ℝ) ≤ (n : ℝ) from Nat.one_le_cast.mpr this]
  -- Square both sides (LHS > 0, RHS ≥ 0)
  have hlhs_pos : 0 < 4 * (e : ℝ) - (n : ℝ) := by linarith
  -- Suffices to show (4e - n)² ≤ n² * (4n - 3)
  -- Then take sqrt of both sides
  have hsq : (4 * (e : ℝ) - (n : ℝ)) ^ 2 ≤ (n : ℝ) ^ 2 * (4 * (n : ℝ) - 3) := by
    nlinarith [sq_nonneg (e : ℝ), sq_nonneg (n : ℝ),
               show (0 : ℝ) ≤ (e : ℝ) from Nat.cast_nonneg e,
               show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n]
  have hrhs_nn : 0 ≤ (n : ℝ) ^ 2 * (4 * (n : ℝ) - 3) := by
    apply mul_nonneg (sq_nonneg _) h4n3
  calc 4 * (e : ℝ) - (n : ℝ)
      ≤ |4 * (e : ℝ) - (n : ℝ)| := le_abs_self _
    _ = Real.sqrt ((4 * (e : ℝ) - (n : ℝ)) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((n : ℝ) ^ 2 * (4 * (n : ℝ) - 3)) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt ((n : ℝ) ^ 2) * Real.sqrt (4 * (n : ℝ) - 3) :=
        Real.sqrt_mul (sq_nonneg _) _
    _ = (n : ℝ) * Real.sqrt (4 * (n : ℝ) - 3) := by
        rw [Real.sqrt_sq (le_of_lt hn_pos)]

/-! ## 4. Numbers again -/

/-- **Double counting for divisor sums:**
    Σ_{j=1}^{n} (number of divisors of j) = Σ_{i=1}^{n} ⌊n/i⌋.

    Both sides count pairs (i, j) with 1 ≤ i ≤ n, 1 ≤ j ≤ n, and i ∣ j.
    LHS groups by j (divisors of j), RHS groups by i (multiples of i up to n). -/
theorem sum_divisor_count (n : ℕ) :
    ∑ j ∈ Finset.Icc 1 n, (Nat.divisors j).card = ∑ i ∈ Finset.Icc 1 n, n / i := by
  have key := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (· ∣ ·)
    (s := Finset.Icc 1 n) (t := Finset.Icc 1 n)
  suffices h1 : ∀ i ∈ Finset.Icc 1 n,
      (Finset.bipartiteAbove (· ∣ ·) (Finset.Icc 1 n) i).card = n / i by
    suffices h2 : ∀ j ∈ Finset.Icc 1 n,
        (Finset.bipartiteBelow (· ∣ ·) (Finset.Icc 1 n) j).card = (Nat.divisors j).card by
      rw [← Finset.sum_congr rfl h1, key, Finset.sum_congr rfl h2]
    · intro j hj
      simp only [Finset.mem_Icc] at hj
      have hj0 : j ≠ 0 := by omega
      congr 1
      simp only [Finset.bipartiteBelow]
      rw [← Nat.filter_dvd_eq_divisors hj0]
      ext d
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
      constructor
      · rintro ⟨⟨hd1, hdn⟩, hdj⟩
        exact ⟨Nat.lt_succ_of_le (Nat.le_of_dvd (by omega) hdj), hdj⟩
      · rintro ⟨hd_lt, hdj⟩
        refine ⟨⟨?_, ?_⟩, hdj⟩
        · by_contra h; push_neg at h; interval_cases d; simp at hdj; exact hj0 hdj
        · exact le_trans (Nat.le_of_dvd (by omega) hdj) hj.2
  · intro i hi
    have hioc : Finset.Ioc 0 n = Finset.Icc 1 n := by
      ext x; simp [Finset.mem_Ioc, Finset.mem_Icc, Nat.lt_iff_add_one_le]
    rw [show Finset.bipartiteAbove (· ∣ ·) (Finset.Icc 1 n) i =
        {j ∈ Finset.Icc 1 n | i ∣ j} from rfl, ← hioc]
    exact Nat.Ioc_filter_dvd_card_eq_div n i

/-- The average number of divisors is bounded by the harmonic sum:
  `∑ j in [1,n], t(j) ≤ n * Hₙ` where `t(j) = #(divisors j)` and `Hₙ = ∑ 1/i`. -/
theorem avg_divisor_count_le_harmonic (n : ℕ) :
    (∑ j ∈ Finset.Icc 1 n, (Nat.divisors j).card : ℚ) ≤
    ↑n * ∑ i ∈ Finset.Icc 1 n, (1 : ℚ) / ↑i := by
  have h := sum_divisor_count n
  have : (∑ j ∈ Finset.Icc 1 n, (Nat.divisors j).card : ℤ) =
      ∑ i ∈ Finset.Icc 1 n, (n / i : ℤ) := by exact_mod_cast h
  calc (∑ j ∈ Finset.Icc 1 n, (Nat.divisors j).card : ℚ)
      = ∑ i ∈ Finset.Icc 1 n, (↑(n / i) : ℚ) := by exact_mod_cast this
    _ ≤ ∑ i ∈ Finset.Icc 1 n, ↑n / ↑i := by
        apply Finset.sum_le_sum
        intro i _
        exact Nat.cast_div_le
    _ = ↑n * ∑ i ∈ Finset.Icc 1 n, 1 / ↑i := by
        rw [Finset.mul_sum]
        congr 1; ext i; ring

/-- Lower bound: ∑ t(j) > n·Hₙ − n, i.e., t̄(n) > Hₙ − 1 > log n − 1. -/
theorem avg_divisor_count_lower_bound (n : ℕ) (hn : 0 < n) :
    ↑n * ∑ i ∈ Finset.Icc 1 n, (1 : ℚ) / ↑i - ↑n <
    (∑ j ∈ Finset.Icc 1 n, (Nat.divisors j).card : ℚ) := by
  have h := sum_divisor_count n
  have hrw : (∑ j ∈ Finset.Icc 1 n, (Nat.divisors j).card : ℚ) =
      ∑ i ∈ Finset.Icc 1 n, (↑(n / i) : ℚ) := by exact_mod_cast h
  rw [hrw, Finset.mul_sum]
  have hsize : (Finset.Icc 1 n).card = n := by simp [Nat.card_Icc]
  suffices h_diff : ∑ i ∈ Finset.Icc 1 n, (↑n * (1 / ↑i) - ↑(n / i) : ℚ) < ↑n by
    have := Finset.sum_sub_distrib (s := Finset.Icc 1 n)
      (f := fun i => ↑n * (1 / (↑i : ℚ))) (g := fun i => (↑(n / i) : ℚ))
    linarith
  calc ∑ i ∈ Finset.Icc 1 n, (↑n * (1 / ↑i) - ↑(n / i) : ℚ)
      < ∑ _i ∈ Finset.Icc 1 n, (1 : ℚ) := by
        apply Finset.sum_lt_sum
        · intro i hi
          have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
          have hi_pos : (0 : ℚ) < ↑i := by positivity
          -- Need: n * (1/i) - ↑(n/i) ≤ 1
          -- i.e. n/i - 1 ≤ ↑(n/i), i.e. n/i < ↑(n/i) + 1 + 1... no.
          -- n * (1/i) - ↑(n/i) ≤ 1
          -- ↔ n/i ≤ ↑(n/i) + 1
          -- ↔ n ≤ (↑(n/i) + 1) * i  (since i > 0)
          -- This follows from Nat.lt_div_mul_add: n < n/i * i + i = (n/i) * i + i
          -- So n ≤ (n/i) * i + i - 1 < (n/i + 1) * i
          rw [mul_one_div, sub_le_iff_le_add, div_le_iff₀ hi_pos]
          have h1 := Nat.lt_div_mul_add (a := n) (by omega : 0 < i)
          have h2 : (↑n : ℚ) < ↑(n / i) * ↑i + ↑i := by exact_mod_cast h1
          linarith
        · exact ⟨1, Finset.mem_Icc.mpr ⟨le_refl _, hn⟩, by simp [Nat.div_one]⟩
    _ = ↑n := by simp [hsize]

/-! ### Dimension of Kₙ via iterated Erdős-Szekeres

The **dimension** of the complete graph Kₙ is the minimum number of linear orders
(permutations) such that no 3-element subset is simultaneously monotone in all orders.

**Theorem:** dim(Kₙ) ≥ ⌈log₂(⌈log₂ n⌉)⌉ for n ≥ 3.

The proof uses an iterated Erdős-Szekeres argument: given p injective functions on n elements
with n > 2^(2^p), repeated extraction of monotone subsequences (one per function) yields
a subset of size > 2 that is simultaneously monotone in all functions.

This means p linear orders cannot "separate" all triples, so dim(Kₙ) > p.
Taking the contrapositive with p = ⌈log₂(⌈log₂ n⌉)⌉ − 1 gives the bound. -/

namespace KnDimension

/-- **Erdős-Szekeres on finsets**: Given a finset S of size > m² and a function f injective
    on S, there exists a subset T ⊆ S of size > m on which f is monotone. -/
theorem erdos_szekeres_finset {n m : ℕ} (f : Fin n → ℝ) (S : Finset (Fin n))
    (hcard : m * m < S.card) (hf : Set.InjOn f (↑S : Set (Fin n))) :
    ∃ T ⊆ S, m < T.card ∧
      (StrictMonoOn f (↑T : Set (Fin n)) ∨ StrictAntiOn f (↑T : Set (Fin n))) := by
  have hfinj : Function.Injective (fun (x : S) => f x.val) := by
    intro ⟨a, ha⟩ ⟨b, hb⟩ (h : f a = f b)
    exact Subtype.ext (hf (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) h)
  have hcard' : m * m < Fintype.card S := by rwa [Fintype.card_coe]
  rcases Theorems100.erdos_szekeres hcard' hfinj with ⟨t, ht_card, ht_mono⟩ | ⟨t, ht_card, ht_anti⟩
  · refine ⟨t.map (Function.Embedding.subtype _), ?_, ?_, Or.inl ?_⟩
    · intro x hx
      simp only [Finset.mem_map, Function.Embedding.subtype] at hx
      obtain ⟨⟨y, hy⟩, _, rfl⟩ := hx; exact hy
    · rw [Finset.card_map]; exact ht_card
    · intro a ha b hb hab
      simp only [Finset.coe_map, Set.mem_image, Function.Embedding.subtype] at ha hb
      obtain ⟨⟨a', ha'S⟩, ha'_mem, rfl⟩ := ha
      obtain ⟨⟨b', hb'S⟩, hb'_mem, rfl⟩ := hb
      exact ht_mono ha'_mem hb'_mem hab
  · refine ⟨t.map (Function.Embedding.subtype _), ?_, ?_, Or.inr ?_⟩
    · intro x hx
      simp only [Finset.mem_map, Function.Embedding.subtype] at hx
      obtain ⟨⟨y, hy⟩, _, rfl⟩ := hx; exact hy
    · rw [Finset.card_map]; exact ht_card
    · intro a ha b hb hab
      simp only [Finset.coe_map, Set.mem_image, Function.Embedding.subtype] at ha hb
      obtain ⟨⟨a', ha'S⟩, ha'_mem, rfl⟩ := ha
      obtain ⟨⟨b', hb'S⟩, hb'_mem, rfl⟩ := hb
      exact ht_anti ha'_mem hb'_mem hab

/-- **Iterated Erdős-Szekeres**: Given p injective functions on Fin n and a finset S
    with |S| > 2^(2^p), there exists a subset T ⊆ S with |T| > 2 that is simultaneously
    monotone (each function is either strictly increasing or strictly decreasing on T). -/
theorem iterated_erdos_szekeres :
    ∀ (p : ℕ) {n : ℕ} (fs : Fin p → (Fin n → ℝ)) (S : Finset (Fin n)),
    (∀ i, Set.InjOn (fs i) (↑S : Set (Fin n))) →
    2 ^ 2 ^ p < S.card →
    ∃ T ⊆ S, 2 < T.card ∧
      ∀ i : Fin p, StrictMonoOn (fs i) (↑T : Set (Fin n)) ∨
                    StrictAntiOn (fs i) (↑T : Set (Fin n))
  | 0, _, _, S, _, hS => by
    simp only [Nat.pow_zero, pow_one] at hS
    exact ⟨S, Finset.Subset.refl S, hS, fun i => i.elim0⟩
  | p + 1, _, fs, S, hfs, hS => by
    have harith : 2 ^ 2 ^ p * (2 ^ 2 ^ p) < S.card := by
      have h : 2 ^ 2 ^ (p + 1) = 2 ^ 2 ^ p * (2 ^ 2 ^ p) := by
        rw [pow_succ, pow_mul, sq]
      linarith
    obtain ⟨T₁, hT₁S, hT₁card, hT₁mono⟩ :=
      erdos_szekeres_finset (fs 0) S harith (hfs 0)
    have hfs' : ∀ i : Fin p, Set.InjOn (fs i.succ) (↑T₁ : Set (Fin _)) :=
      fun i => (hfs i.succ).mono (Finset.coe_subset.mpr hT₁S)
    obtain ⟨T₂, hT₂T₁, hT₂card, hT₂mono⟩ :=
      iterated_erdos_szekeres p (fun i => fs i.succ) T₁ hfs' hT₁card
    refine ⟨T₂, hT₂T₁.trans hT₁S, hT₂card, ?_⟩
    intro ⟨i, hi⟩
    match i, hi with
    | 0, _ =>
      rcases hT₁mono with h | h
      · exact Or.inl (h.mono (Finset.coe_subset.mpr hT₂T₁))
      · exact Or.inr (h.mono (Finset.coe_subset.mpr hT₂T₁))
    | i + 1, hi =>
      exact hT₂mono ⟨i, Nat.lt_of_succ_lt_succ hi⟩

/-- **Simultaneous monotone triple**: For n > 2^(2^p) and p injective functions
    Fin n → ℝ, there exists a subset of size > 2 that is monotone for all of them.

    This captures the lower bound dim(Kₙ) ≥ ⌈log₂(⌈log₂ n⌉)⌉: fewer than
    ⌈log₂(⌈log₂ n⌉)⌉ linear orders cannot separate all triples. -/
theorem kn_dimension_bound (p n : ℕ) (hn : 2 ^ 2 ^ p < n)
    (fs : Fin p → (Fin n → ℝ)) (hfs : ∀ i, Function.Injective (fs i)) :
    ∃ T : Finset (Fin n), 2 < T.card ∧
      ∀ i : Fin p, StrictMonoOn (fs i) ↑T ∨ StrictAntiOn (fs i) ↑T := by
  have huniv : 2 ^ 2 ^ p < (Finset.univ : Finset (Fin n)).card := by
    simp [Finset.card_univ, Fintype.card_fin]; exact hn
  obtain ⟨T, _, hT_card, hT_mono⟩ := iterated_erdos_szekeres p fs Finset.univ
    (fun i => (hfs i).injOn) huniv
  exact ⟨T, hT_card, hT_mono⟩

/-- **Ceiling-log formulation**: If p < ⌈log₂(⌈log₂ n⌉)⌉, then p injective functions
    on Fin n cannot separate all triples. This is the dim(Kₙ) ≥ ⌈log₂(⌈log₂ n⌉)⌉ bound. -/
theorem kn_dimension_clog_bound (n p : ℕ) (hp : p < Nat.clog 2 (Nat.clog 2 n))
    (fs : Fin p → (Fin n → ℝ)) (hfs : ∀ i, Function.Injective (fs i)) :
    ∃ T : Finset (Fin n), 2 < T.card ∧
      ∀ i : Fin p, StrictMonoOn (fs i) ↑T ∨ StrictAntiOn (fs i) ↑T := by
  apply kn_dimension_bound _ _ _ _ hfs
  exact (Nat.lt_clog_iff_pow_lt (by norm_num)).mp
    ((Nat.lt_clog_iff_pow_lt (by norm_num)).mp hp)

end KnDimension

/-! ## 6. Sperner's Lemma -/

/-- An abstract simplicial 2-complex: a collection of triangles (3-element subsets). -/
structure Triangulation (m : ℕ) where
  /-- The collection of triangles (3-element subsets of vertices). -/
  triangles : Finset (Finset (Fin m))
  triangle_card : ∀ t ∈ triangles, t.card = 3

/-- A triangle is rainbow (tricolored) under coloring `c` if its vertices receive
    all three colors {0, 1, 2}. -/
def isRainbow {m : ℕ} (c : Fin m → Fin 3) (t : Finset (Fin m)) : Prop :=
  t.image c = {0, 1, 2}

instance {m : ℕ} (c : Fin m → Fin 3) (t : Finset (Fin m)) : Decidable (isRainbow c t) :=
  inferInstanceAs (Decidable (t.image c = {0, 1, 2}))

omit [Fintype α] [DecidableEq α] in
/-- Auxiliary parity lemma: if `f` maps each element of a finset to `{0, 1, 2}`,
    and the sum `∑ f` is odd, then the number of elements with `f = 1` is odd.
    This is the combinatorial core of Sperner's lemma (the double-counting/parity argument). -/
private theorem odd_card_filter_eq_one {S : Finset α} {f : α → ℕ}
    (hf : ∀ s ∈ S, f s = 0 ∨ f s = 1 ∨ f s = 2)
    (hsum : Odd (∑ s ∈ S, f s)) :
    Odd (S.filter (fun s => f s = 1)).card := by
  -- Show: ∑ f = #{f=1} + 2 * #{f=2}, so #{f=1} has same parity as ∑ f.
  set S₁ := S.filter (fun s => f s = 1)
  set S₂ := S.filter (fun s => f s = 2)
  suffices hkey : ∑ s ∈ S, f s = S₁.card + 2 * S₂.card by
    rw [hkey] at hsum; obtain ⟨k, hk⟩ := hsum; rw [Nat.odd_iff]; omega
  -- Decompose: f s = 𝟙_{f=1}(s) + 2·𝟙_{f=2}(s)
  have hind : ∀ s ∈ S, f s = (if f s = 1 then 1 else 0) + 2 * (if f s = 2 then 1 else 0) := by
    intro s hs; rcases hf s hs with h | h | h <;> simp [h]
  rw [Finset.sum_congr rfl hind, Finset.sum_add_distrib]
  simp only [Finset.sum_boole]
  congr 1
  rw [← Finset.mul_sum, Finset.sum_boole]
  simp; rfl

/-- **Sperner's Lemma** (combinatorial, odd-count version).

    Given a triangulation with a 3-coloring and a "12-edge count" function `count12`
    that assigns to each triangle the number of edges connecting a vertex of color 1
    to a vertex of color 2, if:
    1. Rainbow triangles are exactly those with an odd 12-edge count (`count12 = 1`),
    2. Each triangle has 0, 1, or 2 such edges,
    3. The total sum of 12-edge counts is odd (from the Sperner boundary condition
       and the double-counting argument: each interior 12-edge is shared by exactly
       two triangles, so contributes evenly, while boundary 12-edges contribute once),
    then the number of rainbow triangles is odd. -/
theorem sperner_lemma {m : ℕ} (T : Triangulation m) (c : Fin m → Fin 3)
    (count12 : Finset (Fin m) → ℕ)
    (h_rainbow_iff : ∀ t ∈ T.triangles, isRainbow c t ↔ count12 t = 1)
    (h_range : ∀ t ∈ T.triangles, count12 t = 0 ∨ count12 t = 1 ∨ count12 t = 2)
    (h_odd_sum : Odd (∑ t ∈ T.triangles, count12 t)) :
    Odd (T.triangles.filter (isRainbow c)).card := by
  have hfilt : T.triangles.filter (isRainbow c) =
      T.triangles.filter (fun t => count12 t = 1) := by
    ext t; simp only [Finset.mem_filter]
    constructor
    · rintro ⟨ht, hr⟩; exact ⟨ht, (h_rainbow_iff t ht).mp hr⟩
    · rintro ⟨ht, h1⟩; exact ⟨ht, (h_rainbow_iff t ht).mpr h1⟩
  rw [hfilt]
  exact odd_card_filter_eq_one h_range h_odd_sum

/-- Corollary: at least one rainbow triangle exists. -/
theorem sperner_lemma_exists {m : ℕ} (T : Triangulation m) (c : Fin m → Fin 3)
    (count12 : Finset (Fin m) → ℕ)
    (h_rainbow_iff : ∀ t ∈ T.triangles, isRainbow c t ↔ count12 t = 1)
    (h_range : ∀ t ∈ T.triangles, count12 t = 0 ∨ count12 t = 1 ∨ count12 t = 2)
    (h_odd_sum : Odd (∑ t ∈ T.triangles, count12 t)) :
    ∃ t ∈ T.triangles, isRainbow c t := by
  have hodd := sperner_lemma T c count12 h_rainbow_iff h_range h_odd_sum
  rw [Nat.odd_iff] at hodd
  have hne : (T.triangles.filter (isRainbow c)).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    simp [h] at hodd
  exact let ⟨t, ht⟩ := hne; ⟨t, (Finset.mem_filter.mp ht).1, (Finset.mem_filter.mp ht).2⟩

/-! ## Sperner → Brouwer bridge: infrastructure and proof outline

The book proof (pp.204–205) deduces Brouwer's fixed-point theorem from Sperner's lemma
via the standard 2-simplex Δ² = conv{e₁,e₂,e₃}.  We set up the key definitions and
state the lemmas needed to connect the combinatorial `sperner_lemma` above to the
analytic fixed-point conclusion.

### Proof outline (Proofs from THE BOOK, Chapter 28)

1. **Standard 2-simplex.** Δ² = {(x₁,x₂,x₃) ∈ ℝ³ | xᵢ ≥ 0, x₁+x₂+x₃ = 1}.
2. **Regular triangulation.** Subdivide Δ² into k² small triangles with vertices
   of the form (a/k, b/k, c/k), a+b+c = k.
3. **Sperner coloring.** For a continuous f : Δ² → Δ², color vertex v with
   the smallest i such that f(v)ᵢ < vᵢ.  This is well-defined because
   ∑ f(v)ᵢ = 1 = ∑ vᵢ so f(v) ≠ v implies some coordinate decreases.
4. **Boundary condition.** If v lies on the face opposite eⱼ (i.e. vⱼ = 0),
   then color(v) ≠ j.  This gives a proper Sperner coloring.
5. **Rainbow triangles.** By `sperner_lemma`, each T_k has a rainbow triangle.
6. **Compactness.** Extract a convergent subsequence of rainbow triangle vertices.
7. **Fixed point.** At the limit, f(v)ᵢ ≤ vᵢ for all i, and ∑ = 1 forces equality.
-/

/-- A point in the standard 2-simplex: nonnegative coordinates summing to 1. -/
def stdSimplex2 : Set (Fin 3 → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1}

/-- Vertex of the k-th regular subdivision: (a/k, b/k, c/k) where a+b+c = k. -/
noncomputable def subdivVertex (k : ℕ) (abc : Fin 3 → ℕ) (_h : ∑ i, abc i = k)
    (_hk : 0 < k) : Fin 3 → ℝ :=
  fun i => (abc i : ℝ) / (k : ℝ)

/-- The Sperner coloring for a continuous self-map of Δ².  Given v ∈ Δ² and
    f : Δ² → Δ², color(v) = min {i | f(v)ᵢ < vᵢ}.  Well-defined when f(v) ≠ v
    and ∑ f(v)ᵢ = ∑ vᵢ = 1. When f(v) = v, we default to 0. -/
noncomputable def spernerColor (f : (Fin 3 → ℝ) → (Fin 3 → ℝ)) (v : Fin 3 → ℝ) : Fin 3 :=
  if h : ∃ i : Fin 3, f v i < v i then h.choose else 0

/-! ### Brouwer's fixed-point theorem on the standard 2-simplex via Sperner's lemma

The book proof (pp. 204–205) deduces Brouwer from Sperner via:
1. For each k, subdivide Δ² into small triangles, apply Sperner coloring, get a rainbow triangle
2. Extract convergent subsequence (compactness of Δ²)
3. At the limit, f(x*) = x*

**Gap 1 (Geometric Sperner):** Constructing the regular k-subdivision as an instance of
`Triangulation` and verifying the boundary parity condition is a major formalization effort.
We axiomatize the infrastructure lemmas (triangulation construction, boundary parity,
vertex extraction) below; `sperner_coloring_rainbow_triangles` is proved modulo these.

**Gaps 2–3 (Compactness + Limit):** Fully proved below.
-/

/-- The standard 2-simplex equals Mathlib's `stdSimplex`. -/
private theorem stdSimplex2_eq : stdSimplex2 = stdSimplex ℝ (Fin 3) := by
  ext x; simp only [stdSimplex2, stdSimplex, Set.mem_setOf_eq]

/-- The standard 2-simplex is compact. -/
private theorem stdSimplex2_isCompact : IsCompact stdSimplex2 := by
  rw [stdSimplex2_eq]; exact isCompact_stdSimplex _

/-- The Sperner coloring is well-defined: if v ∈ Δ² and f(v) ≠ v with f(v) ∈ Δ²,
    then some coordinate strictly decreases. -/
private theorem spernerColor_exists {f : (Fin 3 → ℝ) → (Fin 3 → ℝ)}
    {v : Fin 3 → ℝ} (hv : v ∈ stdSimplex2) (hfv : f v ∈ stdSimplex2)
    (hne : f v ≠ v) : ∃ i : Fin 3, f v i < v i := by
  by_contra h; push_neg at h
  have hsum_v := hv.2; have hsum_fv := hfv.2
  have : ∀ i, f v i = v i := by
    intro i
    have hle_sum : ∑ j, v j ≤ ∑ j, f v j := Finset.sum_le_sum (fun j _ => h j)
    rw [hsum_v, hsum_fv] at hle_sum
    have hge : f v i ≤ v i := by
      by_contra hlt; push_neg at hlt
      have : ∑ j, v j < ∑ j, f v j :=
        Finset.sum_lt_sum (fun j _ => h j) ⟨i, Finset.mem_univ _, hlt⟩
      linarith
    exact le_antisymm hge (h i)
  exact hne (funext this)

/-- The Sperner coloring satisfies the boundary condition: if vⱼ = 0 and v ∈ Δ²
    and f(v) ∈ Δ², then color(v) ≠ j (since f(v)ⱼ ≥ 0 = vⱼ). -/
private theorem spernerColor_boundary {f : (Fin 3 → ℝ) → (Fin 3 → ℝ)}
    {v : Fin 3 → ℝ} (hv : v ∈ stdSimplex2) (hfv : f v ∈ stdSimplex2) {j : Fin 3} (hvj : v j = 0)
    (hne : f v ≠ v) : spernerColor f v ≠ j := by
  have hex := spernerColor_exists hv hfv hne
  intro heq
  unfold spernerColor at heq; rw [dif_pos hex] at heq
  have hchoose := hex.choose_spec
  rw [heq] at hchoose
  rw [hvj] at hchoose; linarith [hfv.1 j]

/-! ### Regular k-subdivision of Δ² and geometric Sperner infrastructure

We encode the regular k-subdivision of the standard 2-simplex and connect it
to `sperner_lemma_exists`. The subdivision has vertices (a/k, b/k, c/k) with
a + b + c = k, and small triangles of two types ("up" and "down").

The key steps are:
1. Define the vertex set and its encoding as `Fin m`
2. Define the triangulation
3. Define the 12-edge count and verify boundary parity
4. Extract geometric consequences from the combinatorial rainbow triangle
-/

/-- Number of vertices in the k-th regular subdivision: (k+1)(k+2)/2. -/
private def subdivVertCount (k : ℕ) : ℕ := (k + 1) * (k + 2) / 2

/-- A vertex of the k-th regular subdivision is a triple (a,b,c) with a+b+c = k. -/
private def SubdivVert (k : ℕ) : Type :=
  { abc : Fin 3 → ℕ // ∑ i, abc i = k }

private instance subdivVertFintype (k : ℕ) : Fintype (SubdivVert k) :=
  Fintype.subtype (Finset.Nat.antidiagonalTuple 3 k) fun x => by
    simp [Finset.Nat.mem_antidiagonalTuple]

private instance subdivVertDecEq (k : ℕ) : DecidableEq (SubdivVert k) :=
  inferInstanceAs (DecidableEq { abc : Fin 3 → ℕ // ∑ i, abc i = k })

/-- The coordinate map: send a subdivision vertex to its barycentric point in Δ². -/
private noncomputable def subdivCoord (k : ℕ) (hk : 0 < k) (v : SubdivVert k) : Fin 3 → ℝ :=
  fun i => (v.1 i : ℝ) / (k : ℝ)

private theorem subdivCoord_mem (k : ℕ) (hk : 0 < k) (v : SubdivVert k) :
    subdivCoord k hk v ∈ stdSimplex2 := by
  constructor
  · intro i; apply div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · simp only [subdivCoord, div_add_div_same, ← Finset.sum_div]
    rw [show (∑ i : Fin 3, (v.1 i : ℝ)) = (∑ i : Fin 3, v.1 i : ℕ) from by push_cast; rfl]
    rw [v.2]; field_simp

/-- Distance between adjacent subdivision vertices is at most √2/k.
    Two vertices are adjacent if they differ by at most 1 in each coordinate. -/
private theorem subdivCoord_dist (k : ℕ) (hk : 0 < k) (v w : SubdivVert k)
    (hadj : ∀ i, (v.1 i : ℤ) - (w.1 i : ℤ) ∈ Set.Icc (-1 : ℤ) 1) :
    dist (subdivCoord k hk v) (subdivCoord k hk w) ≤ Real.sqrt 2 / k := by
  have hk' : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  rw [dist_pi_le_iff (div_nonneg (Real.sqrt_nonneg _) (le_of_lt hk'))]
  intro i
  rw [Real.dist_eq, subdivCoord, subdivCoord, div_sub_div_same]
  rw [abs_div, abs_of_nonneg (le_of_lt hk')]
  apply div_le_div_of_nonneg_right _ (le_of_lt hk')
  have hi := hadj i
  simp only [Set.mem_Icc] at hi
  calc |(v.1 i : ℝ) - (w.1 i : ℝ)|
      ≤ 1 := by
        rw [show (v.1 i : ℝ) - (w.1 i : ℝ) = ((v.1 i : ℤ) - (w.1 i : ℤ) : ℤ) from by push_cast; ring]
        rw [show (1 : ℝ) = ((1 : ℤ) : ℝ) from by norm_cast]
        exact_mod_cast abs_le.mpr ⟨hi.1, hi.2⟩
    _ ≤ Real.sqrt 2 := by
        rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by norm_num)

/-- Data bundle for a subdivision triangulation with adjacency. -/
private structure SubdivData (k : ℕ) where
  m : ℕ
  T : Triangulation m
  decode : Fin m → SubdivVert k
  adj : ∀ t ∈ T.triangles, ∀ a ∈ t, ∀ b ∈ t,
    ∀ i, ((decode a).1 i : ℤ) - ((decode b).1 i : ℤ) ∈ Set.Icc (-1 : ℤ) 1

/-- The regular k-subdivision as a `Triangulation` with adjacency proof.
    The key properties are that:
    - Each triangle has 3 vertices from `SubdivVert k` (encoded as `Fin m`)
    - The triangulation covers Δ²
    - Any two vertices in the same triangle differ by ≤ 1 in each coordinate -/
private noncomputable def subdivTriangulation (k : ℕ) (_hk : 0 < k) :
    SubdivData k := by
  classical
  let m := Fintype.card (SubdivVert k)
  let eqv := Fintype.equivFin (SubdivVert k)
  let encode : SubdivVert k → Fin m := eqv
  let decode : Fin m → SubdivVert k := eqv.symm
  -- Helper to make a SubdivVert from (a, b) with a + b ≤ k
  let mkVert : ∀ (a b : ℕ), a + b ≤ k → SubdivVert k := fun a b h =>
    ⟨![a, b, k - a - b], by simp [Fin.sum_univ_three]; omega⟩
  -- Define triangles as a subset of Finset.powerset (Finset.univ : Finset (Fin m))
  -- filtered by the triangulation predicate
  -- An up-triangle has vertices (i,j), (i+1,j), (i,j+1) with i+j < k
  -- A down-triangle has vertices (i+1,j), (i,j+1), (i+1,j+1) with i+j+1 < k
  -- We define the predicate on triples of SubdivVert k
  let isUpTri : SubdivVert k → SubdivVert k → SubdivVert k → Prop :=
    fun v0 v1 v2 => ∃ (i j : ℕ) (h : i + j < k),
      v0 = mkVert i j (by omega) ∧
      v1 = mkVert (i+1) j (by omega) ∧
      v2 = mkVert i (j+1) (by omega)
  let isDownTri : SubdivVert k → SubdivVert k → SubdivVert k → Prop :=
    fun v0 v1 v2 => ∃ (i j : ℕ) (h : i + j + 1 < k),
      v0 = mkVert (i+1) j (by omega) ∧
      v1 = mkVert i (j+1) (by omega) ∧
      v2 = mkVert (i+1) (j+1) (by omega)
  -- Build the triangles as a finset
  let allTris : Finset (Finset (Fin m)) :=
    Finset.univ.biUnion fun (v0 : SubdivVert k) =>
      Finset.univ.biUnion fun (v1 : SubdivVert k) =>
        Finset.univ.biUnion fun (v2 : SubdivVert k) =>
          if (∃ (i j : ℕ) (_ : i + j < k),
                v0 = mkVert i j (by omega) ∧
                v1 = mkVert (i+1) j (by omega) ∧
                v2 = mkVert i (j+1) (by omega)) ∨
             (∃ (i j : ℕ) (_ : i + j + 1 < k),
                v0 = mkVert (i+1) j (by omega) ∧
                v1 = mkVert i (j+1) (by omega) ∧
                v2 = mkVert (i+1) (j+1) (by omega))
          then {({encode v0, encode v1, encode v2} : Finset (Fin m))}
          else ∅
  -- Helper: mkVert produces distinct SubdivVert's when first coords differ
  have mkVert_coord0 : ∀ a b (h : a + b ≤ k), (mkVert a b h).1 0 = a := by
    intro a b h; simp [mkVert, Matrix.cons_val_zero]
  have mkVert_coord1 : ∀ a b (h : a + b ≤ k), (mkVert a b h).1 1 = b := by
    intro a b h; simp [mkVert, Matrix.cons_val_one, Matrix.head_cons]
  have hcard : ∀ t ∈ allTris, t.card = 3 := by
    intro t ht
    simp only [allTris, Finset.mem_biUnion, Finset.mem_univ, true_and] at ht
    obtain ⟨v0, v1, v2, hcond⟩ := ht
    split_ifs at hcond with htri
    · simp only [Finset.mem_singleton] at hcond
      subst hcond
      have hinj : Function.Injective encode := eqv.injective
      rcases htri with ⟨i, j, hij, rfl, rfl, rfl⟩ | ⟨i, j, hij, rfl, rfl, rfl⟩
      · -- Up triangle: (i,j), (i+1,j), (i,j+1)
        have h01 : mkVert i j (by omega) ≠ mkVert (i+1) j (by omega) := by
          intro h; have := congr_arg (fun v => v.1 0) h; simp [mkVert_coord0] at this
        have h02 : mkVert i j (by omega) ≠ mkVert i (j+1) (by omega) := by
          intro h; have := congr_arg (fun v => v.1 1) h; simp [mkVert_coord1] at this
        have h12 : mkVert (i+1) j (by omega) ≠ mkVert i (j+1) (by omega) := by
          intro h; have := congr_arg (fun v => v.1 0) h; simp [mkVert_coord0] at this
        have he01 : encode (mkVert i j (by omega)) ≠ encode (mkVert (i+1) j (by omega)) :=
          fun h => h01 (eqv.injective h)
        have he02 : encode (mkVert i j (by omega)) ≠ encode (mkVert i (j+1) (by omega)) :=
          fun h => h02 (eqv.injective h)
        have he12 : encode (mkVert (i+1) j (by omega)) ≠ encode (mkVert i (j+1) (by omega)) :=
          fun h => h12 (eqv.injective h)
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
        · simp; exact he12
        · simp only [Finset.mem_insert, Finset.mem_singleton]
          push_neg; exact ⟨he01, he02⟩
      · -- Down triangle: (i+1,j), (i,j+1), (i+1,j+1)
        have h01 : mkVert (i+1) j (by omega) ≠ mkVert i (j+1) (by omega) := by
          intro h; have := congr_arg (fun v => v.1 0) h; simp [mkVert_coord0] at this
        have h02 : mkVert (i+1) j (by omega) ≠ mkVert (i+1) (j+1) (by omega) := by
          intro h; have := congr_arg (fun v => v.1 1) h; simp [mkVert_coord1] at this
        have h12 : mkVert i (j+1) (by omega) ≠ mkVert (i+1) (j+1) (by omega) := by
          intro h; have := congr_arg (fun v => v.1 0) h; simp [mkVert_coord0] at this
        have he01 : encode (mkVert (i+1) j (by omega)) ≠ encode (mkVert i (j+1) (by omega)) :=
          fun h => h01 (eqv.injective h)
        have he02 : encode (mkVert (i+1) j (by omega)) ≠ encode (mkVert (i+1) (j+1) (by omega)) :=
          fun h => h02 (eqv.injective h)
        have he12 : encode (mkVert i (j+1) (by omega)) ≠ encode (mkVert (i+1) (j+1) (by omega)) :=
          fun h => h12 (eqv.injective h)
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
        · simp; exact he12
        · simp only [Finset.mem_insert, Finset.mem_singleton]
          push_neg; exact ⟨he01, he02⟩
    · simp at hcond
  refine ⟨m, ⟨allTris, hcard⟩, decode, ?_⟩
  -- Adjacency: any two vertices in the same triangle differ by ≤ 1 in each coordinate
  -- This follows from the construction: up-triangles have vertices (i,j),(i+1,j),(i,j+1)
  -- and down-triangles have vertices (i+1,j),(i,j+1),(i+1,j+1), all differing by ≤ 1.
  intro t ht a ha b hb idx
  simp only [allTris, Finset.mem_biUnion, Finset.mem_univ, true_and] at ht
  obtain ⟨v0, v1, v2, hcond⟩ := ht
  split_ifs at hcond with htri
  · simp only [Finset.mem_singleton] at hcond
    have hmem : a ∈ ({encode v0, encode v1, encode v2} : Finset (Fin m)) := hcond ▸ ha
    have hmem' : b ∈ ({encode v0, encode v1, encode v2} : Finset (Fin m)) := hcond ▸ hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem hmem'
    have hdec : ∀ x, (x = encode v0 ∨ x = encode v1 ∨ x = encode v2) →
        (decode x = v0 ∨ decode x = v1 ∨ decode x = v2) := by
      intro x hx; rcases hx with rfl | rfl | rfl <;>
        simp [decode, encode, Equiv.symm_apply_apply]
    have hda := hdec a hmem
    have hdb := hdec b hmem'
    rcases htri with ⟨ii, jj, hij, rfl, rfl, rfl⟩ | ⟨ii, jj, hij, rfl, rfl, rfl⟩
    · -- Up triangle: mkVert ii jj, mkVert (ii+1) jj, mkVert ii (jj+1)
      rcases hda with ha' | ha' | ha' <;> rcases hdb with hb' | hb' | hb' <;>
        (simp only [Set.mem_Icc]; rw [ha', hb']; fin_cases idx <;>
          simp [mkVert, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;> omega)
    · -- Down triangle: mkVert (ii+1) jj, mkVert ii (jj+1), mkVert (ii+1) (jj+1)
      rcases hda with ha' | ha' | ha' <;> rcases hdb with hb' | hb' | hb' <;>
        (simp only [Set.mem_Icc]; rw [ha', hb']; fin_cases idx <;>
          simp [mkVert, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;> omega)
  · simp at hcond

/-- The boundary parity condition for the Sperner coloring on the k-subdivision.
    The sum of 12-edge counts over all triangles is odd.

    **Proof sketch (not yet formalized):**
    Define `count12 t` = number of {u,v} pairs in triangle t with {col u, col v} = {1,2}.
    - `h_rainbow_iff`: A triangle with colors {0,1,2} has exactly one 1-2 pair → count12 = 1.
    - `h_range`: For a 3-element set, count12 ∈ {0,1,2}.
    - `h_odd_sum`: By double counting, ∑ count12 = ∑_{12-edges e} (triangles containing e).
      Interior edges contribute 2 (even), boundary edges contribute 1.
      Boundary 12-edges exist only on the e₁e₂ face (x₀=0), since:
        • e₀e₁ face has colors ∈ {0,1} (no color-2 vertex)
        • e₀e₂ face has colors ∈ {0,2} (no color-1 vertex)
      On the e₁e₂ face, vertices go from e₂ (color 2) to e₁ (color 1) through k edges.
      The number of 1↔2 color changes is odd (parity argument: starts at 2, ends at 1).
      Therefore ∑ count12 ≡ (boundary 12-edges) ≡ 1 (mod 2). -/
private theorem subdivSperner_odd_sum
    (f : (Fin 3 → ℝ) → (Fin 3 → ℝ)) (_hfS : ∀ x ∈ stdSimplex2, f x ∈ stdSimplex2)
    (k : ℕ) (_hk : 0 < k)
    (m : ℕ) (T : Triangulation m) (decode : Fin m → SubdivVert k)
    (col : Fin m → Fin 3) :
    ∃ count12 : Finset (Fin m) → ℕ,
      (∀ t ∈ T.triangles, isRainbow col t ↔ count12 t = 1) ∧
      (∀ t ∈ T.triangles, count12 t = 0 ∨ count12 t = 1 ∨ count12 t = 2) ∧
      Odd (∑ t ∈ T.triangles, count12 t) :=
  sorry

/-- From a rainbow triangle in the subdivision, extract three vertices with the
    desired geometric properties. -/
private theorem rainbow_triangle_gives_vertices
    (f : (Fin 3 → ℝ) → (Fin 3 → ℝ)) (hfS : ∀ x ∈ stdSimplex2, f x ∈ stdSimplex2)
    (hne : ∀ x ∈ stdSimplex2, f x ≠ x)
    (k : ℕ) (hk : 0 < k) (m : ℕ) (T : Triangulation m) (decode : Fin m → SubdivVert k)
    (col : Fin m → Fin 3) (t : Finset (Fin m)) (ht : t ∈ T.triangles)
    (hcard : t.card = 3) (hrainbow : isRainbow col t)
    (hcol_def : ∀ v, col v = spernerColor f (subdivCoord k hk (decode v)))
    (hadj : ∀ t ∈ T.triangles, ∀ a ∈ t, ∀ b ∈ t,
      ∀ i, ((decode a).1 i : ℤ) - ((decode b).1 i : ℤ) ∈ Set.Icc (-1 : ℤ) 1) :
    ∃ v : Fin 3 → (Fin 3 → ℝ),
      (∀ i, v i ∈ stdSimplex2) ∧
      (∀ i, f (v i) i < (v i) i) ∧
      (∀ i j, dist (v i) (v j) ≤ Real.sqrt 2 / k) := by
  -- Extract the 3 vertices with distinct colors from the rainbow triangle
  rw [isRainbow] at hrainbow
  -- t has 3 elements, image under col is {0,1,2}
  -- We need to find vertices with each color
  have h0 : (0 : Fin 3) ∈ t.image col := by rw [hrainbow]; simp
  have h1 : (1 : Fin 3) ∈ t.image col := by rw [hrainbow]; simp
  have h2 : (2 : Fin 3) ∈ t.image col := by rw [hrainbow]; simp
  rw [Finset.mem_image] at h0 h1 h2
  obtain ⟨a, ha, hca⟩ := h0
  obtain ⟨b, hb, hcb⟩ := h1
  obtain ⟨c, hc, hcc⟩ := h2
  -- Define v i = subdivCoord of the vertex with color i
  let vert : Fin 3 → Fin m := ![a, b, c]
  refine ⟨fun i => subdivCoord k hk (decode (vert i)), ?_, ?_, ?_⟩
  · -- v i ∈ stdSimplex2
    intro i; exact subdivCoord_mem k hk (decode (vert i))
  · -- f (v i) i < (v i) i
    intro i
    have hcol_i : col (vert i) = i := by
      fin_cases i <;> simp only [vert, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons] <;> assumption
    rw [hcol_def] at hcol_i
    unfold spernerColor at hcol_i
    split_ifs at hcol_i with hex
    · have := hex.choose_spec; rw [hcol_i] at this; exact this
    · -- ¬∃ j, f v j < v j means f(v) ≥ v componentwise, and ∑ = 1 forces f(v) = v.
      -- But hne says f(v) ≠ v, contradiction.
      push_neg at hex
      have hv_mem := subdivCoord_mem k hk (decode (vert i))
      have hfv_mem := hfS _ hv_mem
      have heq : f (subdivCoord k hk (decode (vert i))) = subdivCoord k hk (decode (vert i)) := by
        ext j
        exact le_antisymm (by
          by_contra hlt; push_neg at hlt
          have : ∑ l, f (subdivCoord k hk (decode (vert i))) l >
                 ∑ l, subdivCoord k hk (decode (vert i)) l :=
            Finset.sum_lt_sum (fun l _ => hex l)
              ⟨j, Finset.mem_univ _, hlt⟩
          linarith [hfv_mem.2, hv_mem.2]) (hex j)
      exact absurd heq (hne _ hv_mem)
  · -- Distance bound: vertices in the same triangle are adjacent
    -- This requires knowledge of the triangulation structure (adjacency).
    -- Gap: we need that decode maps triangle vertices to adjacent SubdivVert's
    -- (differing by ≤1 in each coordinate). This is a property of the construction
    -- in subdivTriangulation which we axiomatize here.
    intro i j
    apply subdivCoord_dist
    intro idx
    have hvi : vert i ∈ t := by
      fin_cases i <;> simp [vert, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;>
        assumption
    have hvj : vert j ∈ t := by
      fin_cases j <;> simp [vert, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;>
        assumption
    exact hadj t ht (vert i) hvi (vert j) hvj idx

/-- **Geometric Sperner:** For each k ≥ 1, the Sperner coloring of the k-th regular
    subdivision of Δ² applied to a continuous f : Δ² → Δ² yields three points
    v₀, v₁, v₂ ∈ Δ² forming a rainbow triangle. -/
private theorem sperner_coloring_rainbow_triangles
    (f : (Fin 3 → ℝ) → (Fin 3 → ℝ))
    (_hfc : Continuous f) (hfS : ∀ x ∈ stdSimplex2, f x ∈ stdSimplex2)
    (hne : ∀ x ∈ stdSimplex2, f x ≠ x)
    (k : ℕ) (hk : 0 < k) :
    ∃ v : Fin 3 → (Fin 3 → ℝ),
      (∀ i, v i ∈ stdSimplex2) ∧
      (∀ i, f (v i) i < (v i) i) ∧
      (∀ i j, dist (v i) (v j) ≤ Real.sqrt 2 / k) := by
  obtain ⟨m, T, decode, hadj⟩ := subdivTriangulation k hk
  set col : Fin m → Fin 3 := fun v => spernerColor f (subdivCoord k hk (decode v))
  obtain ⟨count12, h_rainbow_iff, h_range, h_odd_sum⟩ :=
    subdivSperner_odd_sum f hfS k hk m T decode col
  obtain ⟨t, ht, hrainbow⟩ := sperner_lemma_exists T col count12 h_rainbow_iff h_range h_odd_sum
  exact rainbow_triangle_gives_vertices f hfS hne k hk m T decode col t ht
    (T.triangle_card t ht) hrainbow (fun v => rfl) hadj

/-- **Brouwer's fixed-point theorem on the standard 2-simplex (Sperner route).**

    If f : Δ² → Δ² is continuous, then f has a fixed point.
    Uses `sperner_coloring_rainbow_triangles` for each k, compactness of Δ²,
    and the sum-to-one constraint. -/
private theorem brouwer_fixed_point_simplex2_sperner
    (f : (Fin 3 → ℝ) → (Fin 3 → ℝ))
    (hfc : Continuous f) (hfS : ∀ x ∈ stdSimplex2, f x ∈ stdSimplex2) :
    ∃ x ∈ stdSimplex2, f x = x := by
  -- Use contradiction: assume no fixed point, then spernerColor is always well-defined
  by_contra hno
  push_neg at hno
  have hne : ∀ x ∈ stdSimplex2, f x ≠ x := by
    intro x hx heq; exact hno x hx heq
  -- For each k ≥ 1, get rainbow triangle vertices
  choose vk hvk_mem hvk_col hvk_diam using
    fun k => sperner_coloring_rainbow_triangles f hfc hfS hne (k + 1) (Nat.succ_pos k)
  -- x k = vk k 0 ∈ stdSimplex2
  set x : ℕ → (Fin 3 → ℝ) := fun k => vk k 0
  -- Extract convergent subsequence by compactness
  obtain ⟨xstar, hxstar_mem, φ, hφ_strict, hφ_lim⟩ :=
    stdSimplex2_isCompact.tendsto_subseq (fun k => hvk_mem k 0)
  have hfxstar_mem : f xstar ∈ stdSimplex2 := hfS xstar hxstar_mem
  -- For each i, show f(xstar) i ≤ xstar i, then sum constraint gives equality
  suffices hle : ∀ i, f xstar i ≤ xstar i by
    have heq : f xstar = xstar := by
      ext i; exact le_antisymm (hle i) (by
        by_contra hlt; push_neg at hlt
        have : ∑ j, f xstar j < ∑ j, xstar j :=
          Finset.sum_lt_sum (fun j _ => hle j) ⟨i, Finset.mem_univ _, hlt⟩
        linarith [hfxstar_mem.2, hxstar_mem.2])
    exact hne xstar hxstar_mem heq
  -- For each i, vk (φ n) i → xstar (since vk (φ n) 0 → xstar and diameter → 0)
  -- and f(vk (φ n) i) i < (vk (φ n) i) i, so by continuity f(xstar) i ≤ xstar i
  intro i
  -- Step 1: vk (φ n) i → xstar
  -- This follows because dist(vk (φ n) i, vk (φ n) 0) ≤ √2/(φ n + 1) → 0
  -- and vk (φ n) 0 = x (φ n) → xstar
  have hvi_tends : Filter.Tendsto (fun n => vk (φ n) i) Filter.atTop (nhds xstar) := by
    rw [Metric.tendsto_atTop] at hφ_lim ⊢
    intro ε hε
    obtain ⟨N₁, hN₁⟩ := hφ_lim (ε / 2) (by linarith)
    obtain ⟨N₂, hN₂⟩ := exists_nat_gt (Real.sqrt 2 / (ε / 2))
    refine ⟨max N₁ N₂, fun n hn => ?_⟩
    have hφn_ge : N₂ ≤ φ n := by
      have hmono : ∀ m, m ≤ φ m := by
        intro m; induction m with
        | zero => omega
        | succ k ih => exact Nat.succ_le_of_lt (lt_of_le_of_lt ih (hφ_strict (Nat.lt_succ_of_le le_rfl)))
      exact le_trans (le_max_right N₁ N₂ |>.trans hn) (hmono n)
    have h_diam : Real.sqrt 2 / (↑(φ n + 1) : ℝ) < ε / 2 := by
      rw [Nat.cast_add, Nat.cast_one, div_lt_iff₀ (by positivity : (0 : ℝ) < ↑(φ n) + 1)]
      calc Real.sqrt 2 < ε / 2 * ↑N₂ := by
              rw [div_lt_iff₀ (half_pos hε)] at hN₂; linarith
        _ ≤ ε / 2 * (↑(φ n) + 1) := by
            apply mul_le_mul_of_nonneg_left _ (by linarith)
            exact_mod_cast Nat.le_succ_of_le hφn_ge
    have h_sub : dist (x (φ n)) xstar < ε / 2 := hN₁ n (le_max_left _ _ |>.trans hn)
    calc dist (vk (φ n) i) xstar
        ≤ dist (vk (φ n) i) (vk (φ n) 0) + dist (vk (φ n) 0) xstar := dist_triangle _ _ _
      _ ≤ Real.sqrt 2 / (↑(φ n + 1) : ℝ) + dist (x (φ n)) xstar := by
          gcongr; exact hvk_diam (φ n) i 0
      _ < ε / 2 + ε / 2 := add_lt_add h_diam h_sub
      _ = ε := by ring
  -- Step 2: f continuous ⟹ f(vk (φ n) i) i → f(xstar) i
  have hfi_cont : Continuous (fun v => f v i) := (continuous_apply i).comp hfc
  have hfi_tends := (hfi_cont.tendsto xstar).comp hvi_tends
  -- Step 3: f(vk (φ n) i) i < (vk (φ n) i) i ⟹ f(xstar) i ≤ xstar i
  have hvi_i_tends := ((continuous_apply i).tendsto xstar).comp hvi_tends
  exact le_of_tendsto_of_tendsto hfi_tends hvi_i_tends
    (Filter.eventually_atTop.mpr ⟨0, fun n _ => le_of_lt (hvk_col (φ n) i)⟩)

/-- Transfer from simplex to disk. -/
theorem brouwer_fixed_point_2d_from_sperner
    (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (hf : Continuous f) (hB : ∀ x, ‖x‖ ≤ 1 → ‖f x‖ ≤ 1) :
    ∃ x, ‖x‖ ≤ 1 ∧ f x = x := by
  -- The disk in ℝ² is homeomorphic to Δ², so we can transfer
  -- For now we derive this from the complex-analysis proof
  exact brouwer_fixed_point_2d_from_complex f hf hB

/-! ## Brouwer's fixed point theorem (n = 2) -/
theorem brouwer_fixed_point_2d
    (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (hf : Continuous f) (hB : ∀ x, ‖x‖ ≤ 1 → ‖f x‖ ≤ 1) :
    ∃ x, ‖x‖ ≤ 1 ∧ f x = x := by
  exact brouwer_fixed_point_2d_from_complex f hf hB

/-! ## The Reiman graph Gp: a tight construction for the C₄-free bound

The book constructs a graph Gp for each odd prime p:
- Vertices = points of PG(2,p), i.e., one-dimensional subspaces of (ZMod p)³
- Two vertices [u],[v] are adjacent iff ⟨u,v⟩ = u₁v₁ + u₂v₂ + u₃v₃ = 0
- Gp is C₄-free
- Edge count achieves the bound from `c4_free_edge_bound`

We use Mathlib's `Projectivization` and `Projectivization.orthogonal`.
-/

section ReimanGraph

open scoped LinearAlgebra.Projectivization

variable (p : ℕ) [Fact (Nat.Prime p)]

/-- The projective plane over 𝔽ₚ. -/
abbrev PG2 := ℙ (ZMod p) (Fin 3 → ZMod p)

/-- The Reiman graph Gp: vertices are points of PG(2,p), adjacency is orthogonality. -/
noncomputable def reimanGraph : SimpleGraph (PG2 p) where
  Adj v w := v ≠ w ∧ Projectivization.orthogonal v w
  symm := by
    intro v w ⟨hne, horth⟩
    exact ⟨hne.symm, Projectivization.orthogonal_comm.mp horth⟩
  loopless := by intro v ⟨h, _⟩; exact h rfl

/-- The number of vertices of Gp is p² + p + 1. -/
theorem reimanGraph_card_vertices (_hp : Odd p) :
    Nat.card (PG2 p) = p ^ 2 + p + 1 := by
  have hfr : Module.finrank (ZMod p) (Fin 3 → ZMod p) = 3 := by
    simp
  rw [Projectivization.card_of_finrank _ _ hfr]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.card_zmod]
  ring

/-- In PG(2,F), if a point x is orthogonal to two distinct points a and c,
    then x = cross a c.  This is the uniqueness of the intersection of two
    hyperplanes (each hyperplane is the set of points orthogonal to a given point).
    Proof: by the BAC-CAB identity, w × (u × v) = (w·v)u − (u·w)v = 0 when
    w·u = 0 and w·v = 0, so the representatives are proportional. -/
lemma orthogonal_both_eq_cross {F : Type*} [Field F] [DecidableEq F]
    {a c : ℙ F (Fin 3 → F)} (hac : a ≠ c)
    {x : ℙ F (Fin 3 → F)} (hxa : Projectivization.orthogonal x a)
    (hxc : Projectivization.orthogonal x c) :
    x = Projectivization.cross a c := by
  induction x with | h w hw =>
  induction a with | h u hu =>
  induction c with | h v hv =>
  rw [Projectivization.orthogonal_mk hw hu] at hxa
  rw [Projectivization.orthogonal_mk hw hv] at hxc
  rw [Projectivization.cross_mk_of_ne hu hv hac,
      Projectivization.mk_eq_mk_iff_crossProduct_eq_zero hw]
  have key := cross_cross_eq_smul_sub_smul' w u v
  rw [hxc, dotProduct_comm, hxa, zero_smul, zero_smul, sub_self] at key
  exact key

/-- Key lemma for no C₄: if two distinct points v, w are both orthogonal to two distinct
    points a, b, then v = w. Equivalently, the "orthogonal complement" hyperplanes of
    distinct points intersect in at most a single projective point.

    This is the projective geometry fact that two distinct hyperplanes in PG(2,p) meet
    in exactly one point. -/
theorem reimanGraph_no_C4 :
    ∀ (a b c d : PG2 p),
      a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      ¬((reimanGraph p).Adj a b ∧ (reimanGraph p).Adj b c ∧
        (reimanGraph p).Adj c d ∧ (reimanGraph p).Adj d a) := by
  intro a b c d hab hac had hbc hbd hcd
  rintro ⟨⟨_, hab_orth⟩, ⟨_, hbc_orth⟩, ⟨_, hcd_orth⟩, ⟨_, hda_orth⟩⟩
  -- b and d are both orthogonal to a and c. Since a ≠ c, both equal cross a c.
  have hb := orthogonal_both_eq_cross hac
    (Projectivization.orthogonal_comm.mp hab_orth) hbc_orth
  have hd := orthogonal_both_eq_cross hac
    hda_orth (Projectivization.orthogonal_comm.mp hcd_orth)
  exact hbd (hb.trans hd.symm)

open Classical in
/-- The projective hyperplane orthogonal to a point has p+1 elements. -/
lemma orthogonal_set_card [Fintype (PG2 p)] [DecidableEq (PG2 p)]
    (v : PG2 p) :
    (Finset.univ.filter (fun w : PG2 p => Projectivization.orthogonal v w)).card = p + 1 := by
  induction v using Projectivization.ind with | h u hu =>
  set φ : Module.Dual (ZMod p) (Fin 3 → ZMod p) :=
    dotProductEquiv (ZMod p) (Fin 3) u with hφ_def
  have hφ_apply : ∀ w, φ w = u ⬝ᵥ w := fun _ => rfl
  have hφ : φ ≠ 0 := by
    intro h; exact hu ((dotProductEquiv (ZMod p) (Fin 3)).map_eq_zero_iff.mp h)
  haveI : FiniteDimensional (ZMod p) (Fin 3 → ZMod p) := inferInstance
  have hfr : Module.finrank (ZMod p) (LinearMap.ker φ) = 2 := by
    have h1 := Module.Dual.finrank_ker_add_one_of_ne_zero hφ; simp at h1; omega
  haveI : Finite (ZMod p) := inferInstance
  have hcard : Nat.card (ℙ (ZMod p) (LinearMap.ker φ)) = p + 1 := by
    rw [Projectivization.card_of_finrank_two _ _ hfr, Nat.card_zmod]
  have hι_inj : Function.Injective (Projectivization.map (LinearMap.ker φ).subtype
    (Submodule.injective_subtype _)) := Projectivization.map_injective _ _
  haveI : Fintype (ℙ (ZMod p) (LinearMap.ker φ)) := Fintype.ofFinite _
  rw [show p + 1 = Finset.card (Finset.univ : Finset (ℙ (ZMod p) (LinearMap.ker φ))) from by
    rw [Finset.card_univ, Fintype.card_eq_nat_card]; exact hcard.symm]
  symm
  apply Finset.card_bij (fun w _ => Projectivization.map (LinearMap.ker φ).subtype
    (Submodule.injective_subtype _) w)
  · intro w _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    induction w using Projectivization.ind with | h k hk =>
    rw [Projectivization.map_mk, Projectivization.orthogonal_mk hu]
    have hk_mem := k.2; rw [LinearMap.mem_ker, hφ_apply] at hk_mem
    show u ⬝ᵥ _ = 0; exact hk_mem
  · intro a _ b _ hab; exact hι_inj hab
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    induction w using Projectivization.ind with | h k hk =>
    rw [Projectivization.orthogonal_mk hu hk] at hw
    have hk_mem : k ∈ LinearMap.ker φ := by rw [LinearMap.mem_ker, hφ_apply]; exact hw
    have hk_ne : (⟨k, hk_mem⟩ : LinearMap.ker φ) ≠ 0 := by
      intro h; apply hk; exact congr_arg Subtype.val h
    exact ⟨Projectivization.mk _ ⟨k, hk_mem⟩ hk_ne, Finset.mem_univ _, by
      rw [Projectivization.map_mk]; rfl⟩

open Classical in
/-- Each vertex's degree: p if self-orthogonal, p+1 otherwise.
    The orthogonal hyperplane of [v] in PG(2,p) has p+1 projective points.
    If v·v = 0, then [v] is among them and the degree is p; otherwise p+1. -/
lemma reimanGraph_degree_eq [Fintype (PG2 p)] [DecidableEq (PG2 p)]
    [DecidableRel (reimanGraph p).Adj] (v : PG2 p) :
    (reimanGraph p).degree v =
      if Projectivization.orthogonal v v then p else p + 1 := by
  rw [SimpleGraph.degree]
  have hN : (reimanGraph p).neighborFinset v =
      Finset.univ.filter (fun w => v ≠ w ∧ Projectivization.orthogonal v w) := by
    ext w; simp [reimanGraph, SimpleGraph.neighborFinset, SimpleGraph.neighborSet]
  rw [hN]
  set S := Finset.univ.filter (fun w : PG2 p => Projectivization.orthogonal v w)
  have hS_card := orthogonal_set_card p v
  split_ifs with h
  · have hv_in : v ∈ S := by simp [S, h]
    have : (Finset.univ.filter (fun w => v ≠ w ∧ Projectivization.orthogonal v w)) =
        S.erase v := by
      ext w; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, S]
      tauto
    rw [this, Finset.card_erase_of_mem hv_in, hS_card]; omega
  · have : (Finset.univ.filter (fun w => v ≠ w ∧ Projectivization.orthogonal v w)) = S := by
      ext w; simp only [Finset.mem_filter, Finset.mem_univ, true_and, S]
      exact ⟨fun ⟨_, hw⟩ => hw, fun hw => ⟨fun heq => h (heq ▸ hw), hw⟩⟩
    rw [this, hS_card]

/- **Edge count of Gp (omitted).**

The precise edge count `|E(Gp)| = (p³+p²+p)/2` requires knowing that a non-degenerate
conic in PG(2,𝔽_p) has exactly p+1 points, equivalently that x²+y²+z²=0 has p² solutions
in 𝔽_p³. This is a classical result from the theory of quadratic forms over finite fields,
typically proved via Gauss sums or character-sum orthogonality. The required character-sum
machinery (Fourier analysis over finite fields, product of Gauss sums giving the exact count)
is not yet available in Mathlib as of 2025.

The key results that ARE proved above without this gap:
  • `reimanGraph_card_vertices`: |V(Gp)| = p²+p+1
  • `reimanGraph_no_C4`: Gp contains no 4-cycle (the main combinatorial content)
  • `reimanGraph_degree_eq`: each vertex has degree p or p+1

Together these already give the Reiman bound  ex(n, C₄) ≥ (1/2)·n^{3/2}·(1-o(1))
since |E| ≈ p·|V|/2 ≈ n^{3/2}/2.
-/

end ReimanGraph

end chapter28
