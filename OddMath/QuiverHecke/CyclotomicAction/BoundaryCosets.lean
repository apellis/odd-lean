/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.BoundaryAssembly
import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# The Mackey boundary from the short-coset decomposition

`MackeyBoundary` (`BoundaryAssembly.lean`) takes the extraction `B₁` and the boundary `A_∂`
as data. In `docs/Nondegeneracy/DeformedMackeyBoundary.md` §§2–3 and
`docs/Nondegeneracy/DeformedCyclotomicTopRow.md` both are *derived*: the source `L₁` is the
sum of the short span `L₁'` and the compatible lifts `ℓ(w_k b)`, the lifts are independent
modulo `L₁'`, and `C₀ P(L₁') = 0`. Then `B₁` is the coordinate of `z` along the lifts modulo
`L₁'`, `C₀` is the polynomial component of the decomposition `L₀ = F(L₀') ⊕ j(V₀)`, and
`A_∂ = C₀ P ℓ`.

`MackeyCosets` records exactly these claims:

* the target decomposition `L₀ = F(L₀') ⊕ j(V₀)` (`direct`, `span`), the dot slides
  (`Rt_F`, `Rt_j`) and `P ρ = R_t P` (`P_ρ`), as in `MackeyBoundary`;
* the short subgroup `L₁'` with `ρ(L₁') ⊆ L₁'` (`ρ_short`) and `C₀ P(L₁') = 0` (`P_short`);
* the lift `ℓ : V₁ → L₁`, covering `L₁` modulo `L₁'` (`cover`), independent modulo `L₁'`
  (`ℓ_short`), with `ρ ℓ ≡ ℓ ρ̄` (`ρ_ℓ`) and right `B`-linear modulo `L₁'` (`ℓ_r`);
* right `B`-actions on `L₁` and `L₀` with `P` right linear (`P_r`), `F(L₀')` stable
  (`F_r`) and `j` right linear (`j_r`).

`MackeyCosets.toMackeyBoundary` builds the `MackeyBoundary`; `MackeyCosets.B₁_ℓ` and
`MackeyCosets.A_apply` identify its `B₁` and `A_∂`. `MackeyCosets.norm_of_short` restates the
norm hypothesis `hz₁` as `z₀ ≡ ℓ(S) mod L₁'`, the form in which the reverse norm identity (5)
of `DeformedBoundaryDivision.md` is proved.
-/

noncomputable section
open Finsupp
namespace OddMath.QuiverHecke.CyclotomicAction.BoundaryPolynomial

variable {B : Type*} [Ring B] (σ : B →+* B)

/-- The short-coset form of the first-order Mackey boundary. -/
structure MackeyCosets (L₁ L₀ L₀' : Type*) [AddCommGroup L₁] [AddCommGroup L₀]
    [AddCommGroup L₀'] where
  /-- The map `P(h ⊗ b) = h f_i(x₁) T ⊗ b`. -/
  P : L₁ →+ L₀
  /-- The corrected operator `ρ` on the source. -/
  ρ : L₁ →+ L₁
  /-- The target right-dot action `R_t`. -/
  Rt : L₀ →+ L₀
  /-- The crossing summand `F : L₀' → L₀`. -/
  F : L₀' →+ L₀
  /-- The polynomial summand `j(t^l b) = x_(n+1)^l e ⊗ b`. -/
  j : (ℕ →₀ B) →+ L₀
  /-- The crossing-contraction operator `X` on `L₀'`. -/
  X : L₀' →+ L₀'
  /-- The degree-zero operator `E : L₀' → B`. -/
  E : L₀' →+ B
  /-- The short span `L₁'`. -/
  short : AddSubgroup L₁
  /-- The compatible lifts `ℓ(w_k b)`. -/
  ℓ : (ℕ →₀ B) →+ L₁
  /-- The right `B`-action on the source. -/
  r₁ : B → L₁ →+ L₁
  /-- The right `B`-action on the target. -/
  r₀ : B → L₀ →+ L₀
  P_ρ : ∀ z, P (ρ z) = Rt (P z)
  Rt_F : ∀ u, Rt (F u) = F (X u) + j (single 0 (E u))
  Rt_j : ∀ f, Rt (j f) = j (tShift σ f)
  direct : ∀ u f, F u + j f = 0 → u = 0 ∧ f = 0
  span : ∀ y, ∃ u f, y = F u + j f
  ρ_short : ∀ z ∈ short, ρ z ∈ short
  P_short : ∀ z ∈ short, ∃ u, P z = F u
  cover : ∀ z, ∃ v, z - ℓ v ∈ short
  ℓ_short : ∀ v, ℓ v ∈ short → v = 0
  ρ_ℓ : ∀ v, ρ (ℓ v) - ℓ (tShift σ v) ∈ short
  ℓ_r : ∀ (b : B) v, ℓ (rsmul b v) - r₁ b (ℓ v) ∈ short
  P_r : ∀ (b : B) z, P (r₁ b z) = r₀ b (P z)
  F_r : ∀ (b : B) u, ∃ u', r₀ b (F u) = F u'
  j_r : ∀ (b : B) f, r₀ b (j f) = j (rsmul b f)

namespace MackeyCosets

variable {σ} {L₁ L₀ L₀' : Type*} [AddCommGroup L₁] [AddCommGroup L₀] [AddCommGroup L₀']
  (M : MackeyCosets σ L₁ L₀ L₀')

theorem eq_of_direct {u u' : L₀'} {f f' : ℕ →₀ B} (h : M.F u + M.j f = M.F u' + M.j f') :
    u = u' ∧ f = f' := by
  have := M.direct (u - u') (f - f') (by
    rw [map_sub, map_sub, sub_add_sub_comm, h, sub_self])
  exact ⟨sub_eq_zero.mp this.1, sub_eq_zero.mp this.2⟩

theorem eq_of_short {v v' : ℕ →₀ B} {z : L₁} (h : z - M.ℓ v ∈ M.short)
    (h' : z - M.ℓ v' ∈ M.short) : v = v' := by
  have : M.ℓ (v' - v) ∈ M.short := by
    rw [map_sub, show M.ℓ v' - M.ℓ v = (z - M.ℓ v) - (z - M.ℓ v') by abel]
    exact M.short.sub_mem h h'
  exact (sub_eq_zero.mp (M.ℓ_short _ this)).symm

/-- The polynomial component `C₀ : L₀ → V₀` of `L₀ = F(L₀') ⊕ j(V₀)`. -/
def C₀ : L₀ →+ (ℕ →₀ B) where
  toFun y := Classical.choose (Classical.choose_spec (M.span y))
  map_zero' := by
    have h := Classical.choose_spec (Classical.choose_spec (M.span 0))
    exact ((M.eq_of_direct (u' := 0) (f' := 0) (by rw [← h, map_zero, map_zero, add_zero])).2)
  map_add' y y' := by
    have h := Classical.choose_spec (Classical.choose_spec (M.span (y + y')))
    have h₁ := Classical.choose_spec (Classical.choose_spec (M.span y))
    have h₂ := Classical.choose_spec (Classical.choose_spec (M.span y'))
    refine (M.eq_of_direct (u' := Classical.choose (M.span y) + Classical.choose (M.span y'))
      (h.symm.trans ?_)).2
    rw [map_add, map_add]
    nth_rw 1 [h₁, h₂]
    abel

theorem exists_eq_F_add_j_C₀ (y : L₀) : ∃ u, y = M.F u + M.j (M.C₀ y) :=
  ⟨_, Classical.choose_spec (Classical.choose_spec (M.span y))⟩

theorem C₀_eq {y : L₀} {u : L₀'} {f : ℕ →₀ B} (h : y = M.F u + M.j f) : M.C₀ y = f := by
  obtain ⟨u', hu'⟩ := M.exists_eq_F_add_j_C₀ y
  exact (M.eq_of_direct (hu'.symm.trans h)).2

theorem C₀_P_short {z : L₁} (hz : z ∈ M.short) : M.C₀ (M.P z) = 0 := by
  obtain ⟨u, hu⟩ := M.P_short z hz
  exact M.C₀_eq (u := u) (f := 0) (by rw [hu, map_zero, add_zero])

/-- The extraction `B₁`: the coordinate of `z` along the lifts, modulo `L₁'`. -/
def B₁ : L₁ →+ (ℕ →₀ B) where
  toFun z := Classical.choose (M.cover z)
  map_zero' := M.eq_of_short (Classical.choose_spec (M.cover 0))
    (by rw [map_zero, sub_zero]; exact M.short.zero_mem)
  map_add' z z' := M.eq_of_short (Classical.choose_spec (M.cover (z + z'))) (by
    rw [map_add, show z + z' - (M.ℓ (Classical.choose (M.cover z)) +
        M.ℓ (Classical.choose (M.cover z'))) = (z - M.ℓ (Classical.choose (M.cover z))) +
        (z' - M.ℓ (Classical.choose (M.cover z'))) by abel]
    exact M.short.add_mem (Classical.choose_spec (M.cover z))
      (Classical.choose_spec (M.cover z')))

theorem sub_ℓ_B₁_mem (z : L₁) : z - M.ℓ (M.B₁ z) ∈ M.short :=
  Classical.choose_spec (M.cover z)

theorem B₁_eq {z : L₁} {v : ℕ →₀ B} (h : z - M.ℓ v ∈ M.short) : M.B₁ z = v :=
  M.eq_of_short (M.sub_ℓ_B₁_mem z) h

theorem B₁_ℓ (v : ℕ →₀ B) : M.B₁ (M.ℓ v) = v :=
  M.B₁_eq (by rw [sub_self]; exact M.short.zero_mem)

/-- The boundary `A_∂ = C₀ P ℓ`. -/
def A : (ℕ →₀ B) →+ (ℕ →₀ B) := M.C₀.comp (M.P.comp M.ℓ)

theorem A_apply (v : ℕ →₀ B) : M.A v = M.C₀ (M.P (M.ℓ v)) := rfl

theorem B₁_ρ (z : L₁) : M.B₁ (M.ρ z) = tShift σ (M.B₁ z) := by
  refine M.B₁_eq ?_
  rw [show M.ρ z - M.ℓ (tShift σ (M.B₁ z)) = M.ρ (z - M.ℓ (M.B₁ z)) +
      (M.ρ (M.ℓ (M.B₁ z)) - M.ℓ (tShift σ (M.B₁ z))) by rw [map_sub]; abel]
  exact M.short.add_mem (M.ρ_short _ (M.sub_ℓ_B₁_mem z)) (M.ρ_ℓ _)

theorem P_split (z : L₁) : ∃ u, M.P z = M.F u + M.j (M.A (M.B₁ z)) := by
  obtain ⟨u, hu⟩ := M.exists_eq_F_add_j_C₀ (M.P (M.ℓ (M.B₁ z)))
  obtain ⟨u', hu'⟩ := M.P_short _ (M.sub_ℓ_B₁_mem z)
  refine ⟨u + u', ?_⟩
  rw [A_apply, map_add, add_right_comm, ← hu, ← hu', ← map_add, add_sub_cancel]

theorem A_rsmul (b : B) (v : ℕ →₀ B) : M.A (rsmul b v) = rsmul b (M.A v) := by
  obtain ⟨u, hu⟩ := M.exists_eq_F_add_j_C₀ (M.P (M.ℓ v))
  obtain ⟨u', hu'⟩ := M.F_r b u
  rw [A_apply, show M.ℓ (rsmul b v) = M.r₁ b (M.ℓ v) + (M.ℓ (rsmul b v) - M.r₁ b (M.ℓ v)) by
      abel, map_add, map_add, M.C₀_P_short (M.ℓ_r b v), add_zero]
  refine M.C₀_eq (u := u') ?_
  rw [M.P_r, hu, map_add, hu', M.j_r, A_apply]

/-- The `MackeyBoundary` of the short-coset decomposition. -/
def toMackeyBoundary : MackeyBoundary σ L₁ L₀ L₀' where
  P := M.P
  ρ := M.ρ
  Rt := M.Rt
  F := M.F
  j := M.j
  X := M.X
  E := M.E
  B₁ := M.B₁
  A := M.A
  P_ρ := M.P_ρ
  Rt_F := M.Rt_F
  Rt_j := M.Rt_j
  direct := M.direct
  B₁_ρ := M.B₁_ρ
  B₁_surjective v := ⟨M.ℓ v, M.B₁_ℓ v⟩
  P_split := M.P_split
  A_rsmul := M.A_rsmul

@[simp] theorem toMackeyBoundary_A : M.toMackeyBoundary.A = M.A := rfl

@[simp] theorem toMackeyBoundary_B₁ : M.toMackeyBoundary.B₁ = M.B₁ := rfl

/-- **(7) for every corrected iterate**, with the lift of `S(ρ̄) w₀` given modulo the short
span: if `z₀ ≡ ℓ(S) mod L₁'` and `P z₀ = j(c F)`, then `Σ_j φ_(k+j) b_j = c F t^k`. -/
theorem norm_of_short {S F : ℕ →₀ B} {D : ℕ} (hS : DegLT S (D + 1)) (hSσ : ∀ j, σ (S j) = S j)
    {c : B} (hc : σ c = c) {z₀ : L₁} (hz₁ : z₀ - M.ℓ S ∈ M.short)
    (hz₀ : M.P z₀ = M.j (lsmul c F)) (k : ℕ) :
    ∑ j ∈ Finset.range (D + 1), rsmul (S j) (M.toMackeyBoundary.φ (k + j)) =
      lsmul c (tPow σ k F) :=
  M.toMackeyBoundary.norm hS hSσ hc (M.B₁_eq hz₁) hz₀ k

/-- **Displays (2) and (4)** for the short-coset boundary, with `z₀ ≡ ℓ(S) mod L₁'`. -/
theorem window_pos_of_short (hσ : Function.Injective σ) {S F : ℕ →₀ B} {D N : ℕ}
    (hS : MonicDeg S D) (hF : MonicDeg F N) (hSσ : ∀ j, σ (S j) = S j) (c : Bˣ)
    (hc : σ c = c) {z₀ : L₁} (hz₁ : z₀ - M.ℓ S ∈ M.short)
    (hz₀ : M.P z₀ = M.j (lsmul (c : B) F)) (hDN : D ≤ N) (p : ℕ →₀ B) :
    ∃! wr : (ℕ →₀ B) × (ℕ →₀ B), DegLT wr.2 (N - D) ∧ M.A wr.1 + wr.2 = p :=
  M.toMackeyBoundary.window_pos hσ hS hF hSσ c hc (M.B₁_eq hz₁) hz₀ hDN p

theorem window_neg_of_short (hσ : Function.Bijective σ) {S F : ℕ →₀ B} {D N : ℕ}
    (hS : MonicDeg S D) (hF : MonicDeg F N) (hSσ : ∀ j, σ (S j) = S j) (c : Bˣ)
    (hc : σ c = c) {z₀ : L₁} (hz₁ : z₀ - M.ℓ S ∈ M.short)
    (hz₀ : M.P z₀ = M.j (lsmul (c : B) F)) (hND : N < D) (p : ℕ →₀ B) (x : ℕ → B) :
    ∃! v : ℕ →₀ B, M.A v = p ∧
      ∀ r < D - N, capRow σ M.toMackeyBoundary.φ r v = x r :=
  M.toMackeyBoundary.window_neg hσ hS hF hSσ c hc (M.B₁_eq hz₁) hz₀ hND p x

end MackeyCosets

end OddMath.QuiverHecke.CyclotomicAction.BoundaryPolynomial
