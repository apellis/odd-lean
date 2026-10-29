/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.AppendContentShortImage
import OddMath.QuiverHecke.CyclotomicAction.AppendContentRhoCoordinates

/-!
# The ordinary cyclotomic content Mackey boundary

The ordinary-polynomial specialization of `DeformedMackeyBoundary.md` (5)–(8).
The short-image inclusion and the normalized moving lifts construct the cosets
and their induced polynomial boundary; no factorization or abstract coset data
is assumed. The first-order defect is the degree-zero contraction of the
crossing component of the prescribed lift. Only polynomial parity is required,
not monicity. Old height is `n + 1`; zero old height and full exterior-deformed
coefficients are not covered here.
-/

noncomputable section
open Finsupp
namespace OddMath.QuiverHecke
open CyclotomicAction.BoundaryPolynomial
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
  (a : I → _root_.Polynomial k) (n : ℕ) (β : Multiset I) (i : I)
  (ha : CyclotomicPolynomialParity D a)
local notation "B" => CyclotomicContentCorner D Sc a n β
local notation "σ" => contentCornerParity D Sc a n β i ha

/-- The two finite-support presentations of parity-twisted raising agree. -/
theorem movingParityRaise_eq_tShift {R : Type*} [Ring R] (τ : R →+* R) :
    movingParityRaise τ.toAddMonoidHom = tShift τ := by
  apply Finsupp.addHom_ext
  intro m b
  rw [movingParityRaise_single, tShift_single]
  rfl

/-- The content Mackey cosets, assembled from the prescribed source and target. -/
def appendContentMackeyCosets :
    MackeyCosets σ (appendContentSource D Sc a n β i)
      (appendTensorFixed D Sc i n B) (appendTensorLeftCoordinates D Sc i n B) :=
  MackeyCosets.ofTarget σ (appendContentMackeyTarget D Sc a n β i ha)
    (appendContentP D Sc a n β i ha) (appendContentRho D Sc a n β i ha)
    (appendContentShort D Sc a n β i) (appendContentRhoLift D Sc a n β i)
    (appendContentSourceRightMul D Sc a n β i)
    (appendContentP_rho D Sc a n β i ha)
    (appendContentShort_rho D Sc a n β i ha)
    (fun z hz => by
      obtain ⟨u, hu⟩ := appendContentP_short_mem D Sc a n β i ha z hz
      exact ⟨u, hu.symm⟩)
    (fun z => ⟨_, appendContentRho_cover D Sc a n β i z⟩)
    (fun f hf => by
      have h := (appendContentRhoExtract_eq_zero_iff D Sc a n β i _).mpr hf
      rwa [appendContentRhoExtract_lift] at h)
    (fun f => by
      rw [appendContentRho_lift, movingParityRaise_eq_tShift, sub_self]
      exact (appendContentShort D Sc a n β i).zero_mem)
    (fun b f => by
      rw [appendContentRhoLift_rightMul, sub_self]
      exact (appendContentShort D Sc a n β i).zero_mem)
    (appendContentP_rightMul D Sc a n β i ha)

local notation "M" => appendContentMackeyCosets D Sc a n β i ha

/-- The induced boundary on the ordinary cyclotomic content corner. -/
def appendContentMackeyBoundary :
    MackeyBoundary σ (appendContentSource D Sc a n β i)
      (appendTensorFixed D Sc i n B) (appendTensorLeftCoordinates D Sc i n B) :=
  (M).toMackeyBoundary

/-- The derived source extraction is the normalized moving-shuffle coefficient. -/
theorem appendContentMackeyCosets_B₁ (z : appendContentSource D Sc a n β i) :
    (M).B₁ z = appendContentRhoExtract D Sc a n β i z :=
  (M).B₁_eq (appendContentRho_cover D Sc a n β i z)

/-- The derived target projection is the polynomial coordinate of the PBW splitting. -/
theorem appendContentMackeyCosets_C₀ (y : appendTensorFixed D Sc i n B) :
    (M).C₀ y = ((appendTensorCornerEquiv D Sc i n B).symm y).2 := by
  apply (M).C₀_eq (u := ((appendTensorCornerEquiv D Sc i n B).symm y).1)
  exact ((appendTensorCornerEquiv D Sc i n B).apply_symm_apply y).symm.trans
    (appendTargetF_add_J D Sc i n B _ _).symm

/-- The boundary is the polynomial component of P on the specified normalized lift. -/
theorem appendContentBoundary_apply (f : ℕ →₀ B) :
    (appendContentMackeyBoundary D Sc a n β i ha).A f =
      ((appendTensorCornerEquiv D Sc i n B).symm
        (appendContentP D Sc a n β i ha (appendContentRhoLift D Sc a n β i f))).2 :=
  appendContentMackeyCosets_C₀ D Sc a n β i ha _

/-- The crossing component of P on the specified normalized lift. -/
def appendContentBoundaryCrossing : (ℕ →₀ B) →+ appendTensorLeftCoordinates D Sc i n B :=
  (AddMonoidHom.fst _ _).comp ((appendTensorCornerEquiv D Sc i n B).symm.toAddMonoidHom.comp
    ((appendContentP D Sc a n β i ha).comp (appendContentRhoLift D Sc a n β i)))

local notation "ψ" => appendContentBoundaryCrossing D Sc a n β i ha
local notation "A" => MackeyBoundary.A (appendContentMackeyBoundary D Sc a n β i ha)
local notation "T" => appendContentMackeyTarget D Sc a n β i ha

/-- Both components of the normalized lifted image are prescribed by target PBW. -/
theorem appendContentBoundary_split (f : ℕ →₀ B) :
    appendContentP D Sc a n β i ha (appendContentRhoLift D Sc a n β i f) =
      (T).F (ψ f) + (T).j (A f) := by
  rw [appendContentBoundary_apply]
  exact ((appendTensorCornerEquiv D Sc i n B).apply_symm_apply _).symm.trans
    (appendTargetF_add_J D Sc i n B _ _).symm

/-- The polynomial component factors through the normalized source extraction. -/
theorem appendContentBoundary_factor (z : appendContentSource D Sc a n β i) :
    ((appendTensorCornerEquiv D Sc i n B).symm (appendContentP D Sc a n β i ha z)).2 =
      A (appendContentRhoExtract D Sc a n β i z) := by
  rw [← appendContentMackeyCosets_C₀ D Sc a n β i ha]
  obtain ⟨u, hu⟩ := (M).P_split z
  rw [appendContentMackeyCosets_B₁] at hu
  exact (M).C₀_eq hu

private theorem target_slide {R L L' : Type*} [Ring R] [AddCommGroup L] [AddCommGroup L']
    (τ : R →+* R) (U : MackeyTarget τ L L') (u : L') (f : ℕ →₀ R) :
    U.Rt (U.F u + U.j f) = U.F (U.X u) + U.j (single 0 (U.E u) + tShift τ f) := by
  rw [map_add, U.Rt_F, U.Rt_j, map_add, add_assoc]

private theorem target_coordinates {R L L' : Type*} [Ring R]
    [AddCommGroup L] [AddCommGroup L'] (τ : R →+* R) (U : MackeyTarget τ L L')
    (u u' : L') (f f' : ℕ →₀ R) (h : U.F u + U.j f = U.F u' + U.j f') :
    u = u' ∧ f = f' := by
  have hz := U.direct (u - u') (f - f') (by
    rw [map_sub, map_sub, sub_add_sub_comm, h, sub_self])
  exact ⟨sub_eq_zero.mp hz.1, sub_eq_zero.mp hz.2⟩

/-- The two first-order identities, including the specified crossing contraction. -/
theorem appendContentBoundary_firstOrder (f : ℕ →₀ B) :
    ψ (tShift σ f) = (T).X (ψ f) ∧
      A (tShift σ f) = single 0 ((T).E (ψ f)) + tShift σ (A f) := by
  have hraise : movingParityRaise (σ).toAddMonoidHom f = tShift σ f :=
    DFunLike.congr_fun (movingParityRaise_eq_tShift σ) f
  have hP := appendContentP_rhoLift D Sc a n β i ha f
  rw [hraise] at hP
  have hslide : (T).Rt ((T).F (ψ f) + (T).j (A f)) =
      (T).F ((T).X (ψ f)) +
        (T).j (single 0 ((T).E (ψ f)) + tShift σ (A f)) :=
    target_slide σ T (ψ f) (A f)
  have he : (T).F (ψ (tShift σ f)) + (T).j (A (tShift σ f)) =
      (T).F ((T).X (ψ f)) +
        (T).j (single 0 ((T).E (ψ f)) + tShift σ (A f)) :=
    (appendContentBoundary_split D Sc a n β i ha (tShift σ f)).symm.trans
      (hP.trans ((congrArg (T).Rt (appendContentBoundary_split D Sc a n β i ha f)).trans
        hslide))
  exact target_coordinates σ T _ _ _ _ he

/-- The degree-zero defect of the induced polynomial boundary. -/
theorem appendContentBoundary_defect (f : ℕ →₀ B) :
    A (tShift σ f) - tShift σ (A f) = single 0 ((T).E (ψ f)) := by
  exact (congrArg (fun g : ℕ →₀ B => g - tShift σ (A f))
    (appendContentBoundary_firstOrder D Sc a n β i ha f).2).trans
      (add_sub_cancel_right (single 0 ((T).E (ψ f))) (tShift σ (A f)))

/-- The boundary recurrence on normalized unit-coefficient moving monomials. -/
theorem appendContentBoundary_recurrence (m : ℕ) :
    A (single (m + 1) 1) = single 0 ((T).E (ψ (single m 1))) +
      tShift σ (A (single m 1)) := by
  simpa only [tShift_single, map_one] using
    (appendContentBoundary_firstOrder D Sc a n β i ha (single m 1)).2

end OddMath.QuiverHecke
