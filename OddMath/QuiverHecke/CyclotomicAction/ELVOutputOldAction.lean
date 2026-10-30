/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVOutputKernel
import OddMath.QuiverHecke.CyclotomicAction.ELVBoundaryRhoCoordinates

/-!
# Old source action on normalized output coordinates

The coefficient-linearity step toward `DeformedMackeyBoundary.md` (2).
Every old endomorphism acts on every extracted coefficient by old precomposition,
with the prescribed total-parity twist. Full ELV quotients are retained.
This does not yet identify the output balanced action or the boundary polynomial S.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped TensorProduct DirectSum Classical
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

private theorem coordinate_pair_transport (p : ZMod 2) {i : I} {v w : List I}
    (x y : PrependIdx i v w) (e : x.oldTarget = y.oldTarget)
    (ht : HEq (prependTail D Sc x) (prependTail D Sc y))
    (b : Old D Sc cutoff v y.oldTarget) :
    prependOldCoordinate D Sc cutoff p x
      (pair D Sc cutoff p i
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
          prependTail D Sc y) b) = e.symm ▸ b := by
  have transport {t t' : List I} (e : t = t')
      (f : (pres D Sc).obj (ob D (i :: t)) ⟶ (pres D Sc).obj (ob D w))
      (g : (pres D Sc).obj (ob D (i :: t')) ⟶ (pres D Sc).obj (ob D w))
      (hf : HEq f g) (b : Old D Sc cutoff v t') :
      pair D Sc cutoff p i ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] g) b =
      pair D Sc cutoff p i ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] f) (e.symm ▸ b) := by
    subst t'
    cases hf
    rfl
  rw [transport e _ _ ht b, prependOldCoordinate_pair]

/-- Every old source endomorphism acts on the extracted old coefficient, with
its total-parity twist. No scalar or homogeneity restriction is imposed. -/
theorem prependOldCoordinate_oldSource (p : ZMod 2) {i : I} {v w : List I}
    (x : PrependIdx i v w) (c : hom D Sc cutoff v v)
    (z : Target D Sc cutoff i v w) :
    prependOldCoordinate D Sc cutoff p x (oldSourceTarget D Sc cutoff i v w c z) =
      oldPrecomp D Sc cutoff v x.oldTarget (twist k p c)
        (prependOldCoordinate D Sc cutoff p x z) := by
  obtain ⟨f, rfl⟩ := prependOldReconstruct_surjective D Sc cutoff p i v w z
  induction f using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | add f g hf hg => simp only [map_add, hf, hg]
  | of q b =>
    change prependOldCoordinate D Sc cutoff p x
      (oldSourceTarget D Sc cutoff i v w c
        (prependOldReconstruct D Sc cutoff p i v w (DirectSum.lof k _ _ q b))) =
      oldPrecomp D Sc cutoff v x.oldTarget (twist k p c)
        (prependOldCoordinate D Sc cutoff p x
          (prependOldReconstruct D Sc cutoff p i v w (DirectSum.lof k _ _ q b)))
    rw [prependOldReconstruct, DirectSum.toModule_lof, oldSourceTarget_pair]
    by_cases h : x.tailKey = q.representative.tailKey
    · have e := x.oldTarget_eq_of_tailKey_eq q.representative h
      have ht := prependTail_heq_of_tailKey_eq D Sc x q.representative h
      rw [coordinate_pair_transport D Sc cutoff p x q.representative e ht,
        coordinate_pair_transport D Sc cutoff p x q.representative e ht]
      exact (show ∀ {t t' : List I} (e : t = t') (b : Old D Sc cutoff v t'),
        e.symm ▸ oldPrecomp D Sc cutoff v t' (twist k p c) b =
          oldPrecomp D Sc cutoff v t (twist k p c) (e.symm ▸ b) from
        by intro t t' e; subst t'; intro b; rfl) e b
    · rw [prependOldCoordinate_pair_off D Sc cutoff p x q.representative h,
        prependOldCoordinate_pair_off D Sc cutoff p x q.representative h, map_zero]

/-- Normalized output coefficients retain the old source action and its twist. -/
theorem outputLongCoordinate_oldSource (p : ZMod 2) (i : I) (v : List I)
    (m : ℕ) (c : hom D Sc cutoff v v) (z : Target D Sc cutoff i v (v ++ [i])) :
    outputLongCoordinate D Sc cutoff p i v m (oldSourceTarget D Sc cutoff i v (v ++ [i]) c z) =
      oldPrecomp D Sc cutoff v v (twist k p c) (outputLongCoordinate D Sc cutoff p i v m z) := by
  have transport {t t' : List I} (e : t = t')
      (f : Target D Sc cutoff i v (v ++ [i]) →ₗ[k] Old D Sc cutoff v t)
      (h : f (oldSourceTarget D Sc cutoff i v (v ++ [i]) c z) =
        oldPrecomp D Sc cutoff v t (twist k p c) (f z)) :
      (Eq.mp (congrArg (fun t => Target D Sc cutoff i v (v ++ [i]) →ₗ[k]
        Old D Sc cutoff v t) e) f) (oldSourceTarget D Sc cutoff i v (v ++ [i]) c z) =
      oldPrecomp D Sc cutoff v t' (twist k p c)
        ((Eq.mp (congrArg (fun t => Target D Sc cutoff i v (v ++ [i]) →ₗ[k]
          Old D Sc cutoff v t) e) f) z) := by
    subst t'
    exact h
  apply transport (longOutputIndex_oldTarget i v m)
  simp only [LinearMap.smul_apply, prependOldCoordinate_oldSource, map_smul]

end OddMath.QuiverHecke.ELVOld