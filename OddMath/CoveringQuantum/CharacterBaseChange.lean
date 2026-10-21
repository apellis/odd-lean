import OddMath.CoveringQuantum.CharacterOrdinary
import OddMath.CoveringQuantum.SerreBaseChange
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Weight dimensions under extension of fields

Extension of scalars commutes with the Serre presentation and with its weight spaces.
This supplies the field-extension step in the character comparison of Hill–Wang.
No transcendence, characteristic, or restriction on the covering parameter is needed.
-/

noncomputable section

open TensorProduct LieLean Module

namespace OddMath.CoveringQuantum.SuperCartanDatum

variable {I k K : Type*} [Field k] [Field K] [Algebra k K]
  (C : SuperCartanDatum I) (q : kˣ) (π : k)

private abbrev qK : Kˣ := Units.map (algebraMap k K).toMonoidHom q

private def serreCoeffsFree : PreF k I →ₐ[k] C.serreF (qK q) (algebraMap k K π) :=
  FreeAlgebra.lift k fun i ↦ C.toSerreF (qK q) (algebraMap k K π) (PreF.θ K i)

private theorem serreCoeffsFree_apply (x : PreF k I) :
    serreCoeffsFree C q π x =
      C.toSerreF (qK q) (algebraMap k K π) (FreeAlgebra.mapCoeffs (algebraMap k K) x) := by
  induction x using FreeAlgebra.induction with
  | grade0 c =>
    rw [AlgHom.commutes, FreeAlgebra.mapCoeffs_algebraMap, AlgHom.commutes]
    exact IsScalarTower.algebraMap_apply k K _ c
  | grade1 i => simp [serreCoeffsFree, PreF.θ]
  | add x y hx hy => simp only [map_add, hx, hy]
  | mul x y hx hy => simp only [map_mul, hx, hy]

private def serreCoeffs : C.serreF q π →ₐ[k] C.serreF (qK q) (algebraMap k K π) :=
  RingQuot.liftAlgHom k ⟨serreCoeffsFree C q π, fun _ _ h ↦ by
    cases h with
    | serre i j hij =>
      rw [serreCoeffsFree_apply, C.mapCoeffs_serreElt,
        C.toSerreF_serreElt _ _ hij, map_zero]⟩

private theorem serreCoeffs_mk (x : PreF k I) :
    serreCoeffs C q π (C.toSerreF q π x) =
      C.toSerreF (qK q) (algebraMap k K π) (FreeAlgebra.mapCoeffs (algebraMap k K) x) := by
  rw [serreCoeffs, toSerreF, RingQuot.liftAlgHom_mkAlgHom_apply]
  exact serreCoeffsFree_apply C q π x

private def serreTensorFree : PreF K I →ₐ[K] K ⊗[k] C.serreF q π :=
  FreeAlgebra.lift K fun i ↦ 1 ⊗ₜ C.toSerreF q π (PreF.θ k i)

private theorem serreTensorFree_map (x : PreF k I) :
    serreTensorFree C q π (FreeAlgebra.mapCoeffs (algebraMap k K) x) =
      1 ⊗ₜ C.toSerreF q π x := by
  induction x using FreeAlgebra.induction with
  | grade0 c =>
    rw [FreeAlgebra.mapCoeffs_algebraMap, AlgHom.commutes, AlgHom.commutes,
      Algebra.TensorProduct.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply, Algebra.TensorProduct.tmul_one_eq_one_tmul]
  | grade1 i => simp [serreTensorFree, PreF.θ]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, tmul_add]
  | mul x y hx hy =>
    rw [map_mul, map_mul, hx, hy, map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

private def serreTensorInv : C.serreF (qK q) (algebraMap k K π) →ₐ[K]
    K ⊗[k] C.serreF q π :=
  RingQuot.liftAlgHom K ⟨serreTensorFree C q π, fun _ _ h ↦ by
    cases h with
    | serre i j hij =>
      rw [← C.mapCoeffs_serreElt (algebraMap k K) q π, serreTensorFree_map,
        C.toSerreF_serreElt q π hij, tmul_zero, map_zero]⟩

private theorem serreTensorInv_mk (x : PreF K I) :
    serreTensorInv C q π (C.toSerreF (qK q) (algebraMap k K π) x) =
      serreTensorFree C q π x := by
  rw [serreTensorInv, toSerreF, RingQuot.liftAlgHom_mkAlgHom_apply]

private theorem serreTensorInv_coeffs (x : C.serreF q π) :
    serreTensorInv (K := K) C q π (serreCoeffs C q π x) = 1 ⊗ₜ x := by
  obtain ⟨y, rfl⟩ := C.toSerreF_surjective q π x
  rw [serreCoeffs_mk, serreTensorInv_mk, serreTensorFree_map]

private def serreTensorHom : K ⊗[k] C.serreF q π →ₐ[K]
    C.serreF (qK q) (algebraMap k K π) :=
  Algebra.TensorProduct.lift (Algebra.ofId K _) (serreCoeffs C q π)
    (fun c _ ↦ Algebra.commute_algebraMap_left c _)

private theorem serreTensorHom_tmul (c : K) (x : C.serreF q π) :
    serreTensorHom C q π (c ⊗ₜ x) = c • serreCoeffs C q π x := by
  rw [serreTensorHom, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply,
    ← Algebra.smul_def]

/-- Scalar extension of the Serre-presented half algebra. -/
def serreBaseChangeEquiv : K ⊗[k] C.serreF q π ≃ₐ[K]
    C.serreF (Units.map (algebraMap k K).toMonoidHom q) (algebraMap k K π) :=
  AlgEquiv.ofAlgHom (serreTensorHom C q π) (serreTensorInv C q π)
    (by
      apply RingQuot.ringQuot_ext'
      apply FreeAlgebra.hom_ext
      funext i
      change serreTensorHom C q π
        (serreTensorInv C q π (C.toSerreF _ _ (FreeAlgebra.ι K i))) = _
      rw [serreTensorInv_mk, serreTensorFree, FreeAlgebra.lift_ι_apply,
        serreTensorHom_tmul, one_smul, serreCoeffs_mk]
      simp only [PreF.θ, FreeAlgebra.mapCoeffs_ι]
      rfl)
    (by
      apply Algebra.TensorProduct.ext'
      intro c x
      simp only [AlgHom.comp_apply, serreTensorHom_tmul, map_smul,
        serreTensorInv_coeffs, AlgHom.id_apply, smul_tmul', smul_eq_mul, mul_one])

@[simp] theorem serreBaseChangeEquiv_tmul_toSerreF (c : K) (x : PreF k I) :
    C.serreBaseChangeEquiv (K := K) q π (c ⊗ₜ C.toSerreF q π x) =
      c • C.toSerreF (Units.map (algebraMap k K).toMonoidHom q) (algebraMap k K π)
        (FreeAlgebra.mapCoeffs (algebraMap k K) x) := by
  simp only [serreBaseChangeEquiv, AlgEquiv.ofAlgHom_apply,
    serreTensorHom_tmul, serreCoeffs_mk]

/-- The quotient weight space is spanned by the images of words of that weight. -/
theorem serreWeightSpace_eq_span (ν : I →₀ ℕ) :
    C.serreWeightSpace q π ν = Submodule.span k
      (Set.range fun w : LusztigF.Words ν ↦ C.toSerreF q π (FreeAlgebra.wordBasis k I w.1)) := by
  classical
  change (LusztigF.weightSpace k ν).map _ = _
  rw [LusztigF.weightSpace_eq_span, Submodule.map_span, ← Set.range_comp]
  rfl

/-- The Serre base-change equivalence preserves each weight space. -/
theorem serreBaseChangeEquiv_weightSpace (ν : I →₀ ℕ) :
    ((C.serreWeightSpace q π ν).baseChange K).map
        (C.serreBaseChangeEquiv (K := K) q π).toLinearMap =
      C.serreWeightSpace (Units.map (algebraMap k K).toMonoidHom q)
        (algebraMap k K π) ν := by
  classical
  rw [C.serreWeightSpace_eq_span, Submodule.baseChange_span, Submodule.map_span,
    C.serreWeightSpace_eq_span, Set.image_image, ← Set.range_comp]
  congr 2
  funext w
  simp only [Function.comp_apply, TensorProduct.mk_apply,
    AlgEquiv.toLinearMap_apply, serreBaseChangeEquiv_tmul_toSerreF,
    one_smul, FreeAlgebra.mapCoeffs_wordBasis]

/-- Weight dimensions in the Serre presentation are invariant under field extension. -/
theorem finrank_serreWeightSpace_baseChange (ν : I →₀ ℕ) :
    finrank k (C.serreWeightSpace q π ν) =
      finrank K (C.serreWeightSpace (Units.map (algebraMap k K).toMonoidHom q)
        (algebraMap k K π) ν) := by
  let S := C.serreWeightSpace q π ν
  let : Module.Free k S := Module.Free.of_divisionRing k S
  let e := C.serreBaseChangeEquiv (K := K) q π
  have h₁ := (Submodule.toBaseChange.toLinearEquiv K S).finrank_eq
  have h₂ := (Submodule.equivMapOfInjective e.toLinearMap e.injective
    (S.baseChange K)).finrank_eq
  rw [Module.finrank_baseChange] at h₁
  rw [C.serreBaseChangeEquiv_weightSpace] at h₂
  exact h₁.trans h₂

end OddMath.CoveringQuantum.SuperCartanDatum
