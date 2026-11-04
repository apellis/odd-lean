import OddMath.QuiverHecke.SwappedAssembly.SupportedTensorCoefficientAction

/-! # Source coefficients on the complete supported tensor matrix

SwappedVacuumCoordinates §§6–7: assemble the raw source-coefficient
postcomposition actions on every source, target and path entry into the
endomorphism algebra of the same supported matrix module.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath.SKM
namespace OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
open CyclotomicAction ELVOld
universe u
section Product
variable {k B : Type*} [CommRing k] [Semiring B] [Algebra k B]
  {J : Type*} {V : J → Type*} [∀ j, AddCommGroup (V j)] [∀ j, Module k (V j)]
private def piCoefficientAction (ρ : ∀ j, B →ₐ[k] Module.End k (V j)) :
    B →ₐ[k] Module.End k (∀ j, V j) :=
  AlgHom.ofLinearMap
    { toFun b :=
        { toFun := fun v j => ρ j b (v j)
          map_add' := by intro v w; funext j; exact (ρ j b).map_add _ _
          map_smul' := by intro r v; funext j; exact (ρ j b).map_smul r _ }
      map_add' := by
        intro b c
        apply LinearMap.ext
        intro v
        funext j
        exact congrArg (fun f => f (v j)) ((ρ j).map_add b c)
      map_smul' := by
        intro r b
        apply LinearMap.ext
        intro v
        funext j
        exact congrArg (fun f => f (v j)) ((ρ j).toLinearMap.map_smul r b) }
    (by
      apply LinearMap.ext
      intro v
      funext j
      exact congrArg (fun f => f (v j)) (ρ j).map_one)
    (by
      intro b c
      apply LinearMap.ext
      intro v
      funext j
      exact congrArg (fun f => f (v j)) ((ρ j).map_mul b c))
end Product

variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : Datum I X) (Sc : Scalars D k) (m cutoff : I → ℕ) (ΛP ΛR : X) (L : I × ℕ → ℕ)
local notation "Tw" => parameterTwist D Sc
local notation "N" => PowerWordContent.powerBound D cutoff L

/-- The original coefficient ring acts on the entire supported matrix,
with all source sectors, weighted target sectors and formal paths retained. -/
def tensorMatrixCoefficientAction (sourceWord : List I) (b : Obj (SKM.sig D)) :
    SYM D k →ₐ[k] Module.End k
      (matrixModule D Sc m cutoff N ΛP ΛR
        (tensorSourceFamily D Sc m cutoff ΛP ΛR L sourceWord)
        (tensorTargetFamily D Sc m cutoff ΛP ΛR L) b) :=
  piCoefficientAction (fun _ => piCoefficientAction (fun _ => piCoefficientAction (fun p =>
    tensorFamilyWordHomCoefficientAction D Sc m cutoff L ΛP ΛR p sourceWord)))

/-- Every matrix entry is acted on by chronological postcomposition with
the coefficient on its same actual path target. -/
@[simp] theorem tensorMatrixCoefficientAction_apply (sourceWord : List I) (b : Obj (SKM.sig D))
    (a : SYM D k)
    (x : matrixModule D Sc m cutoff N ΛP ΛR
      (tensorSourceFamily D Sc m cutoff ΛP ΛR L sourceWord)
      (tensorTargetFamily D Sc m cutoff ΛP ΛR L) b)
    (sl : Sector I)
    (sr : {t : Sector I // (ΛP - contentWeight D t.1) + (-ΛR + contentWeight D t.2) = b.endR})
    (p : SPath b.word sl sr.1) :
    tensorMatrixCoefficientAction D Sc m cutoff ΛP ΛR L sourceWord b a x sl sr p =
      x sl sr p ≫ tensorFamilyPathCoefficientAction D Sc m cutoff L ΛP ΛR p a := rfl
end OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
