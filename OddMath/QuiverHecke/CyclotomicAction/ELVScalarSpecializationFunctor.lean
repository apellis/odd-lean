import OddMath.SKM.ELVScalarParity
import StringDiagrams.Super.BoxProductMonoidal

/-! # Ordinary specialization of the signed ELV coefficient category

The coefficient evaluation of `InvertibleDotProbe.md` §1 is a superfunctor:
odd homogeneous coefficients vanish, so the target coefficient category is
BoxUnit. Applying the existing box-product map and left unitor constructs the
literal specialization a tensor f ↦ eval(a) • f, preserving signed composition.
No old-strand cyclotomic relation is killed by this module.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.SKM.SYM
open scoped Classical TensorProduct
namespace OddMath.QuiverHecke
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (values : I × ℕ → k)
  (hvalues : ∀ i r, elvElementaryRank D cutoff i ≤ r → values (i,r) = 0)

def elvCoefficientScalarFunctor :
    Superfunctor k (SuperalgebraCat (elvCoefficientParity (k := k) D cutoff))
      (BoxUnit.{u,u} k) :=
  Superfunctor.ofLinearMaps (fun _ => BoxUnit.star)
    (fun _ _ => (elvScalarEvaluation D cutoff values hvalues).toLinearMap)
    (fun _ => by
      change elvScalarEvaluation D cutoff values hvalues 1 = 1
      exact map_one _)
    (fun f g => by
      change elvScalarEvaluation D cutoff values hvalues
          (SuperalgebraCat.toElem g * SuperalgebraCat.toElem f) =
        elvScalarEvaluation D cutoff values hvalues (SuperalgebraCat.toElem g) *
          elvScalarEvaluation D cutoff values hvalues (SuperalgebraCat.toElem f)
      exact map_mul _ _ _)
    (by
      intro A B p f hf
      rcases parity_eq_zero_or_one p with rfl | rfl
      · exact BoxUnit.mem_parity_zero _
      · change elvScalarEvaluation D cutoff values hvalues
          (SuperalgebraCat.toElem f) ∈ trivialGrading k 1
        rw [trivialGrading_one, Submodule.mem_bot]
        exact elvScalarEvaluation_odd_zero D cutoff values hvalues
          ((SuperalgebraCat.mem_parity_iff (elvCoefficientParity D cutoff)).mp hf))

/-- Actual scalar specialization of the signed coefficient category, built
from existing superfunctorial tensor and unitor comparisons. -/
def elvAffineScalarSpecialization :
    Superfunctor k (ELVCoefficientCategory D Sc cutoff) (H D Sc) :=
  (BoxProd.map (elvCoefficientScalarFunctor D cutoff values hvalues)
    (Superfunctor.id k (H D Sc))).comp (BoxProd.lunit (H D Sc))

theorem elvAffineScalarSpecialization_tmul
    {A B : ELVCoefficientCategory D Sc cutoff}
    (c : A.fst ⟶ B.fst) (f : A.snd ⟶ B.snd) :
    (elvAffineScalarSpecialization D Sc cutoff values hvalues).map (BoxProd.tmulHom c f) =
      elvScalarEvaluation D cutoff values hvalues (SuperalgebraCat.toElem c) • f := by
  change (BoxProd.lunit (H D Sc)).map
    ((BoxProd.map (elvCoefficientScalarFunctor D cutoff values hvalues)
      (Superfunctor.id k (H D Sc))).map (BoxProd.tmulHom c f)) = _
  rw [BoxProd.map_tmulHom, BoxProd.lunit_map_tmulHom]
  rfl

/-- Full source coefficient insertion specializes by the chosen scalar
evaluation, with the affine diagram left unchanged. -/
theorem elvAffineScalarSpecialization_source {s t : List I}
    (c : SKM.SYM D k) (f : (pres D Sc).obj (ob D s) ⟶ (pres D Sc).obj (ob D t)) :
    (elvAffineScalarSpecialization D Sc cutoff values hvalues).map
      (elvQuotientMap D Sc cutoff _ _ (sourceCoefficientHom D Sc c f)) =
        scalarEvaluation D values c • f := by
  rw [elvQuotientMap_source]
  change (elvAffineScalarSpecialization D Sc cutoff values hvalues).map
    (BoxProd.tmulHom
      (X := elvQuotientObj D Sc cutoff (coefficientObj D Sc s))
      (Y := elvQuotientObj D Sc cutoff (coefficientObj D Sc t))
      (SuperalgebraCat.ofElem (elvCoefficientQuotient D cutoff c)) f) = _
  rw [elvAffineScalarSpecialization_tmul, SuperalgebraCat.toElem_ofElem,
    elvScalarEvaluation_quotient]

/-- Affine Homs are reached by inserting coefficient one. Surjectivity here
does not concern the cyclotomic quotient or assert faithfulness. -/
theorem elvAffineScalarSpecialization_surjective (s t : List I) :
    Function.Surjective
      ((elvAffineScalarSpecialization D Sc cutoff values hvalues).map :
        (elvQuotientObj D Sc cutoff (coefficientObj D Sc s) ⟶
          elvQuotientObj D Sc cutoff (coefficientObj D Sc t)) →
        ((pres D Sc).obj (ob D s) ⟶ (pres D Sc).obj (ob D t))) := by
  intro f
  refine ⟨BoxProd.tmulHom (SuperalgebraCat.ofElem 1) f, ?_⟩
  rw [elvAffineScalarSpecialization_tmul, SuperalgebraCat.toElem_ofElem, map_one, one_smul]

end OddMath.QuiverHecke
