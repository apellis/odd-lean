import StringDiagrams.Super.BoxProductMonoidal
import OddMath.QuiverHecke.CyclotomicAction.CoefficientTransport.CyclotomicTarget
import OddMath.QuiverHecke.CyclotomicAction.PrefixScalarRelations.PrefixQPDistinct
import OddMath.SKM.ELVScalarParity

/-!
# Prefix scalar relations

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

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
end

end

section

/-!
# Right contexts in the old ELV coefficient category

For the relation-killing step of `DeformedGlobalQP.md` §2, adjoining an arbitrary
spectator word preserves the old cyclotomic ideal. The map fixes the full ELV
coefficient algebra and right-whiskers only the affine factor. In particular it
preserves signed composition and commutes with insertion of a strand on the left.

`rightContext_relation` preserves the colour-dependent ELV relation, with its odd
exterior coefficients and arbitrary cutoff, and `ideal_rightContext` extends this
to the two-sided old ideal. No finiteness condition on the colour set is needed.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped TensorProduct
namespace OddMath.QuiverHecke.ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Adjoin identity strands on the right of an affine morphism. -/
def affineRightContext (σ v w : List I) :
    ((pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w)) →ₗ[k]
    ((pres D Sc).obj (ob D (v ++ σ)) ⟶ (pres D Sc).obj (ob D (w ++ σ))) where
  toFun f := f ▷ (pres D Sc).obj (ob D σ)
  map_add' f g := MonoidalSupercategory.add_whiskerRight (R := k) f g _
  map_smul' c f := MonoidalSupercategory.smul_whiskerRight (R := k) c f _

/-- Right extension fixes all polynomial and exterior coefficients. -/
def rightContext (σ v w : List I) : hom D Sc cutoff v w →ₗ[k]
    hom D Sc cutoff (v ++ σ) (w ++ σ) :=
  TensorProduct.map LinearMap.id (affineRightContext D Sc σ v w)

@[simp] theorem rightContext_tmul (σ : List I) {v w : List I}
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff)
    (f : (pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w)) :
    rightContext D Sc cutoff σ v w (a ⊗ₜ[k] f) =
      a ⊗ₜ[k] affineRightContext D Sc σ v w f := rfl

private theorem rightContext_induction_hom {v w : List I}
    {P : hom D Sc cutoff v w → Prop} (x : hom D Sc cutoff v w) (zero : P 0)
    (tmul : ∀ (p q : ZMod 2) (a : (obj D Sc cutoff v).fst ⟶ (obj D Sc cutoff w).fst)
      (f : (pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w)),
      a ∈ parity (R := k) _ _ p → f ∈ parity (R := k) _ _ q → P (BoxProd.tmulHom a f))
    (add : ∀ x y, P x → P y → P (x + y)) : P x :=
  BoxProd.induction_on_homogeneous (P := P) x zero tmul add

/-- Right extension respects the signed coefficient-category composition. -/
theorem rightContext_comp (σ : List I) {v w z : List I}
    (f : hom D Sc cutoff v w) (g : hom D Sc cutoff w z) :
    rightContext D Sc cutoff σ v z (f ≫ g) =
      rightContext D Sc cutoff σ v w f ≫ rightContext D Sc cutoff σ w z g := by
  induction f using rightContext_induction_hom D Sc cutoff with
  | zero => simp only [Limits.zero_comp, map_zero]
  | add f f' hf hf' => simp only [Preadditive.add_comp, map_add, hf, hf']
  | tmul p q a f ha hf =>
    induction g using rightContext_induction_hom D Sc cutoff with
    | zero => simp only [Limits.comp_zero, map_zero]
    | add g g' hg hg' => simp only [Preadditive.comp_add, map_add, hg, hg']
    | tmul r s b g hb hg =>
      have hi : affineRightContext D Sc σ w z g ∈ parity (R := k) _ _ s :=
        MonoidalSupercategory.whiskerRight_mem ((pres D Sc).obj (ob D σ)) hg
      rw [BoxProd.tmulHom_comp_tmulHom ha f b hg, map_zsmul]
      change koszulSign p s • BoxProd.tmulHom
        (X := obj D Sc cutoff (v ++ σ)) (Y := obj D Sc cutoff (z ++ σ))
        (a ≫ b) (affineRightContext D Sc σ v z (f ≫ g)) =
        BoxProd.tmulHom (X := obj D Sc cutoff (v ++ σ))
          (Y := obj D Sc cutoff (w ++ σ)) a (affineRightContext D Sc σ v w f) ≫
        BoxProd.tmulHom (X := obj D Sc cutoff (w ++ σ))
          (Y := obj D Sc cutoff (z ++ σ)) b (affineRightContext D Sc σ w z g)
      rw [BoxProd.tmulHom_comp_tmulHom
        (X := obj D Sc cutoff (v ++ σ)) (Y := obj D Sc cutoff (w ++ σ))
        (Z := obj D Sc cutoff (z ++ σ)) ha _ b hi]
      congr 2
      exact MonoidalSupercategory.comp_whiskerRight (R := k) f g ((pres D Sc).obj (ob D σ))

/-- Left insertion and right extension commute, with coefficients unchanged. -/
theorem rightContext_insert (σ : List I) (i : I) {v w : List I}
    (f : hom D Sc cutoff v w) :
    rightContext D Sc cutoff σ (i :: v) (i :: w) (insert D Sc cutoff i v w f) =
      insert D Sc cutoff i (v ++ σ) (w ++ σ) (rightContext D Sc cutoff σ v w f) := by
  induction f using TensorProduct.inductionOn with
  | add f g hf hg => simp only [map_add, hf, hg]
  | tmul a f =>
    exact congrArg (fun g => a ⊗ₜ[k] g) (whiskerLeft_whiskerRight_cons D Sc i f σ)

private theorem affineRightContext_firstDotPower (σ : List I) (j : I) (v : List I)
    (n : ℕ) :
    affineRightContext D Sc σ (j :: v) (j :: v) (firstDotPower D Sc (j :: v) n) =
      firstDotPower D Sc (j :: (v ++ σ)) n := by
  have hp (w : List I) : firstDotPower D Sc w n = dotE D Sc w 0 ^ n := by
    simp only [dotE_pow, firstDotPower, List.map_replicate]
  change whiskerWordRingHom D Sc (j :: v) σ (firstDotPower D Sc (j :: v) n) = _
  rw [hp, map_pow]
  have hd : whiskerWordRingHom D Sc (j :: v) σ (dotE D Sc (j :: v) 0) =
      dotE D Sc (j :: (v ++ σ)) 0 :=
    dotE_whiskerRight D Sc (j :: v) σ 0 (by simp)
  rw [hd]
  exact (hp (j :: (v ++ σ))).symm

/-- Right extension preserves every first-position polynomial with full source coefficients. -/
theorem rightContext_deformedCyclotomic (σ : List I) (j : I) (v : List I)
    (N : ℕ) (c : Fin (N + 1) → SKM.SYM D k) :
    rightContext D Sc cutoff σ (j :: v) (j :: v)
      ((elvQuotientFunctor D Sc cutoff).map (deformedCyclotomic D Sc (j :: v) N c)) =
      (elvQuotientFunctor D Sc cutoff).map
        (deformedCyclotomic D Sc (j :: (v ++ σ)) N c) := by
  change rightContext D Sc cutoff σ (j :: v) (j :: v)
    (elvQuotientMap D Sc cutoff _ _ (deformedCyclotomic D Sc (j :: v) N c)) =
    elvQuotientMap D Sc cutoff _ _ (deformedCyclotomic D Sc (j :: (v ++ σ)) N c)
  unfold deformedCyclotomic
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [elvQuotientMap_source, elvQuotientMap_source, rightContext_tmul,
    affineRightContext_firstDotPower]

/-- The odd ELV and even cyclotomic relations both retain their coefficients and cutoff. -/
theorem rightContext_relation (σ : List I) (j : I) (v : List I) :
    rightContext D Sc cutoff σ (j :: v) (j :: v) (relation D Sc cutoff j v) =
      relation D Sc cutoff j (v ++ σ) := by
  unfold relation
  split_ifs with hj
  · exact rightContext_deformedCyclotomic D Sc cutoff σ j v (cutoff j)
      (SKM.SYM.elvMonicCoefficient D k ⟨j, hj⟩ (cutoff j))
  · exact rightContext_deformedCyclotomic D Sc cutoff σ j v (cutoff j)
      (SKM.SYM.evenMonicCoefficient D k j (cutoff j))

/-- Adjoining an arbitrary spectator context preserves the two-sided old ideal. -/
theorem ideal_rightContext (σ : List I) {v w : List I} {f : hom D Sc cutoff v w}
    (hf : f ∈ ideal D Sc cutoff v w) :
    rightContext D Sc cutoff σ v w f ∈ ideal D Sc cutoff (v ++ σ) (w ++ σ) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨j, t, a, b, rfl⟩ := hf
    rw [rightContext_comp, rightContext_comp, rightContext_relation]
    exact Submodule.subset_span ⟨j, t ++ σ,
      rightContext D Sc cutoff σ v (j :: t) a,
      rightContext D Sc cutoff σ (j :: t) w b, rfl⟩
  | zero => simpa only [map_zero] using (ideal D Sc cutoff (v ++ σ) (w ++ σ)).zero_mem
  | add f g _ _ hf hg => simpa only [map_add] using Submodule.add_mem _ hf hg
  | smul c f _ hf => simpa only [map_smul] using Submodule.smul_mem _ c hf

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Scalar images of the actual ELV dot polynomials

The polynomial below records the chosen scalar coefficient images. This module
computes the actual signed specialization on every strand. Identifying these
coefficients with the prescribed binomial probe remains a separate calculation.
-/
noncomputable section
open CategoryTheory StringDiagrams
open OddMath.SKM.SYM
open scoped Classical
namespace OddMath.QuiverHecke
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (values : I × ℕ → k)
  (hvalues : ∀ i r, elvElementaryRank D cutoff i ≤ r → values (i,r) = 0)

/-- The ordinary polynomial whose coefficients are the chosen scalar images. -/
def scalarCoefficientPolynomial (N : ℕ) (c : Fin (N+1) → SKM.SYM D k) :
    Polynomial k :=
  ∑ j, Polynomial.C (scalarEvaluation D values (c j)) * Polynomial.X ^ j.val

theorem elvAffineScalarSpecialization_dotPolynomial
    (w : List I) (r N : ℕ) (c : Fin (N+1) → SKM.SYM D k) :
    (elvAffineScalarSpecialization D Sc cutoff values hvalues).map
      (elvQuotientMap D Sc cutoff _ _ (coefficientDotPolynomial D Sc w r N c)) =
        Polynomial.aeval (dotE D Sc w r)
          (scalarCoefficientPolynomial D values N c) := by
  simp only [coefficientDotPolynomial, scalarCoefficientPolynomial, map_sum, Functor.map_sum,
    elvAffineScalarSpecialization_source, map_mul, Polynomial.aeval_C, map_pow,
    Polynomial.aeval_X, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]

/-- The odd first-strand generator maps to its literal ordinary scalar polynomial. -/
theorem elvAffineScalarSpecialization_elvCyclotomic
    (i : {i : I // D.parity i = 1}) (tail : List I) (N : ℕ) :
    (elvAffineScalarSpecialization D Sc cutoff values hvalues).map
      (elvQuotientMap D Sc cutoff _ _ (elvCyclotomic D Sc i tail N)) =
        Polynomial.aeval (dotE D Sc (i.1 :: tail) 0)
          (scalarCoefficientPolynomial D values N (elvMonicCoefficient D k i N)) := by
  rw [← elvDotPolynomial_first]
  exact elvAffineScalarSpecialization_dotPolynomial D Sc cutoff values hvalues
    (i.1 :: tail) 0 N (elvMonicCoefficient D k i N)

/-- The same scalar polynomial formula for the original first-dot presentation. -/
theorem elvAffineScalarSpecialization_deformedCyclotomic
    (w : List I) (N : ℕ) (c : Fin (N+1) → SKM.SYM D k) :
    (elvAffineScalarSpecialization D Sc cutoff values hvalues).map
      (elvQuotientMap D Sc cutoff _ _ (deformedCyclotomic D Sc w N c)) =
        Polynomial.aeval (dotE D Sc w 0)
          (scalarCoefficientPolynomial D values N c) := by
  have hp : deformedCyclotomic D Sc w N c = coefficientDotPolynomial D Sc w 0 N c := by
    unfold deformedCyclotomic coefficientDotPolynomial
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    simp only [dotE_pow, firstDotPower, List.map_replicate]
  rw [hp]
  exact elvAffineScalarSpecialization_dotPolynomial D Sc cutoff values hvalues w 0 N c

/-- The actual even-colour first-strand relation has the corresponding scalar image. -/
theorem elvAffineScalarSpecialization_evenCyclotomic
    (i : I) (tail : List I) (N : ℕ) :
    (elvAffineScalarSpecialization D Sc cutoff values hvalues).map
      (elvQuotientMap D Sc cutoff _ _ (evenCyclotomic D Sc i tail N)) =
        Polynomial.aeval (dotE D Sc (i :: tail) 0)
          (scalarCoefficientPolynomial D values N (evenMonicCoefficient D k i N)) :=
  elvAffineScalarSpecialization_deformedCyclotomic D Sc cutoff values hvalues
    (i :: tail) N (evenMonicCoefficient D k i N)

/-- Appending spectator strands commutes with actual scalar specialization.
This supplies the append-range compatibility before quotient descent. -/
theorem elvAffineScalarSpecialization_rightContext
    (σ v w : List I) (f : ELV.hom D Sc cutoff v w) :
    (elvAffineScalarSpecialization D Sc cutoff values hvalues).map
      (ELV.rightContext D Sc cutoff σ v w f) =
        ELV.affineRightContext D Sc σ v w
          ((elvAffineScalarSpecialization D Sc cutoff values hvalues).map f) := by
  let F : ELV.hom D Sc cutoff v w →ₗ[k]
      ((pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w)) :=
    (elvAffineScalarSpecialization D Sc cutoff values hvalues).toFunctor.mapLinearMap k
  let G : ELV.hom D Sc cutoff (v ++ σ) (w ++ σ) →ₗ[k]
      ((pres D Sc).obj (ob D (v ++ σ)) ⟶ (pres D Sc).obj (ob D (w ++ σ))) :=
    (elvAffineScalarSpecialization D Sc cutoff values hvalues).toFunctor.mapLinearMap k
  change G (ELV.rightContext D Sc cutoff σ v w f) =
    ELV.affineRightContext D Sc σ v w (F f)
  induction f using TensorProduct.inductionOn with
  | add f g hf hg => simp only [map_add, hf, hg]
  | tmul a f =>
    change (elvAffineScalarSpecialization D Sc cutoff values hvalues).map
      (BoxProd.tmulHom
        (X := ELV.obj D Sc cutoff (v ++ σ))
        (Y := ELV.obj D Sc cutoff (w ++ σ))
        (SuperalgebraCat.ofElem a) (ELV.affineRightContext D Sc σ v w f)) =
      ELV.affineRightContext D Sc σ v w
        ((elvAffineScalarSpecialization D Sc cutoff values hvalues).map
          (BoxProd.tmulHom
            (X := ELV.obj D Sc cutoff v) (Y := ELV.obj D Sc cutoff w)
            (SuperalgebraCat.ofElem a) f))
    rw [elvAffineScalarSpecialization_tmul, elvAffineScalarSpecialization_tmul]
    exact (map_smul (ELV.affineRightContext D Sc σ v w) _ _).symm

end OddMath.QuiverHecke
end

end
