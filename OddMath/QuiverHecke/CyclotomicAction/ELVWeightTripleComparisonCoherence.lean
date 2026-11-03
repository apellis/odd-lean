import OddMath.QuiverHecke.CyclotomicAction.ELVWeightTripleInduction
import OddMath.QuiverHecke.CyclotomicAction.ELVContentTensorCoherence
import OddMath.QuiverHecke.CyclotomicAction.ELVContentComparisonCoherence

/-! # Coherence of triple comparisons through the true content intermediates

Brundan--Ellis (1.9), DeformedActionAssembly §6. Both orders of flattening
three selected inductions agree. Their actual intermediate contents remain
explicit, as required when transporting the two given weight crossings.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVOld
universe u
private theorem tripleEvaluation_reencode
    {C B E : Type*} [Category* C] [Category* B] [Category* E]
    (R : C ⥤ B) {F : C ⥤ E} {G H K : B ⥤ E}
    (h₁ : F = R ⋙ G) (h₂ : G = H) (h₃ : F = R ⋙ H) (e : H ≅ K) :
    eqToIso h₃ ≪≫ Functor.isoWhiskerLeft R e =
      eqToIso h₁ ≪≫ Functor.isoWhiskerLeft R (eqToIso h₂ ≪≫ e) := by
  cases h₂
  simp only [eqToIso_refl, Iso.refl_trans]

private theorem tripleEvaluation_component
    {C B E : Type*} [Category* C] [Category* B] [Category* E]
    (R : C ⥤ B) {F : C ⥤ E} {G H : B ⥤ E}
    (h : F = R ⋙ G) (e : G ≅ H) (s : F ≅ R ⋙ H)
    (hs : s = eqToIso h ≪≫ Functor.isoWhiskerLeft R e) (M : C) :
    s.hom.app M = (eqToIso h).hom.app M ≫ e.hom.app (R.obj M) := by
  cases hs
  rfl

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)

section Content
variable (β : Multiset I) (a b c : I) (δ₁ δ₂ γ : Multiset I)
  (h₁ : β + ([a] : Multiset I) = δ₁)
  (h₂ : δ₁ + ([b] : Multiset I) = δ₂)
  (h₃ : δ₂ + ([c] : Multiset I) = γ)
  (hp : β + ([a,b] : Multiset I) = δ₂)
  (hq : δ₁ + ([b,c] : Multiset I) = γ)
  (h : β + ([a,b,c] : Multiset I) = γ)
local notation "E₁" => contentInductionTo D Sc cutoff bound β [a] δ₁ h₁
local notation "E₂" => contentInductionTo D Sc cutoff bound δ₁ [b] δ₂ h₂
local notation "E₃" => contentInductionTo D Sc cutoff bound δ₂ [c] γ h₃

/-- Flatten the first pair, then append the last letter, using true contents. -/
def contentTripleComparisonViaFirst :
    (E₁ ⋙ E₂) ⋙ E₃ ≅ contentInductionTo D Sc cutoff bound β [a,b,c] γ h :=
  Functor.isoWhiskerRight
    (contentInductionCompTo D Sc cutoff bound β [a] δ₁ h₁ [b] δ₂ h₂ hp) E₃ ≪≫
      contentInductionCompTo D Sc cutoff bound β [a,b] δ₂ hp [c] γ h₃ h

/-- Flatten the last pair, then append that pair, with the same source grouping. -/
def contentTripleComparisonViaLast :
    (E₁ ⋙ E₂) ⋙ E₃ ≅ contentInductionTo D Sc cutoff bound β [a,b,c] γ h :=
  Functor.associator E₁ E₂ E₃ ≪≫
    Functor.isoWhiskerLeft E₁
      (contentInductionCompTo D Sc cutoff bound δ₁ [b] δ₂ h₂ [c] γ h₃ hq) ≪≫
        contentInductionCompTo D Sc cutoff bound β [a] δ₁ h₁ [b,c] γ hq h

/-- The two selected comparison paths agree, before evaluating any module. -/
theorem contentTripleComparisonVia_assoc :
    contentTripleComparisonViaFirst D Sc cutoff bound β a b c δ₁ δ₂ γ h₁ h₂ h₃ hp h =
      contentTripleComparisonViaLast D Sc cutoff bound β a b c δ₁ δ₂ γ h₁ h₂ h₃ hq h := by
  simp only [contentTripleComparisonViaFirst, contentTripleComparisonViaLast,
    contentInductionCompTo_eq]
  exact inductionCompOfEq_assoc _ _ _ _ _ _ _ _ _ _

/-- Component coherence keeps the native induction-module endpoints. -/
theorem contentTripleComparisonVia_assoc_hom
    (M : ContentModules D Sc cutoff bound β) :
    (contentTripleComparisonViaFirst D Sc cutoff bound β a b c δ₁ δ₂ γ h₁ h₂ h₃ hp h).hom.app M =
      (contentTripleComparisonViaLast D Sc cutoff bound β a b c δ₁ δ₂ γ h₁ h₂ h₃ hq h).hom.app M := by
  rw [contentTripleComparisonVia_assoc D Sc cutoff bound β a b c δ₁ δ₂ γ h₁ h₂ h₃ hp hq h]

/-- First-pair flattening retains exactly the canonical triple comparison. -/
theorem contentTripleComparisonViaFirst_eq :
    contentTripleComparisonViaFirst D Sc cutoff bound β a b c δ₁ δ₂ γ h₁ h₂ h₃ hp h =
      eqToIso (contentTripleInductionTo_eq D Sc cutoff bound β a b c δ₁ δ₂ γ h₁ h₂ h₃ h) ≪≫
        contentETripleComparison D Sc cutoff bound β a b c γ h := by
  cases h₁
  cases h₂
  change _ = (Iso.refl (contentETripleTo D Sc cutoff bound β a b c γ h)) ≪≫
    contentETripleComparison D Sc cutoff bound β a b c γ h
  rw [Iso.refl_trans]
  rfl

/-- Last-pair flattening therefore has the identical canonical comparison. -/
theorem contentTripleComparisonViaLast_eq :
    contentTripleComparisonViaLast D Sc cutoff bound β a b c δ₁ δ₂ γ h₁ h₂ h₃ hq h =
      eqToIso (contentTripleInductionTo_eq D Sc cutoff bound β a b c δ₁ δ₂ γ h₁ h₂ h₃ h) ≪≫
        contentETripleComparison D Sc cutoff bound β a b c γ h := by
  have hp' : β + ([a,b] : Multiset I) = δ₂ := by
    rw [← h₂, ← h₁, add_assoc]
    rfl
  exact (contentTripleComparisonVia_assoc D Sc cutoff bound β a b c δ₁ δ₂ γ h₁ h₂ h₃ hp' hq h).symm.trans
    (contentTripleComparisonViaFirst_eq D Sc cutoff bound β a b c δ₁ δ₂ γ h₁ h₂ h₃ hp' h)
end Content

section Weight
variable (i j l : I) (Λ : X) {x₀ x₁ x₂ x₃ : X}
  (h₁ : x₀ + D.α l = x₁) (h₂ : x₁ + D.α j = x₂) (h₃ : x₂ + D.α i = x₃)
  (β : WeightBlocks D Λ x₀)
local notation "β₁" => blockSucc D Λ l h₁ β
local notation "β₂" => blockSucc₂ D j l Λ h₁ h₂ β
local notation "β₃" => elvBlockSucc₃ D i j l Λ h₁ h₂ h₃ β
local notation "hc₁" => elvBlockSucc_content_eq D l Λ h₁ β
local notation "hc₂" => elvBlockSucc_content_eq D j Λ h₂ β₁
local notation "hc₃" => elvBlockSucc_content_eq D i Λ h₃ β₂
local notation "hP" => elvBlockPair_content_eq D j l Λ h₁ h₂ β
local notation "hQ" => elvBlockPair_content_eq D i j Λ h₂ h₃ β₁
local notation "hT" => elvBlockTriple_content_eq D i j l Λ h₁ h₂ h₃ β

/-- The chosen weight triple chart equals flattening its actual first block pair. -/
theorem elvWeightTripleComparison_viaFirst :
    elvWeightTripleComparison D Sc cutoff bound i j l Λ h₁ h₂ h₃ β β₃ rfl =
      eqToIso (elvEFunctor_comp₃_blockSucc D Sc cutoff bound i j l Λ h₁ h₂ h₃ β) ≪≫
        Functor.isoWhiskerLeft (elvBlockEval D Sc cutoff bound Λ β).toFunctor
          (contentTripleComparisonViaFirst D Sc cutoff bound β.1 l j i
            β₁.1 β₂.1 β₃.1 hc₁ hc₂ hc₃ hP hT) := by
  rw [contentTripleComparisonViaFirst_eq]
  exact tripleEvaluation_reencode (elvBlockEval D Sc cutoff bound Λ β).toFunctor
    (elvEFunctor_comp₃_blockSucc D Sc cutoff bound i j l Λ h₁ h₂ h₃ β)
    (elvBlockTripleInd_content_eq D Sc cutoff bound i j l Λ h₁ h₂ h₃ β)
    (elvEFunctor_comp₃_contentTriple_eq D Sc cutoff bound i j l Λ h₁ h₂ h₃ β β₃ rfl)
    (contentETripleComparison D Sc cutoff bound β.1 l j i β₃.1 hT)

/-- The identical weight triple chart also equals flattening its actual last pair. -/
theorem elvWeightTripleComparison_viaLast :
    elvWeightTripleComparison D Sc cutoff bound i j l Λ h₁ h₂ h₃ β β₃ rfl =
      eqToIso (elvEFunctor_comp₃_blockSucc D Sc cutoff bound i j l Λ h₁ h₂ h₃ β) ≪≫
        Functor.isoWhiskerLeft (elvBlockEval D Sc cutoff bound Λ β).toFunctor
          (contentTripleComparisonViaLast D Sc cutoff bound β.1 l j i
            β₁.1 β₂.1 β₃.1 hc₁ hc₂ hc₃ hQ hT) := by
  rw [contentTripleComparisonViaLast_eq]
  exact tripleEvaluation_reencode (elvBlockEval D Sc cutoff bound Λ β).toFunctor
    (elvEFunctor_comp₃_blockSucc D Sc cutoff bound i j l Λ h₁ h₂ h₃ β)
    (elvBlockTripleInd_content_eq D Sc cutoff bound i j l Λ h₁ h₂ h₃ β)
    (elvEFunctor_comp₃_contentTriple_eq D Sc cutoff bound i j l Λ h₁ h₂ h₃ β β₃ rfl)
    (contentETripleComparison D Sc cutoff bound β.1 l j i β₃.1 hT)
/-- The actual first-pair component formula keeps native module endpoints. -/
theorem elvWeightTripleComparison_viaFirst_hom
    (M : ELVWeightProduct D Sc cutoff bound Λ x₀) :
    (elvWeightTripleComparison D Sc cutoff bound i j l Λ h₁ h₂ h₃ β β₃ rfl).hom.app M =
      (eqToIso (elvEFunctor_comp₃_blockSucc D Sc cutoff bound i j l Λ h₁ h₂ h₃ β)).hom.app M ≫
        (contentTripleComparisonViaFirst D Sc cutoff bound β.1 l j i
          β₁.1 β₂.1 β₃.1 hc₁ hc₂ hc₃ hP hT).hom.app (M β) :=
  tripleEvaluation_component (elvBlockEval D Sc cutoff bound Λ β).toFunctor
    (elvEFunctor_comp₃_blockSucc D Sc cutoff bound i j l Λ h₁ h₂ h₃ β)
    (contentTripleComparisonViaFirst D Sc cutoff bound β.1 l j i
      β₁.1 β₂.1 β₃.1 hc₁ hc₂ hc₃ hP hT)
    (elvWeightTripleComparison D Sc cutoff bound i j l Λ h₁ h₂ h₃ β β₃ rfl)
    (elvWeightTripleComparison_viaFirst D Sc cutoff bound i j l Λ h₁ h₂ h₃ β) M

/-- Last-pair flattening evaluates to that identical chosen component. -/
theorem elvWeightTripleComparison_viaLast_hom
    (M : ELVWeightProduct D Sc cutoff bound Λ x₀) :
    (elvWeightTripleComparison D Sc cutoff bound i j l Λ h₁ h₂ h₃ β β₃ rfl).hom.app M =
      (eqToIso (elvEFunctor_comp₃_blockSucc D Sc cutoff bound i j l Λ h₁ h₂ h₃ β)).hom.app M ≫
        (contentTripleComparisonViaLast D Sc cutoff bound β.1 l j i
          β₁.1 β₂.1 β₃.1 hc₁ hc₂ hc₃ hQ hT).hom.app (M β) :=
  tripleEvaluation_component (elvBlockEval D Sc cutoff bound Λ β).toFunctor
    (elvEFunctor_comp₃_blockSucc D Sc cutoff bound i j l Λ h₁ h₂ h₃ β)
    (contentTripleComparisonViaLast D Sc cutoff bound β.1 l j i
      β₁.1 β₂.1 β₃.1 hc₁ hc₂ hc₃ hQ hT)
    (elvWeightTripleComparison D Sc cutoff bound i j l Λ h₁ h₂ h₃ β β₃ rfl)
    (elvWeightTripleComparison_viaLast D Sc cutoff bound i j l Λ h₁ h₂ h₃ β) M
end Weight

end OddMath.QuiverHecke.ELVOld
