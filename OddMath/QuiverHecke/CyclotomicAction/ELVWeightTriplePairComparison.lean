import OddMath.QuiverHecke.CyclotomicAction.ELVWeightBraidComponents

/-! # Triple comparison through the selected weight pair chart

Brundan--Ellis (1.9), DeformedActionAssembly §6. The selected triple chart
factors through the already selected first weight-pair chart, without a
new choice of crossing or intermediate module identification.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVOld
universe u
private theorem tripleEvaluation_pairFirst
    {C A B E : Type*} [Category* C] [Category* A] [Category* B] [Category* E]
    (R : C ⥤ A) (P Q : A ⥤ B) (U : B ⥤ E) (V : A ⥤ E)
    (Fp : C ⥤ B) (Ft : C ⥤ E)
    (hp : Fp = R ⋙ P) (ho : Ft = Fp ⋙ U) (ht : Ft = R ⋙ (P ⋙ U))
    (e : P ≅ Q) (f : Q ⋙ U ≅ V) :
    eqToIso ht ≪≫ Functor.isoWhiskerLeft R (Functor.isoWhiskerRight e U ≪≫ f) =
      eqToIso ho ≪≫ Functor.isoWhiskerRight (eqToIso hp ≪≫ Functor.isoWhiskerLeft R e) U ≪≫
        Functor.associator R Q U ≪≫ Functor.isoWhiskerLeft R f := by
  cases hp
  cases ho
  ext M
  simp

private theorem tripleEvaluation_pairFirst_component
    {C A B E : Type*} [Category* C] [Category* A] [Category* B] [Category* E]
    (R : C ⥤ A) (Q : A ⥤ B) (U : B ⥤ E) (V : A ⥤ E)
    (Fp : C ⥤ B) (Ft : C ⥤ E) (ho : Ft = Fp ⋙ U)
    (e : Fp ≅ R ⋙ Q) (f : Q ⋙ U ≅ V) (t : Ft ≅ R ⋙ V)
    (ht : t = eqToIso ho ≪≫ Functor.isoWhiskerRight e U ≪≫
      Functor.associator R Q U ≪≫ Functor.isoWhiskerLeft R f) (M : C) :
    t.hom.app M = (eqToIso ho).hom.app M ≫ U.map (e.hom.app M) ≫ f.hom.app (R.obj M) := by
  rw [ht]
  simp

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i j l : I) (Λ : X) {x₀ x₁ x₂ x₃ : X}
  (h₁ : x₀ + D.α l = x₁) (h₂ : x₁ + D.α j = x₂) (h₃ : x₂ + D.α i = x₃)
  (β : WeightBlocks D Λ x₀)
local notation "β₁" => blockSucc D Λ l h₁ β
local notation "β₂" => blockSucc₂ D j l Λ h₁ h₂ β
local notation "β₃" => elvBlockSucc₃ D i j l Λ h₁ h₂ h₃ β
local notation "E₁" => elvEFunctor D Sc cutoff bound l Λ h₁
local notation "E₂" => elvEFunctor D Sc cutoff bound j Λ h₂
/-- Outer predecessor dispatch factors the triple through its true pair coordinate. -/
theorem elvEFunctor_comp₃_pairFirst :
    (E₁ ⋙ E₂) ⋙ (elvInductionComponent D Sc cutoff bound i Λ h₃ β₃).toFunctor =
      (E₁ ⋙ (elvInductionComponent D Sc cutoff bound j Λ h₂ β₂).toFunctor) ⋙ (elvBlockInd D Sc cutoff bound i Λ h₃ β₂).toFunctor := by
  rw [elvInductionComponent_blockSucc]
  rfl

/-- The given triple chart factors through the given first-pair chart. -/
theorem elvWeightTripleComparison_pairFirst :
    elvWeightTripleComparison D Sc cutoff bound i j l Λ h₁ h₂ h₃ β β₃ rfl =
      eqToIso (elvEFunctor_comp₃_pairFirst D Sc cutoff bound i j l Λ h₁ h₂ h₃ β) ≪≫
        Functor.isoWhiskerRight
          (elvWeightPairComparison D Sc cutoff bound j l Λ h₁ h₂ β β₂ rfl) (elvBlockInd D Sc cutoff bound i Λ h₃ β₂).toFunctor ≪≫
          Functor.associator (elvBlockEval D Sc cutoff bound Λ β).toFunctor (contentInductionTo D Sc cutoff bound β.1 [l,j] β₂.1 (elvBlockPair_content_eq D j l Λ h₁ h₂ β)) (elvBlockInd D Sc cutoff bound i Λ h₃ β₂).toFunctor ≪≫ Functor.isoWhiskerLeft (elvBlockEval D Sc cutoff bound Λ β).toFunctor (contentInductionCompTo D Sc cutoff bound β.1 [l,j] β₂.1 (elvBlockPair_content_eq D j l Λ h₁ h₂ β) [i] β₃.1 (elvBlockSucc_content_eq D i Λ h₃ β₂) (elvBlockTriple_content_eq D i j l Λ h₁ h₂ h₃ β)) := by
  rw [elvWeightTripleComparison_viaFirst]
  exact tripleEvaluation_pairFirst (elvBlockEval D Sc cutoff bound Λ β).toFunctor
    (elvBlockPairInd D Sc cutoff bound j l Λ h₁ h₂ β).toFunctor (contentInductionTo D Sc cutoff bound β.1 [l,j] β₂.1 (elvBlockPair_content_eq D j l Λ h₁ h₂ β)) (elvBlockInd D Sc cutoff bound i Λ h₃ β₂).toFunctor
    (contentInductionTo D Sc cutoff bound β.1 [l,j,i] β₃.1
      (elvBlockTriple_content_eq D i j l Λ h₁ h₂ h₃ β))
    (E₁ ⋙ (elvInductionComponent D Sc cutoff bound j Λ h₂ β₂).toFunctor)
    ((E₁ ⋙ E₂) ⋙ (elvInductionComponent D Sc cutoff bound i Λ h₃ β₃).toFunctor)
    (elvEFunctor_comp₂_blockSucc D Sc cutoff bound j l Λ h₁ h₂ β)
    (elvEFunctor_comp₃_pairFirst D Sc cutoff bound i j l Λ h₁ h₂ h₃ β)
    (elvEFunctor_comp₃_blockSucc D Sc cutoff bound i j l Λ h₁ h₂ h₃ β)
    (elvBlockPairComparison D Sc cutoff bound j l Λ h₁ h₂ β) (contentInductionCompTo D Sc cutoff bound β.1 [l,j] β₂.1 (elvBlockPair_content_eq D j l Λ h₁ h₂ β) [i] β₃.1 (elvBlockSucc_content_eq D i Λ h₃ β₂) (elvBlockTriple_content_eq D i j l Λ h₁ h₂ h₃ β))

/-- Native module component of the factorization through the selected first pair. -/
theorem elvWeightTripleComparison_pairFirst_hom
    (M : ELVWeightProduct D Sc cutoff bound Λ x₀) :
    (elvWeightTripleComparison D Sc cutoff bound i j l Λ h₁ h₂ h₃ β β₃ rfl).hom.app M =
      (eqToIso (elvEFunctor_comp₃_pairFirst D Sc cutoff bound i j l Λ h₁ h₂ h₃ β)).hom.app M ≫
        (elvBlockInd D Sc cutoff bound i Λ h₃ β₂).map
          ((elvWeightPairComparison D Sc cutoff bound j l Λ h₁ h₂ β β₂ rfl).hom.app M) ≫
        (contentInductionCompTo D Sc cutoff bound β.1 [l,j] β₂.1
          (elvBlockPair_content_eq D j l Λ h₁ h₂ β) [i] β₃.1
          (elvBlockSucc_content_eq D i Λ h₃ β₂)
          (elvBlockTriple_content_eq D i j l Λ h₁ h₂ h₃ β)).hom.app (M β) :=
  tripleEvaluation_pairFirst_component
    (elvBlockEval D Sc cutoff bound Λ β).toFunctor
    (contentInductionTo D Sc cutoff bound β.1 [l,j] β₂.1
      (elvBlockPair_content_eq D j l Λ h₁ h₂ β))
    (elvBlockInd D Sc cutoff bound i Λ h₃ β₂).toFunctor
    (contentInductionTo D Sc cutoff bound β.1 [l,j,i] β₃.1
      (elvBlockTriple_content_eq D i j l Λ h₁ h₂ h₃ β))
    (E₁ ⋙ (elvInductionComponent D Sc cutoff bound j Λ h₂ β₂).toFunctor)
    ((E₁ ⋙ E₂) ⋙ (elvInductionComponent D Sc cutoff bound i Λ h₃ β₃).toFunctor)
    (elvEFunctor_comp₃_pairFirst D Sc cutoff bound i j l Λ h₁ h₂ h₃ β)
    (elvWeightPairComparison D Sc cutoff bound j l Λ h₁ h₂ β β₂ rfl)
    (contentInductionCompTo D Sc cutoff bound β.1 [l,j] β₂.1
      (elvBlockPair_content_eq D j l Λ h₁ h₂ β) [i] β₃.1
      (elvBlockSucc_content_eq D i Λ h₃ β₂)
      (elvBlockTriple_content_eq D i j l Λ h₁ h₂ h₃ β))
    (elvWeightTripleComparison D Sc cutoff bound i j l Λ h₁ h₂ h₃ β β₃ rfl)
    (elvWeightTripleComparison_pairFirst D Sc cutoff bound i j l Λ h₁ h₂ h₃ β) M

end OddMath.QuiverHecke.ELVOld
