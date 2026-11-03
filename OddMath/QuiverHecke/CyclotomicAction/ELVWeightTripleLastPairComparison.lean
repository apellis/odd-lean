import OddMath.QuiverHecke.CyclotomicAction.ELVWeightTriplePairComparison

/-! # Triple comparison through the selected last weight pair

Brundan--Ellis (1.9), DeformedActionAssembly §6. The same selected triple
chart factors through the selected last pair and the literal first-value
comparison, without changing either prescribed crossing.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVOld
universe u
private theorem tripleEvaluation_pairLast
    {C₀ C₁ A A₁ A₂ B : Type*}
    [Category* C₀] [Category* C₁] [Category* A] [Category* A₁] [Category* A₂] [Category* B]
    (F₀ : C₀ ⥤ C₁) (R₁ : C₁ ⥤ A₁) (R : C₀ ⥤ A) (J : A ⥤ A₁)
    (K : A₁ ⥤ A₂) (U : A₂ ⥤ B) (Q : A₁ ⥤ B) (V : A ⥤ B) (Fp : C₁ ⥤ B)
    (h₁ : F₀ ⋙ R₁ = R ⋙ J) (hp : Fp = R₁ ⋙ (K ⋙ U)) (ht : F₀ ⋙ Fp = R ⋙ ((J ⋙ K) ⋙ U))
    (e : K ⋙ U ≅ Q) (f : J ⋙ Q ≅ V) :
    eqToIso ht ≪≫ Functor.isoWhiskerLeft R (Functor.associator J K U ≪≫ Functor.isoWhiskerLeft J e ≪≫ f) =
      Functor.isoWhiskerLeft F₀ (eqToIso hp ≪≫ Functor.isoWhiskerLeft R₁ e) ≪≫
        (Functor.associator F₀ R₁ Q).symm ≪≫ Functor.isoWhiskerRight (eqToIso h₁) Q ≪≫
          Functor.associator R J Q ≪≫ Functor.isoWhiskerLeft R f := by
  ext M
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Iso.symm_hom, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, eqToIso.hom, eqToHom_app, Category.assoc]
  have hobj : R₁.obj (F₀.obj M) = J.obj (R.obj M) := Functor.congr_obj h₁ M
  have hn := e.hom.naturality_assoc (eqToHom hobj) (f.hom.app (R.obj M))
  rw [← hn]
  simp only [eqToHom_map, eqToHom_trans_assoc]

private theorem tripleEvaluation_pairLast_component
    {C₀ C₁ A A₁ B : Type*}
    [Category* C₀] [Category* C₁] [Category* A] [Category* A₁] [Category* B]
    (F₀ : C₀ ⥤ C₁) (R₁ : C₁ ⥤ A₁) (R : C₀ ⥤ A) (J : A ⥤ A₁)
    (Q : A₁ ⥤ B) (V : A ⥤ B) (Fp : C₁ ⥤ B)
    (h₁ : F₀ ⋙ R₁ = R ⋙ J) (e : Fp ≅ R₁ ⋙ Q) (f : J ⋙ Q ≅ V)
    (t : F₀ ⋙ Fp ≅ R ⋙ V)
    (ht : t = Functor.isoWhiskerLeft F₀ e ≪≫
      (Functor.associator F₀ R₁ Q).symm ≪≫ Functor.isoWhiskerRight (eqToIso h₁) Q ≪≫
        Functor.associator R J Q ≪≫ Functor.isoWhiskerLeft R f) (M : C₀) :
    t.hom.app M = e.hom.app (F₀.obj M) ≫
      Q.map ((eqToIso h₁).hom.app M) ≫ f.hom.app (R.obj M) := by
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
local notation "R₁" => Superfunctor.toFunctor (elvBlockEval D Sc cutoff bound Λ β₁)
local notation "R" => Superfunctor.toFunctor (elvBlockEval D Sc cutoff bound Λ β)
local notation "J" => Superfunctor.toFunctor (elvBlockInd D Sc cutoff bound l Λ h₁ β)
local notation "K" => Superfunctor.toFunctor (elvBlockInd D Sc cutoff bound j Λ h₂ β₁)
local notation "U" => Superfunctor.toFunctor (elvBlockInd D Sc cutoff bound i Λ h₃ β₂)
local notation "Fₚ" => E₂ ⋙ Superfunctor.toFunctor (elvInductionComponent D Sc cutoff bound i Λ h₃ β₃)
local notation "hQ" => elvBlockPair_content_eq D i j Λ h₂ h₃ β₁
local notation "hT" => elvBlockTriple_content_eq D i j l Λ h₁ h₂ h₃ β
local notation "hc₁" => elvBlockSucc_content_eq D l Λ h₁ β
local notation "Q" => contentInductionTo D Sc cutoff bound (Subtype.val β₁) [j,i] (Subtype.val β₃) hQ
local notation "V" => contentInductionTo D Sc cutoff bound (Subtype.val β) [l,j,i] (Subtype.val β₃) hT
local notation "f" => contentInductionCompTo D Sc cutoff bound (Subtype.val β) [l] (Subtype.val β₁) hc₁
  [j,i] (Subtype.val β₃) hQ hT

/-- The first induced value at its true successor, as a whole functor. -/
theorem elvEFunctor_blockSucc_eval : E₁ ⋙ R₁ = R ⋙ J := by
  change (elvInductionComponent D Sc cutoff bound l Λ h₁ β₁).toFunctor = _
  rw [elvInductionComponent_blockSucc]
  rfl

/-- The identical triple chart factors through the selected last weight-pair chart. -/
theorem elvWeightTripleComparison_pairLast :
    elvWeightTripleComparison D Sc cutoff bound i j l Λ h₁ h₂ h₃ β β₃ rfl =
      Functor.isoWhiskerLeft E₁
        (elvWeightPairComparison D Sc cutoff bound i j Λ h₂ h₃ β₁ β₃ rfl) ≪≫
        (Functor.associator E₁ R₁ Q).symm ≪≫
          Functor.isoWhiskerRight (eqToIso (elvEFunctor_blockSucc_eval D Sc cutoff bound l Λ h₁ β)) Q ≪≫
            Functor.associator R J Q ≪≫ Functor.isoWhiskerLeft R f := by
  rw [elvWeightTripleComparison_viaLast]
  exact tripleEvaluation_pairLast E₁ R₁ R J K U Q V Fₚ
    (elvEFunctor_blockSucc_eval D Sc cutoff bound l Λ h₁ β)
    (elvEFunctor_comp₂_blockSucc D Sc cutoff bound i j Λ h₂ h₃ β₁)
    (elvEFunctor_comp₃_blockSucc D Sc cutoff bound i j l Λ h₁ h₂ h₃ β)
    (elvBlockPairComparison D Sc cutoff bound i j Λ h₂ h₃ β₁) f

/-- Component formula keeps the selected first-value cast under pair-word induction. -/
theorem elvWeightTripleComparison_pairLast_hom
    (M : ELVWeightProduct D Sc cutoff bound Λ x₀) :
    (elvWeightTripleComparison D Sc cutoff bound i j l Λ h₁ h₂ h₃ β β₃ rfl).hom.app M =
      (elvWeightPairComparison D Sc cutoff bound i j Λ h₂ h₃ β₁ β₃ rfl).hom.app ((E₁).obj M) ≫
        (Q).map ((eqToIso (elvEFunctor_blockSucc_eval D Sc cutoff bound l Λ h₁ β)).hom.app M) ≫
          (f).hom.app (M β) :=
  tripleEvaluation_pairLast_component E₁ R₁ R J Q V Fₚ
    (elvEFunctor_blockSucc_eval D Sc cutoff bound l Λ h₁ β)
    (elvWeightPairComparison D Sc cutoff bound i j Λ h₂ h₃ β₁ β₃ rfl) f
    (elvWeightTripleComparison D Sc cutoff bound i j l Λ h₁ h₂ h₃ β β₃ rfl)
    (elvWeightTripleComparison_pairLast D Sc cutoff bound i j l Λ h₁ h₂ h₃ β) M

end OddMath.QuiverHecke.ELVOld
