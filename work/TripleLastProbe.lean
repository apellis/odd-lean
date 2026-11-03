import OddMath.QuiverHecke.CyclotomicAction.ELVWeightTriplePairComparison
noncomputable section
open CategoryTheory
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
