import OddMath.QuiverHecke.CyclotomicAction.ELVWeightTripleComparisonCoherence
noncomputable section
open CategoryTheory
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

private theorem braid_prefix_comparison
    {C B : Type*} [Category* C] [Category* B]
    (F : B ⥤ C) {A P : B} {X W : C}
    (d : X ≅ F.obj A) (e : A ≅ P) (w : F.obj P ≅ W)
    (t : X ≅ W) (x : A ⟶ A) (y : X ⟶ X) (c : P ⟶ P) (z : W ⟶ W)
    (hx : x = e.hom ≫ c ≫ e.inv)
    (hy : y = d.hom ≫ F.map x ≫ d.inv)
    (ht : t.hom = d.hom ≫ F.map e.hom ≫ w.hom)
    (hc : F.map c ≫ w.hom = w.hom ≫ z) :
    y ≫ t.hom = t.hom ≫ z := by
  have he : F.map e.inv ≫ F.map e.hom = 𝟙 _ := by
    rw [← F.map_comp, e.inv_hom_id, F.map_id]
  calc
    y ≫ t.hom = d.hom ≫ F.map e.hom ≫ F.map c ≫ w.hom := by
      simp only [hy, ht, hx, Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc]
      rw [← Category.assoc (F.map e.inv), he, Category.id_comp]
    _ = t.hom ≫ z := by rw [hc, ht]; simp only [Category.assoc]
