import OddMath.QuiverHecke.CyclotomicAction.ELVVacuumWordPairing
import OddMath.QuiverHecke.CyclotomicAction.ELVContentTripleCrossingNormalization
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.VacuumWordBraid
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

theorem evaluate_induction (β : Multiset I) (σ : List I)
    (v w : ContentCategory D Sc cutoff N β)
    (f : contentRepresentable D Sc cutoff N β v ⟶ contentRepresentable D Sc cutoff N β w) :
    ContentYoneda.evaluate D Sc cutoff N (β + (σ : Multiset I))
      ((InductionRepresentable.iso D Sc cutoff N β σ v).inv ≫
        (contentInduction D Sc cutoff N β σ).map f ≫
        (InductionRepresentable.iso D Sc cutoff N β σ w).hom) =
      (contentAppend D Sc cutoff N β σ).map (ContentYoneda.evaluate D Sc cutoff N β f) := by
  change ((InductionRepresentable.iso D Sc cutoff N β σ v).inv ≫
    (contentInduction D Sc cutoff N β σ).map f ≫
    (InductionRepresentable.iso D Sc cutoff N β σ w).hom).total _ (𝟙 _) = _
  have hf (z : ContentCategory D Sc cutoff N (β + (σ : Multiset I)))
      (x : BalancedInduction.Obj (contentAppend D Sc cutoff N β σ)
        (contentRepresentableFunctor D Sc cutoff N β w) z) :
      (InductionRepresentable.iso D Sc cutoff N β σ w).hom.total z x =
        InductionRepresentable.forward D Sc cutoff N β σ w z x := by
    change InductionRepresentable.forward D Sc cutoff N β σ w z x + 0 = _
    exact add_zero _
  have hb (z : ContentCategory D Sc cutoff N (β + (σ : Multiset I)))
      (x : (contentAppend D Sc cutoff N β σ).obj v ⟶ z) :
      (InductionRepresentable.iso D Sc cutoff N β σ v).inv.total z x =
        InductionRepresentable.backward D Sc cutoff N β σ v z x := by
    change InductionRepresentable.backward D Sc cutoff N β σ v z x + 0 = _
    exact add_zero _
  rw [Superfunctor.comp_total, Superfunctor.comp_total]
  change (InductionRepresentable.iso D Sc cutoff N β σ w).hom.total _
    (((contentInduction D Sc cutoff N β σ).map f).total _
      ((InductionRepresentable.iso D Sc cutoff N β σ v).inv.total _ (𝟙 _))) = _
  refine (hf _ _).trans ?_
  refine (congrArg (fun x => InductionRepresentable.forward D Sc cutoff N β σ w _
    (((contentInduction D Sc cutoff N β σ).map f).total _ x)) (hb _ (𝟙 _))).trans ?_
  change InductionRepresentable.forward D Sc cutoff N β σ w _
    (BalancedInduction.mapComponent (contentAppend D Sc cutoff N β σ) f 0
      ((contentAppend D Sc cutoff N β σ).obj v)
      (InductionRepresentable.backward D Sc cutoff N β σ v _ (𝟙 _)) +
    BalancedInduction.mapComponent (contentAppend D Sc cutoff N β σ) f 1
      ((contentAppend D Sc cutoff N β σ).obj v)
      (InductionRepresentable.backward D Sc cutoff N β σ v _ (𝟙 _))) = _
  have hc (p : ZMod 2) :
      InductionRepresentable.forward D Sc cutoff N β σ w _
        (BalancedInduction.mapComponent (contentAppend D Sc cutoff N β σ) f p
          ((contentAppend D Sc cutoff N β σ).obj v)
          (InductionRepresentable.backward D Sc cutoff N β σ v _ (𝟙 _))) =
      (contentAppend D Sc cutoff N β σ).map (f.app p v (𝟙 v)) := by
    calc
      _ = InductionRepresentable.forward D Sc cutoff N β σ w _
          (BalancedInduction.tensor (contentAppend D Sc cutoff N β σ)
            (contentRepresentableFunctor D Sc cutoff N β w) v
            (twist k p (𝟙 ((contentAppend D Sc cutoff N β σ).obj v)))
            (f.app p v (𝟙 v))) :=
        congrArg (InductionRepresentable.forward D Sc cutoff N β σ w _)
          (BalancedInduction.mapComponent_tensor (contentAppend D Sc cutoff N β σ) f p
            ((contentAppend D Sc cutoff N β σ).obj v) v (𝟙 _) (𝟙 v))
      _ = (contentAppend D Sc cutoff N β σ).map (f.app p v (𝟙 v)) ≫
          twist k p (𝟙 ((contentAppend D Sc cutoff N β σ).obj v)) :=
        InductionRepresentable.forward_tensor D Sc cutoff N β σ w _ v _ _
      _ = _ := by rw [twist_id, Category.comp_id]
  exact (map_add (InductionRepresentable.forward D Sc cutoff N β σ w _) _ _).trans
    ((congrArg₂ (· + ·) (hc 0) (hc 1)).trans
      (Functor.map_add (contentAppend D Sc cutoff N β σ)).symm)

theorem homEquiv_induction (β : Multiset I) (σ : List I)
    {M P : ContentModules D Sc cutoff N β} {v w : ContentCategory D Sc cutoff N β}
    (a : M ≅ contentRepresentable D Sc cutoff N β v)
    (b : P ≅ contentRepresentable D Sc cutoff N β w) (f : M ⟶ P) :
    ContentYoneda.homEquivOfIso D Sc cutoff N (β + (σ : Multiset I))
      ((contentInduction D Sc cutoff N β σ).mapIso a ≪≫
        InductionRepresentable.iso D Sc cutoff N β σ v)
      ((contentInduction D Sc cutoff N β σ).mapIso b ≪≫
        InductionRepresentable.iso D Sc cutoff N β σ w)
      ((contentInduction D Sc cutoff N β σ).map f) =
    (contentAppend D Sc cutoff N β σ).map
      (ContentYoneda.homEquivOfIso D Sc cutoff N β a b f) := by
  change ContentYoneda.evaluate D Sc cutoff N _
    (((contentInduction D Sc cutoff N β σ).mapIso a ≪≫
        InductionRepresentable.iso D Sc cutoff N β σ v).inv ≫
      (contentInduction D Sc cutoff N β σ).map f ≫
      ((contentInduction D Sc cutoff N β σ).mapIso b ≪≫
        InductionRepresentable.iso D Sc cutoff N β σ w).hom) = _
  simp only [Iso.trans_inv, Iso.trans_hom, Functor.mapIso_inv, Functor.mapIso_hom,
    Category.assoc, ← Functor.map_comp_assoc]
  exact evaluate_induction D Sc cutoff N β σ v w (a.inv ≫ f ≫ b.hom)


theorem wordHomEquiv_id (ρ : List I) (β : Multiset I)
    (hρ : VacuumRepresentable.content ρ = β) :
    VacuumRepresentable.wordHomEquiv D Sc cutoff N ρ ρ β hρ hρ (𝟙 _) = 𝟙 _ := by
  change ContentYoneda.evaluate D Sc cutoff N β
    ((VacuumRepresentable.wordIsoAt D Sc cutoff N ρ β hρ).inv ≫ 𝟙 _ ≫
      (VacuumRepresentable.wordIsoAt D Sc cutoff N ρ β hρ).hom) = _
  rw [Category.id_comp, Iso.inv_hom_id]
  change (𝟙 _ : VacuumRepresentable.wordObjectAt D Sc cutoff N ρ β hρ ⟶ _) + 0 = _
  exact add_zero _

def inducedWordIso (ρ : List I) (β : Multiset I)
    (hρ : VacuumRepresentable.content ρ = β) (l : I) :=
  (contentInduction D Sc cutoff N β [l]).mapIso
    (VacuumRepresentable.wordIsoAt D Sc cutoff N ρ β hρ) ≪≫
  InductionRepresentable.iso D Sc cutoff N β [l]
    (VacuumRepresentable.wordObjectAt D Sc cutoff N ρ β hρ)

theorem inner_cross_coordinates (ρ : List I) (β : Multiset I)
    (hρ : VacuumRepresentable.content ρ = β) (i j l : I) (δ : Multiset I)
    (hij : β + ([i,j] : Multiset I) = δ) (hji : β + ([j,i] : Multiset I) = δ)
    (heij : VacuumRepresentable.content (j :: i :: ρ) = δ)
    (heji : VacuumRepresentable.content (i :: j :: ρ) = δ) :
    ContentYoneda.homEquivOfIso D Sc cutoff N (δ + ([l] : Multiset I))
      (inducedWordIso D Sc cutoff N (i :: j :: ρ) δ heji l)
      (inducedWordIso D Sc cutoff N (j :: i :: ρ) δ heij l)
      ((contentInduction D Sc cutoff N δ [l]).map
        (VacuumWordPairing.wordCross D Sc cutoff N ρ β hρ i j δ hij hji heij heji)) =
    (contentAppend D Sc cutoff N δ [l]).map
      (VacuumWordPairing.wordCrossArrow D Sc cutoff N ρ β hρ i j δ hij hji heij heji) := by
  rw [inducedWordIso, inducedWordIso, homEquiv_induction]
  change (contentAppend D Sc cutoff N δ [l]).map
    (VacuumRepresentable.wordHomEquiv D Sc cutoff N (i :: j :: ρ) (j :: i :: ρ)
      δ heji heij (VacuumWordPairing.wordCross D Sc cutoff N ρ β hρ i j δ hij hji heij heji)) = _
  have hc := VacuumWordPairing.wordHomEquiv_cross D Sc cutoff N ρ (j :: i :: ρ)
    β hρ i j δ hij hji heij heji heij (𝟙 _)
  rw [Category.comp_id, wordHomEquiv_id, twist_id, Category.id_comp] at hc
  exact congrArg ((contentAppend D Sc cutoff N δ [l]).map) hc


def consModuleIso (ρ : List I) (β : Multiset I)
    (hρ : VacuumRepresentable.content ρ = β) (l : I) :
    (contentInduction D Sc cutoff N β [l]).obj
      (VacuumRepresentable.wordModuleAt D Sc cutoff N ρ β hρ) ≅
    VacuumRepresentable.wordModuleAt D Sc cutoff N (l :: ρ) (β + ([l] : Multiset I))
      (congrArg (· + ([l] : Multiset I)) hρ) :=
  eqToIso (by cases hρ; rfl)

theorem consObjectEq (ρ : List I) (β : Multiset I)
    (hρ : VacuumRepresentable.content ρ = β) (l : I) :
    (contentAppend D Sc cutoff N β [l]).obj
      (VacuumRepresentable.wordObjectAt D Sc cutoff N ρ β hρ) =
    VacuumRepresentable.wordObjectAt D Sc cutoff N (l :: ρ) (β + ([l] : Multiset I))
      (congrArg (· + ([l] : Multiset I)) hρ) := by cases hρ; rfl

theorem consIso_hom (ρ : List I) (β : Multiset I)
    (hρ : VacuumRepresentable.content ρ = β) (l : I) :
    (consModuleIso D Sc cutoff N ρ β hρ l).hom ≫
      (VacuumRepresentable.wordIsoAt D Sc cutoff N (l :: ρ) (β + ([l] : Multiset I))
        (congrArg (· + ([l] : Multiset I)) hρ)).hom =
    (inducedWordIso D Sc cutoff N ρ β hρ l).hom ≫
      eqToHom (congrArg (contentRepresentable D Sc cutoff N (β + ([l] : Multiset I)))
        (consObjectEq D Sc cutoff N ρ β hρ l)) := by
  cases hρ
  change 𝟙 _ ≫ (VacuumRepresentable.wordIso D Sc cutoff N (l :: ρ)).hom =
    (VacuumRepresentable.wordIso D Sc cutoff N (l :: ρ)).hom ≫ 𝟙 _
  exact (Category.id_comp _).trans (Category.comp_id _).symm


theorem evaluate_transport {β : Multiset I} {v w v' w' : ContentCategory D Sc cutoff N β}
    (hv : v = v') (hw : w = w')
    (f : contentRepresentable D Sc cutoff N β v ⟶ contentRepresentable D Sc cutoff N β w) :
    ContentYoneda.evaluate D Sc cutoff N β
      (eqToHom (congrArg (contentRepresentable D Sc cutoff N β) hv.symm) ≫ f ≫
        eqToHom (congrArg (contentRepresentable D Sc cutoff N β) hw)) =
    eqToHom hw.symm ≫ ContentYoneda.evaluate D Sc cutoff N β f ≫ eqToHom hv := by
  cases hv
  cases hw
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

theorem consIso_inv (ρ : List I) (β : Multiset I)
    (hρ : VacuumRepresentable.content ρ = β) (l : I) :
    (VacuumRepresentable.wordIsoAt D Sc cutoff N (l :: ρ) (β + ([l] : Multiset I))
        (congrArg (· + ([l] : Multiset I)) hρ)).inv ≫
      (consModuleIso D Sc cutoff N ρ β hρ l).inv =
    eqToHom (congrArg (contentRepresentable D Sc cutoff N (β + ([l] : Multiset I)))
        (consObjectEq D Sc cutoff N ρ β hρ l).symm) ≫
      (inducedWordIso D Sc cutoff N ρ β hρ l).inv := by
  cases hρ
  change (VacuumRepresentable.wordIso D Sc cutoff N (l :: ρ)).inv ≫ 𝟙 _ =
    𝟙 _ ≫ (VacuumRepresentable.wordIso D Sc cutoff N (l :: ρ)).inv
  exact (Category.comp_id _).trans (Category.id_comp _).symm

theorem wordHomEquiv_cons (ρ τ : List I) (β : Multiset I)
    (hρ : VacuumRepresentable.content ρ = β) (hτ : VacuumRepresentable.content τ = β)
    (l : I)
    (f : VacuumRepresentable.wordModuleAt D Sc cutoff N ρ β hρ ⟶
      VacuumRepresentable.wordModuleAt D Sc cutoff N τ β hτ) :
    VacuumRepresentable.wordHomEquiv D Sc cutoff N (l :: ρ) (l :: τ)
      (β + ([l] : Multiset I)) (congrArg (· + ([l] : Multiset I)) hρ)
      (congrArg (· + ([l] : Multiset I)) hτ)
      ((consModuleIso D Sc cutoff N ρ β hρ l).inv ≫
        (contentInduction D Sc cutoff N β [l]).map f ≫
        (consModuleIso D Sc cutoff N τ β hτ l).hom) =
    eqToHom (consObjectEq D Sc cutoff N τ β hτ l).symm ≫
      (contentAppend D Sc cutoff N β [l]).map
        (VacuumRepresentable.wordHomEquiv D Sc cutoff N ρ τ β hρ hτ f) ≫
      eqToHom (consObjectEq D Sc cutoff N ρ β hρ l) := by
  change ContentYoneda.evaluate D Sc cutoff N _
    ((VacuumRepresentable.wordIsoAt D Sc cutoff N (l :: ρ) _ _).inv ≫
      ((consModuleIso D Sc cutoff N ρ β hρ l).inv ≫
        (contentInduction D Sc cutoff N β [l]).map f ≫
        (consModuleIso D Sc cutoff N τ β hτ l).hom) ≫
      (VacuumRepresentable.wordIsoAt D Sc cutoff N (l :: τ) _ _).hom) = _
  simp only [Category.assoc]
  rw [consIso_hom, ← Category.assoc, consIso_inv]
  simp only [Category.assoc]
  rw [← Category.assoc (inducedWordIso D Sc cutoff N ρ β hρ l).inv,
    ← Category.assoc ((inducedWordIso D Sc cutoff N ρ β hρ l).inv ≫ _)]
  rw [evaluate_transport D Sc cutoff N
    (consObjectEq D Sc cutoff N ρ β hρ l) (consObjectEq D Sc cutoff N τ β hτ l)]
  rw [Category.assoc (inducedWordIso D Sc cutoff N ρ β hρ l).inv]
  exact congrArg (fun a => eqToHom (consObjectEq D Sc cutoff N τ β hτ l).symm ≫ a ≫
    eqToHom (consObjectEq D Sc cutoff N ρ β hρ l))
    (homEquiv_induction D Sc cutoff N β [l]
      (VacuumRepresentable.wordIsoAt D Sc cutoff N ρ β hρ)
      (VacuumRepresentable.wordIsoAt D Sc cutoff N τ β hτ) f)


theorem wordHomEquiv_inner_cross (ρ : List I) (β : Multiset I)
    (hρ : VacuumRepresentable.content ρ = β) (i j l : I) (δ : Multiset I)
    (hij : β + ([i,j] : Multiset I) = δ) (hji : β + ([j,i] : Multiset I) = δ)
    (heij : VacuumRepresentable.content (j :: i :: ρ) = δ)
    (heji : VacuumRepresentable.content (i :: j :: ρ) = δ) :
    VacuumRepresentable.wordHomEquiv D Sc cutoff N (l :: i :: j :: ρ) (l :: j :: i :: ρ)
      (δ + ([l] : Multiset I)) (congrArg (· + ([l] : Multiset I)) heji)
      (congrArg (· + ([l] : Multiset I)) heij)
      ((consModuleIso D Sc cutoff N (i :: j :: ρ) δ heji l).inv ≫
        (contentInduction D Sc cutoff N δ [l]).map
          (VacuumWordPairing.wordCross D Sc cutoff N ρ β hρ i j δ hij hji heij heji) ≫
        (consModuleIso D Sc cutoff N (j :: i :: ρ) δ heij l).hom) =
    eqToHom (consObjectEq D Sc cutoff N (j :: i :: ρ) δ heij l).symm ≫
      (contentAppend D Sc cutoff N δ [l]).map
        (VacuumWordPairing.wordCrossArrow D Sc cutoff N ρ β hρ i j δ hij hji heij heji) ≫
      eqToHom (consObjectEq D Sc cutoff N (i :: j :: ρ) δ heji l) := by
  rw [wordHomEquiv_cons]
  have hc := VacuumWordPairing.wordHomEquiv_cross D Sc cutoff N ρ (j :: i :: ρ)
    β hρ i j δ hij hji heij heji heij (𝟙 _)
  rw [Category.comp_id, wordHomEquiv_id, twist_id, Category.id_comp] at hc
  rw [hc]


theorem evaluate_comp {β : Multiset I} {v w z : ContentCategory D Sc cutoff N β}
    (s : contentRepresentable D Sc cutoff N β v ⟶ contentRepresentable D Sc cutoff N β w)
    (t : contentRepresentable D Sc cutoff N β w ⟶ contentRepresentable D Sc cutoff N β z)
    (p : ZMod 2) (ha : ContentYoneda.evaluate D Sc cutoff N β s ∈ parity (R := k) _ _ p) :
    ContentYoneda.evaluate D Sc cutoff N β (s ≫ t) =
      twist k p (ContentYoneda.evaluate D Sc cutoff N β t) ≫
        ContentYoneda.evaluate D Sc cutoff N β s := by
  change (s ≫ t).total v (𝟙 v) = _
  rw [Superfunctor.comp_total]
  change ContentYoneda.componentMap D Sc cutoff N β t 0 v
      (ContentYoneda.evaluate D Sc cutoff N β s) +
    ContentYoneda.componentMap D Sc cutoff N β t 1 v
      (ContentYoneda.evaluate D Sc cutoff N β s) = _
  rw [ContentYoneda.app_formula D Sc cutoff N β t 0 v,
    ContentYoneda.app_formula D Sc cutoff N β t 1 v,
    twist_of_mem _ ha, twist_of_mem _ ha]
  unfold ContentYoneda.evaluate
  rw [map_add, Preadditive.add_comp,
    twist_of_mem _ (ContentYoneda.evaluate_part D Sc cutoff N β t 0),
    twist_of_mem _ (ContentYoneda.evaluate_part D Sc cutoff N β t 1)]
  simp only [zero_mul, mul_zero, one_mul, mul_one, sign_zero, one_smul,
    Linear.comp_smul, Linear.smul_comp]


theorem wordHomEquiv_comp (ρ σ τ : List I) (β : Multiset I)
    (hρ : VacuumRepresentable.content ρ = β) (hσ : VacuumRepresentable.content σ = β)
    (hτ : VacuumRepresentable.content τ = β)
    (s : VacuumRepresentable.wordModuleAt D Sc cutoff N ρ β hρ ⟶
      VacuumRepresentable.wordModuleAt D Sc cutoff N σ β hσ)
    (t : VacuumRepresentable.wordModuleAt D Sc cutoff N σ β hσ ⟶
      VacuumRepresentable.wordModuleAt D Sc cutoff N τ β hτ)
    (p : ZMod 2)
    (hs : VacuumRepresentable.wordHomEquiv D Sc cutoff N ρ σ β hρ hσ s ∈
      parity (R := k) _ _ p) :
    VacuumRepresentable.wordHomEquiv D Sc cutoff N ρ τ β hρ hτ (s ≫ t) =
      twist k p (VacuumRepresentable.wordHomEquiv D Sc cutoff N σ τ β hσ hτ t) ≫
        VacuumRepresentable.wordHomEquiv D Sc cutoff N ρ σ β hρ hσ s := by
  have he :
      (VacuumRepresentable.wordIsoAt D Sc cutoff N ρ β hρ).inv ≫ (s ≫ t) ≫
        (VacuumRepresentable.wordIsoAt D Sc cutoff N τ β hτ).hom =
      ((VacuumRepresentable.wordIsoAt D Sc cutoff N ρ β hρ).inv ≫ s ≫
        (VacuumRepresentable.wordIsoAt D Sc cutoff N σ β hσ).hom) ≫
      ((VacuumRepresentable.wordIsoAt D Sc cutoff N σ β hσ).inv ≫ t ≫
        (VacuumRepresentable.wordIsoAt D Sc cutoff N τ β hτ).hom) := by
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact (congrArg (ContentYoneda.evaluate D Sc cutoff N β) he).trans
    (evaluate_comp D Sc cutoff N _ _ p hs)


theorem wordCrossArrow_mem (ρ : List I) (β : Multiset I)
    (hρ : VacuumRepresentable.content ρ = β) (i j : I) (δ : Multiset I)
    (hij : β + ([i,j] : Multiset I) = δ) (hji : β + ([j,i] : Multiset I) = δ)
    (heij : VacuumRepresentable.content (j :: i :: ρ) = δ)
    (heji : VacuumRepresentable.content (i :: j :: ρ) = δ) :
    VacuumWordPairing.wordCrossArrow D Sc cutoff N ρ β hρ i j δ hij hji heij heji ∈
      parity (R := k) _ _ (D.parity i * D.parity j) := by
  unfold VacuumWordPairing.wordCrossArrow
  simpa only [zero_add, add_zero] using
    comp_mem (eqToHom_mem (R := k) _)
      (comp_mem ((contentAppendTo_supernatural D Sc cutoff N hij hji
        (contentCrossAffine_mem D Sc i j)).mem
          (VacuumRepresentable.wordObjectAt D Sc cutoff N ρ β hρ))
        (eqToHom_mem (R := k) _))

theorem wordHomEquiv_inner_cross_reservoir (ρ τ : List I) (β : Multiset I)
    (hρ : VacuumRepresentable.content ρ = β) (i j l : I) (δ : Multiset I)
    (hij : β + ([i,j] : Multiset I) = δ) (hji : β + ([j,i] : Multiset I) = δ)
    (heij : VacuumRepresentable.content (j :: i :: ρ) = δ)
    (heji : VacuumRepresentable.content (i :: j :: ρ) = δ)
    (hτ : VacuumRepresentable.content τ = δ + ([l] : Multiset I))
    (t : VacuumRepresentable.wordModuleAt D Sc cutoff N (l :: j :: i :: ρ)
      (δ + ([l] : Multiset I)) (congrArg (· + ([l] : Multiset I)) heij) ⟶
      VacuumRepresentable.wordModuleAt D Sc cutoff N τ (δ + ([l] : Multiset I)) hτ) :
    VacuumRepresentable.wordHomEquiv D Sc cutoff N (l :: i :: j :: ρ) τ
      (δ + ([l] : Multiset I)) (congrArg (· + ([l] : Multiset I)) heji) hτ
      (((consModuleIso D Sc cutoff N (i :: j :: ρ) δ heji l).inv ≫ (contentInduction D Sc cutoff N δ [l]).map (VacuumWordPairing.wordCross D Sc cutoff N ρ β hρ i j δ hij hji heij heji) ≫ (consModuleIso D Sc cutoff N (j :: i :: ρ) δ heij l).hom) ≫ t) =
    twist k (D.parity i * D.parity j)
      (VacuumRepresentable.wordHomEquiv D Sc cutoff N (l :: j :: i :: ρ) τ
        (δ + ([l] : Multiset I)) (congrArg (· + ([l] : Multiset I)) heij) hτ t) ≫
      (eqToHom (consObjectEq D Sc cutoff N (j :: i :: ρ) δ heij l).symm ≫ (contentAppend D Sc cutoff N δ [l]).map (VacuumWordPairing.wordCrossArrow D Sc cutoff N ρ β hρ i j δ hij hji heij heji) ≫ eqToHom (consObjectEq D Sc cutoff N (i :: j :: ρ) δ heji l)) := by
  have hc := wordHomEquiv_inner_cross D Sc cutoff N ρ β hρ i j l δ hij hji heij heji
  have hm : (eqToHom (consObjectEq D Sc cutoff N (j :: i :: ρ) δ heij l).symm ≫ (contentAppend D Sc cutoff N δ [l]).map (VacuumWordPairing.wordCrossArrow D Sc cutoff N ρ β hρ i j δ hij hji heij heji) ≫ eqToHom (consObjectEq D Sc cutoff N (i :: j :: ρ) δ heji l)) ∈ parity (R := k) _ _ (D.parity i * D.parity j) := by
    simpa only [zero_add, add_zero] using comp_mem (eqToHom_mem (R := k) _)
      (comp_mem (IsSuperfunctor.map_mem (F := contentAppend D Sc cutoff N δ [l])
        (wordCrossArrow_mem D Sc cutoff N ρ β hρ i j δ hij hji heij heji))
        (eqToHom_mem (R := k) _))
  have hm' : VacuumRepresentable.wordHomEquiv D Sc cutoff N (l :: i :: j :: ρ)
      (l :: j :: i :: ρ) (δ + ([l] : Multiset I))
      (congrArg (· + ([l] : Multiset I)) heji) (congrArg (· + ([l] : Multiset I)) heij)
      (((consModuleIso D Sc cutoff N (i :: j :: ρ) δ heji l).inv ≫ (contentInduction D Sc cutoff N δ [l]).map (VacuumWordPairing.wordCross D Sc cutoff N ρ β hρ i j δ hij hji heij heji) ≫ (consModuleIso D Sc cutoff N (j :: i :: ρ) δ heij l).hom)) ∈
      parity (R := k) _ _ (D.parity i * D.parity j) := Set.mem_of_eq_of_mem hc hm
  exact (wordHomEquiv_comp D Sc cutoff N (l :: i :: j :: ρ) (l :: j :: i :: ρ) τ
    (δ + ([l] : Multiset I)) _ _ hτ
    (((consModuleIso D Sc cutoff N (i :: j :: ρ) δ heji l).inv ≫ (contentInduction D Sc cutoff N δ [l]).map (VacuumWordPairing.wordCross D Sc cutoff N ρ β hρ i j δ hij hji heij heji) ≫ (consModuleIso D Sc cutoff N (j :: i :: ρ) δ heij l).hom)) t _ hm').trans
    (congrArg (fun a => twist k (D.parity i * D.parity j)
      (VacuumRepresentable.wordHomEquiv D Sc cutoff N (l :: j :: i :: ρ) τ
        (δ + ([l] : Multiset I)) (congrArg (· + ([l] : Multiset I)) heij) hτ t) ≫ a) hc)


def consModuleIsoTo (ρ : List I) (β : Multiset I)
    (hρ : VacuumRepresentable.content ρ = β) (l : I) (γ : Multiset I)
    (hγ : β + ([l] : Multiset I) = γ) :
    (contentInductionTo D Sc cutoff N β [l] γ hγ).obj
      (VacuumRepresentable.wordModuleAt D Sc cutoff N ρ β hρ) ≅
    VacuumRepresentable.wordModuleAt D Sc cutoff N (l :: ρ) γ
      ((congrArg (· + ([l] : Multiset I)) hρ).trans hγ) :=
  eqToIso (by cases hγ; cases hρ; rfl)

theorem consObjectEqTo (ρ : List I) (β : Multiset I)
    (hρ : VacuumRepresentable.content ρ = β) (l : I) (γ : Multiset I)
    (hγ : β + ([l] : Multiset I) = γ) :
    (contentAppendTo D Sc cutoff N β [l] γ hγ).obj
      (VacuumRepresentable.wordObjectAt D Sc cutoff N ρ β hρ) =
    VacuumRepresentable.wordObjectAt D Sc cutoff N (l :: ρ) γ
      ((congrArg (· + ([l] : Multiset I)) hρ).trans hγ) := by
  cases hγ; cases hρ; rfl

theorem wordHomEquiv_inner_cross_to (ρ : List I) (β : Multiset I)
    (hρ : VacuumRepresentable.content ρ = β) (i j l : I) (δ γ : Multiset I)
    (hij : β + ([i,j] : Multiset I) = δ) (hji : β + ([j,i] : Multiset I) = δ)
    (heij : VacuumRepresentable.content (j :: i :: ρ) = δ)
    (heji : VacuumRepresentable.content (i :: j :: ρ) = δ)
    (hγ : δ + ([l] : Multiset I) = γ) :
    VacuumRepresentable.wordHomEquiv D Sc cutoff N (l :: i :: j :: ρ) (l :: j :: i :: ρ)
      γ ((congrArg (· + ([l] : Multiset I)) heji).trans hγ)
      ((congrArg (· + ([l] : Multiset I)) heij).trans hγ)
      ((consModuleIsoTo D Sc cutoff N (i :: j :: ρ) δ heji l γ hγ).inv ≫
        (contentInductionTo D Sc cutoff N δ [l] γ hγ).map
          (VacuumWordPairing.wordCross D Sc cutoff N ρ β hρ i j δ hij hji heij heji) ≫
        (consModuleIsoTo D Sc cutoff N (j :: i :: ρ) δ heij l γ hγ).hom) =
    eqToHom (consObjectEqTo D Sc cutoff N (j :: i :: ρ) δ heij l γ hγ).symm ≫
      (contentAppendTo D Sc cutoff N δ [l] γ hγ).map
        (VacuumWordPairing.wordCrossArrow D Sc cutoff N ρ β hρ i j δ hij hji heij heji) ≫
      eqToHom (consObjectEqTo D Sc cutoff N (i :: j :: ρ) δ heji l γ hγ) := by
  cases hγ
  simpa only [consModuleIsoTo, consModuleIso, contentInductionTo, contentInduction,
    contentAppendTo, contentAppend] using
    wordHomEquiv_inner_cross D Sc cutoff N ρ β hρ i j l δ hij hji heij heji

end OddMath.QuiverHecke.ELVOld.VacuumWordBraid
