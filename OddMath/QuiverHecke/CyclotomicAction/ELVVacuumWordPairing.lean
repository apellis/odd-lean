import OddMath.QuiverHecke.CyclotomicAction.ELVVacuumWordEvaluation

/-! # Crossing on vacuum-word Hom coordinates

`wordHomEquiv_cross` proves that precomposition by the actual iterated
normalized crossing becomes twisted postcomposition on the existing reverse
word-Hom coordinates. Canonical module and object equality transports retain
the terminal content. Its specializations retain mixed colours, the
equal-colour minus sign, and arbitrary total kernel parity.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.VacuumWordPairing
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

private theorem moduleCarrier (ρ : List I) (β : Multiset I)
    (hρ : VacuumRepresentable.content ρ = β) (i j : I) (γ : Multiset I)
    (h : β + ([i,j] : Multiset I) = γ)
    (he : VacuumRepresentable.content (j :: i :: ρ) = γ) :
    (contentEPairTo D Sc cutoff N β i j γ h).obj
      (VacuumRepresentable.wordModuleAt D Sc cutoff N ρ β hρ) =
    VacuumRepresentable.wordModuleAt D Sc cutoff N (j :: i :: ρ) γ he := by
  cases hρ
  cases he
  rfl

private theorem objectCarrier (ρ : List I) (β : Multiset I)
    (hρ : VacuumRepresentable.content ρ = β) (i j : I) (γ : Multiset I)
    (h : β + ([i,j] : Multiset I) = γ)
    (he : VacuumRepresentable.content (j :: i :: ρ) = γ) :
    (contentAppendTo D Sc cutoff N β [i,j] γ h).obj
      (VacuumRepresentable.wordObjectAt D Sc cutoff N ρ β hρ) =
    VacuumRepresentable.wordObjectAt D Sc cutoff N (j :: i :: ρ) γ he := by
  cases hρ
  cases he
  exact (congrArg (fun F => F.obj (VacuumRepresentable.wordObject D Sc cutoff N ρ))
    (contentAppend_comp_eq D Sc cutoff N _ [i] [j] _ rfl h)).symm

private theorem homogeneous_total_ext {C : Type u} [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {M L : Superfunctor k C (SVec k)} {f g : M ⟶ L} {p : ZMod 2}
    (hf : f ∈ parity (R := k) _ _ p) (hg : g ∈ parity (R := k) _ _ p)
    (h : ∀ w, f.total w = g.total w) : f = g := by
  apply Superfunctor.hom_ext
  intro q w
  by_cases hq : q = p
  · subst q
    rcases parity_eq_zero_or_one p with rfl | rfl
    · simpa only [SuperNatTrans.total,
        Superfunctor.app_eq_zero_of_mem hf (show (1 : ZMod 2) ≠ 0 by decide),
        Superfunctor.app_eq_zero_of_mem hg (show (1 : ZMod 2) ≠ 0 by decide), add_zero] using h w
    · simpa only [SuperNatTrans.total,
        Superfunctor.app_eq_zero_of_mem hf (show (0 : ZMod 2) ≠ 1 by decide),
        Superfunctor.app_eq_zero_of_mem hg (show (0 : ZMod 2) ≠ 1 by decide), zero_add] using h w
  · rw [Superfunctor.app_eq_zero_of_mem hf hq, Superfunctor.app_eq_zero_of_mem hg hq]

/-- Canonical endpoint transport, independent of evaluation or crossing. -/
def pairModuleIso (ρ : List I) (β : Multiset I)
    (hρ : VacuumRepresentable.content ρ = β) (i j : I) (γ : Multiset I)
    (h : β + ([i,j] : Multiset I) = γ)
    (he : VacuumRepresentable.content (j :: i :: ρ) = γ) :=
  eqToIso (moduleCarrier D Sc cutoff N ρ β hρ i j γ h he)

private def representableIsoTo (β : Multiset I) (σ : List I) (γ : Multiset I)
    (h : β + (σ : Multiset I) = γ) (v : ContentCategory D Sc cutoff N β) :
    (contentInductionTo D Sc cutoff N β σ γ h).obj (contentRepresentable D Sc cutoff N β v) ≅
      contentRepresentable D Sc cutoff N γ ((contentAppendTo D Sc cutoff N β σ γ h).obj v) := by
  subst γ
  exact InductionRepresentable.iso D Sc cutoff N β σ v

private theorem representableIsoTo_even (β : Multiset I) (σ : List I) (γ : Multiset I)
    (h : β + (σ : Multiset I) = γ) (v : ContentCategory D Sc cutoff N β) :
    (representableIsoTo D Sc cutoff N β σ γ h v).hom ∈ parity (R := k) _ _ 0 := by
  subst γ
  exact VacuumSourceComparison.representableIso_even D Sc cutoff N β σ v

private theorem representableIsoTo_total (β : Multiset I) (σ : List I) (γ : Multiset I)
    (h : β + (σ : Multiset I) = γ) (v : ContentCategory D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N γ) :
    (representableIsoTo D Sc cutoff N β σ γ h v).hom.total w =
      (VacuumGeneratorCoordinates.equivTo D Sc cutoff N β σ γ h v w).toLinearMap := by
  subst γ
  simp only [representableIsoTo, InductionRepresentable.iso, SuperNatTrans.total,
    InductionRepresentable.forwardTransform_app, ite_true, one_ne_zero, ite_false, add_zero]
  rfl

private theorem representable_transport_total (β : Multiset I)
    {v w : ContentCategory D Sc cutoff N β} (h : v = w)
    (z : ContentCategory D Sc cutoff N β) (f : v ⟶ z) :
    (eqToHom (congrArg (contentRepresentable D Sc cutoff N β) h)).total z f =
      eqToHom h.symm ≫ f := by
  subst w
  simp only [eqToHom_refl, SuperNatTrans.total, Superfunctor.id_app_zero,
    Superfunctor.id_app_one, add_zero, Category.id_comp]
  rfl

private theorem comparison_representable (β : Multiset I) (σ τ : List I) (γ : Multiset I)
    (h : (β + (σ : Multiset I)) + (τ : Multiset I) = γ)
    (h' : β + ((σ ++ τ : List I) : Multiset I) = γ)
    (v : ContentCategory D Sc cutoff N β) :
    (contentInductionComp D Sc cutoff N β σ τ γ h h').hom.app
        (contentRepresentable D Sc cutoff N β v) ≫
      (representableIsoTo D Sc cutoff N β (σ ++ τ) γ h' v).hom =
    (contentInductionTo D Sc cutoff N (β + (σ : Multiset I)) τ γ h).map
        (InductionRepresentable.iso D Sc cutoff N β σ v).hom ≫
      (representableIsoTo D Sc cutoff N (β + (σ : Multiset I)) τ γ h
        ((contentAppend D Sc cutoff N β σ).obj v)).hom ≫
      eqToHom (congrArg (contentRepresentable D Sc cutoff N γ)
        (congrArg (fun F => F.obj v) (contentAppend_comp_eq D Sc cutoff N β σ τ γ h h'))) := by
  apply homogeneous_total_ext
  · simpa only [zero_add] using comp_mem
      (contentInductionComp_mem D Sc cutoff N β σ τ γ h h' _).1
      (representableIsoTo_even D Sc cutoff N β (σ ++ τ) γ h' v)
  · have hm := IsSuperfunctor.map_mem
      (F := contentInductionTo D Sc cutoff N (β + (σ : Multiset I)) τ γ h)
      (VacuumSourceComparison.representableIso_even D Sc cutoff N β σ v)
    have he := eqToHom_mem (R := k) (congrArg (contentRepresentable D Sc cutoff N γ)
      (congrArg (fun F => F.obj v) (contentAppend_comp_eq D Sc cutoff N β σ τ γ h h')))
    have hh := comp_mem hm (comp_mem
      (representableIsoTo_even D Sc cutoff N (β + (σ : Multiset I)) τ γ h
        ((contentAppend D Sc cutoff N β σ).obj v)) he)
    simp only [zero_add] at hh
    convert hh using 1 <;> rfl
  · intro w
    have ht : ∀ {C : Type u} [Category.{u} C] [Preadditive C] [Linear k C]
        [Supercategory k C] {A B E : Superfunctor k C (SVec k)}
        (f : A ⟶ B) (g : B ⟶ E) (z : C),
        (f ≫ g).total z = g.total z ∘ₗ f.total z :=
      fun f g z => Superfunctor.comp_total f g z
    rw [ht, representableIsoTo_total]
    erw [VacuumSourceComparison.comparison]
    rw [ht, ht, representableIsoTo_total]
    apply LinearMap.ext
    intro x
    change VacuumSourceComparison.sourceCoordinates D Sc cutoff N β σ τ γ h h' v w x =
      (eqToHom (congrArg (contentRepresentable D Sc cutoff N γ)
        (congrArg (fun F => F.obj v) (contentAppend_comp_eq D Sc cutoff N β σ τ γ h h')))).total w
        (VacuumGeneratorCoordinates.equivTo D Sc cutoff N (β + (σ : Multiset I)) τ γ h
          ((contentAppend D Sc cutoff N β σ).obj v) w
          (((contentInductionTo D Sc cutoff N (β + (σ : Multiset I)) τ γ h).map
            (InductionRepresentable.iso D Sc cutoff N β σ v).hom).total w x))
    rw [representable_transport_total D Sc cutoff N γ
      (congrArg (fun F => F.obj v) (contentAppend_comp_eq D Sc cutoff N β σ τ γ h h'))]
    have hz := Superfunctor.app_eq_zero_of_mem
      (IsSuperfunctor.map_mem
        (F := contentInductionTo D Sc cutoff N (β + (σ : Multiset I)) τ γ h)
        (VacuumSourceComparison.representableIso_even D Sc cutoff N β σ v))
      (show (1 : ZMod 2) ≠ 0 by decide) w
    simp only [SuperNatTrans.total, hz, add_zero]
    rfl

private theorem word_comparison (ρ : List I) (β : Multiset I)
    (hρ : VacuumRepresentable.content ρ = β) (i j : I) (γ : Multiset I)
    (h : β + ([i,j] : Multiset I) = γ)
    (he : VacuumRepresentable.content (j :: i :: ρ) = γ) :
    (pairModuleIso D Sc cutoff N ρ β hρ i j γ h he).hom ≫
      (VacuumRepresentable.wordIsoAt D Sc cutoff N (j :: i :: ρ) γ he).hom ≫
      eqToHom (congrArg (contentRepresentable D Sc cutoff N γ)
        (objectCarrier D Sc cutoff N ρ β hρ i j γ h he).symm) =
    (contentEPairToComparison D Sc cutoff N β i j γ h).hom.app
        (VacuumRepresentable.wordModuleAt D Sc cutoff N ρ β hρ) ≫
      (contentInductionTo D Sc cutoff N β [i,j] γ h).map
        (VacuumRepresentable.wordIsoAt D Sc cutoff N ρ β hρ).hom ≫
      (representableIsoTo D Sc cutoff N β [i,j] γ h
        (VacuumRepresentable.wordObjectAt D Sc cutoff N ρ β hρ)).hom := by
  conv_rhs => rw [← Category.assoc, ← NatTrans.naturality, Category.assoc]
  rw [show (contentEPairToComparison D Sc cutoff N β i j γ h).hom.app
      (contentRepresentable D Sc cutoff N β (VacuumRepresentable.wordObjectAt D Sc cutoff N ρ β hρ)) ≫
      (representableIsoTo D Sc cutoff N β [i,j] γ h
        (VacuumRepresentable.wordObjectAt D Sc cutoff N ρ β hρ)).hom = _ from
    comparison_representable D Sc cutoff N β [i] [j] γ _ h
      (VacuumRepresentable.wordObjectAt D Sc cutoff N ρ β hρ)]
  cases hρ
  cases he
  simp only [pairModuleIso, eqToIso.hom, eqToHom_refl, Category.id_comp,
    VacuumRepresentable.wordIsoAt, VacuumRepresentable.wordIso,
    Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp, Functor.comp_map,
    Category.assoc]
  rfl

private theorem evaluate_precompose {β : Multiset I}
    {v w z : ContentCategory D Sc cutoff N β}
    (s : contentRepresentable D Sc cutoff N β v ⟶ contentRepresentable D Sc cutoff N β w)
    (t : contentRepresentable D Sc cutoff N β w ⟶ contentRepresentable D Sc cutoff N β z)
    (p : ZMod 2) (a : w ⟶ v) (ha : a ∈ parity (R := k) _ _ p)
    (hs : s.total v (𝟙 v) = a) :
    ContentYoneda.evaluate D Sc cutoff N β (s ≫ t) =
      twist k p (ContentYoneda.evaluate D Sc cutoff N β t) ≫ a := by
  change (s ≫ t).total v (𝟙 v) = _
  rw [Superfunctor.comp_total]
  change t.total v (s.total v (𝟙 v)) = _
  rw [hs]
  change ContentYoneda.componentMap D Sc cutoff N β t 0 v a +
    ContentYoneda.componentMap D Sc cutoff N β t 1 v a = _
  rw [ContentYoneda.app_formula D Sc cutoff N β t 0 v a,
    ContentYoneda.app_formula D Sc cutoff N β t 1 v a,
    twist_of_mem _ ha, twist_of_mem _ ha]
  unfold ContentYoneda.evaluate
  rw [map_add, Preadditive.add_comp,
    twist_of_mem _ (ContentYoneda.evaluate_part D Sc cutoff N β t 0),
    twist_of_mem _ (ContentYoneda.evaluate_part D Sc cutoff N β t 1)]
  simp only [zero_mul, mul_zero, one_mul, mul_one, sign_zero, one_smul,
    Linear.comp_smul, Linear.smul_comp]

private theorem fromArrow_mem {β : Multiset I}
    {v w : ContentCategory D Sc cutoff N β} {p : ZMod 2}
    (a : w ⟶ v) (ha : a ∈ parity (R := k) _ _ p) :
    ContentYoneda.fromArrow D Sc cutoff N β a ∈ parity (R := k) _ _ p := by
  rw [Superfunctor.mem_parity_iff_isHomogeneous]
  intro q hq
  funext z
  apply LinearMap.ext
  intro x
  change proj k q a ≫ twist k q x = 0
  rw [proj_of_mem_ne ha (Ne.symm hq)]
  simp

private theorem fromArrow_total {β : Multiset I}
    {v w : ContentCategory D Sc cutoff N β} {p : ZMod 2}
    (a : w ⟶ v) (ha : a ∈ parity (R := k) _ _ p)
    (z : ContentCategory D Sc cutoff N β) (x : v ⟶ z) :
    (ContentYoneda.fromArrow D Sc cutoff N β a).total z x = a ≫ twist k p x := by
  change proj k 0 a ≫ twist k 0 x + proj k 1 a ≫ twist k 1 x = _
  rcases parity_eq_zero_or_one p with rfl | rfl
  · rw [proj_of_mem ha, proj_of_mem_ne ha (by decide)]
    simp
  · rw [proj_of_mem_ne ha (by decide), proj_of_mem ha]
    simp

private theorem block_cross_total (β : Multiset I) (i j : I) (γ : Multiset I)
    (hij : β + ([i,j] : Multiset I) = γ) (hji : β + ([j,i] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β) (w : ContentCategory D Sc cutoff N γ) :
    ((contentInductionTransform D Sc cutoff N hij hji
      (contentCrossAffine_mem D Sc i j)).app (D.parity i * D.parity j) M).total w =
      BalancedInduction.transformLinear
        (contentAppendTo_supernatural D Sc cutoff N hij hji (contentCrossAffine_mem D Sc i j)) M w := by
  have ht := congrFun (IsSupernatural.toSuperNatTrans_app
    (BalancedInduction.transformComponent_supernatural
      (contentAppendTo_supernatural D Sc cutoff N hij hji (contentCrossAffine_mem D Sc i j)))) M
  refine (congrArg (fun a => a.total w) ht).trans ?_
  have hh := BalancedInduction.transformLinear_supernatural
    (contentAppendTo_supernatural D Sc cutoff N hij hji (contentCrossAffine_mem D Sc i j)) M
  change hh.toSuperNatTrans.total w = _
  rcases parity_eq_zero_or_one (D.parity i * D.parity j) with hp | hp
  all_goals simp [SuperNatTrans.total, IsSupernatural.toSuperNatTrans, hp]

private theorem block_cross_representable (β : Multiset I) (i j : I) (γ : Multiset I)
    (hij : β + ([i,j] : Multiset I) = γ) (hji : β + ([j,i] : Multiset I) = γ)
    (v : ContentCategory D Sc cutoff N β) :
    (contentInductionTransform D Sc cutoff N hij hji (contentCrossAffine_mem D Sc i j)).app
        (D.parity i * D.parity j) (contentRepresentable D Sc cutoff N β v) ≫
      (representableIsoTo D Sc cutoff N β [i,j] γ hij v).hom =
    (representableIsoTo D Sc cutoff N β [j,i] γ hji v).hom ≫
      ContentYoneda.fromArrow D Sc cutoff N γ
        (contentAppendToComponent D Sc cutoff N hij hji (contentCrossAffine D Sc i j) v) := by
  have ha := (contentAppendTo_supernatural D Sc cutoff N hij hji
    (contentCrossAffine_mem D Sc i j)).mem v
  apply homogeneous_total_ext
  · simpa only [add_zero] using comp_mem
      ((contentInductionTransform D Sc cutoff N hij hji (contentCrossAffine_mem D Sc i j)).app_mem _ _)
      (representableIsoTo_even D Sc cutoff N β [i,j] γ hij v)
  · simpa only [zero_add] using comp_mem
      (representableIsoTo_even D Sc cutoff N β [j,i] γ hji v)
      (fromArrow_mem D Sc cutoff N _ ha)
  · intro w
    rw [Superfunctor.comp_total, Superfunctor.comp_total]
    apply LinearMap.ext
    intro x
    change (representableIsoTo D Sc cutoff N β [i,j] γ hij v).hom.total w
      (((contentInductionTransform D Sc cutoff N hij hji (contentCrossAffine_mem D Sc i j)).app
        (D.parity i * D.parity j) (contentRepresentable D Sc cutoff N β v)).total w x) =
      (ContentYoneda.fromArrow D Sc cutoff N γ
        (contentAppendToComponent D Sc cutoff N hij hji (contentCrossAffine D Sc i j) v)).total w
          ((representableIsoTo D Sc cutoff N β [j,i] γ hji v).hom.total w x)
    rw [fromArrow_total D Sc cutoff N _ ha, representableIsoTo_total, representableIsoTo_total,
      block_cross_total]
    change VacuumGeneratorCoordinates.equivTo D Sc cutoff N β [i,j] γ hij v w
      (BalancedInduction.transformLinear
        (contentAppendTo_supernatural D Sc cutoff N hij hji (contentCrossAffine_mem D Sc i j))
        (contentRepresentable D Sc cutoff N β v) w x) =
      contentAppendToComponent D Sc cutoff N hij hji (contentCrossAffine D Sc i j) v ≫
        twist k (D.parity i * D.parity j)
          (VacuumGeneratorCoordinates.equivTo D Sc cutoff N β [j,i] γ hji v w x)
    obtain ⟨a, rfl⟩ := (VacuumGeneratorCoordinates.equivTo D Sc cutoff N β [j,i] γ hji v w).symm.surjective x
    simp only [LinearEquiv.apply_symm_apply]
    rw [VacuumGeneratorCoordinates.equivTo_symm]
    have ht := BalancedInduction.transformLinear_tensor
      (contentAppendTo_supernatural D Sc cutoff N hij hji (contentCrossAffine_mem D Sc i j))
      (contentRepresentable D Sc cutoff N β v) w v a (𝟙 v)
    refine (congrArg (VacuumGeneratorCoordinates.equivTo D Sc cutoff N β [i,j] γ hij v w) ht).trans ?_
    exact (VacuumGeneratorCoordinates.equivTo_tensor D Sc cutoff N β [i,j] γ hij v v w
      (contentAppendToComponent D Sc cutoff N hij hji (contentCrossAffine D Sc i j) v ≫
        twist k (D.parity i * D.parity j) a) (𝟙 v)).trans
      (by rw [CategoryTheory.Functor.map_id, Category.id_comp])

private theorem cross_comparison (β : Multiset I) (i j : I) (γ : Multiset I)
    (hij : β + ([i,j] : Multiset I) = γ) (hji : β + ([j,i] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β) (v : ContentCategory D Sc cutoff N β)
    (f : M ⟶ contentRepresentable D Sc cutoff N β v) (hf : f ∈ parity (R := k) _ _ 0) :
    (contentEPairCrossTransform D Sc cutoff N β i j γ hij hji).app (D.parity i * D.parity j) M ≫
      (contentEPairToComparison D Sc cutoff N β i j γ hij).hom.app M ≫
      (contentInductionTo D Sc cutoff N β [i,j] γ hij).map f ≫
      (representableIsoTo D Sc cutoff N β [i,j] γ hij v).hom =
    (contentEPairToComparison D Sc cutoff N β j i γ hji).hom.app M ≫
      (contentInductionTo D Sc cutoff N β [j,i] γ hji).map f ≫
      (representableIsoTo D Sc cutoff N β [j,i] γ hji v).hom ≫
      ContentYoneda.fromArrow D Sc cutoff N γ
        (contentAppendToComponent D Sc cutoff N hij hji (contentCrossAffine D Sc i j) v) := by
  rw [contentEPairCross_component]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  have hn := (contentInductionTransform D Sc cutoff N hij hji
    (contentCrossAffine_mem D Sc i j)).naturality (D.parity i * D.parity j) f hf
  simp only [koszulSign_zero_right, one_smul] at hn
  rw [← Category.assoc _ ((contentInductionTo D Sc cutoff N β [i,j] γ hij).map f), ← hn]
  simp only [Category.assoc]
  rw [block_cross_representable]

private theorem transport_fromArrow {β : Multiset I}
    {v v' w w' : ContentCategory D Sc cutoff N β}
    (hv : v = v') (hw : w = w') (a : w' ⟶ v') :
    eqToHom (congrArg (contentRepresentable D Sc cutoff N β) hv) ≫
      ContentYoneda.fromArrow D Sc cutoff N β a ≫
      eqToHom (congrArg (contentRepresentable D Sc cutoff N β) hw.symm) =
    ContentYoneda.fromArrow D Sc cutoff N β (eqToHom hw ≫ a ≫ eqToHom hv.symm) := by
  cases hv
  cases hw
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

/-- Actual iterated crossing, transported only by canonical module equalities. -/
def wordCross (ρ : List I) (β : Multiset I) (hρ : VacuumRepresentable.content ρ = β)
    (i j : I) (γ : Multiset I)
    (hij : β + ([i,j] : Multiset I) = γ) (hji : β + ([j,i] : Multiset I) = γ)
    (heij : VacuumRepresentable.content (j :: i :: ρ) = γ)
    (heji : VacuumRepresentable.content (i :: j :: ρ) = γ) :
    VacuumRepresentable.wordModuleAt D Sc cutoff N (i :: j :: ρ) γ heji ⟶
      VacuumRepresentable.wordModuleAt D Sc cutoff N (j :: i :: ρ) γ heij :=
  (pairModuleIso D Sc cutoff N ρ β hρ j i γ hji heji).inv ≫
    (contentEPairCrossTransform D Sc cutoff N β i j γ hij hji).app (D.parity i * D.parity j)
      (VacuumRepresentable.wordModuleAt D Sc cutoff N ρ β hρ) ≫
    (pairModuleIso D Sc cutoff N ρ β hρ i j γ hij heij).hom

/-- Normalized diagram crossing with canonical whole-word object endpoints. -/
def wordCrossArrow (ρ : List I) (β : Multiset I) (hρ : VacuumRepresentable.content ρ = β)
    (i j : I) (γ : Multiset I)
    (hij : β + ([i,j] : Multiset I) = γ) (hji : β + ([j,i] : Multiset I) = γ)
    (heij : VacuumRepresentable.content (j :: i :: ρ) = γ)
    (heji : VacuumRepresentable.content (i :: j :: ρ) = γ) :
    VacuumRepresentable.wordObjectAt D Sc cutoff N (j :: i :: ρ) γ heij ⟶
      VacuumRepresentable.wordObjectAt D Sc cutoff N (i :: j :: ρ) γ heji :=
  eqToHom (objectCarrier D Sc cutoff N ρ β hρ i j γ hij heij).symm ≫
    contentAppendToComponent D Sc cutoff N hij hji (contentCrossAffine D Sc i j)
      (VacuumRepresentable.wordObjectAt D Sc cutoff N ρ β hρ) ≫
    eqToHom (objectCarrier D Sc cutoff N ρ β hρ j i γ hji heji)

private theorem word_cross_intertwine (ρ : List I) (β : Multiset I)
    (hρ : VacuumRepresentable.content ρ = β) (i j : I) (γ : Multiset I)
    (hij : β + ([i,j] : Multiset I) = γ) (hji : β + ([j,i] : Multiset I) = γ)
    (heij : VacuumRepresentable.content (j :: i :: ρ) = γ)
    (heji : VacuumRepresentable.content (i :: j :: ρ) = γ) :
    wordCross D Sc cutoff N ρ β hρ i j γ hij hji heij heji ≫
      (VacuumRepresentable.wordIsoAt D Sc cutoff N (j :: i :: ρ) γ heij).hom =
    (VacuumRepresentable.wordIsoAt D Sc cutoff N (i :: j :: ρ) γ heji).hom ≫
      ContentYoneda.fromArrow D Sc cutoff N γ
        (wordCrossArrow D Sc cutoff N ρ β hρ i j γ hij hji heij heji) := by
  have hc := cross_comparison D Sc cutoff N β i j γ hij hji
    (VacuumRepresentable.wordModuleAt D Sc cutoff N ρ β hρ)
    (VacuumRepresentable.wordObjectAt D Sc cutoff N ρ β hρ)
    (VacuumRepresentable.wordIsoAt D Sc cutoff N ρ β hρ).hom
    (VacuumSourceComparison.wordIsoAt_even D Sc cutoff N ρ β hρ)
  rw [← word_comparison D Sc cutoff N ρ β hρ i j γ hij heij] at hc
  conv_rhs at hc =>
    rw [← Category.assoc, ← Category.assoc]
    lhs
    rw [Category.assoc, ← word_comparison D Sc cutoff N ρ β hρ j i γ hji heji]
  have hc' := congrArg (fun f =>
    (pairModuleIso D Sc cutoff N ρ β hρ j i γ hji heji).inv ≫ f ≫
    eqToHom (congrArg (contentRepresentable D Sc cutoff N γ)
      (objectCarrier D Sc cutoff N ρ β hρ i j γ hij heij))) hc
  simp only [Category.assoc, Iso.inv_hom_id_assoc, eqToHom_trans, eqToHom_refl,
    Category.comp_id] at hc'
  unfold wordCross wordCrossArrow
  rw [← transport_fromArrow D Sc cutoff N
    (objectCarrier D Sc cutoff N ρ β hρ j i γ hji heji).symm
    (objectCarrier D Sc cutoff N ρ β hρ i j γ hij heij).symm]
  simpa only [Category.assoc] using hc'

private theorem wordCrossArrow_mem (ρ : List I) (β : Multiset I)
    (hρ : VacuumRepresentable.content ρ = β) (i j : I) (γ : Multiset I)
    (hij : β + ([i,j] : Multiset I) = γ) (hji : β + ([j,i] : Multiset I) = γ)
    (heij : VacuumRepresentable.content (j :: i :: ρ) = γ)
    (heji : VacuumRepresentable.content (i :: j :: ρ) = γ) :
    wordCrossArrow D Sc cutoff N ρ β hρ i j γ hij hji heij heji ∈
      parity (R := k) _ _ (D.parity i * D.parity j) := by
  have hh := comp_mem
    (eqToHom_mem (R := k) (objectCarrier D Sc cutoff N ρ β hρ i j γ hij heij).symm)
    (comp_mem ((contentAppendTo_supernatural D Sc cutoff N hij hji
      (contentCrossAffine_mem D Sc i j)).mem (VacuumRepresentable.wordObjectAt D Sc cutoff N ρ β hρ))
      (eqToHom_mem (R := k) (objectCarrier D Sc cutoff N ρ β hρ j i γ hji heji)))
  simp only [zero_add, add_zero] at hh
  convert hh using 1
  rfl

/-- Combined source-and-reservoir word Hom crossing. The reservoir kernel is
arbitrary: the twist retains its entire coefficient-plus-diagram parity. -/
theorem wordHomEquiv_cross (ρ τ : List I) (β : Multiset I)
    (hρ : VacuumRepresentable.content ρ = β) (i j : I) (γ : Multiset I)
    (hij : β + ([i,j] : Multiset I) = γ) (hji : β + ([j,i] : Multiset I) = γ)
    (heij : VacuumRepresentable.content (j :: i :: ρ) = γ)
    (heji : VacuumRepresentable.content (i :: j :: ρ) = γ)
    (hτ : VacuumRepresentable.content τ = γ)
    (t : VacuumRepresentable.wordModuleAt D Sc cutoff N (j :: i :: ρ) γ heij ⟶
      VacuumRepresentable.wordModuleAt D Sc cutoff N τ γ hτ) :
    VacuumRepresentable.wordHomEquiv D Sc cutoff N (i :: j :: ρ) τ γ heji hτ
      (wordCross D Sc cutoff N ρ β hρ i j γ hij hji heij heji ≫ t) =
    twist k (D.parity i * D.parity j)
      (VacuumRepresentable.wordHomEquiv D Sc cutoff N (j :: i :: ρ) τ γ heij hτ t) ≫
      wordCrossArrow D Sc cutoff N ρ β hρ i j γ hij hji heij heji := by
  have hg := congrArg (fun f =>
    (VacuumRepresentable.wordIsoAt D Sc cutoff N (i :: j :: ρ) γ heji).inv ≫ f ≫
      (VacuumRepresentable.wordIsoAt D Sc cutoff N (j :: i :: ρ) γ heij).inv)
    (word_cross_intertwine D Sc cutoff N ρ β hρ i j γ hij hji heij heji)
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.inv_hom_id_assoc] at hg
  change ContentYoneda.evaluate D Sc cutoff N γ
    ((VacuumRepresentable.wordIsoAt D Sc cutoff N (i :: j :: ρ) γ heji).inv ≫
      (wordCross D Sc cutoff N ρ β hρ i j γ hij hji heij heji ≫ t) ≫
      (VacuumRepresentable.wordIsoAt D Sc cutoff N τ γ hτ).hom) = _
  rw [← Category.assoc, ← Category.assoc, hg]
  simp only [Category.assoc]
  apply evaluate_precompose D Sc cutoff N
  · exact wordCrossArrow_mem D Sc cutoff N ρ β hρ i j γ hij hji heij heji
  · rw [fromArrow_total D Sc cutoff N _
      (wordCrossArrow_mem D Sc cutoff N ρ β hρ i j γ hij hji heij heji), twist_id,
      Category.comp_id]


/-- Unnormalized diagram crossing with independent canonical endpoints. -/
def wordDiagramCross (ρ : List I) (β : Multiset I) (hρ : VacuumRepresentable.content ρ = β)
    (i j : I) (γ : Multiset I)
    (hij : β + ([i,j] : Multiset I) = γ) (hji : β + ([j,i] : Multiset I) = γ)
    (heij : VacuumRepresentable.content (j :: i :: ρ) = γ)
    (heji : VacuumRepresentable.content (i :: j :: ρ) = γ) :
    VacuumRepresentable.wordObjectAt D Sc cutoff N (j :: i :: ρ) γ heij ⟶
      VacuumRepresentable.wordObjectAt D Sc cutoff N (i :: j :: ρ) γ heji :=
  eqToHom (objectCarrier D Sc cutoff N ρ β hρ i j γ hij heij).symm ≫
    contentAppendToComponent D Sc cutoff N hij hji (crossTwo D Sc i j)
      (VacuumRepresentable.wordObjectAt D Sc cutoff N ρ β hρ) ≫
    eqToHom (objectCarrier D Sc cutoff N ρ β hρ j i γ hji heji)


theorem wordHomEquiv_cross_mixed (ρ τ : List I) (β : Multiset I)
    (hρ : VacuumRepresentable.content ρ = β) (i j : I) (γ : Multiset I)
    (hij : β + ([i,j] : Multiset I) = γ) (hji : β + ([j,i] : Multiset I) = γ)
    (heij : VacuumRepresentable.content (j :: i :: ρ) = γ)
    (heji : VacuumRepresentable.content (i :: j :: ρ) = γ)
    (hτ : VacuumRepresentable.content τ = γ)
    (t : VacuumRepresentable.wordModuleAt D Sc cutoff N (j :: i :: ρ) γ heij ⟶
      VacuumRepresentable.wordModuleAt D Sc cutoff N τ γ hτ) (hne : i ≠ j) :
    VacuumRepresentable.wordHomEquiv D Sc cutoff N (i :: j :: ρ) τ γ heji hτ
      (wordCross D Sc cutoff N ρ β hρ i j γ hij hji heij heji ≫ t) =
    twist k (D.parity i * D.parity j)
      (VacuumRepresentable.wordHomEquiv D Sc cutoff N (j :: i :: ρ) τ γ heij hτ t) ≫
      wordDiagramCross D Sc cutoff N ρ β hρ i j γ hij hji heij heji := by
  rw [wordHomEquiv_cross]
  unfold wordCrossArrow wordDiagramCross
  rw [contentCrossAffine_distinct D Sc i j hne]

theorem wordHomEquiv_cross_equal (ρ τ : List I) (β : Multiset I)
    (hρ : VacuumRepresentable.content ρ = β) (i : I) (γ : Multiset I)
    (hij : β + ([i,i] : Multiset I) = γ) (hji : β + ([i,i] : Multiset I) = γ)
    (heij : VacuumRepresentable.content (i :: i :: ρ) = γ)
    (heji : VacuumRepresentable.content (i :: i :: ρ) = γ)
    (hτ : VacuumRepresentable.content τ = γ)
    (t : VacuumRepresentable.wordModuleAt D Sc cutoff N (i :: i :: ρ) γ heij ⟶
      VacuumRepresentable.wordModuleAt D Sc cutoff N τ γ hτ) :
    VacuumRepresentable.wordHomEquiv D Sc cutoff N (i :: i :: ρ) τ γ heji hτ
      (wordCross D Sc cutoff N ρ β hρ i i γ hij hji heij heji ≫ t) =
    -(twist k (D.parity i * D.parity i)
      (VacuumRepresentable.wordHomEquiv D Sc cutoff N (i :: i :: ρ) τ γ heij hτ t) ≫
      wordDiagramCross D Sc cutoff N ρ β hρ i i γ hij hji heij heji) := by
  rw [wordHomEquiv_cross]
  unfold wordCrossArrow wordDiagramCross
  rw [contentCrossAffine_equal, contentAppendToComponent_neg]
  simp only [Preadditive.neg_comp, Preadditive.comp_neg]

theorem wordHomEquiv_cross_of_mem (ρ τ : List I) (β : Multiset I)
    (hρ : VacuumRepresentable.content ρ = β) (i j : I) (γ : Multiset I)
    (hij : β + ([i,j] : Multiset I) = γ) (hji : β + ([j,i] : Multiset I) = γ)
    (heij : VacuumRepresentable.content (j :: i :: ρ) = γ)
    (heji : VacuumRepresentable.content (i :: j :: ρ) = γ)
    (hτ : VacuumRepresentable.content τ = γ)
    (t : VacuumRepresentable.wordModuleAt D Sc cutoff N (j :: i :: ρ) γ heij ⟶
      VacuumRepresentable.wordModuleAt D Sc cutoff N τ γ hτ)
    (q : ZMod 2)
    (ht : VacuumRepresentable.wordHomEquiv D Sc cutoff N (j :: i :: ρ) τ γ heij hτ t ∈
      parity (R := k) _ _ q) :
    VacuumRepresentable.wordHomEquiv D Sc cutoff N (i :: j :: ρ) τ γ heji hτ
      (wordCross D Sc cutoff N ρ β hρ i j γ hij hji heij heji ≫ t) =
    sign k ((D.parity i * D.parity j) * q) •
      ((VacuumRepresentable.wordHomEquiv D Sc cutoff N (j :: i :: ρ) τ γ heij hτ t) ≫
      wordCrossArrow D Sc cutoff N ρ β hρ i j γ hij hji heij heji) := by
  rw [wordHomEquiv_cross, twist_of_mem _ ht, Linear.smul_comp]

end OddMath.QuiverHecke.ELVOld.VacuumWordPairing
