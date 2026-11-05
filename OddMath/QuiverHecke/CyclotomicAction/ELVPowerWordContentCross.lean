import OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordAppendUnits
import OddMath.QuiverHecke.CyclotomicAction.ELVNormalizedContentRectangularCross
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightRectangularCross
import OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordComposition

/-! # Chosen content crossings in regular-power word coordinates

SwappedVacuumCoordinates §§4–6: identify the chosen content-induction
crossing with the signed old-Hom operator through the prescribed append
comparisons, retaining all exterior coefficients and intermediate labels. -/
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.PowerWordContentCross
universe u
section Generic
variable {k C B : Type u} [CommRing k] [Category.{u} C] [Category.{u} B]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive B] [Linear k B] [Supercategory k B]
  (J : C ⥤ B) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
open BalancedInduction
private def mapLinear {M N : Superfunctor k C (SVec k)} (f : M ⟶ N) (w : B) :
    Obj J M.toFunctor w →ₗ[k] Obj J N.toFunctor w := (moduleMap J f).total w

 theorem even_unit_components {M N : Superfunctor k C (SVec k)} (f : M ⟶ N)
    (s : C) (b : M.obj s) (c : N.obj s)
    (hb : b ∈ (M.obj s).part 0) (hc : c ∈ (N.obj s).part 0)
    (h : f.total s b = c) : f.app 0 s b = c ∧ f.app 1 s b = 0 := by
  have h0 := SVec.apply_mem_part (f.app_mem 0 s) hb
  have h1 := SVec.apply_mem_part (f.app_mem 1 s) hb
  rw [zero_add] at h0 h1
  have hp0 := congrArg ((N.obj s).proj 0) h
  have hp1 := congrArg ((N.obj s).proj 1) h
  change (N.obj s).proj 0 (f.app 0 s b + f.app 1 s b) = _ at hp0
  change (N.obj s).proj 1 (f.app 0 s b + f.app 1 s b) = _ at hp1
  rw [map_add, SVec.proj_apply_of_mem_part _ h0, SVec.proj_apply_of_mem_part _ h1,
    SVec.proj_apply_of_mem_part _ hc] at hp0 hp1
  have hz : (0 : ZMod 2) ≠ 1 := by decide
  have ho : (1 : ZMod 2) ≠ 0 := by decide
  constructor
  · simpa only [ite_true, hz, ho, ite_false, add_zero] using hp0
  · simpa only [hz, ho, ite_false, ite_true, zero_add] using hp1

private theorem moduleMap_tensor_even_unit {M N : Superfunctor k C (SVec k)} (f : M ⟶ N)
    (s : C) (w : B) (g : J.obj s ⟶ w) (b : M.obj s) (c : N.obj s)
    (hb : b ∈ (M.obj s).part 0) (hc : c ∈ (N.obj s).part 0)
    (h : f.total s b = c) :
    mapLinear J f w (tensor J M.toFunctor s g b) = tensor J N.toFunctor s g c := by
  change (moduleMap J f).total w _ = _
  obtain ⟨h0,h1⟩ := even_unit_components f s b c hb hc h
  rw [moduleMap_total_tensor, h0, h1, tensor_zero_right, add_zero]
section Rectangular
variable {A E : Type u} [Category.{u} A] [Category.{u} E]
  [Preadditive A] [Linear k A] [Supercategory k A]
  [Preadditive E] [Linear k E] [Supercategory k E]

private def doubleUnit (K : B ⥤ E) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
    (M : Superfunctor k C (SVec k)) (s : C) (b : M.obj s) :
    (induced K (induced J M)).obj (K.obj (J.obj s)) :=
  unit K (induced J M).toFunctor (J.obj s) (unit J M.toFunctor s b)

private theorem rectangle_unit
    (T : C ⥤ A) [T.Additive] [T.Linear k] [IsSuperfunctor k T]
    (K : C ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
    (L : A ⥤ E) [L.Additive] [L.Linear k] [IsSuperfunctor k L]
    (U : B ⥤ E) [U.Additive] [U.Linear k] [IsSuperfunctor k U]
    {p : ZMod 2} {α : ∀ s, (T ⋙ L).obj s ⟶ (K ⋙ U).obj s}
    (hα : IsSupernatural k p α) (M : Superfunctor k C (SVec k)) (s : C) (b : M.obj s) :
    (rectangularCrossComponent T K L U hα M).total (U.obj (K.obj s)) (doubleUnit K U M s b) =
      tensor L (induced T M).toFunctor (T.obj s) (α s) (unit T M.toFunctor s b) := by
  simp only [doubleUnit, unit_apply]
  erw [rectangularCrossComponent_total_tensor, CategoryTheory.Functor.map_id,
    Category.id_comp, twist_id, Category.comp_id]
private theorem rectangle_unit_image
    (T : C ⥤ A) [T.Additive] [T.Linear k] [IsSuperfunctor k T]
    (K : C ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
    (L : A ⥤ E) [L.Additive] [L.Linear k] [IsSuperfunctor k L]
    (U : B ⥤ E) [U.Additive] [U.Linear k] [IsSuperfunctor k U]
    {p : ZMod 2} {α : ∀ s, (T ⋙ L).obj s ⟶ (K ⋙ U).obj s}
    (hα : IsSupernatural k p α) (M : Superfunctor k C (SVec k))
    {P : Superfunctor k E (SVec k)} (eT : induced L (induced T M) ≅ P)
    (s : C) (b : M.obj s) (a : L.obj (T.obj s) ⟶ U.obj (K.obj s))
    (z : P.obj (U.obj (K.obj s))) (hc : α s = a)
    (hr : eT.hom.total (U.obj (K.obj s))
      (tensor L (induced T M).toFunctor (T.obj s) a (unit T M.toFunctor s b)) = z) :
    eT.hom.total (U.obj (K.obj s))
      ((rectangularCrossComponent T K L U hα M).total (U.obj (K.obj s))
        (doubleUnit K U M s b)) = z := by
  have h₁ := congrArg (eT.hom.total (U.obj (K.obj s))) (rectangle_unit T K L U hα M s b)
  have h₂ := congrArg (fun g : L.obj (T.obj s) ⟶ U.obj (K.obj s) =>
    eT.hom.total (U.obj (K.obj s))
      (tensor L (induced T M).toFunctor (T.obj s) g (unit T M.toFunctor s b))) hc
  exact h₁.trans (h₂.trans hr)

end Rectangular

private theorem comp_total_eval {M N P : Superfunctor k C (SVec k)}
    (f : M ⟶ N) (g : N ⟶ P) (w : C) (x : M.obj w) :
    (f ≫ g).total w x = g.total w (f.total w x) := by
  rw [Superfunctor.comp_total, SVec.comp_apply]

private theorem inverse_at_image {M N : Superfunctor k C (SVec k)} (e : M ≅ N)
    (w : C) (b : M.obj w) (c : N.obj w) (h : e.hom.total w b = c) :
    e.inv.total w c = b := by
  have hi := (moduleIsoLinearEquiv e w).symm_apply_apply b
  change e.inv.total w (e.hom.total w b) = b at hi
  rw [h] at hi
  exact hi

private theorem family_apply_heq {ι : Type u} {A B : ι → Type u}
    (F : ∀ x, A x → B x) {x y : ι} (h : x = y) {a : A x} {b : A y} (hab : HEq a b) :
    HEq (F x a) (F y b) := by
  cases h
  cases hab
  rfl

private theorem eq_of_heq_square {A B : Type u} {a b : A} {c d : B}
    (hac : HEq a c) (hab : a = b) (hbd : HEq b d) : c = d :=
  eq_of_heq (hac.symm.trans ((heq_of_eq hab).trans hbd))

private theorem hom_ext_transfer {M N : Superfunctor k C (SVec k)}
    {x y : C} (hxy : x = y) (b : M.obj x) (c : M.obj y) (hbc : HEq b c)
    (H : Function.Injective (fun f : M ⟶ N => f.total x b)) :
    Function.Injective (fun f : M ⟶ N => f.total y c) := by
  cases hxy
  cases hbc
  exact H

end Generic
open CyclotomicCrossingTensor
variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (L : I × ℕ → ℕ)

private theorem contentAppendIsoTo_canonical (ν : List I) (i : I) :
    PowerWordWeight.contentAppendIsoTo D Sc cutoff L ν i (ν : Multiset I)
      ((ν ++ [i] : List I) : Multiset I) rfl (Multiset.coe_add ν [i]) =
      PowerWordContent.contentAppendIso D Sc cutoff L ν i := rfl

/-- The same frozen selected append comparison at arbitrary equal content labels. -/
theorem content_append_tensor_unit_to (ν : List I) (i : I) (β γ : Multiset I)
    (hν : (ν : Multiset I) = β) (hγ : β + ([i] : Multiset I) = γ)
    (w : ContentCategory D Sc cutoff (PowerWordContent.powerBound D cutoff L) γ)
    (g : (append D Sc cutoff i).obj (OldCategory.mk ν) ⟶ OldCategory.mk w.obj.word) :
    (PowerWordWeight.contentAppendIsoTo D Sc cutoff L ν i β γ hν hγ).hom.total w
      (BalancedInduction.tensor
        (contentAppendTo D Sc cutoff (PowerWordContent.powerBound D cutoff L) β [i] γ hγ)
        (PowerWordWeight.wordAt D Sc cutoff L ν β).toFunctor
        (PowerWordContentCyclicity.wordObject D Sc cutoff L ν β hν)
        (truncateOld D Sc cutoff (PowerWordContent.powerBound D cutoff L) (ν ++ [i]) w.obj.word g)
        (PowerWordContentCyclicity.wordUnit D Sc cutoff L ν β hν)) =
    powerWordGenerator D Sc cutoff L (ν ++ [i]) (OldCategory.mk w.obj.word) g := by
  subst β
  have h : γ = ((ν ++ [i] : List I) : Multiset I) := hγ.symm.trans (Multiset.coe_add ν [i])
  cases h
  rw [contentAppendIsoTo_canonical]
  have hh := PowerWordAppendUnits.content_append_tensor_unit D Sc cutoff L ν i w g
  convert hh using 1
  · rfl
  · apply congrArg ((PowerWordContent.contentAppendIso D Sc cutoff L ν i).hom.total w)
    rfl

omit [Fintype I] in
/-- The source word's content equality after the given append step. -/
theorem appendContentEq (ν : List I) (i : I) (β γ : Multiset I)
    (hν : (ν : Multiset I) = β) (hi : β + ([i] : Multiset I) = γ) :
    ((ν ++ [i] : List I) : Multiset I) = γ :=
  (Multiset.coe_add ν [i]).symm.trans ((congrArg (fun δ => δ + ([i] : Multiset I)) hν).trans hi)

/-- The chosen append comparison sends its actual coend unit to the next word unit. -/
theorem append_unit_to (ν : List I) (i : I) (β γ : Multiset I)
    (hν : (ν : Multiset I) = β) (hi : β + ([i] : Multiset I) = γ) :
    (PowerWordWeight.contentAppendIsoTo D Sc cutoff L ν i β γ hν hi).hom.total
      ((contentAppendTo D Sc cutoff (PowerWordContent.powerBound D cutoff L) β [i] γ hi).obj
        (PowerWordContentCyclicity.wordObject D Sc cutoff L ν β hν))
      (BalancedInduction.unit
        (contentAppendTo D Sc cutoff (PowerWordContent.powerBound D cutoff L) β [i] γ hi)
        (PowerWordWeight.wordAt D Sc cutoff L ν β).toFunctor
        (PowerWordContentCyclicity.wordObject D Sc cutoff L ν β hν)
        (PowerWordContentCyclicity.wordUnit D Sc cutoff L ν β hν)) =
      PowerWordContentCyclicity.wordUnit D Sc cutoff L (ν ++ [i]) γ
        (appendContentEq ν i β γ hν hi) := by
  have hh := content_append_tensor_unit_to D Sc cutoff L ν i β γ hν hi
    ((contentAppendTo D Sc cutoff (PowerWordContent.powerBound D cutoff L) β [i] γ hi).obj
      (PowerWordContentCyclicity.wordObject D Sc cutoff L ν β hν)) (𝟙 _)
  convert hh using 1
  · apply congrArg ((PowerWordWeight.contentAppendIsoTo D Sc cutoff L ν i β γ hν hi).hom.total _)
    rw [BalancedInduction.unit_apply]
    rfl
  · rfl

/-- Recursively chosen single-append comparisons, retaining both actual intermediate labels. -/
def pairIsoTo (ν : List I) (i j : I) (β δ γ : Multiset I)
    (hν : (ν : Multiset I) = β) (hj : β + ([j] : Multiset I) = δ)
    (hi : δ + ([i] : Multiset I) = γ) :
    BalancedInduction.induced
      (contentAppendTo D Sc cutoff (PowerWordContent.powerBound D cutoff L) δ [i] γ hi)
      (BalancedInduction.induced
        (contentAppendTo D Sc cutoff (PowerWordContent.powerBound D cutoff L) β [j] δ hj)
        (PowerWordWeight.wordAt D Sc cutoff L ν β)) ≅
      PowerWordWeight.wordAt D Sc cutoff L ((ν ++ [j]) ++ [i]) γ :=
  (BalancedInduction.induction
    (contentAppendTo D Sc cutoff (PowerWordContent.powerBound D cutoff L) δ [i] γ hi)).mapIso
      (PowerWordWeight.contentAppendIsoTo D Sc cutoff L ν j β δ hν hj) ≪≫
    PowerWordWeight.contentAppendIsoTo D Sc cutoff L (ν ++ [j]) i δ γ
      (appendContentEq ν j β δ hν hj) hi

private def appendLinearTo (ν : List I) (i : I) (β γ : Multiset I)
    (hν : (ν : Multiset I) = β) (hi : β + ([i] : Multiset I) = γ)
    (w : ContentCategory D Sc cutoff (PowerWordContent.powerBound D cutoff L) γ) :
    BalancedInduction.Obj
      (contentAppendTo D Sc cutoff (PowerWordContent.powerBound D cutoff L) β [i] γ hi)
      (PowerWordWeight.wordAt D Sc cutoff L ν β).toFunctor w →ₗ[k]
      (PowerWordWeight.wordAt D Sc cutoff L (ν ++ [i]) γ).obj w :=
  (PowerWordWeight.contentAppendIsoTo D Sc cutoff L ν i β γ hν hi).hom.total w

private def pairLinear (ν : List I) (i j : I) (β δ γ : Multiset I)
    (hν : (ν : Multiset I) = β) (hj : β + ([j] : Multiset I) = δ)
    (hi : δ + ([i] : Multiset I) = γ)
    (w : ContentCategory D Sc cutoff (PowerWordContent.powerBound D cutoff L) γ) :
    BalancedInduction.Obj
      (contentAppendTo D Sc cutoff (PowerWordContent.powerBound D cutoff L) δ [i] γ hi)
      (BalancedInduction.induced
        (contentAppendTo D Sc cutoff (PowerWordContent.powerBound D cutoff L) β [j] δ hj)
        (PowerWordWeight.wordAt D Sc cutoff L ν β)).toFunctor w →ₗ[k]
      (PowerWordWeight.wordAt D Sc cutoff L ((ν ++ [j]) ++ [i]) γ).obj w :=
  (pairIsoTo D Sc cutoff L ν i j β δ γ hν hj hi).hom.total w

private theorem pairLinear_factor (ν : List I) (i j : I) (β δ γ : Multiset I)
    (hν : (ν : Multiset I) = β) (hj : β + ([j] : Multiset I) = δ)
    (hi : δ + ([i] : Multiset I) = γ)
    (w : ContentCategory D Sc cutoff (PowerWordContent.powerBound D cutoff L) γ) :
    pairLinear D Sc cutoff L ν i j β δ γ hν hj hi w =
      (appendLinearTo D Sc cutoff L (ν ++ [j]) i δ γ
        (appendContentEq ν j β δ hν hj) hi w).comp
      (mapLinear
        (contentAppendTo D Sc cutoff (PowerWordContent.powerBound D cutoff L) δ [i] γ hi)
        (PowerWordWeight.contentAppendIsoTo D Sc cutoff L ν j β δ hν hj).hom w) := by
  unfold pairLinear pairIsoTo mapLinear appendLinearTo
  rw [Iso.trans_hom, Functor.mapIso_hom, Superfunctor.comp_total]
  rfl

/-- The recursively selected pair comparison on an arbitrary entire old-arrow
tail and the nested actual coefficient unit. -/
theorem pair_tensor_unit (ν : List I) (i j : I) (β δ γ : Multiset I)
    (hν : (ν : Multiset I) = β) (hj : β + ([j] : Multiset I) = δ)
    (hi : δ + ([i] : Multiset I) = γ)
    (w : ContentCategory D Sc cutoff (PowerWordContent.powerBound D cutoff L) γ)
    (g : (OldCategory.mk ((ν ++ [j]) ++ [i]) : OldCategory D Sc cutoff) ⟶ OldCategory.mk w.obj.word) :
    (pairIsoTo D Sc cutoff L ν i j β δ γ hν hj hi).hom.total w
      (BalancedInduction.tensor
        (contentAppendTo D Sc cutoff (PowerWordContent.powerBound D cutoff L) δ [i] γ hi)
        (BalancedInduction.induced
          (contentAppendTo D Sc cutoff (PowerWordContent.powerBound D cutoff L) β [j] δ hj)
          (PowerWordWeight.wordAt D Sc cutoff L ν β)).toFunctor
        ((contentAppendTo D Sc cutoff (PowerWordContent.powerBound D cutoff L) β [j] δ hj).obj
          (PowerWordContentCyclicity.wordObject D Sc cutoff L ν β hν))
        (truncateOld D Sc cutoff (PowerWordContent.powerBound D cutoff L) ((ν ++ [j]) ++ [i]) w.obj.word g)
        (BalancedInduction.unit
          (contentAppendTo D Sc cutoff (PowerWordContent.powerBound D cutoff L) β [j] δ hj)
          (PowerWordWeight.wordAt D Sc cutoff L ν β).toFunctor
          (PowerWordContentCyclicity.wordObject D Sc cutoff L ν β hν)
          (PowerWordContentCyclicity.wordUnit D Sc cutoff L ν β hν))) =
      powerWordGenerator D Sc cutoff L ((ν ++ [j]) ++ [i]) (OldCategory.mk w.obj.word) g := by
  let J := contentAppendTo D Sc cutoff (PowerWordContent.powerBound D cutoff L) β [j] δ hj
  let U := contentAppendTo D Sc cutoff (PowerWordContent.powerBound D cutoff L) δ [i] γ hi
  let M := PowerWordWeight.wordAt D Sc cutoff L ν β
  let s := PowerWordContentCyclicity.wordObject D Sc cutoff L ν β hν
  let b := PowerWordContentCyclicity.wordUnit D Sc cutoff L ν β hν
  let c := PowerWordContentCyclicity.wordUnit D Sc cutoff L (ν ++ [j]) δ (appendContentEq ν j β δ hν hj)
  have hb := SVec.apply_mem_part (BalancedInduction.unit_mem J M s)
    (PowerWordContentCyclicity.wordUnit_even D Sc cutoff L ν β hν)
  rw [zero_add] at hb
  have hm := moduleMap_tensor_even_unit U
    (PowerWordWeight.contentAppendIsoTo D Sc cutoff L ν j β δ hν hj).hom
    (J.obj s) w
    (truncateOld D Sc cutoff (PowerWordContent.powerBound D cutoff L) ((ν ++ [j]) ++ [i]) w.obj.word g)
    (BalancedInduction.unit J M.toFunctor s b) c hb
    (PowerWordContentCyclicity.wordUnit_even D Sc cutoff L (ν ++ [j]) δ
      (appendContentEq ν j β δ hν hj))
    (append_unit_to D Sc cutoff L ν j β δ hν hj)
  change pairLinear D Sc cutoff L ν i j β δ γ hν hj hi w _ = _
  rw [pairLinear_factor, LinearMap.comp_apply]
  rw [hm]
  have hh := content_append_tensor_unit_to D Sc cutoff L (ν ++ [j]) i δ γ
    (appendContentEq ν j β δ hν hj) hi w g
  change appendLinearTo D Sc cutoff L (ν ++ [j]) i δ γ
    (appendContentEq ν j β δ hν hj) hi w _ = _ at hh
  convert hh using 1
  apply congrArg (appendLinearTo D Sc cutoff L (ν ++ [j]) i δ γ
    (appendContentEq ν j β δ hν hj) hi w)
  rfl

/-- The recursively chosen pair comparison sends the literal nested coend
unit to the actual next-word unit at the same prescribed content. -/
private theorem pair_unit_to (ν : List I) (i j : I) (β δ γ : Multiset I)
    (hν : (ν : Multiset I) = β) (hj : β + ([j] : Multiset I) = δ)
    (hi : δ + ([i] : Multiset I) = γ) :
    let K := contentAppendTo D Sc cutoff (PowerWordContent.powerBound D cutoff L) β [j] δ hj
    let U := contentAppendTo D Sc cutoff (PowerWordContent.powerBound D cutoff L) δ [i] γ hi
    (pairIsoTo D Sc cutoff L ν i j β δ γ hν hj hi).hom.total
      (U.obj (K.obj (PowerWordContentCyclicity.wordObject D Sc cutoff L ν β hν)))
      (doubleUnit K U (PowerWordWeight.wordAt D Sc cutoff L ν β)
        (PowerWordContentCyclicity.wordObject D Sc cutoff L ν β hν)
        (PowerWordContentCyclicity.wordUnit D Sc cutoff L ν β hν)) =
      PowerWordContentCyclicity.wordUnit D Sc cutoff L ((ν ++ [j]) ++ [i]) γ
        (appendContentEq (ν ++ [j]) i δ γ (appendContentEq ν j β δ hν hj) hi) := by
  dsimp only
  have hh := pair_tensor_unit D Sc cutoff L ν i j β δ γ hν hj hi
    ((contentAppendTo D Sc cutoff (PowerWordContent.powerBound D cutoff L) δ [i] γ hi).obj
      ((contentAppendTo D Sc cutoff (PowerWordContent.powerBound D cutoff L) β [j] δ hj).obj
        (PowerWordContentCyclicity.wordObject D Sc cutoff L ν β hν))) (𝟙 _)
  convert hh using 1
  · apply congrArg ((pairIsoTo D Sc cutoff L ν i j β δ γ hν hj hi).hom.total _)
    simp only [doubleUnit, BalancedInduction.unit_apply]
    rfl
  · rfl

/-- The already chosen full old-Hom map, descended on the unchanged word carriers. -/
def weightedWordArrow (s t : List I)
    (g : (OldCategory.mk t : OldCategory D Sc cutoff) ⟶ OldCategory.mk s) :
    PowerWordContent.weightedWord D Sc cutoff L s ⟶ PowerWordContent.weightedWord D Sc cutoff L t :=
  weightedModuleHom D Sc cutoff (PowerWordContent.powerBound D cutoff L)
    (powerWordModule D Sc cutoff L s) (powerWordModule D Sc cutoff L t)
    (PowerWordContent.word_killsWeighted D Sc cutoff L s)
    (PowerWordContent.word_killsWeighted D Sc cutoff L t)
    (PowerWordMorphisms.fromArrow D Sc cutoff L s t g)

/-- Exact-content restriction of the actual full-coefficient word operator. -/
def contentWordArrow (β : Multiset I) (s t : List I)
    (g : (OldCategory.mk t : OldCategory D Sc cutoff) ⟶ OldCategory.mk s) :
    PowerWordWeight.wordAt D Sc cutoff L s β ⟶ PowerWordWeight.wordAt D Sc cutoff L t β :=
  (BalancedInduction.restriction
    (contentInclusion D Sc cutoff (PowerWordContent.powerBound D cutoff L) β)).map
    (weightedWordArrow D Sc cutoff L s t g)

/-- Both homogeneous components are literally retained through descent and restriction. -/
theorem contentWordArrow_total (β : Multiset I) (s t : List I)
    (g : (OldCategory.mk t : OldCategory D Sc cutoff) ⟶ OldCategory.mk s)
    (w : ContentCategory D Sc cutoff (PowerWordContent.powerBound D cutoff L) β) :
    (contentWordArrow D Sc cutoff L β s t g).total w =
      (PowerWordMorphisms.fromArrow D Sc cutoff L s t g).total (OldCategory.mk w.obj.word) := rfl

/-- Evaluation on the actual even word unit is the full old-arrow generator. -/
theorem contentWordArrow_unit (β : Multiset I) (s t : List I) (hs : (s : Multiset I) = β)
    (g : (OldCategory.mk t : OldCategory D Sc cutoff) ⟶ OldCategory.mk s) :
    (contentWordArrow D Sc cutoff L β s t g).total
      (PowerWordContentCyclicity.wordObject D Sc cutoff L s β hs)
      (PowerWordContentCyclicity.wordUnit D Sc cutoff L s β hs) =
      powerWordGenerator D Sc cutoff L t (OldCategory.mk s) g := by
  rw [contentWordArrow_total]
  change PowerWordYoneda.evaluate D Sc cutoff L s (powerWordObject D Sc cutoff L t)
    (PowerWordMorphisms.fromArrow D Sc cutoff L s t g) = _
  exact (PowerWordYoneda.homEquiv D Sc cutoff L s (powerWordObject D Sc cutoff L t)).apply_symm_apply _

/-- The original normalized physical crossing, with the required extra minus
in equal colour and positive representative in distinct colours. -/
def normalizedOldCross (ν : List I) (i j : I) :
    (OldCategory.mk ((ν ++ [i]) ++ [j]) : OldCategory D Sc cutoff) ⟶
      OldCategory.mk ((ν ++ [j]) ++ [i]) :=
  if i = j then -Distinct.crossComponent D Sc cutoff j i (OldCategory.mk ν)
  else Distinct.crossComponent D Sc cutoff j i (OldCategory.mk ν)

/-- The full signed old-Hom crossing in the actual scheduled content word carriers. -/
def wordCross (β : Multiset I) (ν : List I) (i j : I) :
    PowerWordWeight.wordAt D Sc cutoff L ((ν ++ [j]) ++ [i]) β ⟶
      PowerWordWeight.wordAt D Sc cutoff L ((ν ++ [i]) ++ [j]) β :=
  contentWordArrow D Sc cutoff L β ((ν ++ [j]) ++ [i]) ((ν ++ [i]) ++ [j])
    (normalizedOldCross D Sc cutoff ν i j)

/-- The normalized physical crossing descends literally through the actual
old-to-weighted quotient at every prescribed content successor. -/
theorem normalizedOldCross_quotient (ν : List I) (β : Multiset I) (hν : (ν : Multiset I) = β)
    (i j : I) (δj δi γ : Multiset I)
    (hj : β + ([j] : Multiset I) = δj) (hi : β + ([i] : Multiset I) = δi)
    (hSource : δj + ([i] : Multiset I) = γ) (hTarget : δi + ([j] : Multiset I) = γ) :
    (oldTruncateFunctor D Sc cutoff (PowerWordContent.powerBound D cutoff L)).map
      (normalizedOldCross D Sc cutoff ν i j) =
      normalizedContentTargetsCross D Sc cutoff (PowerWordContent.powerBound D cutoff L)
        β j i δi δj γ hi hj hTarget hSource
        (PowerWordContentCyclicity.wordObject D Sc cutoff L ν β hν) := by
  by_cases h : i = j
  · subst j
    simp only [normalizedOldCross, normalizedContentTargetsCross, contentDistinctTargetsCross, ite_true,
      Functor.map_neg, oldTruncateFunctor_map_distinctCross]
    rfl
  · simp only [normalizedOldCross, normalizedContentTargetsCross, ite_eq_right h,
      ite_eq_right (Ne.symm h)]
    exact oldTruncateFunctor_map_distinctCross D Sc cutoff (PowerWordContent.powerBound D cutoff L)
      j i (OldCategory.mk ν)

omit [Fintype I] in
private theorem append_obj_word (N : ℕ) (β : Multiset I) (σ : List I) (γ : Multiset I)
    (h : β + (σ : Multiset I) = γ) (s : ContentCategory D Sc cutoff N β) :
    ((contentAppendTo D Sc cutoff N β σ γ h).obj s).obj.word = s.obj.word ++ σ := rfl

private theorem wordObject_word (ν : List I) (β : Multiset I) (hν : (ν : Multiset I) = β) :
    (PowerWordContentCyclicity.wordObject D Sc cutoff L ν β hν).obj.word = ν := rfl

omit [Fintype I] in
private theorem pairContentEq (β δ γ : Multiset I) (i j : I)
    (hj : β + ([j] : Multiset I) = δ) (hi : δ + ([i] : Multiset I) = γ) :
    β + ([j,i] : Multiset I) = γ := by
  change β + (([j] ++ [i] : List I) : Multiset I) = γ
  rw [← Multiset.coe_add, ← add_assoc, hj, hi]

section UnitWord
variable (ν : List I) (β : Multiset I) (hν : (ν : Multiset I) = β)
  (i j : I) (δj δi γ : Multiset I)
  (hj : β + ([j] : Multiset I) = δj) (hi : β + ([i] : Multiset I) = δi)
  (hSource : δj + ([i] : Multiset I) = γ) (hTarget : δi + ([j] : Multiset I) = γ)
local notation "CT" => contentAppendTo D Sc cutoff (PowerWordContent.powerBound D cutoff L) β [i] δi hi
local notation "CK" => contentAppendTo D Sc cutoff (PowerWordContent.powerBound D cutoff L) β [j] δj hj
local notation "CL" => contentAppendTo D Sc cutoff (PowerWordContent.powerBound D cutoff L) δi [j] γ hTarget
local notation "CU" => contentAppendTo D Sc cutoff (PowerWordContent.powerBound D cutoff L) δj [i] γ hSource
local notation "CM" => PowerWordWeight.wordAt D Sc cutoff L ν β
local notation "CS" => PowerWordContentCyclicity.wordObject D Sc cutoff L ν β hν
local notation "CB" => PowerWordContentCyclicity.wordUnit D Sc cutoff L ν β hν
local notation "CW" => CategoryTheory.Functor.obj CU (CategoryTheory.Functor.obj CK CS)
local notation "CH" => normalizedContentTargetsCross_supernatural D Sc cutoff (PowerWordContent.powerBound D cutoff L)
  β j i δi δj γ hi hj hTarget hSource
local notation "ET" => pairIsoTo D Sc cutoff L ν j i β δi γ hν hi hTarget
local notation "CG" => normalizedOldCross D Sc cutoff ν i j
local notation "CA" => truncateOld D Sc cutoff (PowerWordContent.powerBound D cutoff L)
  ((ν ++ [i]) ++ [j]) (TruncatedCategory.word (ContentCategory.obj CW)) CG
local notation "CZ" => powerWordGenerator D Sc cutoff L ((ν ++ [i]) ++ [j]) (OldCategory.mk (TruncatedCategory.word (ContentCategory.obj CW))) CG

private theorem rectangular_unit_word :
    (ET).hom.total CW ((BalancedInduction.rectangularCrossComponent CT CK CL CU CH CM).total CW
      (doubleUnit CK CU CM CS CB)) = CZ := by
  apply rectangle_unit_image CT CK CL CU CH CM ET CS CB CA CZ
  · have hc := normalizedOldCross_quotient D Sc cutoff L ν β hν i j δj δi γ hj hi hSource hTarget
    simpa only [oldTruncateFunctor, append_obj_word, wordObject_word] using hc.symm
  · exact pair_tensor_unit D Sc cutoff L ν j i β δi γ hν hi hTarget CW CG
local notation "ES" => pairIsoTo D Sc cutoff L ν i j β δj γ hν hj hSource
local notation "HS" => appendContentEq (ν ++ [j]) i δj γ (appendContentEq ν j β δj hν hj) hSource
local notation "CSW" => PowerWordContentCyclicity.wordObject D Sc cutoff L ((ν ++ [j]) ++ [i]) γ HS
local notation "CUB" => PowerWordContentCyclicity.wordUnit D Sc cutoff L ((ν ++ [j]) ++ [i]) γ HS
local notation "CX" => BalancedInduction.rectangularCrossComponent CT CK CL CU CH CM
local notation "WW" => wordCross D Sc cutoff L γ ν i j

private theorem inverse_pair_unit :
    (ES).inv.total CW CUB = doubleUnit CK CU CM CS CB := by
  exact inverse_at_image ES CW _ CUB (pair_unit_to D Sc cutoff L ν i j β δj γ hν hj hSource)

/-- The independently chosen normalized rectangular crossing is the full signed
old-Hom word operator through the recursively selected pair comparisons.
All actual intermediate labels and all exterior coefficient vectors are retained. -/
theorem selected_pair_cross :
    CX ≫ (ET).hom = (ES).hom ≫ WW := by
  have hObj : CSW = CW := rfl
  have hExt : Function.Injective (fun f :
      PowerWordWeight.wordAt D Sc cutoff L ((ν ++ [j]) ++ [i]) γ ⟶
        PowerWordWeight.wordAt D Sc cutoff L ((ν ++ [i]) ++ [j]) γ => f.total CW CUB) := by
    apply hom_ext_transfer hObj CUB CUB (HEq.refl CUB)
    intro f g h
    exact PowerWordContentCyclicity.hom_ext D Sc cutoff L ((ν ++ [j]) ++ [i]) γ HS
      (PowerWordWeight.wordAt D Sc cutoff L ((ν ++ [i]) ++ [j]) γ) f g h
  have hconj : (ES).inv ≫ CX ≫ (ET).hom = WW := by
    apply hExt
    change ((ES).inv ≫ CX ≫ (ET).hom).total CW CUB = (WW).total CW CUB
    rw [comp_total_eval, comp_total_eval, inverse_pair_unit]
    have hr := rectangular_unit_word D Sc cutoff L ν β hν i j δj δi γ hj hi hSource hTarget
    have ho := contentWordArrow_unit D Sc cutoff L γ ((ν ++ [j]) ++ [i]) ((ν ++ [i]) ++ [j]) HS CG
    change (WW).total CSW CUB =
      PowerWordContentCyclicity.generator D Sc cutoff L ((ν ++ [i]) ++ [j]) γ CSW CG at ho
    have he := family_apply_heq
      (A := fun x : ContentCategory D Sc cutoff (PowerWordContent.powerBound D cutoff L) γ =>
        (PowerWordWeight.wordAt D Sc cutoff L ((ν ++ [j]) ++ [i]) γ).obj x)
      (B := fun x : ContentCategory D Sc cutoff (PowerWordContent.powerBound D cutoff L) γ =>
        (PowerWordWeight.wordAt D Sc cutoff L ((ν ++ [i]) ++ [j]) γ).obj x)
      (fun x z => (WW).total x z) hObj (HEq.refl CUB)
    have hg := family_apply_heq
      (A := fun x : ContentCategory D Sc cutoff (PowerWordContent.powerBound D cutoff L) γ =>
        (OldCategory.mk ((ν ++ [i]) ++ [j]) : OldCategory D Sc cutoff) ⟶ OldCategory.mk x.obj.word)
      (B := fun x : ContentCategory D Sc cutoff (PowerWordContent.powerBound D cutoff L) γ =>
        (PowerWordWeight.wordAt D Sc cutoff L ((ν ++ [i]) ++ [j]) γ).obj x)
      (fun x g => PowerWordContentCyclicity.generator D Sc cutoff L ((ν ++ [i]) ++ [j]) γ x g)
      hObj (HEq.refl CG)
    have hWord := eq_of_heq_square he ho hg
    change (ET).hom.total CW ((CX).total CW (doubleUnit CK CU CM CS CB)) =
      PowerWordContentCyclicity.generator D Sc cutoff L ((ν ++ [i]) ++ [j]) γ CW CG at hr
    exact hr.trans hWord.symm
  have hh := congrArg (fun f => (ES).hom ≫ f) hconj
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hh
local notation "HJI" => pairContentEq β δj γ i j hj hSource
local notation "HIJ" => pairContentEq β δi γ j i hi hTarget

end UnitWord

end OddMath.QuiverHecke.ELVOld.PowerWordContentCross
