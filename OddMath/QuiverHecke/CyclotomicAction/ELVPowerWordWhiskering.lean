import OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordPairCrossing
import OddMath.QuiverHecke.CyclotomicAction.ELVDistinctModuleMate
import OddMath.Algebra.FiniteSupermoduleFunctor

/-! # Selected word comparison and induction of signed old-Hom maps

SwappedVacuumCoordinates §§4–5 require compatibility with arbitrary right
contexts, beyond the last dot and crossing. The selected append comparison
is used to identify the independently induced old-Hom module map.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.PowerWordWhiskering
open CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (L : I × ℕ → ℕ)
  (s t : List I) (i : I)

private def comparisonIso {C B E : Type u} [Category.{u} C] [Category.{u} B] [Category.{u} E]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    [Preadditive E] [Linear k E] [Supercategory k E]
    (J : C ⥤ B) (K : B ⥤ E) (P : C ⥤ E)
    [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    [K.Additive] [K.Linear k] [IsSuperfunctor k K]
    [P.Additive] [P.Linear k] [IsSuperfunctor k P] (e : J ⋙ K = P)
    (R : Superfunctor k C (SVec k)) :
    (BalancedInduction.induction K).obj (BalancedInduction.induced J R) ≅
      (BalancedInduction.induction P).obj R := (inductionCompOfEq J K P e).app R

private def inducedTransform {C B : Type u} [Category.{u} C] [Category.{u} B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    (J K : C ⥤ B) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    [K.Additive] [K.Linear k] [IsSuperfunctor k K]
    {p : ZMod 2} {α : ∀ v, J.obj v ⟶ K.obj v} (hα : IsSupernatural k p α)
    (R : Superfunctor k C (SVec k)) :
    (BalancedInduction.induction K).obj R ⟶ (BalancedInduction.induction J).obj R :=
  BalancedInduction.transformComponent hα R

private theorem total_of_mem {C B : Type*} [Category* C] [Category* B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    {F G : Superfunctor k C B} {p : ZMod 2} {f : F ⟶ G}
    (hf : f ∈ parity (R := k) _ _ p) (z : C) : f.total z = f.app p z := by
  rcases parity_eq_zero_or_one p with rfl | rfl
  · rw [SuperNatTrans.total, Superfunctor.app_eq_zero_of_mem hf (q := 1) (by decide), add_zero]
  · rw [SuperNatTrans.total, Superfunctor.app_eq_zero_of_mem hf (q := 0) (by decide), zero_add]
section Inner
variable {C B E : Type u} [Category.{u} C] [Category.{u} B] [Category.{u} E]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive B] [Linear k B] [Supercategory k B]
  [Preadditive E] [Linear k E] [Supercategory k E]
  (J₀ J₁ : C ⥤ B) (K : B ⥤ E) (P₀ P₁ : C ⥤ E)
  [J₀.Additive] [J₀.Linear k] [IsSuperfunctor k J₀]
  [J₁.Additive] [J₁.Linear k] [IsSuperfunctor k J₁]
  [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  [P₀.Additive] [P₀.Linear k] [IsSuperfunctor k P₀]
  [P₁.Additive] [P₁.Linear k] [IsSuperfunctor k P₁]
  (e₀ : J₀ ⋙ K = P₀) (e₁ : J₁ ⋙ K = P₁)
  {p : ZMod 2} {α : ∀ v, J₀.obj v ⟶ J₁.obj v} (hα : IsSupernatural k p α)
  {β : ∀ v, P₀.obj v ⟶ P₁.obj v} (hβ : IsSupernatural k p β)
  (R : Superfunctor k C (SVec k))
private def innerEquation : Prop :=
  (BalancedInduction.induction K).map (inducedTransform J₀ J₁ hα R) ≫
    (comparisonIso J₀ K P₀ e₀ R).hom =
  (comparisonIso J₁ K P₁ e₁ R).hom ≫ inducedTransform P₀ P₁ hβ R
private theorem inner_hom (hαβ : ∀ v, HEq (K.map (α v)) (β v)) :
    innerEquation J₀ J₁ K P₀ P₁ e₀ e₁ hα hβ R := by
  unfold innerEquation comparisonIso inducedTransform
  simp only [Iso.app_hom]
  subst P₀
  subst P₁
  have hb : (fun v => K.map (α v)) = β := funext (fun v => eq_of_heq (hαβ v))
  subst β
  simp only [inductionCompOfEq, eqToIso_refl, Iso.trans_refl]
  have hc₀ := BalancedInduction.inductionComp_hom_mem J₀ K R
  have hc₁ := BalancedInduction.inductionComp_hom_mem J₁ K R
  have hx := IsSuperfunctor.map_mem (F := BalancedInduction.induction K)
    (BalancedInduction.transformComponent_mem hα R)
  have hy := BalancedInduction.transformComponent_mem hβ R
  apply FiniteSupermodule.hom_ext_total
  intro w
  rw [Superfunctor.comp_total, Superfunctor.comp_total,
    total_of_mem hx, total_of_mem hy, total_of_mem hc₀, total_of_mem hc₁,
    BalancedInduction.transformComponent_app, ite_eq_left rfl]
  change BalancedInduction.compForward J₀ K R w ∘ₗ
      BalancedInduction.mapComponent K (BalancedInduction.transformComponent hα R) p w =
    BalancedInduction.transformLinear hβ R w ∘ₗ BalancedInduction.compForward J₁ K R w
  exact BalancedInduction.compForward_transform_inner K hα R w
end Inner

private def appendEquation {C B : Type u} [Category.{u} C] [Category.{u} B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    (K : C ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
    {P Q : Superfunctor k C (SVec k)} {V W : Superfunctor k B (SVec k)}
    (e : (BalancedInduction.induction K).obj P ≅ V)
    (f : (BalancedInduction.induction K).obj Q ≅ W) (x : P ⟶ Q) (y : V ⟶ W) : Prop :=
  (BalancedInduction.induction K).map x ≫ f.hom = e.hom ≫ y

section Chosen
variable {C B E : Type u} [Category.{u} C] [Category.{u} B] [Category.{u} E]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive B] [Linear k B] [Supercategory k B]
  [Preadditive E] [Linear k E] [Supercategory k E]
  (J₀ J₁ : C ⥤ B) (K : B ⥤ E) (P₀ P₁ : C ⥤ E)
  [J₀.Additive] [J₀.Linear k] [IsSuperfunctor k J₀]
  [J₁.Additive] [J₁.Linear k] [IsSuperfunctor k J₁]
  [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  [P₀.Additive] [P₀.Linear k] [IsSuperfunctor k P₀]
  [P₁.Additive] [P₁.Linear k] [IsSuperfunctor k P₁]
  (e₀ : J₀ ⋙ K = P₀) (e₁ : J₁ ⋙ K = P₁)
  {p : ZMod 2} {α : ∀ v, J₀.obj v ⟶ J₁.obj v} (hα : IsSupernatural k p α)
  {β : ∀ v, P₀.obj v ⟶ P₁.obj v} (hβ : IsSupernatural k p β)
  (R : Superfunctor k C (SVec k))
private theorem inner_chosen (hαβ : ∀ v, HEq (K.map (α v)) (β v))
    (e : (BalancedInduction.induction K).obj (BalancedInduction.induced J₁ R) ≅
      (BalancedInduction.induction P₁).obj R)
    (f : (BalancedInduction.induction K).obj (BalancedInduction.induced J₀ R) ≅
      (BalancedInduction.induction P₀).obj R)
    (x : BalancedInduction.induced J₁ R ⟶ BalancedInduction.induced J₀ R)
    (y : (BalancedInduction.induction P₁).obj R ⟶ (BalancedInduction.induction P₀).obj R)
    (he : e = comparisonIso J₁ K P₁ e₁ R) (hf : f = comparisonIso J₀ K P₀ e₀ R)
    (hx : x = inducedTransform J₀ J₁ hα R) (hy : y = inducedTransform P₀ P₁ hβ R) :
    appendEquation K e f x y := by
  subst e
  subst f
  subst x
  subst y
  exact inner_hom J₀ J₁ K P₀ P₁ e₀ e₁ hα hβ R hαβ
end Chosen

/-- The selected append comparison intertwines induction of every homogeneous
signed old-Hom map with the literal appended old arrow. The input vector
is arbitrary, including all exterior coefficient classes. -/
theorem append_fromArrow {p : ZMod 2}
    (g : (OldCategory.mk t : OldCategory D Sc cutoff) ⟶ OldCategory.mk s)
    (hg : g ∈ parity (R := k) _ _ p) :
    appendEquation (append D Sc cutoff i)
      (powerWordAppendIso D Sc cutoff L s i) (powerWordAppendIso D Sc cutoff L t i)
      (PowerWordMorphisms.fromArrow D Sc cutoff L s t g)
      (PowerWordMorphisms.fromArrow D Sc cutoff L (s ++ [i]) (t ++ [i])
        ((append D Sc cutoff i).map g)) :=
  inner_chosen (powerWordCoefficientSource D Sc cutoff t) (powerWordCoefficientSource D Sc cutoff s)
    (append D Sc cutoff i) (powerWordCoefficientSource D Sc cutoff (t ++ [i]))
    (powerWordCoefficientSource D Sc cutoff (s ++ [i]))
    (powerWordCoefficientSource_append D Sc cutoff t i)
    (powerWordCoefficientSource_append D Sc cutoff s i)
    (PowerWordMorphisms.coefficientSourceNatural D Sc cutoff s t g hg)
    (PowerWordMorphisms.coefficientSourceNatural D Sc cutoff (s ++ [i]) (t ++ [i])
      ((append D Sc cutoff i).map g) (IsSuperfunctor.map_mem (F := append D Sc cutoff i) hg))
    (liftedPowerRegular D cutoff L) (fun _ => HEq.rfl)
    (powerWordAppendIso D Sc cutoff L s i) (powerWordAppendIso D Sc cutoff L t i)
    (PowerWordMorphisms.fromArrow D Sc cutoff L s t g)
    (PowerWordMorphisms.fromArrow D Sc cutoff L (s ++ [i]) (t ++ [i]) ((append D Sc cutoff i).map g))
    (PowerWordPair.selectedAppend_eq D Sc cutoff L s i)
    (PowerWordPair.selectedAppend_eq D Sc cutoff L t i)
    (PowerWordMorphisms.fromArrow_eq_transform D Sc cutoff L s t g hg)
    (PowerWordMorphisms.fromArrow_eq_transform D Sc cutoff L (s ++ [i]) (t ++ [i])
      ((append D Sc cutoff i).map g) (IsSuperfunctor.map_mem (F := append D Sc cutoff i) hg))

/-- The full old-Hom chart is additive, including inhomogeneous arrows. -/
theorem fromArrow_add
    (g h : (OldCategory.mk t : OldCategory D Sc cutoff) ⟶ OldCategory.mk s) :
    PowerWordMorphisms.fromArrow D Sc cutoff L s t (g + h) =
      PowerWordMorphisms.fromArrow D Sc cutoff L s t g +
        PowerWordMorphisms.fromArrow D Sc cutoff L s t h := by
  unfold PowerWordMorphisms.fromArrow
  rw [map_add]
  exact (PowerWordYoneda.homEquiv D Sc cutoff L s (powerWordObject D Sc cutoff L t)).symm.map_add _ _

private theorem appendEquation_add {C B : Type u} [Category.{u} C] [Category.{u} B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    (K : C ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
    {P Q : Superfunctor k C (SVec k)} {V W : Superfunctor k B (SVec k)}
    (e : (BalancedInduction.induction K).obj P ≅ V)
    (f : (BalancedInduction.induction K).obj Q ≅ W) (x₀ x₁ : P ⟶ Q) (y₀ y₁ : V ⟶ W)
    (h₀ : appendEquation K e f x₀ y₀) (h₁ : appendEquation K e f x₁ y₁) :
    appendEquation K e f (x₀ + x₁) (y₀ + y₁) := by
  unfold appendEquation at *
  rw [Functor.map_add, Preadditive.add_comp, Preadditive.comp_add, h₀, h₁]

/-- The chosen append square for an arbitrary full old arrow: both parity
components are retained, and the module vector is unrestricted. -/
theorem append_fromArrow_all
    (g : (OldCategory.mk t : OldCategory D Sc cutoff) ⟶ OldCategory.mk s) :
    appendEquation (append D Sc cutoff i)
      (powerWordAppendIso D Sc cutoff L s i) (powerWordAppendIso D Sc cutoff L t i)
      (PowerWordMorphisms.fromArrow D Sc cutoff L s t g)
      (PowerWordMorphisms.fromArrow D Sc cutoff L (s ++ [i]) (t ++ [i])
        ((append D Sc cutoff i).map g)) := by
  have h₀ := append_fromArrow D Sc cutoff L s t i (proj k 0 g) (proj_mem 0 g)
  have h₁ := append_fromArrow D Sc cutoff L s t i (proj k 1 g) (proj_mem 1 g)
  have hsum := appendEquation_add (append D Sc cutoff i)
    (powerWordAppendIso D Sc cutoff L s i) (powerWordAppendIso D Sc cutoff L t i)
    _ _ _ _ h₀ h₁
  rw [← fromArrow_add, ← fromArrow_add, ← Functor.map_add, proj_add_proj] at hsum
  exact hsum

end OddMath.QuiverHecke.ELVOld.PowerWordWhiskering
