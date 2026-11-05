import OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordAppendDot
import OddMath.QuiverHecke.CyclotomicAction.ELVContentWhiskering
import OddMath.QuiverHecke.CyclotomicAction.ELVContentComparisonCoherence
import OddMath.QuiverHecke.CyclotomicAction.ELVOldModuleAdjunction
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionCrossTensor

/-! Selected recursive word comparisons and the actual signed equal-colour
crossing, via existing whole-comparison coherence and outer recasting. -/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.PowerWordPair
open CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (L : I × ℕ → ℕ)
  (ν : List I) (i : I)

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
    (J : C ⥤ B) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {p : ZMod 2} {α : ∀ v, J.obj v ⟶ J.obj v} (hα : IsSupernatural k p α)
    (R : Superfunctor k C (SVec k)) :
    (BalancedInduction.induction J).obj R ⟶ (BalancedInduction.induction J).obj R :=
  BalancedInduction.transformComponent hα R

section Recursive
variable {C B : Type u} [Category.{u} C] [Category.{u} B]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive B] [Linear k B] [Supercategory k B]
  (J : C ⥤ B) (K : B ⥤ B) (P Q : C ⥤ B)
  [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  [P.Additive] [P.Linear k] [IsSuperfunctor k P]
  [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
  (eP : J ⋙ K = P) (eQ : P ⋙ K = Q) (R : Superfunctor k C (SVec k))
private def recursiveIso :
    (BalancedInduction.induction K ⋙ BalancedInduction.induction K).obj
      (BalancedInduction.induced J R) ≅ (BalancedInduction.induction Q).obj R :=
  (BalancedInduction.induction K).mapIso (comparisonIso J K P eP R) ≪≫
    comparisonIso P K Q eQ R
private def recursiveEquation (e : J ⋙ (K ⋙ K) = Q) : Prop :=
    (recursiveIso J K P Q eP eQ R).hom =
      ((inductionCompOfEq K K (K ⋙ K) rfl).app (BalancedInduction.induced J R)).hom ≫
        (comparisonIso J (K ⋙ K) Q e R).hom
private theorem recursiveIso_hom (e : J ⋙ (K ⋙ K) = Q) :
    recursiveEquation J K P Q eP eQ R e := by
  unfold recursiveEquation recursiveIso comparisonIso
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
  exact inductionCompOfEq_assoc_hom J K K P (K ⋙ K) Q eP rfl eQ e R
end Recursive

section Outer
private theorem total_of_mem {C B : Type*} [Category* C] [Category* B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    {F G : Superfunctor k C B} {p : ZMod 2} {f : F ⟶ G}
    (hf : f ∈ parity (R := k) _ _ p) (z : C) : f.total z = f.app p z := by
  rcases parity_eq_zero_or_one p with rfl | rfl
  · rw [SuperNatTrans.total, Superfunctor.app_eq_zero_of_mem hf (q := 1) (by decide), add_zero]
  · rw [SuperNatTrans.total, Superfunctor.app_eq_zero_of_mem hf (q := 0) (by decide), zero_add]
private theorem homogeneous_total_ext {C B : Type*} [Category* C] [Category* B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    {F G : Superfunctor k C B} {p : ZMod 2} {f g : F ⟶ G}
    (hf : f ∈ parity (R := k) _ _ p) (hg : g ∈ parity (R := k) _ _ p)
    (h : ∀ z, f.total z = g.total z) : f = g := by
  apply SuperNatTrans.ext
  funext q z
  by_cases hq : q = p
  · subst q
    rw [← total_of_mem hf, ← total_of_mem hg]
    exact h z
  · rw [Superfunctor.app_eq_zero_of_mem hf hq, Superfunctor.app_eq_zero_of_mem hg hq]
private def outerEquation {C B E : Type u} [Category.{u} C] [Category.{u} B] [Category.{u} E]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    [Preadditive E] [Linear k E] [Supercategory k E]
    (J : C ⥤ B) (K : B ⥤ E) (P : C ⥤ E)
    [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    [K.Additive] [K.Linear k] [IsSuperfunctor k K]
    [P.Additive] [P.Linear k] [IsSuperfunctor k P] (e : J ⋙ K = P)
    {p : ZMod 2} {β : ∀ w, K.obj w ⟶ K.obj w} (hβ : IsSupernatural k p β)
    {α : ∀ v, P.obj v ⟶ P.obj v} (hα : IsSupernatural k p α)
    (R : Superfunctor k C (SVec k)) : Prop :=
    inducedTransform K hβ (BalancedInduction.induced J R) ≫
      (comparisonIso J K P e R).hom =
    (comparisonIso J K P e R).hom ≫ inducedTransform P hα R

private theorem outer_hom {C B E : Type u} [Category.{u} C] [Category.{u} B] [Category.{u} E]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    [Preadditive E] [Linear k E] [Supercategory k E]
    (J : C ⥤ B) (K : B ⥤ E) (P : C ⥤ E)
    [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    [K.Additive] [K.Linear k] [IsSuperfunctor k K]
    [P.Additive] [P.Linear k] [IsSuperfunctor k P] (e : J ⋙ K = P)
    {p : ZMod 2} {β : ∀ w, K.obj w ⟶ K.obj w} (hβ : IsSupernatural k p β)
    {α : ∀ v, P.obj v ⟶ P.obj v} (hα : IsSupernatural k p α)
    (hβα : ∀ v, HEq (β (J.obj v)) (α v)) (R : Superfunctor k C (SVec k)) :
    outerEquation J K P e hβ hα R := by
  unfold outerEquation comparisonIso inducedTransform
  simp only [Iso.app_hom]
  subst P
  have ha : (fun v => β (J.obj v)) = α := funext (fun v => eq_of_heq (hβα v))
  subst α
  simp only [inductionCompOfEq, eqToIso_refl, Iso.trans_refl]
  have hc : (BalancedInduction.inductionComp J K).hom.app R ∈ parity (R := k)
      (BalancedInduction.induced K (BalancedInduction.induced J R))
      (BalancedInduction.induced (J ⋙ K) R) 0 :=
    BalancedInduction.inductionComp_hom_mem J K R
  have hx : BalancedInduction.transformComponent hβ (BalancedInduction.induced J R) ∈
      parity (R := k) (BalancedInduction.induced K (BalancedInduction.induced J R))
        (BalancedInduction.induced K (BalancedInduction.induced J R)) p :=
    BalancedInduction.transformComponent_mem hβ (BalancedInduction.induced J R)
  have hy : BalancedInduction.transformComponent hα R ∈ parity (R := k)
      (BalancedInduction.induced (J ⋙ K) R) (BalancedInduction.induced (J ⋙ K) R) p :=
    BalancedInduction.transformComponent_mem hα R
  apply homogeneous_total_ext
    (F := BalancedInduction.induced K (BalancedInduction.induced J R))
    (G := BalancedInduction.induced (J ⋙ K) R)
    (by simpa only [add_zero] using comp_mem hx hc)
    (by simpa only [zero_add] using comp_mem hc hy)
  intro w
  rw [Superfunctor.comp_total, Superfunctor.comp_total,
    total_of_mem hx, total_of_mem hy, total_of_mem hc,
    BalancedInduction.transformComponent_app, BalancedInduction.transformComponent_app,
    ite_eq_left rfl, ite_eq_left rfl]
  change BalancedInduction.compForward J K R w ∘ₗ
      BalancedInduction.transformLinear hβ (BalancedInduction.induced J R) w =
    BalancedInduction.transformLinear hα R w ∘ₗ BalancedInduction.compForward J K R w
  exact BalancedInduction.compForward_transform_outer J hβ R w
end Outer

private def signedComparisonEquation {C : Type*} [Category* C] [Preadditive C]
    {A E : C} (s : A ⟶ A) (g : A ⟶ E) (n : E ⟶ E) : Prop :=
  s ≫ g = g ≫ (-n)
private theorem signed_by_comparison {C : Type*} [Category* C] [Preadditive C]
    {A B E : C} (e₀ e : A ≅ B) (f : B ⟶ E) (g : A ⟶ E)
    (x : B ⟶ B) (n : E ⟶ E) (s : A ⟶ A)
    (he : e₀ = e) (hg : g = e₀.hom ≫ f) (hx : x ≫ f = f ≫ n)
    (hs : s = -(e.hom ≫ x ≫ e.inv)) : signedComparisonEquation s g n := by
  subst e₀
  unfold signedComparisonEquation
  rw [hs, hg, Preadditive.neg_comp, Preadditive.comp_neg]
  apply congrArg Neg.neg
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [hx]

private theorem refl_comparison {C B E : Type u} [Category.{u} C] [Category.{u} B] [Category.{u} E]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    [Preadditive E] [Linear k E] [Supercategory k E]
    (J : C ⥤ B) (K : B ⥤ E)
    [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    [K.Additive] [K.Linear k] [IsSuperfunctor k K]
    (R : Superfunctor k C (SVec k)) :
    (inductionCompOfEq J K (J ⋙ K) rfl).app R = (BalancedInduction.inductionComp J K).app R := by
  simp only [inductionCompOfEq, eqToIso_refl, Iso.trans_refl]

section Signed
variable {C B : Type u} [Category.{u} C] [Category.{u} B]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive B] [Linear k B] [Supercategory k B]
  (J : C ⥤ B) (K : B ⥤ B) (P Q : C ⥤ B)
  [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  [P.Additive] [P.Linear k] [IsSuperfunctor k P]
  [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
  (eP : J ⋙ K = P) (eQ : P ⋙ K = Q) (R : Superfunctor k C (SVec k))
  (e : J ⋙ (K ⋙ K) = Q) {p : ZMod 2}
  {β : ∀ w, (K ⋙ K).obj w ⟶ (K ⋙ K).obj w} (hβ : IsSupernatural k p β)
  {α : ∀ v, Q.obj v ⟶ Q.obj v} (hα : IsSupernatural k p α)

private theorem word_coherence_eq (e : J ⋙ (K ⋙ K) = Q) :
    (recursiveIso J K P Q eP eQ R).hom =
      ((inductionCompOfEq K K (K ⋙ K) rfl).app (BalancedInduction.induced J R)).hom ≫
        (comparisonIso J (K ⋙ K) Q e R).hom :=
  recursiveIso_hom J K P Q eP eQ R e

private theorem word_outer_eq (e : J ⋙ (K ⋙ K) = Q)
    (hβα : ∀ v, HEq (β (J.obj v)) (α v)) :
    @Eq ((BalancedInduction.induction (K ⋙ K)).obj (BalancedInduction.induced J R) ⟶
      (BalancedInduction.induction Q).obj R)
      (inducedTransform (K ⋙ K) hβ (BalancedInduction.induced J R) ≫
        (comparisonIso J (K ⋙ K) Q e R).hom)
      ((comparisonIso J (K ⋙ K) Q e R).hom ≫
        inducedTransform Q hα R) :=
  outer_hom J (K ⋙ K) Q e hβ hα hβα R

private def wordSignedEquation
    (s : (BalancedInduction.induction K ⋙ BalancedInduction.induction K).obj
      (BalancedInduction.induced J R) ⟶
      (BalancedInduction.induction K ⋙ BalancedInduction.induction K).obj (BalancedInduction.induced J R)) : Prop :=
  signedComparisonEquation s (recursiveIso J K P Q eP eQ R).hom
    (inducedTransform Q hα R)

private theorem word_signed (e : J ⋙ (K ⋙ K) = Q)
    (hβα : ∀ v, HEq (β (J.obj v)) (α v))
    (s : (BalancedInduction.induction K ⋙ BalancedInduction.induction K).obj
      (BalancedInduction.induced J R) ⟶
      (BalancedInduction.induction K ⋙ BalancedInduction.induction K).obj (BalancedInduction.induced J R))
    (hs : s = -(((BalancedInduction.inductionComp K K).app (BalancedInduction.induced J R)).hom ≫
      inducedTransform (K ⋙ K) hβ (BalancedInduction.induced J R) ≫
      ((BalancedInduction.inductionComp K K).app (BalancedInduction.induced J R)).inv)) :
    wordSignedEquation J K P Q eP eQ R hα s := by
  unfold wordSignedEquation
  exact signed_by_comparison
    ((inductionCompOfEq K K (K ⋙ K) rfl).app (BalancedInduction.induced J R))
    ((BalancedInduction.inductionComp K K).app (BalancedInduction.induced J R))
    (comparisonIso J (K ⋙ K) Q e R).hom
    (recursiveIso J K P Q eP eQ R).hom
    (inducedTransform (K ⋙ K) hβ (BalancedInduction.induced J R))
    (inducedTransform Q hα R) s
    (refl_comparison K K (BalancedInduction.induced J R))
    (word_coherence_eq J K P Q eP eQ R e)
    (word_outer_eq J K Q R hβ hα e hβα) hs
end Signed

private theorem comparison_eq {C B E : Type u} [Category.{u} C] [Category.{u} B] [Category.{u} E]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    [Preadditive E] [Linear k E] [Supercategory k E]
    (J : C ⥤ B) (K : B ⥤ E) (P : C ⥤ E)
    [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    [K.Additive] [K.Linear k] [IsSuperfunctor k K]
    [P.Additive] [P.Linear k] [IsSuperfunctor k P] (e : J ⋙ K = P) :
    BalancedInduction.inductionComp (k := k) J K ≪≫ BalancedInduction.inductionFunctorIsoOfEq (k := k) _ _ e =
      inductionCompOfEq (k := k) J K P e := by
  subst P
  rfl

/-- The original selected single-append isomorphism is exactly the existing
 equality-transported composition comparison. -/
theorem selectedAppend_eq : powerWordAppendIso D Sc cutoff L ν i =
    (inductionCompOfEq (powerWordCoefficientSource D Sc cutoff ν) (append D Sc cutoff i)
      (powerWordCoefficientSource D Sc cutoff (ν ++ [i]))
      (powerWordCoefficientSource_append D Sc cutoff ν i)).app (liftedPowerRegular D cutoff L) := by
  have hh := congrArg (fun e => e.app (liftedPowerRegular (k := k) D cutoff L))
    (comparison_eq (powerWordCoefficientSource D Sc cutoff ν) (append D Sc cutoff i)
      (powerWordCoefficientSource D Sc cutoff (ν ++ [i]))
      (powerWordCoefficientSource_append D Sc cutoff ν i))
  unfold powerWordAppendIso powerWordModule
  exact hh

/-- Literal two-letter coefficient-source equality, with the original order. -/
theorem pairSource_eq :
    powerWordCoefficientSource D Sc cutoff ν ⋙ (append D Sc cutoff i ⋙ append D Sc cutoff i) =
      powerWordCoefficientSource D Sc cutoff (ν ++ [i] ++ [i]) := by
  calc
    _ = (powerWordCoefficientSource D Sc cutoff ν ⋙ append D Sc cutoff i) ⋙
        append D Sc cutoff i := rfl
    _ = powerWordCoefficientSource D Sc cutoff (ν ++ [i]) ⋙ append D Sc cutoff i :=
      congrArg (fun F => F ⋙ append D Sc cutoff i) (powerWordCoefficientSource_append D Sc cutoff ν i)
    _ = _ := powerWordCoefficientSource_append D Sc cutoff (ν ++ [i]) i

/-- The collapsed comparison uses the same existing induction comparison,
with the independently proved literal coefficient-source equality. -/
def collapsedIso :
    (BalancedInduction.induction (append D Sc cutoff i ⋙ append D Sc cutoff i)).obj
      (BalancedInduction.induced (powerWordCoefficientSource D Sc cutoff ν)
        (liftedPowerRegular D cutoff L)) ≅
    (BalancedInduction.induction (powerWordCoefficientSource D Sc cutoff (ν ++ [i] ++ [i]))).obj
      (liftedPowerRegular D cutoff L) :=
  (inductionCompOfEq (powerWordCoefficientSource D Sc cutoff ν)
    (append D Sc cutoff i ⋙ append D Sc cutoff i)
    (powerWordCoefficientSource D Sc cutoff (ν ++ [i] ++ [i]))
    (pairSource_eq D Sc cutoff ν i)).app (liftedPowerRegular D cutoff L)

/-- Exactly the two recursively selected single-word comparisons. -/
def selectedPairIso :
    (BalancedInduction.induction (append D Sc cutoff i) ⋙
      BalancedInduction.induction (append D Sc cutoff i)).obj
        (BalancedInduction.induced (powerWordCoefficientSource D Sc cutoff ν)
          (liftedPowerRegular D cutoff L)) ≅
    (BalancedInduction.induction (powerWordCoefficientSource D Sc cutoff (ν ++ [i] ++ [i]))).obj
      (liftedPowerRegular D cutoff L) :=
  recursiveIso (powerWordCoefficientSource D Sc cutoff ν) (append D Sc cutoff i)
    (powerWordCoefficientSource D Sc cutoff (ν ++ [i]))
    (powerWordCoefficientSource D Sc cutoff (ν ++ [i] ++ [i]))
    (powerWordCoefficientSource_append D Sc cutoff ν i)
    (powerWordCoefficientSource_append D Sc cutoff (ν ++ [i]) i)
    (liftedPowerRegular D cutoff L)

/-- Existing whole-comparison coherence identifies the actual recursive
choice with flattening followed by the collapsed word comparison. -/
theorem selectedPair_hom_eq :
    recursiveEquation (powerWordCoefficientSource D Sc cutoff ν)
    (append D Sc cutoff i) (powerWordCoefficientSource D Sc cutoff (ν ++ [i]))
    (powerWordCoefficientSource D Sc cutoff (ν ++ [i] ++ [i]))
    (powerWordCoefficientSource_append D Sc cutoff ν i)
    (powerWordCoefficientSource_append D Sc cutoff (ν ++ [i]) i)
    (liftedPowerRegular D cutoff L) (pairSource_eq D Sc cutoff ν i) :=
  recursiveIso_hom (powerWordCoefficientSource D Sc cutoff ν)
    (append D Sc cutoff i) (powerWordCoefficientSource D Sc cutoff (ν ++ [i]))
    (powerWordCoefficientSource D Sc cutoff (ν ++ [i] ++ [i]))
    (powerWordCoefficientSource_append D Sc cutoff ν i)
    (powerWordCoefficientSource_append D Sc cutoff (ν ++ [i]) i)
    (liftedPowerRegular D cutoff L) (pairSource_eq D Sc cutoff ν i)

private def crossArrow : (OldCategory.mk (ν ++ [i] ++ [i]) : OldCategory D Sc cutoff) ⟶
    OldCategory.mk (ν ++ [i] ++ [i]) := equalCrossComponent D Sc cutoff i (OldCategory.mk ν)
private theorem crossArrow_mem : crossArrow D Sc cutoff ν i ∈
    parity (R := k) _ _ (D.parity i * D.parity i) :=
  (equalCross_supernatural D Sc cutoff i).mem (OldCategory.mk ν)

/-- The native old crossing before the prescribed extra minus. -/
def nativeCross :
    (BalancedInduction.induction (powerWordCoefficientSource D Sc cutoff (ν ++ [i] ++ [i]))).obj
      (liftedPowerRegular D cutoff L) ⟶
    (BalancedInduction.induction (powerWordCoefficientSource D Sc cutoff (ν ++ [i] ++ [i]))).obj
      (liftedPowerRegular D cutoff L) :=
  BalancedInduction.transformComponent
    (PowerWordMorphisms.coefficientSourceNatural D Sc cutoff (ν ++ [i] ++ [i]) (ν ++ [i] ++ [i])
      (crossArrow D Sc cutoff ν i) (crossArrow_mem D Sc cutoff ν i))
    (liftedPowerRegular D cutoff L)

/-- The full-coefficient Hom chart identifies this native map literally. -/
theorem nativeCross_eq_fromArrow : nativeCross D Sc cutoff L ν i =
    PowerWordMorphisms.fromArrow D Sc cutoff L (ν ++ [i] ++ [i]) (ν ++ [i] ++ [i])
      (crossArrow D Sc cutoff ν i) :=
  (PowerWordMorphisms.fromArrow_eq_transform D Sc cutoff L (ν ++ [i] ++ [i]) (ν ++ [i] ++ [i])
    (crossArrow D Sc cutoff ν i) (crossArrow_mem D Sc cutoff ν i)).symm

/-- The all-vector outer-recast square for the actual regular-power word.
The equation definition stages metadata only; it contains the literal
comparison and native transformation, with no assumed action premise. -/
theorem collapsed_cross :
    outerEquation (powerWordCoefficientSource D Sc cutoff ν)
      (append D Sc cutoff i ⋙ append D Sc cutoff i)
      (powerWordCoefficientSource D Sc cutoff (ν ++ [i] ++ [i]))
      (pairSource_eq D Sc cutoff ν i) (equalCross_supernatural D Sc cutoff i)
      (PowerWordMorphisms.coefficientSourceNatural D Sc cutoff (ν ++ [i] ++ [i]) (ν ++ [i] ++ [i])
        (crossArrow D Sc cutoff ν i) (crossArrow_mem D Sc cutoff ν i))
      (liftedPowerRegular D cutoff L) :=
  outer_hom (powerWordCoefficientSource D Sc cutoff ν)
    (append D Sc cutoff i ⋙ append D Sc cutoff i)
    (powerWordCoefficientSource D Sc cutoff (ν ++ [i] ++ [i]))
    (pairSource_eq D Sc cutoff ν i) (equalCross_supernatural D Sc cutoff i)
    (PowerWordMorphisms.coefficientSourceNatural D Sc cutoff (ν ++ [i] ++ [i]) (ν ++ [i] ++ [i])
      (crossArrow D Sc cutoff ν i) (crossArrow_mem D Sc cutoff ν i))
    (fun _ => HEq.rfl) (liftedPowerRegular D cutoff L)


private theorem actual_signed_conjugate
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
    (signedEqualInductionCross D Sc cutoff i).app (D.parity i * D.parity i) M =
      -(((BalancedInduction.inductionComp (append D Sc cutoff i) (append D Sc cutoff i)).app M).hom ≫
        inducedTransform (append D Sc cutoff i ⋙ append D Sc cutoff i)
          (equalCross_supernatural D Sc cutoff i) M ≫
        ((BalancedInduction.inductionComp (append D Sc cutoff i) (append D Sc cutoff i)).app M).inv) := by
  rw [signedEqualInductionCross_app, ite_eq_left rfl]
  unfold equalCrossOnDoubleInduction inducedTransform
  simp only [Iso.app_hom, Iso.app_inv]

/-- The ACTUAL signed double-induction crossing under the recursively
selected word comparisons, on the entire full-coefficient module. -/
theorem selected_signed_cross :
    wordSignedEquation (powerWordCoefficientSource D Sc cutoff ν) (append D Sc cutoff i)
      (powerWordCoefficientSource D Sc cutoff (ν ++ [i]))
      (powerWordCoefficientSource D Sc cutoff (ν ++ [i] ++ [i]))
      (powerWordCoefficientSource_append D Sc cutoff ν i)
      (powerWordCoefficientSource_append D Sc cutoff (ν ++ [i]) i)
      (liftedPowerRegular D cutoff L)
      (PowerWordMorphisms.coefficientSourceNatural D Sc cutoff (ν ++ [i] ++ [i]) (ν ++ [i] ++ [i])
        (crossArrow D Sc cutoff ν i) (crossArrow_mem D Sc cutoff ν i))
      ((signedEqualInductionCross D Sc cutoff i).app (D.parity i * D.parity i)
        (BalancedInduction.induced (powerWordCoefficientSource D Sc cutoff ν)
          (liftedPowerRegular D cutoff L))) :=
  word_signed (powerWordCoefficientSource D Sc cutoff ν) (append D Sc cutoff i)
    (powerWordCoefficientSource D Sc cutoff (ν ++ [i]))
    (powerWordCoefficientSource D Sc cutoff (ν ++ [i] ++ [i]))
    (powerWordCoefficientSource_append D Sc cutoff ν i)
    (powerWordCoefficientSource_append D Sc cutoff (ν ++ [i]) i)
    (liftedPowerRegular D cutoff L)
    (equalCross_supernatural D Sc cutoff i)
    (PowerWordMorphisms.coefficientSourceNatural D Sc cutoff (ν ++ [i] ++ [i]) (ν ++ [i] ++ [i])
      (crossArrow D Sc cutoff ν i) (crossArrow_mem D Sc cutoff ν i))
    (e := pairSource_eq D Sc cutoff ν i) (fun _ => HEq.rfl) _
    (actual_signed_conjugate D Sc cutoff i
      (BalancedInduction.induced (powerWordCoefficientSource D Sc cutoff ν) (liftedPowerRegular D cutoff L)))

end OddMath.QuiverHecke.ELVOld.PowerWordPair
