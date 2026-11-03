import OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordAppendDot
import OddMath.QuiverHecke.CyclotomicAction.ELVContentWhiskering
import OddMath.QuiverHecke.CyclotomicAction.ELVContentComparisonCoherence
import OddMath.QuiverHecke.CyclotomicAction.ELVOldMateTensors

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
    ((BalancedInduction.induction J ⋙ BalancedInduction.induction K) ⋙
      BalancedInduction.induction K).obj R ≅ (BalancedInduction.induction Q).obj R :=
  (BalancedInduction.induction K).mapIso ((inductionCompOfEq J K P eP).app R) ≪≫
    (inductionCompOfEq P K Q eQ).app R
private theorem recursiveIso_hom (e : J ⋙ (K ⋙ K) = Q) :
    (recursiveIso J K P Q eP eQ R).hom =
      (inductionCompOfEq K K (K ⋙ K) rfl).hom.app (BalancedInduction.induced J R) ≫
        (inductionCompOfEq J (K ⋙ K) Q e).hom.app R := by
  unfold recursiveIso
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
    BalancedInduction.transformComponent hβ (BalancedInduction.induced J R) ≫
      (inductionCompOfEq J K P e).hom.app R =
    (inductionCompOfEq J K P e).hom.app R ≫ BalancedInduction.transformComponent hα R := by
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
    (BalancedInduction.induction (powerWordCoefficientSource D Sc cutoff ν) ⋙
      BalancedInduction.induction (append D Sc cutoff i ⋙ append D Sc cutoff i)).obj
        (liftedPowerRegular D cutoff L) ≅
    (BalancedInduction.induction (powerWordCoefficientSource D Sc cutoff (ν ++ [i] ++ [i]))).obj
      (liftedPowerRegular D cutoff L) :=
  (inductionCompOfEq (powerWordCoefficientSource D Sc cutoff ν)
    (append D Sc cutoff i ⋙ append D Sc cutoff i)
    (powerWordCoefficientSource D Sc cutoff (ν ++ [i] ++ [i]))
    (pairSource_eq D Sc cutoff ν i)).app (liftedPowerRegular D cutoff L)

/-- The selected single comparison with its raw endpoints fixed before
applying another induction functor. -/
def singleIso :
    (BalancedInduction.induction (powerWordCoefficientSource D Sc cutoff ν) ⋙
      BalancedInduction.induction (append D Sc cutoff i)).obj (liftedPowerRegular D cutoff L) ≅
    (BalancedInduction.induction (powerWordCoefficientSource D Sc cutoff (ν ++ [i]))).obj
      (liftedPowerRegular D cutoff L) :=
  (inductionCompOfEq (powerWordCoefficientSource D Sc cutoff ν) (append D Sc cutoff i)
    (powerWordCoefficientSource D Sc cutoff (ν ++ [i]))
    (powerWordCoefficientSource_append D Sc cutoff ν i)).app (liftedPowerRegular D cutoff L)

private theorem single_eq : singleIso D Sc cutoff L ν i =
    (inductionCompOfEq (powerWordCoefficientSource D Sc cutoff ν) (append D Sc cutoff i)
      (powerWordCoefficientSource D Sc cutoff (ν ++ [i]))
      (powerWordCoefficientSource_append D Sc cutoff ν i)).app (liftedPowerRegular D cutoff L) :=
  rfl

/-- Exactly the two recursively selected single-word comparisons. -/
def selectedPairIso :
    ((BalancedInduction.induction (powerWordCoefficientSource D Sc cutoff ν) ⋙
      BalancedInduction.induction (append D Sc cutoff i)) ⋙
        BalancedInduction.induction (append D Sc cutoff i)).obj (liftedPowerRegular D cutoff L) ≅
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
    (selectedPairIso D Sc cutoff L ν i).hom =
      ((inductionCompOfEq (append D Sc cutoff i) (append D Sc cutoff i)
        (append D Sc cutoff i ⋙ append D Sc cutoff i) rfl).hom.app
        (BalancedInduction.induced (powerWordCoefficientSource D Sc cutoff ν)
          (liftedPowerRegular D cutoff L))) ≫ (collapsedIso D Sc cutoff L ν i).hom := by
  unfold selectedPairIso collapsedIso
  simp only [Iso.app_hom]
  exact recursiveIso_hom (powerWordCoefficientSource D Sc cutoff ν)
    (append D Sc cutoff i) (powerWordCoefficientSource D Sc cutoff (ν ++ [i]))
    (powerWordCoefficientSource D Sc cutoff (ν ++ [i] ++ [i]))
    (powerWordCoefficientSource_append D Sc cutoff ν i)
    (powerWordCoefficientSource_append D Sc cutoff (ν ++ [i]) i)
    (liftedPowerRegular D cutoff L) (pairSource_eq D Sc cutoff ν i)

/-- The native old crossing before its prescribed extra minus. -/
def nativeCross :
    BalancedInduction.induced (powerWordCoefficientSource D Sc cutoff (ν ++ [i] ++ [i]))
      (liftedPowerRegular D cutoff L) ⟶
    BalancedInduction.induced (powerWordCoefficientSource D Sc cutoff (ν ++ [i] ++ [i]))
      (liftedPowerRegular D cutoff L) :=
  PowerWordMorphisms.fromArrow D Sc cutoff L (ν ++ [i] ++ [i]) (ν ++ [i] ++ [i])
    (equalCrossComponent D Sc cutoff i (OldCategory.mk ν))

end OddMath.QuiverHecke.ELVOld.PowerWordPair
