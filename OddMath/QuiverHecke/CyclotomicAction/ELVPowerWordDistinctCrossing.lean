import OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordPairCrossing
import OddMath.QuiverHecke.CyclotomicAction.ELVDistinctModuleMate
import OddMath.Algebra.FiniteSupermoduleFunctor

/-! # Chosen two-colour crossing through selected word comparisons

The crossing in Brundan–Ellis (1.12), required by SwappedVacuumCoordinates
§§4–5, is compared with the full old-Hom chart using the existing selected
append comparisons, without replacing the chosen action map.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.PowerWordDistinct
open CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (L : I × ℕ → ℕ)
  (ν : List I) (i j : I)

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

section Recursive
variable {C B : Type u} [Category.{u} C] [Category.{u} B]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive B] [Linear k B] [Supercategory k B]
  (J : C ⥤ B) (A B' : B ⥤ B) (P Q : C ⥤ B)
  [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  [A.Additive] [A.Linear k] [IsSuperfunctor k A]
  [B'.Additive] [B'.Linear k] [IsSuperfunctor k B']
  [P.Additive] [P.Linear k] [IsSuperfunctor k P]
  [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
  (eP : J ⋙ A = P) (eQ : P ⋙ B' = Q) (R : Superfunctor k C (SVec k))
private def recursiveIso :
    (BalancedInduction.induction A ⋙ BalancedInduction.induction B').obj
      (BalancedInduction.induced J R) ≅ (BalancedInduction.induction Q).obj R :=
  (BalancedInduction.induction B').mapIso (comparisonIso J A P eP R) ≪≫
    comparisonIso P B' Q eQ R
private def recursiveEquation (e : J ⋙ (A ⋙ B') = Q) : Prop :=
    (recursiveIso J A B' P Q eP eQ R).hom =
      ((inductionCompOfEq A B' (A ⋙ B') rfl).app (BalancedInduction.induced J R)).hom ≫
        (comparisonIso J (A ⋙ B') Q e R).hom
private theorem recursiveIso_hom (e : J ⋙ (A ⋙ B') = Q) :
    recursiveEquation J A B' P Q eP eQ R e := by
  unfold recursiveEquation recursiveIso comparisonIso
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
  exact inductionCompOfEq_assoc_hom J A B' P (A ⋙ B') Q eP rfl eQ e R
end Recursive

private theorem total_of_mem {C B : Type*} [Category* C] [Category* B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    {F G : Superfunctor k C B} {p : ZMod 2} {f : F ⟶ G}
    (hf : f ∈ parity (R := k) _ _ p) (z : C) : f.total z = f.app p z := by
  rcases parity_eq_zero_or_one p with rfl | rfl
  · rw [SuperNatTrans.total, Superfunctor.app_eq_zero_of_mem hf (q := 1) (by decide), add_zero]
  · rw [SuperNatTrans.total, Superfunctor.app_eq_zero_of_mem hf (q := 0) (by decide), zero_add]
section Outer
variable {C B E : Type u} [Category.{u} C] [Category.{u} B] [Category.{u} E]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive B] [Linear k B] [Supercategory k B]
  [Preadditive E] [Linear k E] [Supercategory k E]
  (J : C ⥤ B) (K₀ K₁ : B ⥤ E) (P₀ P₁ : C ⥤ E)
  [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  [K₀.Additive] [K₀.Linear k] [IsSuperfunctor k K₀]
  [K₁.Additive] [K₁.Linear k] [IsSuperfunctor k K₁]
  [P₀.Additive] [P₀.Linear k] [IsSuperfunctor k P₀]
  [P₁.Additive] [P₁.Linear k] [IsSuperfunctor k P₁]
  (e₀ : J ⋙ K₀ = P₀) (e₁ : J ⋙ K₁ = P₁)
  {p : ZMod 2} {β : ∀ w, K₀.obj w ⟶ K₁.obj w} (hβ : IsSupernatural k p β)
  {α : ∀ v, P₀.obj v ⟶ P₁.obj v} (hα : IsSupernatural k p α)
  (R : Superfunctor k C (SVec k))
private def outerEquation : Prop :=
  inducedTransform K₀ K₁ hβ (BalancedInduction.induced J R) ≫
    (comparisonIso J K₀ P₀ e₀ R).hom =
  (comparisonIso J K₁ P₁ e₁ R).hom ≫ inducedTransform P₀ P₁ hα R
private theorem outer_hom (hβα : ∀ v, HEq (β (J.obj v)) (α v)) :
    outerEquation J K₀ K₁ P₀ P₁ e₀ e₁ hβ hα R := by
  unfold outerEquation comparisonIso inducedTransform
  simp only [Iso.app_hom]
  subst P₀
  subst P₁
  have ha : (fun v => β (J.obj v)) = α := funext (fun v => eq_of_heq (hβα v))
  subst α
  simp only [inductionCompOfEq, eqToIso_refl, Iso.trans_refl]
  have hc₀ := BalancedInduction.inductionComp_hom_mem J K₀ R
  have hc₁ := BalancedInduction.inductionComp_hom_mem J K₁ R
  have hx := BalancedInduction.transformComponent_mem hβ (BalancedInduction.induced J R)
  have hy := BalancedInduction.transformComponent_mem hα R
  apply FiniteSupermodule.hom_ext_total
  intro w
  rw [Superfunctor.comp_total, Superfunctor.comp_total,
    total_of_mem hx, total_of_mem hy, total_of_mem hc₀, total_of_mem hc₁,
    BalancedInduction.transformComponent_app, BalancedInduction.transformComponent_app,
    ite_eq_left rfl, ite_eq_left rfl]
  change BalancedInduction.compForward J K₀ R w ∘ₗ
      BalancedInduction.transformLinear hβ (BalancedInduction.induced J R) w =
    BalancedInduction.transformLinear hα R w ∘ₗ BalancedInduction.compForward J K₁ R w
  exact BalancedInduction.compForward_transform_outer J hβ R w
end Outer

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

private theorem crossing_by_comparison {C : Type*} [Category* C]
    {A B C' D E F : C} (e₀ e : A ≅ B) (d₀ d : C' ≅ D)
    (f : B ⟶ E) (g : D ⟶ F) (u : A ⟶ E) (v : C' ⟶ F)
    (x : B ⟶ D) (n : E ⟶ F) (s : A ⟶ C')
    (he : e₀ = e) (hd : d₀ = d) (hu : u = e₀.hom ≫ f) (hv : v = d₀.hom ≫ g)
    (hx : x ≫ g = f ≫ n) (hs : s = e.hom ≫ x ≫ d.inv) : s ≫ v = u ≫ n := by
  subst e₀
  subst d₀
  rw [hs, hu, hv]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [hx]

section WordCrossing
variable {C B : Type u} [Category.{u} C] [Category.{u} B]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive B] [Linear k B] [Supercategory k B]
  (J : C ⥤ B) (A B' : B ⥤ B) (Pi Pj Qij Qji : C ⥤ B)
  [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  [A.Additive] [A.Linear k] [IsSuperfunctor k A]
  [B'.Additive] [B'.Linear k] [IsSuperfunctor k B']
  [Pi.Additive] [Pi.Linear k] [IsSuperfunctor k Pi]
  [Pj.Additive] [Pj.Linear k] [IsSuperfunctor k Pj]
  [Qij.Additive] [Qij.Linear k] [IsSuperfunctor k Qij]
  [Qji.Additive] [Qji.Linear k] [IsSuperfunctor k Qji]
  (ePi : J ⋙ A = Pi) (ePj : J ⋙ B' = Pj)
  (eQij : Pi ⋙ B' = Qij) (eQji : Pj ⋙ A = Qji)
  (R : Superfunctor k C (SVec k))
  {p : ZMod 2} {β : ∀ w, (B' ⋙ A).obj w ⟶ (A ⋙ B').obj w}
  (hβ : IsSupernatural k p β)
  {α : ∀ v, Qji.obj v ⟶ Qij.obj v} (hα : IsSupernatural k p α)

private def wordCrossingEquation
    (s : (BalancedInduction.induction A ⋙ BalancedInduction.induction B').obj
      (BalancedInduction.induced J R) ⟶
      (BalancedInduction.induction B' ⋙ BalancedInduction.induction A).obj
        (BalancedInduction.induced J R)) : Prop :=
  s ≫ (recursiveIso J B' A Pj Qji ePj eQji R).hom =
    (recursiveIso J A B' Pi Qij ePi eQij R).hom ≫ inducedTransform Qji Qij hα R

private theorem word_outer_eq (eij : J ⋙ (A ⋙ B') = Qij) (eji : J ⋙ (B' ⋙ A) = Qji)
    (hβα : ∀ v, HEq (β (J.obj v)) (α v)) :
    @Eq ((BalancedInduction.induction (A ⋙ B')).obj (BalancedInduction.induced J R) ⟶
      (BalancedInduction.induction Qji).obj R)
      (inducedTransform (B' ⋙ A) (A ⋙ B') hβ (BalancedInduction.induced J R) ≫
        (comparisonIso J (B' ⋙ A) Qji eji R).hom)
      ((comparisonIso J (A ⋙ B') Qij eij R).hom ≫ inducedTransform Qji Qij hα R) :=
  outer_hom J (B' ⋙ A) (A ⋙ B') Qji Qij eji eij hβ hα R hβα

private theorem word_crossing (eij : J ⋙ (A ⋙ B') = Qij) (eji : J ⋙ (B' ⋙ A) = Qji)
    (hβα : ∀ v, HEq (β (J.obj v)) (α v))
    (s : (BalancedInduction.induction A ⋙ BalancedInduction.induction B').obj
      (BalancedInduction.induced J R) ⟶
      (BalancedInduction.induction B' ⋙ BalancedInduction.induction A).obj
        (BalancedInduction.induced J R))
    (hs : s = ((BalancedInduction.inductionComp A B').app (BalancedInduction.induced J R)).hom ≫
      inducedTransform (B' ⋙ A) (A ⋙ B') hβ (BalancedInduction.induced J R) ≫
      ((BalancedInduction.inductionComp B' A).app (BalancedInduction.induced J R)).inv) :
    wordCrossingEquation J A B' Pi Pj Qij Qji ePi ePj eQij eQji R hα s := by
  unfold wordCrossingEquation
  exact crossing_by_comparison
    ((inductionCompOfEq A B' (A ⋙ B') rfl).app (BalancedInduction.induced J R))
    ((BalancedInduction.inductionComp A B').app (BalancedInduction.induced J R))
    ((inductionCompOfEq B' A (B' ⋙ A) rfl).app (BalancedInduction.induced J R))
    ((BalancedInduction.inductionComp B' A).app (BalancedInduction.induced J R))
    (comparisonIso J (A ⋙ B') Qij eij R).hom
    (comparisonIso J (B' ⋙ A) Qji eji R).hom
    (recursiveIso J A B' Pi Qij ePi eQij R).hom
    (recursiveIso J B' A Pj Qji ePj eQji R).hom
    (inducedTransform (B' ⋙ A) (A ⋙ B') hβ (BalancedInduction.induced J R))
    (inducedTransform Qji Qij hα R) s
    (refl_comparison A B' (BalancedInduction.induced J R))
    (refl_comparison B' A (BalancedInduction.induced J R))
    (recursiveIso_hom J A B' Pi Qij ePi eQij R eij)
    (recursiveIso_hom J B' A Pj Qji ePj eQji R eji)
    (word_outer_eq J A B' Qij Qji R hβ hα eij eji hβα) hs
end WordCrossing

/-- Literal two-letter coefficient-source equality in the original order. -/
theorem pairSource_eq :
    powerWordCoefficientSource D Sc cutoff ν ⋙ (append D Sc cutoff i ⋙ append D Sc cutoff j) =
      powerWordCoefficientSource D Sc cutoff (ν ++ [i] ++ [j]) := by
  calc
    _ = (powerWordCoefficientSource D Sc cutoff ν ⋙ append D Sc cutoff i) ⋙
        append D Sc cutoff j := rfl
    _ = powerWordCoefficientSource D Sc cutoff (ν ++ [i]) ⋙ append D Sc cutoff j :=
      congrArg (fun F => F ⋙ append D Sc cutoff j) (powerWordCoefficientSource_append D Sc cutoff ν i)
    _ = _ := powerWordCoefficientSource_append D Sc cutoff (ν ++ [i]) j

/-- The two successive selected single-append comparisons. Their single
factors are identified with `powerWordAppendIso` by `PowerWordPair.selectedAppend_eq`. -/
def selectedPairIso :
    (BalancedInduction.induction (append D Sc cutoff i) ⋙
      BalancedInduction.induction (append D Sc cutoff j)).obj
        (BalancedInduction.induced (powerWordCoefficientSource D Sc cutoff ν)
          (liftedPowerRegular D cutoff L)) ≅
    (BalancedInduction.induction (powerWordCoefficientSource D Sc cutoff (ν ++ [i] ++ [j]))).obj
      (liftedPowerRegular D cutoff L) :=
  recursiveIso (powerWordCoefficientSource D Sc cutoff ν)
    (append D Sc cutoff i) (append D Sc cutoff j)
    (powerWordCoefficientSource D Sc cutoff (ν ++ [i]))
    (powerWordCoefficientSource D Sc cutoff (ν ++ [i] ++ [j]))
    (powerWordCoefficientSource_append D Sc cutoff ν i)
    (powerWordCoefficientSource_append D Sc cutoff (ν ++ [i]) j)
    (liftedPowerRegular D cutoff L)

/-- Selected pair coherence includes all endpoint equality transports. -/
theorem selectedPair_hom_eq :
    recursiveEquation (powerWordCoefficientSource D Sc cutoff ν)
      (append D Sc cutoff i) (append D Sc cutoff j)
      (powerWordCoefficientSource D Sc cutoff (ν ++ [i]))
      (powerWordCoefficientSource D Sc cutoff (ν ++ [i] ++ [j]))
      (powerWordCoefficientSource_append D Sc cutoff ν i)
      (powerWordCoefficientSource_append D Sc cutoff (ν ++ [i]) j)
      (liftedPowerRegular D cutoff L) (pairSource_eq D Sc cutoff ν i j) :=
  recursiveIso_hom (powerWordCoefficientSource D Sc cutoff ν)
    (append D Sc cutoff i) (append D Sc cutoff j)
    (powerWordCoefficientSource D Sc cutoff (ν ++ [i]))
    (powerWordCoefficientSource D Sc cutoff (ν ++ [i] ++ [j]))
    (powerWordCoefficientSource_append D Sc cutoff ν i)
    (powerWordCoefficientSource_append D Sc cutoff (ν ++ [i]) j)
    (liftedPowerRegular D cutoff L) (pairSource_eq D Sc cutoff ν i j)

private def crossArrow : (OldCategory.mk (ν ++ [j] ++ [i]) : OldCategory D Sc cutoff) ⟶
    OldCategory.mk (ν ++ [i] ++ [j]) := Distinct.crossComponent D Sc cutoff i j (OldCategory.mk ν)
private theorem crossArrow_mem : crossArrow D Sc cutoff ν i j ∈ parity (R := k) _ _
    (D.parity i * D.parity j) := (Distinct.cross_supernatural D Sc cutoff i j).mem (OldCategory.mk ν)

/-- Full-coefficient signed old-Hom map for the positive two-colour crossing. -/
def wordCross :
    (BalancedInduction.induction (powerWordCoefficientSource D Sc cutoff (ν ++ [i] ++ [j]))).obj
      (liftedPowerRegular D cutoff L) ⟶
    (BalancedInduction.induction (powerWordCoefficientSource D Sc cutoff (ν ++ [j] ++ [i]))).obj
      (liftedPowerRegular D cutoff L) :=
  inducedTransform (powerWordCoefficientSource D Sc cutoff (ν ++ [j] ++ [i]))
    (powerWordCoefficientSource D Sc cutoff (ν ++ [i] ++ [j]))
    (PowerWordMorphisms.coefficientSourceNatural D Sc cutoff (ν ++ [i] ++ [j]) (ν ++ [j] ++ [i])
      (crossArrow D Sc cutoff ν i j) (crossArrow_mem D Sc cutoff ν i j))
    (liftedPowerRegular D cutoff L)

theorem wordCross_eq_fromArrow : wordCross D Sc cutoff L ν i j =
    PowerWordMorphisms.fromArrow D Sc cutoff L (ν ++ [i] ++ [j]) (ν ++ [j] ++ [i])
      (crossArrow D Sc cutoff ν i j) :=
  (PowerWordMorphisms.fromArrow_eq_transform D Sc cutoff L (ν ++ [i] ++ [j]) (ν ++ [j] ++ [i])
    (crossArrow D Sc cutoff ν i j) (crossArrow_mem D Sc cutoff ν i j)).symm

private theorem chosen_crossing
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
    (Distinct.moduleCross D Sc cutoff i j).app (D.parity i * D.parity j) M =
      ((BalancedInduction.inductionComp (append D Sc cutoff i) (append D Sc cutoff j)).app M).hom ≫
        inducedTransform (append D Sc cutoff j ⋙ append D Sc cutoff i)
          (append D Sc cutoff i ⋙ append D Sc cutoff j)
          (Distinct.cross_supernatural D Sc cutoff i j) M ≫
        ((BalancedInduction.inductionComp (append D Sc cutoff j) (append D Sc cutoff i)).app M).inv := by
  rw [Distinct.moduleCross_app, ite_eq_left rfl]
  unfold BalancedInduction.mixedCrossComponent inducedTransform
  rfl

/-- The independently chosen crossing intertwines the two selected word
comparisons on every vector. For distinct colours its positive normalization
has no extra minus. Full coefficient classes remain inside the total twist. -/
theorem selected_cross :
    wordCrossingEquation (powerWordCoefficientSource D Sc cutoff ν)
      (append D Sc cutoff i) (append D Sc cutoff j)
      (powerWordCoefficientSource D Sc cutoff (ν ++ [i]))
      (powerWordCoefficientSource D Sc cutoff (ν ++ [j]))
      (powerWordCoefficientSource D Sc cutoff (ν ++ [i] ++ [j]))
      (powerWordCoefficientSource D Sc cutoff (ν ++ [j] ++ [i]))
      (powerWordCoefficientSource_append D Sc cutoff ν i)
      (powerWordCoefficientSource_append D Sc cutoff ν j)
      (powerWordCoefficientSource_append D Sc cutoff (ν ++ [i]) j)
      (powerWordCoefficientSource_append D Sc cutoff (ν ++ [j]) i)
      (liftedPowerRegular D cutoff L)
      (PowerWordMorphisms.coefficientSourceNatural D Sc cutoff (ν ++ [i] ++ [j]) (ν ++ [j] ++ [i])
        (crossArrow D Sc cutoff ν i j) (crossArrow_mem D Sc cutoff ν i j))
      ((Distinct.moduleCross D Sc cutoff i j).app (D.parity i * D.parity j)
        (BalancedInduction.induced (powerWordCoefficientSource D Sc cutoff ν)
          (liftedPowerRegular D cutoff L))) :=
  word_crossing (powerWordCoefficientSource D Sc cutoff ν)
    (append D Sc cutoff i) (append D Sc cutoff j)
    (powerWordCoefficientSource D Sc cutoff (ν ++ [i]))
    (powerWordCoefficientSource D Sc cutoff (ν ++ [j]))
    (powerWordCoefficientSource D Sc cutoff (ν ++ [i] ++ [j]))
    (powerWordCoefficientSource D Sc cutoff (ν ++ [j] ++ [i]))
    (powerWordCoefficientSource_append D Sc cutoff ν i)
    (powerWordCoefficientSource_append D Sc cutoff ν j)
    (powerWordCoefficientSource_append D Sc cutoff (ν ++ [i]) j)
    (powerWordCoefficientSource_append D Sc cutoff (ν ++ [j]) i)
    (liftedPowerRegular D cutoff L) (Distinct.cross_supernatural D Sc cutoff i j)
    (PowerWordMorphisms.coefficientSourceNatural D Sc cutoff (ν ++ [i] ++ [j]) (ν ++ [j] ++ [i])
      (crossArrow D Sc cutoff ν i j) (crossArrow_mem D Sc cutoff ν i j))
    (pairSource_eq D Sc cutoff ν i j) (pairSource_eq D Sc cutoff ν j i)
    (fun _ => HEq.rfl) _ (chosen_crossing D Sc cutoff i j _)

end OddMath.QuiverHecke.ELVOld.PowerWordDistinct
