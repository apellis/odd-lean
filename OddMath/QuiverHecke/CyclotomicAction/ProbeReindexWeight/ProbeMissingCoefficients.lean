import OddMath.QuiverHecke.CyclotomicAction.ContentBlockMatrix.ContentMissingCoefficients
import OddMath.QuiverHecke.CyclotomicAction.ProbeReindexWeight.ProbeAppendToRows

/-!
# Probe reindex weight

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # The prescribed missing-colour coefficients on evaluated probes

Brundan–Ellis (1.13)–(1.14): restrict every constructed inverse row
and its finite identities to the full scalar-evaluated module category.
The ordinary adjunction and all powers of its specified dot are retained.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open scoped BigOperators
namespace OddMath.QuiverHecke
open ELV ELV.BalancedInduction ELV.CyclotomicCrossingTensor CyclotomicAction
universe u
attribute [local irreducible] contentMissingBoundaryCoefficients
private def evaluation {k C R : Type*} [CommRing k]
    [Category C] [Category R] [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive R] [Linear k R] [Supercategory k R] (N : C) :
    Superfunctor k C R ⥤ R where
  obj F := F.obj N
  map f := f.total N
  map_id F := SuperNatTrans.id_total F.toFunctor N
  map_comp f g := Superfunctor.comp_total f g N
private instance evaluation_additive {k C R : Type*} [CommRing k]
    [Category C] [Category R] [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive R] [Linear k R] [Supercategory k R] (N : C) :
    (evaluation (k := k) (R := R) N).Additive where
  map_add := by intros; change (_ + _) + (_ + _) = (_ + _) + (_ + _); abel
private def forgetEvaluation {k C : Type*} [CommRing k]
    [Category C] [Preadditive C] [Linear k C] [Supercategory k C]
    (P : ObjectProperty C) (N : P.FullSubcategory) :
    Superfunctor k P.FullSubcategory P.FullSubcategory ⥤ C where
  obj F := (F.obj N).obj
  map f := (f.total N).hom
  map_id F := congrArg (fun f => f.hom) (SuperNatTrans.id_total F.toFunctor N)
  map_comp f g := congrArg (fun f => f.hom) (Superfunctor.comp_total f g N)
private instance forgetEvaluation_additive {k C : Type*} [CommRing k]
    [Category C] [Preadditive C] [Linear k C] [Supercategory k C]
    (P : ObjectProperty C) (N : P.FullSubcategory) :
    (forgetEvaluation (k := k) P N).Additive where
  map_add := by intros; change (_ + _) + (_ + _) = (_ + _) + (_ + _); abel

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (γ : List I) (i : I)
local notation "cut" => probeCutoff D m
local notation "K" => oldContentAppend D Sc cut γ i
local notation "hDot" => oldContentAppendDot_supernatural D Sc cut γ i
local notation "P" => ProbeEvaluatesCoefficients D m Sc γ
local notation "A" => probeAppendToRightAdjunction D Sc m γ i (i :: γ) (List.Perm.refl _)
local notation "x" => probeAppendToInductionDot D Sc m γ i (i :: γ) (List.Perm.refl _)
local notation "count" => contentUnitCount D cut i (γ : Multiset I)
private abbrev modules := Superfunctor k (OldContentCategory D Sc cut γ) (SVec k)
private abbrev oldUpper_2 : Superfunctor k (modules D Sc m γ) (modules D Sc m γ) :=
  ⟨(induction K) ⋙ (restriction K)⟩
private abbrev upper_2 : Superfunctor k (ProbeEvaluatedModules D Sc m γ) (ProbeEvaluatedModules D Sc m γ) :=
  ⟨(probeEvaluatedAppendTo D Sc m γ i (i :: γ) (List.Perm.refl _)) ⋙
    (probeEvaluatedRestrictTo D Sc m γ i (i :: γ) (List.Perm.refl _))⟩
private abbrev oldCup (n : ℕ) : Superfunctor.id k (modules D Sc m γ) ⟶ oldUpper_2 D Sc m γ i :=
  SKM.RouquierBoundary.cup (inductionModuleAdjunction (k := k) K) (inductionModuleDot K hDot) n
private abbrev evaluatedCup (n : ℕ) : Superfunctor.id k (ProbeEvaluatedModules D Sc m γ) ⟶ upper_2 D Sc m γ i :=
  SKM.RouquierBoundary.cup A x n

/-- Every selected dotted unit retains its native OLD component. -/
theorem probeEvaluatedUnitPower_app (n : ℕ) (q : ZMod 2)
    (N : ProbeEvaluatedModules D Sc m γ) :
    ((evaluatedCup D Sc m γ i n).app q N).hom = (oldCup D Sc m γ i n).app q N.obj :=
  probeAppendToUnitColumn_app D Sc m γ i (List.Perm.refl (i :: γ)) n q N
private theorem cup_total (n : ℕ) (N : ProbeEvaluatedModules D Sc m γ) :
    ((evaluatedCup D Sc m γ i n).total N).hom = (oldCup D Sc m γ i n).total N.obj := by
  change ((evaluatedCup D Sc m γ i n).app 0 N).hom +
    ((evaluatedCup D Sc m γ i n).app 1 N).hom = _
  rw [probeEvaluatedUnitPower_app, probeEvaluatedUnitPower_app]
  rfl

private abbrev rawBoundary := SKM.RouquierBoundary.Coefficients
  (inductionModuleAdjunction (k := k) K) (inductionModuleDot K hDot) (D.parity i) count
private def evaluatedCoefficient (V : rawBoundary D Sc m γ i) (n : ℕ) :
    upper_2 D Sc m γ i ⟶ Superfunctor.id k (ProbeEvaluatedModules D Sc m γ) where
  app q N := ⟨(V.coeff n).app q N.obj⟩
  app_mem q N := by
    exact (V.coeff n).app_mem q N.obj
  naturality q M N s f hf := by
    apply InducedCategory.hom_ext
    exact (V.coeff n).naturality q f.hom hf
variable (V : rawBoundary D Sc m γ i)
private theorem coefficient_mem (n : ℕ) :
    evaluatedCoefficient D Sc m γ i V n ∈ parity (R := k)
      (upper_2 D Sc m γ i) (Superfunctor.id k (ProbeEvaluatedModules D Sc m γ))
      ((n : ZMod 2) * D.parity i) := by
  apply Superfunctor.mem_parity_iff_isHomogeneous.mpr
  intro q hq
  funext N
  apply InducedCategory.hom_ext
  exact congrFun (Superfunctor.mem_parity_iff_isHomogeneous.mp (V.coeff_mem n) q hq) N.obj
private theorem coefficient_total (n : ℕ) (N : ProbeEvaluatedModules D Sc m γ) :
    ((evaluatedCoefficient D Sc m γ i V n).total N).hom = (V.coeff n).total N.obj := rfl
private theorem coefficients_total :
    ∑ j ∈ Finset.range count, evaluatedCoefficient D Sc m γ i V j ≫ evaluatedCup D Sc m γ i j =
      𝟙 (upper_2 D Sc m γ i) := by
  apply OddMath.HomogeneousSuperfunctorIso.total_ext
  intro N
  apply InducedCategory.hom_ext
  change (forgetEvaluation P N).map _ = (forgetEvaluation P N).map _
  rw [CategoryTheory.Functor.map_sum, CategoryTheory.Functor.map_id]
  simp only [CategoryTheory.Functor.map_comp]
  have h := congrArg (evaluation (k := k) N.obj).map V.total
  rw [CategoryTheory.Functor.map_sum, CategoryTheory.Functor.map_id] at h
  simp only [CategoryTheory.Functor.map_comp] at h
  change (∑ j ∈ Finset.range count,
    ((evaluatedCoefficient D Sc m γ i V j).total N).hom ≫
      ((evaluatedCup D Sc m γ i j).total N).hom) = _
  simp only [coefficient_total, cup_total]
  exact h
private theorem coefficients_entry (j l : ℕ) (hj : j < count) (hl : l < count) :
    evaluatedCup D Sc m γ i j ≫ evaluatedCoefficient D Sc m γ i V l =
      if j = l then 𝟙 (Superfunctor.id k (ProbeEvaluatedModules D Sc m γ)) else 0 := by
  apply OddMath.HomogeneousSuperfunctorIso.total_ext
  intro N
  apply InducedCategory.hom_ext
  have h := congrArg (evaluation (k := k) N.obj).map (V.entry j l hj hl)
  by_cases he : j = l
  · rw [ite_eq_left he] at h ⊢
    change (forgetEvaluation P N).map _ = (forgetEvaluation P N).map _
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id]
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] at h
    change ((evaluatedCup D Sc m γ i j).total N).hom ≫
      ((evaluatedCoefficient D Sc m γ i V l).total N).hom = _
    rw [cup_total, coefficient_total]
    exact h
  · rw [ite_eq_right he] at h ⊢
    change (forgetEvaluation P N).map _ = (forgetEvaluation P N).map _
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_zero]
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_zero] at h
    change ((evaluatedCup D Sc m γ i j).total N).hom ≫
      ((evaluatedCoefficient D Sc m γ i V l).total N).hom = _
    rw [cup_total, coefficient_total]
    exact h
private def evaluatedCoefficients : SKM.RouquierBoundary.Coefficients A x (D.parity i) count where
  dot_mem := probeAppendToInductionDot_mem D Sc m γ i (i :: γ) (List.Perm.refl _)
  coeff := evaluatedCoefficient D Sc m γ i V
  coeff_mem := coefficient_mem D Sc m γ i V
  total := coefficients_total D Sc m γ i V
  entry := coefficients_entry D Sc m γ i V

/-- Every prescribed missing-colour row survives restriction to evaluated modules. -/
def probeEvaluatedMissingCoefficients (hi : i ∉ γ) :
    SKM.RouquierBoundary.Coefficients A x (D.parity i) count :=
  evaluatedCoefficients D Sc m γ i (contentMissingBoundaryCoefficients D Sc cut γ i hi)

/-- The top cap, including the empty-window convention, retains the original full OLD cap. -/
theorem probeEvaluatedMissingCoefficients_cap_total (hi : i ∉ γ)
    (N : ProbeEvaluatedModules D Sc m γ) :
    ((probeEvaluatedMissingCoefficients D Sc m γ i hi).cap.total N).hom =
      (contentMissingBoundaryCoefficients D Sc cut γ i hi).cap.total N.obj := by
  by_cases h : 0 < count
  · simp only [SKM.RouquierBoundary.Coefficients.cap, h, ite_true]
    rfl
  · simp only [SKM.RouquierBoundary.Coefficients.cap, h, ite_false]
    rfl

end OddMath.QuiverHecke
end

end

section

/-! # The chosen equal crossing on scalar-evaluated OLD probes

Brundan–Ellis Definition 1.5, (1.7): restrict the prescribed negative
double-induction crossing to the full scalar-evaluated module category.
The actual balanced flattening, every input module map, and odd crossing
parity are retained. No inverse or complete-factor hypothesis is supplied.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELV ELV.BalancedInduction
open CyclotomicAction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (ν : List I) (i : I)
local notation "cut" => probeCutoff D m
local notation "J" => oldContentAppend D Sc cut ν i
local notation "K" => oldContentAppend D Sc cut (i :: ν) i
private theorem equalCross_degree :
    IsSupernatural k (D.parity i) (oldContentEqualCross D Sc cut ν i) := by
  simpa only [SKM.zmod2_mul_self] using oldContentEqualCross_supernatural D Sc cut ν i
local notation "hCross" => equalCross_degree D Sc m ν i
local notation "E" => probeEvaluatedInduction D Sc m ν i
local notation "E'" => probeEvaluatedInduction D Sc m (i :: ν) i
local notation "P" => ProbeEvaluatesCoefficients D m Sc ν
local notation "Q" => ProbeEvaluatesCoefficients D m Sc (i :: i :: ν)

private theorem doubleInduction_closed
    (N : Superfunctor k (OldContentCategory D Sc cut ν) (SVec k)) (hN : P N) :
    Q (((inductionModuleCell (k := k) J) ≫ inductionModuleCell (k := k) K).obj N) :=
  ((E ⋙ E').obj ⟨N, hN⟩).property

/-- The prescribed negative crossing, with its full underlying module map. -/
def probeEvaluatedEqualCrossComponent (N : ProbeEvaluatedModules D Sc m ν) :
    (E ⋙ E').obj N ⟶ (E ⋙ E').obj N :=
  ⟨(inductionModuleCross J K hCross).app (D.parity i) N.obj⟩

/-- The homogeneous crossing on the actual evaluated double induction. -/
def probeEvaluatedEqualCross :
    End (⟨E ⋙ E'⟩ : Superfunctor k (ProbeEvaluatedModules D Sc m ν)
      (ProbeEvaluatedModules D Sc m (i :: i :: ν))) :=
  fullLiftTrans P Q (doubleInduction_closed D Sc m ν i)
    (doubleInduction_closed D Sc m ν i) (inductionModuleCross J K hCross)

theorem probeEvaluatedEqualCross_mem :
    probeEvaluatedEqualCross D Sc m ν i ∈ parity (R := k) _ _ (D.parity i) :=
  Superfunctor.mem_parity_iff_isHomogeneous.mpr
    (fullLiftTrans_homogeneous P Q (doubleInduction_closed D Sc m ν i)
      (doubleInduction_closed D Sc m ν i) (inductionModuleCross J K hCross)
      (Superfunctor.mem_parity_iff_isHomogeneous.mp (inductionModuleCross_mem J K hCross)))

/-- Each parity component is the identical chosen OLD component. -/
theorem probeEvaluatedEqualCross_app (q : ZMod 2)
    (N : ProbeEvaluatedModules D Sc m ν) :
    ((probeEvaluatedEqualCross D Sc m ν i).app q N).hom =
      (inductionModuleCross J K hCross).app q N.obj := rfl

end OddMath.QuiverHecke
end

end
