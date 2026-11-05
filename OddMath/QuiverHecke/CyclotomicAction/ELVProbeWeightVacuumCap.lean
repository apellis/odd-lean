import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightLeftCounit
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeMissingCapCoordinates
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightTensorVacuum

/-! # Empty-content coordinates of the whole-weight vacuum cap

SwappedActionAssembly F2 and SwappedVacuumNonpositiveBubbles §1 (2):
retain the empty-content forgetting map on the upper probe loop and its
full OLD boundary cap. These are the source coordinates required by the
regular-probe evaluation of the chosen central bend.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld.WeightTensorVacuum
open CyclotomicAction BalancedInduction CyclotomicCrossingTensor
attribute [local irreducible] probeAppendUpperLoopSuperIso
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)

/-- Empty-content forgetting retains the selected upper loop literally. -/
theorem forgetEmpty_upper_obj (ν : List I) (hν : ν = []) (i : I)
    (N : ProbeEvaluatedModules D Sc m ν) :
    (emptyContentForget D Sc m ν hν).obj
      ((probeEvaluatedRestriction D Sc m ν i).obj ((probeEvaluatedInduction D Sc m ν i).obj N)) =
    (restriction (oldContentAppend D Sc (probeCutoff D m) [] i)).obj
      ((induction (oldContentAppend D Sc (probeCutoff D m) [] i)).obj
        ((emptyContentForget D Sc m ν hν).obj N)) := by
  subst ν
  rfl

/-- The full boundary cap follows the same empty-content source equality. -/
theorem forgetEmpty_boundary_cap (ν : List I) (hν : ν = []) (i : I)
    (N : ProbeEvaluatedModules D Sc m ν) :
    (emptyContentForget D Sc m ν hν).map
      ((probeEvaluatedMissingCoefficients D Sc m ν i (by rw [hν]; simp)).cap.total N) =
    eqToHom (forgetEmpty_upper_obj D Sc m ν hν i N) ≫
      (contentMissingBoundaryCoefficients D Sc (probeCutoff D m) [] i (by simp)).cap.total
        ((emptyContentForget D Sc m ν hν).obj N) := by
  subst ν
  simp only [eqToHom_refl, Category.id_comp]
  change ((probeEvaluatedMissingCoefficients D Sc m [] i (by simp)).cap.total N).hom =
    (contentMissingBoundaryCoefficients D Sc (probeCutoff D m) [] i (by simp)).cap.total N.obj
  exact probeEvaluatedMissingCoefficients_cap_total D Sc m [] i (by simp) N

private def totalEvaluation {k C A : Type*} [CommRing k]
    [Category C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category A] [Preadditive A] [Linear k A] [Supercategory k A] (M : C) :
    Superfunctor k C A ⥤ A where
  obj F := F.obj M
  map f := f.total M
  map_id F := SuperNatTrans.id_total F.toFunctor M
  map_comp f g := Superfunctor.comp_total f g M

private theorem family_eqToHom {C : Type*} [Category C] (G : C ⥤ C)
    (a : ∀ M, G.obj M ⟶ M) {M N : C} (h : M = N) :
    a M ≫ eqToHom h = G.map (eqToHom h) ≫ a N := by
  subst N
  simp

private theorem emptyBlock_list (Λ : X) :
    (emptyBlock D Λ).1.toList = [] := Multiset.toList_zero

variable (Λ : X) (i : I) {y : X} (edge : -Λ + D.α i = y)
local notation "δ₀" => emptyBlock D Λ
local notation "N₀" => regularProbe D Sc m Λ
local notation "γ₀" => Multiset.toList (Subtype.val (emptyBlock D Λ))
local notation "perm" => probeOldBlockTarget_perm D i Λ edge δ₀ (blockSucc D Λ i edge δ₀) rfl
local notation "F₀" => emptyContentForget D Sc m γ₀ (emptyBlock_list D Λ)
local notation "K" => oldContentAppend D Sc (probeCutoff D m) [] i

/-- The selected successor, upper-loop, and empty-content charts identify
FE of the regular whole-weight probe with the literal native cap source. -/
def vacuumCapSourceIso [Fintype I] :
    (emptyProbe D Sc m Λ).obj
      (((probeOldE D Sc m i Λ edge) ≫ (probeOldF D Sc m i Λ edge)).obj N₀) ≅
      ProbeVacuumCap.source D Sc m i :=
  (F₀).mapIso (eqToIso (probeOldWeightFollowing_obj D Sc m i Λ edge δ₀ N₀)) ≪≫
    (F₀).mapIso ((totalEvaluation (N₀ δ₀)).mapIso
      (probeAppendUpperLoopSuperIso D Sc m γ₀ i perm).symm) ≪≫
    eqToIso (forgetEmpty_upper_obj D Sc m γ₀ (emptyBlock_list D Λ) i (N₀ δ₀)) ≪≫
    ((induction K) ⋙ (restriction K)).mapIso (eqToIso (emptyProbe_regular D Sc m Λ))

/-- The normalized whole-weight left counit at the regular probe is the
prescribed native vacuum cap under the actual FE source chart. The
nontrivial diagonal parity factor is retained explicitly. -/
theorem vacuumLeftCounit_eq [Fintype I]
    (hc : ∀ j, (probeCutoff D m j : ℤ) = D.h j Λ) (hP : 0 < probeCutoff D m i) :
    koszulSign (SKM.leftAdjParity D i (-Λ)) (SKM.leftAdjParity D i (-Λ)) •
      ((emptyProbe D Sc m Λ).map
        (((probeOldRouquierFamily D Sc m Λ hc).leftAdjoints.adjL i edge).counit.total N₀) ≫
          eqToHom (emptyProbe_regular D Sc m Λ)) =
      (vacuumCapSourceIso D Sc m Λ i edge).hom ≫ ProbeVacuumCap.cap D Sc m i hP := by
  have hneg : D.h i (-Λ) = -D.h i Λ := map_neg (D.cd.coroot i) Λ
  have hh : D.h i (-Λ) < 0 := by rw [hneg, ← hc i]; omega
  have hδ : ¬ ∃ β, blockSucc D Λ i (sub_add_cancel (-Λ) (D.α i)) β = δ₀ := by
    rw [exists_blockSucc_iff]
    change i ∉ (0 : Multiset I)
    simp
  have hi : i ∉ γ₀ := by
    change i ∉ (0 : Multiset I).toList
    rw [Multiset.toList_zero]; simp
  have hn : 0 < contentUnitCount D (probeCutoff D m) i (γ₀ : Multiset I) := by
    change 0 < contentUnitCount D (probeCutoff D m) i ((0 : Multiset I).toList : Multiset I)
    rw [Multiset.toList_zero, VacuumCoefficient.count]
    exact hP
  have hw := probeOldLeftCounit_missing D Sc m Λ hc i edge hh δ₀ hδ N₀
  have he := congrArg (F₀).map hw
  rw [CategoryTheory.Functor.map_zsmul, CategoryTheory.Functor.map_comp] at he
  have hs := probeMissingStoredLoc_cap_chart D Sc m γ₀ i perm hi hn
  have hst := congrArg (fun η => η.total (N₀ δ₀)) hs
  rw [Superfunctor.comp_total] at hst
  rw [hst, CategoryTheory.Functor.map_comp,
    forgetEmpty_boundary_cap D Sc m γ₀ (emptyBlock_list D Λ) i (N₀ δ₀)] at he
  have hout := congrArg (fun f => f ≫ eqToHom (emptyProbe_regular D Sc m Λ)) he
  rw [Preadditive.zsmul_comp] at hout
  refine hout.trans ?_
  rw [Category.assoc, Category.assoc, Category.assoc]
  have hN : (F₀).obj (N₀ δ₀) = probeOldVacuumRegular D Sc m := emptyProbe_regular D Sc m Λ
  rw [family_eqToHom ((induction K) ⋙ (restriction K))
    (fun M => (contentMissingBoundaryCoefficients D Sc (probeCutoff D m) [] i (by simp)).cap.total M)
    hN, probeMissingBoundary_regular_cap D Sc m i hP]
  simp only [vacuumCapSourceIso, Iso.trans_hom, Functor.mapIso_hom, eqToIso.hom,
    totalEvaluation, Iso.symm_hom, Category.assoc]

end OddMath.QuiverHecke.ELVOld.WeightTensorVacuum
