import OddMath.QuiverHecke.CyclotomicAction.ELVProbeMissingStoredLocal
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumVector
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.ELVOld.BalancedInduction
open OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
open OddMath.QuiverHecke.CyclotomicAction
namespace NonVacuity.ELVProbeMissingStoredLocal
private abbrev D := WeightedAppendFixture.datum
private abbrev Sc := WeightedAppendFixture.scalars
private def m (i : Bool) : ℕ := if i then 2 else 3
private abbrev cut := probeCutoff D m
private abbrev a : Bool → Polynomial ℚ := probePolynomial (probeDotExponent D) m
private def R (γ : List Bool) := SuperBimodule.regular
  (heightParity D Sc a (probePolynomial_parity D m) γ.length)
private def N (γ : List Bool) : ProbeEvaluatedModules D Sc m γ :=
  ⟨probeOldModule D m Sc γ (R γ), probeOldModule_evaluatesCoefficients D m Sc γ (R γ)⟩
private def shifted (γ : List Bool) : ProbeEvaluatedModules D Sc m γ :=
  ⟨supermoduleParityObj (N γ).obj,
    probeEvaluatesCoefficients_parity D Sc m γ (N γ).obj (N γ).property⟩
private def oddInput (γ : List Bool) : shifted γ ⟶ N γ := ⟨(supermoduleParityIso (N γ).obj).hom⟩
private theorem oddInput_mem (γ : List Bool) : oddInput γ ∈ parity (R := ℚ) _ _ 1 :=
  supermoduleParityIso_hom_mem (N γ).obj
private abbrev count (γ : List Bool) (i : Bool) := contentUnitCount D cut i (γ : Multiset Bool)
private theorem upper (γ : List Bool) (i : Bool) : (i :: γ).Perm (γ ++ [i]) :=
  (show ([i] ++ γ).Perm (γ ++ [i]) from List.perm_append_comm)
private def L (γ : List Bool) (i : Bool) (hi : i ∉ γ) :=
  probeMissingStoredLoc D Sc m γ i (upper γ i) hi
private theorem negative (γ : List Bool) (i : Bool) (hi : i ∉ γ) :
    -contentCrossingHeight D cut i (γ : Multiset Bool) ≤ 0 :=
  neg_nonpos.mpr (contentCrossingHeight_nonneg_of_not_mem D cut γ i hi)
private def J (γ : List Bool) (i : Bool) (hi : i ∉ γ) :=
  (L γ i hi).invNeg (negative γ i hi)
private theorem window (γ : List Bool) (i : Bool) :
    (-(-contentCrossingHeight D cut i (γ : Multiset Bool))).toNat = count γ i := by
  rw [neg_neg]
  rfl
private def other (i : Bool) : List Bool := [!i]
private theorem absent (i : Bool) : i ∉ other i := by cases i <;> decide
private theorem positive (i : Bool) : 0 < count [] i := by
  cases i <;> decide

private theorem inverse_column_apply
    {C : Type} [Category.{0} C] [Preadditive C] [Linear ℚ C] [Supercategory ℚ C]
    {M T : Superfunctor ℚ C (SVec ℚ)} (u : M ⟶ T) (v : T ⟶ M) (h : u ≫ v = 𝟙 M)
    (w : C) (b : M.obj w) : v.total w (u.total w b) = b := by
  have he := congrArg (fun f : M ⟶ M => f.total w b) h
  rw [Superfunctor.comp_total, SVec.comp_apply] at he
  have hi : (𝟙 M : M ⟶ M).total w = 𝟙 (M.obj w) := SuperNatTrans.id_total M.toFunctor w
  rw [hi, SVec.id_apply] at he
  exact he

-- The source is the actual regular evaluated probe with its nonzero PBW vacuum.
example : (N []).obj = probeOldVacuumRegular D Sc m := rfl
example : probeOldVacuumVector D Sc m ≠ 0 := probeOldVacuumVector_ne_zero D Sc m

example (i : Bool) := (L [] i (by simp)).slide_left
example (i : Bool) := (L [] i (by simp)).slide_right
example (i : Bool) := (J [] i (by simp)).total
example (i : Bool) := (J [] i (by simp)).ff
example (i : Bool) (n : ℕ) := (J [] i (by simp)).g'_mem n
example (i : Bool) := (J (other i) i (absent i)).total
example (i : Bool) := (L (other i) i (absent i)).dot₂_mem
example (i : Bool) (j l : ℕ) (hj : j < count (other i) i) (hl : l < count (other i) i) :=
  (J (other i) i (absent i)).gg j l (by simpa only [window] using hj) (by simpa only [window] using hl)
example (i : Bool) (n : ℕ) := ((J (other i) i (absent i)).g' n).naturality
  ((n : ZMod 2) * D.parity i) (oddInput (other i)) (oddInput_mem (other i))

-- The actual local inverse row extracts a nonzero ground vector from its prescribed dotted unit.
example (i : Bool) :
    ((((J [] i (by simp)).g' (count [] i - 1)).total (N [])).hom).total (probeOldVacuumObject D Sc m)
      ((((SKM.RouquierBoundary.cup (probeAppendToRightAdjunction D Sc m [] i ([] ++ [i]) (upper [] i))
        (probeAppendToInductionDot D Sc m [] i ([] ++ [i]) (upper [] i)) (count [] i - 1)).total (N [])).hom).total
          (probeOldVacuumObject D Sc m) (probeOldVacuumVector D Sc m)) ≠ 0 := by
  have h := (J [] i (by simp)).gg (count [] i - 1) (count [] i - 1)
    (by simpa only [window] using Nat.sub_lt (positive i) (by decide))
    (by simpa only [window] using Nat.sub_lt (positive i) (by decide))
  rw [ite_eq_left rfl] at h
  have hN := congrArg (fun f : (𝟙 (probeEvaluatedTarget D Sc m [])) ⟶
      (𝟙 (probeEvaluatedTarget D Sc m [])) => (f.total (N [])).hom) h
  rw [Superfunctor.comp_total] at hN
  have hid : (𝟙 (𝟙 (probeEvaluatedTarget D Sc m [])) :
      End (𝟙 (probeEvaluatedTarget D Sc m []))).total (N []) = 𝟙 (N []) :=
    SuperNatTrans.id_total (𝟭 (ProbeEvaluatedModules D Sc m [])) (N [])
  rw [hid, InducedCategory.comp_hom, InducedCategory.id_hom] at hN
  have hv := inverse_column_apply _ _ hN (probeOldVacuumObject D Sc m) (probeOldVacuumVector D Sc m)
  exact fun hz => probeOldVacuumVector_ne_zero D Sc m (hv.symm.trans hz)

-- Empty finite window is retained without a positive-cutoff hypothesis.
example (i : Bool) : contentUnitCount D (probeCutoff D (fun _ : Bool => 0)) i (0 : Multiset Bool) = 0 := by
  cases i <;> decide
private def Lzero (i : Bool) := probeMissingStoredLoc D Sc (fun _ => 0) [] i (upper [] i) (by simp)
example (i : Bool) := ((Lzero i).invPos (by cases i <;> decide)).total
example (i : Bool) := ((Lzero i).invPos (by cases i <;> decide)).ff
example (i : Bool) := ((Lzero i).invNeg (by cases i <;> decide)).total
example (i : Bool) := ((Lzero i).invNeg (by cases i <;> decide)).ff
example : probeOldVacuumVector D Sc (fun _ : Bool => 0) ≠ 0 :=
  probeOldVacuumVector_ne_zero D Sc (fun _ : Bool => 0)
end NonVacuity.ELVProbeMissingStoredLocal
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeMissingStoredLocal
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations in {owner}"
