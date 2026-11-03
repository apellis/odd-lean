import OddMath.QuiverHecke.CyclotomicAction.ELVContentCapNaturality
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeCapWindow
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.ELVOld OddMath.QuiverHecke.ELVOld.BalancedInduction
open OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
namespace NonVacuity.ELVContentCapNaturality
private theorem post_iso_nonzero {C : Type*} [Category* C] [Preadditive C]
    {X Y Z : C} (f : X ⟶ Y) (e : Y ≅ Z) (hf : f ≠ 0) : f ≫ e.hom ≠ 0 := by
  intro h
  apply hf
  have hh := congrArg (fun g => g ≫ e.inv) h
  simpa [Category.assoc] using hh

private theorem neg_ne_self_of_ne_zero {V : Type*} [AddCommGroup V] [Module ℚ V]
    (v : V) (hv : v ≠ 0) : -v ≠ v := by
  intro h
  have ha : v + v = 0 := (congrArg (fun z => v + z) h.symm).trans (add_neg_cancel v)
  have hs : (2 : ℚ) • v = 0 := by simpa only [two_smul] using ha
  exact hv ((smul_eq_zero.mp hs).resolve_left (by norm_num))

private theorem odd_supernatural_sign
    {C B : Type*} [Category* C] [Category* B]
    [Preadditive C] [Linear ℚ C] [Supercategory ℚ C]
    [Preadditive B] [Linear ℚ B] [Supercategory ℚ B]
    {F G : C ⥤ B} {p : ZMod 2} {a : ∀ M, F.obj M ⟶ G.obj M}
    (ha : IsSupernatural ℚ p a) (hp : p = 1)
    {M N : C} {f : M ⟶ N} (hf : f ∈ parity (R := ℚ) M N 1) :
    F.map f ≫ a N = -(a M ≫ G.map f) := by
  have h := ha.naturality hf
  rw [hp, mul_one, sign_one, neg_one_smul] at h
  exact h

private theorem odd_shift_naturality
    {C : Type*} [Category* C] [Preadditive C] [Linear ℚ C] [Supercategory ℚ C]
    [PiSupercategory ℚ C] {F : C ⥤ C} {p : ZMod 2} {a : ∀ M, F.obj M ⟶ M}
    (ha : IsSupernatural ℚ p (F := F) (G := 𝟭 C) a) (hp : p = 1) (M : C) :
    F.map (((SKM.homParityShiftDatum (k := ℚ) 1).iso M).inv) ≫
      a ((SKM.homParityShift (k := ℚ) 1).obj M) =
    -(a M ≫ ((SKM.homParityShiftDatum (k := ℚ) 1).iso M).inv) :=
  odd_supernatural_sign ha hp ((SKM.homParityShiftDatum (k := ℚ) 1).inv_mem M)

private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev Sc := CyclotomicAction.AsymmetricParameters.scalars
private def m (i : Bool) : ℕ := if i then 2 else 1
private abbrev cut := probeCutoff D m
private abbrev C := OldContentCategory D Sc cut []
private def N : Superfunctor ℚ C (SVec ℚ) := probeOldVacuumRegular D Sc m
private abbrev K (i : Bool) := oldContentAppend D Sc cut [] i
private theorem positive (i : Bool) : 0 < cut i := by cases i <;> decide
private theorem row_degree (i : Bool) : (cut i - 1) • D.parity i = (1 : ZMod 2) := by
  cases i <;> decide
private theorem height (i : Bool) : 0 ≤ contentCrossingHeight D cut i (([] : List Bool) : Multiset Bool) := by
  simp [contentCrossingHeight]
private def last (i : Bool) : Fin (contentUnitCount D cut i (([] : List Bool) : Multiset Bool)) :=
  ⟨cut i - 1, by rw [VacuumCoefficient.count]; exact Nat.sub_lt (positive i) (by decide)⟩
local instance : PiSupercategory ℚ (Superfunctor ℚ C (SVec ℚ)) := supermodulePiSupercategory
private abbrev P := SKM.homParityShiftDatum (k := ℚ) (C := Superfunctor ℚ C (SVec ℚ)) 1
private abbrev N' := (SKM.homParityShift (k := ℚ) 1).obj N
private abbrev f : N ⟶ N' := (P.iso N).inv
private abbrev row (i : Bool) (M : Superfunctor ℚ C (SVec ℚ)) :=
  contentCoefficientCap D Sc cut [] i M (height i) (last i)

/-- The canonical odd shift comparison is a genuine odd input map. The
actual odd inverse row anticommutes with this map, including at empty output. -/
private theorem signed_naturality (i : Bool) :
    (induction (K i) ⋙ restriction (K i)).map f ≫ row i N' = -(row i N ≫ f) := by
  exact odd_shift_naturality
    (contentCoefficientCap_supernatural D Sc cut [] i (height i) (last i))
    (row_degree i) N

private theorem row_ne_zero (i : Bool) : row i N ≠ 0 := by
  exact ProbeVacuumCap.cap_ne_zero D Sc m i (positive i)

private theorem post_row_ne_zero (i : Bool) : row i N ≫ f ≠ 0 :=
  post_iso_nonzero (row i N) (P.iso N).symm (row_ne_zero i)

/-- The odd input map exposes a nonzero minus sign; ordinary unsigned
input naturality would be false on this actual regular probe. -/
example (i : Bool) :
    (induction (K i) ⋙ restriction (K i)).map f ≫ row i N' ≠ row i N ≫ f := by
  rw [signed_naturality]
  exact neg_ne_self_of_ne_zero _ (post_row_ne_zero i)

example (i : Bool) (M : Superfunctor ℚ C (SVec ℚ)) :
    (contentCoefficientCapFamily D Sc cut [] i (height i) (last i)).total M = row i M :=
  contentCoefficientCapFamily_total D Sc cut [] i (height i) (last i) M
end NonVacuity.ELVContentCapNaturality
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVContentCapNaturality
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing module: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module: {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} owned declarations in {owner}: standard axioms"
