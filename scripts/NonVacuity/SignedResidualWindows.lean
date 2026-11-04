import OddMath.QuiverHecke.SwappedAssembly.CentralInverse.SignedResidualWindows
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory
open OddMath.QuiverHecke.SwappedAssembly.ProbeWindow
namespace NonVacuity.SignedResidualWindows
private abbrev L := ModuleCat.of ℚ ℚ
private abbrev Z := ModuleCat.of ℚ (Fin 0 → ℚ)
private theorem id_zero : (𝟙 Z : Z ⟶ Z) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  funext i
  exact Fin.elim0 i

private def oneAut (A : ModuleCat ℚ) : Aut A := 1
@[local simp] private theorem oneAut_zpow_hom (A : ModuleCat ℚ) (n : ℤ) :
    (oneAut A ^ n).hom = 𝟙 A := by
  change ((1 : Aut A) ^ n).hom = 𝟙 A
  rw [one_zpow]
  rfl
@[local simp] private theorem aut_one_hom (A : ModuleCat ℚ) :
    (1 : Aut A).hom = 𝟙 A := rfl
@[local simp] private theorem oneAut_inv_hom (A : ModuleCat ℚ) :
    (oneAut A)⁻¹.hom = 𝟙 A := rfl

private def J : CoefficientIdeal (ModuleCat ℚ) where
  mem n {_ _} f := n = 0 ∨ f = 0
  zero_mem _ := Or.inr rfl
  add_mem := by rintro n A B f g (hn | hf) (hm | hg) <;> simp_all
  neg_mem := by rintro n A B f (hn | hf) <;> simp_all
  mono := by rintro n A B f (hn | hf); omega; exact Or.inr hf
  comp_mem := by
    rintro m n A B C f g (hm | hf) (hn | hg) <;> simp_all
  bound := 1
  eq_zero := by rintro A B f (hn | hf); omega; exact hf

private theorem probeInverse : IsCupInverse (0 : Z ⟶ L)
    (fun _ : Fin 1 => (𝟙 L : L ⟶ L)) (0 : L ⟶ Z) (fun _ => 𝟙 L) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [id_zero]
  · intro n; simp
  · intro n; simp
  · intro m n; have he : m = n := Subsingleton.elim _ _; simp [he]
  · simp

private def rows (n : ℕ) : L ⟶ L := if n = 0 then 𝟙 L else 0
private theorem reservoirCap : IsCapInverse (0 : L ⟶ Z)
    (fun n : Fin 1 => rows n.val) (0 : Z ⟶ L) (fun _ => 𝟙 L) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [id_zero]
  · intro n; simp
  · intro n; simp
  · intro m n; fin_cases m; fin_cases n; simp [rows]
  · simp [rows]
private theorem reservoirCup : IsCupInverse (0 : Z ⟶ L)
    (fun n : Fin 1 => rows n.val) (0 : L ⟶ Z) (fun _ => 𝟙 L) := by
  simpa [rows] using probeInverse

-- The signed-height theorem derives the residual errors from the two bend series.
example : IsIso (posMap (0 : L ⟶ Z) (0 : Z ⟶ L) (𝟙 L) (0 : Z ⟶ Z)
    rows (fun a : Fin ((1 : ℤ) + (-1)).toNat =>
      ((oneAut Z) ^ (a : ℤ)).hom ≫ (0 : Z ⟶ L))) := by
  apply isIso_posMap_of_signed_windows J (fun _ => Or.inl rfl) rows (fun _ => (0 : L ⟶ Z))
    (oneAut Z) (oneAut L) (0 : Z ⟶ L) (𝟙 L) (-1) (by norm_num) (by simp)
    1 (-1) (N := 1)
  · norm_num
  · simp
  · simp [rows]
  · intro _
    refine ⟨0, fun _ => 𝟙 L, reservoirCap, ?_, ?_⟩
    · intro r s; exact Or.inr (by simp)
    · intro n m hm; exact Or.inr (by simp [rows, show m ≠ 0 by omega])
  · intro hr; omega
  · intro hp; omega
  · intro _
    refine ⟨0, fun _ => 𝟙 L, ?_⟩
    simpa using probeInverse
  · norm_num

example : IsIso (negMap (0 : Z ⟶ L) (0 : Z ⟶ L) (0 : Z ⟶ L) (0 : Z ⟶ L)
    rows (fun a : Fin (-((-1 : ℤ) + (-1))).toNat =>
      (𝟙 L) ≫ ((oneAut L) ^ (a : ℤ)).hom)) := by
  apply isIso_negMap_of_signed_windows J (fun _ => Or.inl rfl) (fun _ => (0 : Z ⟶ L)) rows
    (oneAut Z) (oneAut L) (0 : Z ⟶ L) (𝟙 L) (-1) (by norm_num) (by simp)
    (-1) (-1) (N := 1)
  · norm_num
  · simp
  · simp
  · intro hr; omega
  · intro _
    refine ⟨0, fun _ => 𝟙 L, reservoirCup, ?_, ?_⟩
    · intro r s; exact Or.inr (by simp)
    · intro n m hm; exact Or.inr (by simp [rows, show m ≠ 0 by omega])
  · intro hp; omega
  · intro _
    refine ⟨0, fun _ => 𝟙 L, ?_⟩
    simpa using probeInverse
  · norm_num

example : (𝟙 L : L ⟶ L) ≠ 0 := by
  intro h
  have hh := congrArg (fun f : L ⟶ L => f.hom 1) h
  norm_num at hh

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.SwappedAssembly.CentralInverse.SignedResidualWindows
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing module"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "No owned declarations"
  for name in names do
    for axiomName in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
  logInfo m!"Audited {names.size} owned declarations: standard axioms only"
end NonVacuity.SignedResidualWindows
