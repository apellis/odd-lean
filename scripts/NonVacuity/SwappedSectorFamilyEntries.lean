import OddMath.QuiverHecke.SwappedAssembly.Sigma.SectorFamilyEntries
import Mathlib.Algebra.Category.ModuleCat.Basic
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory OddMath.QuiverHecke.SwappedAssembly
open scoped ZeroObject
namespace SwappedSectorFamilyEntriesConsumer
open Classical
private def V (p : Bool → Prop) (_ : {a : Bool // p a}) : ModuleCat ℚ := ModuleCat.of ℚ ℚ
private def X (p : Bool → Prop) (n : ℕ) : Sum {a : Bool // p a} (Fin n) → ModuleCat ℚ :=
  Sum.elim (V p) (fun _ => ModuleCat.of ℚ ℚ)
private def chart (p : Bool → Prop) (n : ℕ) :=
  sectorFamilyIso p (Equiv.refl _) (X p n) (V p) (ModuleCat.of ℚ ℚ)
    (fun _ => Iso.refl _) (fun _ => Iso.refl _)
example (p : Bool → Prop) (n : ℕ) : (chart p n).hom ≫ (chart p n).inv = 𝟙 _ :=
  (chart p n).hom_inv_id
example (p : Bool → Prop) (n : ℕ) : (chart p n).inv ≫ (chart p n).hom = 𝟙 _ :=
  (chart p n).inv_hom_id
example := chart (fun _ => True) 2
example := chart (fun a => a = true) 2
example := chart (fun a => a = false) 2
example := chart (fun _ => True) 0
example := chart (fun a => a = true) 0
example := chart (fun a => a = false) 0
example : Limits.IsZero (sectorFamilyCorner (fun a => a = true) (V _) false) := by
  simpa only [sectorFamilyCorner, Bool.false_eq_true, dite_eq_right, not_false_eq_true] using
    Limits.isZero_zero (ModuleCat ℚ)
example : sectorFamilyCorner (fun a => a = true) (V _) true = ModuleCat.of ℚ ℚ := by
  simp [sectorFamilyCorner, V]
example (p q : Bool → Prop) (n m : ℕ)
    (f : ∀ a b, X p n a ⟶ X q m b)
    (z : Sum {a : Bool // p a} (Fin n)) (z' : Sum {a : Bool // q a} (Fin m)) :=
  sectorFamilyMap_entry p (Equiv.refl _) (X p n) (V p) (ModuleCat.of ℚ ℚ)
    (fun _ => Iso.refl _) (fun _ => Iso.refl _)
    q (Equiv.refl _) (X q m) (V q) (ModuleCat.of ℚ ℚ)
    (fun _ => Iso.refl _) (fun _ => Iso.refl _) f z z'
example (p : Bool → Prop) (n : ℕ) (a : {a : Bool // p a}) :=
  sectorFamilyComponentIso_pure p (Equiv.refl _) (X p n) (V p) (ModuleCat.of ℚ ℚ)
    (fun _ => Iso.refl _) (fun _ => Iso.refl _) a
example (p : Bool → Prop) (n : ℕ) (a : Fin n) :=
  sectorFamilyComponentIso_window p (Equiv.refl _) (X p n) (V p) (ModuleCat.of ℚ ℚ)
    (fun _ => Iso.refl _) (fun _ => Iso.refl _) a
end SwappedSectorFamilyEntriesConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for owner in #[`OddMath.QuiverHecke.SwappedAssembly.Sigma.SectorFamilyEntries] do
    let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
    let names := env.header.moduleData[idx]!.constNames
    if names.isEmpty then throwError "Empty owner {owner}"
    for name in names do
      for ax in ← Lean.collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
    logInfo m!"Audited all {names.size} owned declarations in {owner}"
