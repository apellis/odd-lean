import OddMath.QuiverHecke.CyclotomicAction.ELVProbeEntryParity
import OddMath.QuiverHecke.CyclotomicAction.GlobalHeightDot
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.CyclotomicAction
namespace ELVProbeEntryParityConsumer
private def D : SKM.Datum Bool (Bool → ℤ) where
  cd :=
    { root := fun i j => if i = j then 2 else 0
      coroot := fun i => LinearMap.proj i
      coroot_root_self := fun i => by simp }
  isGCM :=
    { diag := fun i => by simp [CartanDatum.cartanMatrix_apply]
      offDiag_nonpos := fun i j h => by
        simp [CartanDatum.cartanMatrix_apply, Ne.symm h]
      zero_comm := fun i j => by
        by_cases h : i = j
        · subst j
          simp [CartanDatum.cartanMatrix_apply]
        · simp [CartanDatum.cartanMatrix_apply, h, Ne.symm h] }
  parity := fun i => if i then 0 else 1
  even_of_odd := by
    intro i j _
    change Even (if j = i then (2 : ℤ) else 0)
    split_ifs <;> norm_num

private def Sc : SKM.Scalars D ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := fun _ => (by norm_num : (2 : ℚ) ≠ 0).isUnit


private def m : Bool → ℕ := fun i => if i then 5 else 3
private abbrev cut := probeCutoff D m
private abbrev a : Bool → Polynomial ℚ := probePolynomial (probeDotExponent D) m
private abbrev ha := probePolynomial_parity (k := ℚ) D m

example : probeHeightMk D m Sc 0 (1 : Hn D Sc 0) ∈ heightParity D Sc a ha 0 0 :=
  probeHeightMk_parity D m Sc ha 0 (SetLike.one_mem_graded _)

example : probeHeightMk D m Sc 2 (affineLastDot D Sc false 1) ∈
    heightParity D Sc a ha 2 1 := by
  apply probeHeightMk_parity D m Sc ha 2
  exact affineLastDot_parity D Sc false 1

private abbrev w : Word Bool 2 := ⟨[false,true],rfl⟩
private def f : ELVOld.Old D Sc cut w.val w.val :=
  (ELVOld.ideal D Sc cut w.val w.val).mkQ (𝟙 (ELVOld.obj D Sc cut w.val))

example : elvProbeHeightWordEntry D m Sc w w f ∈ heightParity D Sc a ha 2 0 := by
  apply elvProbeHeightWordEntry_probeParity
  exact Submodule.mem_map_of_mem (Supercategory.id_mem _)

example : probeHeightMk D m Sc 2 (Hn.wordIdempotent w) *
    elvProbeHeightWordEntry D m Sc w w f = elvProbeHeightWordEntry D m Sc w w f :=
  elvProbeHeightWordEntry_target D m Sc w w f

example : elvProbeHeightWordEntry D m Sc w w f *
    probeHeightMk D m Sc 2 (Hn.wordIdempotent w) = elvProbeHeightWordEntry D m Sc w w f :=
  elvProbeHeightWordEntry_source D m Sc w w f

end ELVProbeEntryParityConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeEntryParity
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing owned module {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} declarations in {owner}."
