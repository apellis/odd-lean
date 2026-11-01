import OddMath.QuiverHecke.CyclotomicAction.ELVProbeContentSpecialization
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams OddMath OddMath.QuiverHecke OddMath.SKM.SYM
open OddMath.QuiverHecke.CyclotomicAction
namespace ELVProbeContentSpecializationConsumer
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
private abbrev ν : List Bool := [false,true]
private abbrev v : ELVOld.ContentWords ν := ⟨ν, List.Perm.refl _⟩

example : ProbeHeightContentCorner D m Sc [false,true] =
    CyclotomicContentCorner D Sc a 1 ([false,true] : Multiset Bool) :=
  probeHeightContentCorner_cons D m Sc false [true]

example : (elvProbeContentSpecialization D m Sc [] 1).val = (1 : Hn D Sc 0) :=
  elvProbeContentSpecialization_nil_one D m Sc

example : (elvProbeContentSpecialization D m Sc ν
    (FiniteHomMatrix.single v v ((ELVOld.ideal D Sc cut ν ν).mkQ (𝟙 (ELVOld.obj D Sc cut ν))))).val =
      probeHeightMk D m Sc 2 (Hn.wordIdempotent (probeContentWord ν v)) := by
  rw [elvProbeContentSpecialization_single]
  exact elvProbeHeightWordEntry_id D m Sc (⟨[false,true],rfl⟩ : Word Bool 2)

private def c : ELVOld.hom D Sc cut ν ν :=
  elvQuotientMap D Sc cut _ _ (sourceCoefficientHom D Sc (e D ℚ false 0)
    (𝟙 ((pres D Sc).obj (ob D ν))))

example : (elvProbeContentSpecialization D m Sc ν
    (FiniteHomMatrix.single v v ((ELVOld.ideal D Sc cut ν ν).mkQ c))).val =
      (-3 : ℚ) • probeHeightMk D m Sc 2 (Hn.wordIdempotent (probeContentWord ν v)) := by
  rw [elvProbeContentSpecialization_single]
  change elvProbeHeightWordEntry D m Sc (⟨ν,rfl⟩ : Word Bool 2) (⟨ν,rfl⟩ : Word Bool 2)
    ((ELVOld.ideal D Sc cut ν ν).mkQ c) = _
  rw [elvProbeHeightWordEntry_mk]
  change probeHeightMk D m Sc 2
      (FiniteHomMatrix.single (⟨ν,rfl⟩ : Word Bool 2) (⟨ν,rfl⟩ : Word Bool 2)
        ((elvProbeAffineSpecialization D m Sc).map
          (elvQuotientMap D Sc cut _ _ (sourceCoefficientHom D Sc (e D ℚ false 0)
            (𝟙 ((pres D Sc).obj (ob D ν))))))) = _
  rw [elvAffineScalarSpecialization_source, scalarEvaluation_e]
  have hv : probeScalarValues (k := ℚ) D m (false,0) = -3 := by
    norm_num [probeScalarValues, D, m]
  rw [hv, FiniteHomMatrix.single_smul, map_smul]
  rfl

private def w0 : Word Bool 0 := vacuumWord
private def f0 : ELVOld.Old D Sc cut [] [] := (ELVOld.ideal D Sc cut [] []).mkQ (𝟙 (ELVOld.obj D Sc cut []))

example : heightAppend D Sc a false 0 (elvProbeHeightWordEntry D m Sc w0 w0 f0) =
    elvProbeHeightWordEntry D m Sc (appendWord false w0) (appendWord false w0)
      (elvProbeOldRightContext D m Sc [false] [] [] f0) :=
  elvProbeHeightWordEntry_append D m Sc false w0 w0 f0

example :
    heightAppend D Sc a true 2
        (elvProbeContentSpecialization D m Sc ν
          (FiniteHomMatrix.single v v ((ELVOld.ideal D Sc cut ν ν).mkQ c))).val =
      (elvProbeContentSpecialization D m Sc (true::ν)
        (FiniteHomMatrix.single (probeContentAppendWord true ν v) (probeContentAppendWord true ν v)
          (elvProbeOldRightContext D m Sc [true] ν ν ((ELVOld.ideal D Sc cut ν ν).mkQ c)))).val :=
  elvProbeContentSpecialization_append_single D m Sc true ν v v _

end ELVProbeContentSpecializationConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeContentSpecialization
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing owned module {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} declarations in {owner}."
