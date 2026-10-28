import OddMath.QuiverHecke.SwappedVacuumBasisEvaluation
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams OddMath.QuiverHecke OddMath.SKM
open scoped Classical

private def oddDatum : Datum Bool (Bool → ℤ) where
  cd :=
    { root := fun j i => if i = j then 2 else 0
      coroot := fun i => LinearMap.proj i
      coroot_root_self := fun i => by simp }
  isGCM :=
    { diag := fun i => by simp [CartanDatum.cartanMatrix_apply]
      offDiag_nonpos := fun i j h => by simp [CartanDatum.cartanMatrix_apply, h]
      zero_comm := fun i j => by simp [CartanDatum.cartanMatrix_apply, eq_comm] }
  parity := fun _ => 1
  even_of_odd := by
    intro i j _
    change Even (if i = j then (2 : ℤ) else 0)
    split <;> simp

private def params : Scalars oddDatum ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := fun _ => isUnit_iff_ne_zero.mpr (by norm_num)

private def bubbles : CScalars params where
  c := fun _ _ => 1
  shift := fun _ _ _ => by simp [params]

/-- The Koszul sign on the tensor basis is `±1`, at the odd datum. -/
example {t t' : List Bool} (a : SYM.CoefficientIndex oddDatum) (i : NFIdx t t') :
    basisKoszulSign (D := oddDatum) ℚ a i = 1 ∨
      basisKoszulSign (D := oddDatum) ℚ a i = -1 := by
  unfold basisKoszulSign; split <;> simp

/-- (A18) from the tensor-basis values, at the odd datum. -/
example (μ : Bool → ℤ) {t t' : List Bool} (A : UpwardModuleAction oddDatum params μ)
    (vacuum : A.V t) (raw : SYM oddDatum ℚ →ₐ[ℚ] Module.End ℚ (A.V t))
    (ideal : Submodule ℚ (coefficientObj oddDatum params t ⟶ coefficientObj oddDatum params t'))
    (coordinate : A.V t' →ₗ[ℚ]
      ((coefficientObj oddDatum params t ⟶ coefficientObj oddDatum params t') ⧸ ideal))
    (h : ∀ (a : SYM.CoefficientIndex oddDatum) (i : NFIdx t t'),
      coordinate (A.act t t' ((alpha oddDatum params μ).map i.nf)
        (raw (SYM.coefficientBasis oddDatum ℚ a) vacuum)) =
        basisKoszulSign ℚ a i • ideal.mkQ
          (sourceCoefficientHom oddDatum params (SYM.coefficientBasis oddDatum ℚ a) i.nf))
    (θ : SYM oddDatum ℚ ≃ₐ[ℚ] SYM oddDatum ℚ) (a : SYM oddDatum ℚ)
    (f : (OddMath.QuiverHecke.pres oddDatum params).obj (OddMath.QuiverHecke.ob oddDatum t) ⟶
      (OddMath.QuiverHecke.pres oddDatum params).obj (OddMath.QuiverHecke.ob oddDatum t')) :
    coordinate (A.act t t' ((alpha oddDatum params μ).map f) (raw (θ a) vacuum)) =
      ideal.mkQ (placementSign oddDatum params t t'
        (coefficientSubstitution oddDatum params θ t t'
          (sourceCoefficientHom oddDatum params a f))) :=
  vacuum_evaluation_of_basis A vacuum raw ideal coordinate θ h a f

#print axioms SwappedVacuumBlock.ofMoments

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for i in [:env.header.moduleNames.size] do
    if env.header.moduleNames[i]! == `OddMath.QuiverHecke.SwappedVacuumBasisEvaluation then
      for name in env.header.moduleData[i]!.constNames do
        for axiomName in ← Lean.collectAxioms name do
          unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
            throwError "Disallowed axiom {axiomName} in {name}"
        count := count + 1
  if count == 0 then throwError "No owned declarations found"
  logInfo m!"Audited {count} owned declarations: standard axioms only"
