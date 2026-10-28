import OddMath.QuiverHecke.SwappedVacuumCornerEvaluation
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

/-- The quotient by the whole Hom space gives a corner evaluation of any upward action:
every field of `VacuumCornerEvaluation` is satisfiable, at the odd datum. -/
def topCornerEvaluation (μ : Bool → ℤ) (A : UpwardModuleAction oddDatum params μ)
    (s : List Bool) (raw : SYM oddDatum ℚ →ₐ[ℚ] Module.End ℚ (A.V s)) (vacuum : A.V s) :
    VacuumCornerEvaluation oddDatum params A s raw vacuum where
  K _ := ⊤
  ev _ := 0
  ev_layer _ _ _ _ _ := Subsingleton.elim _ _
  ev_vacuum _ := Subsingleton.elim _ _

/-- (7): the corner evaluation of a placed coefficient, at the odd datum. -/
example (μ : Bool → ℤ) {s t' : List Bool} (A : UpwardModuleAction oddDatum params μ)
    (raw : SYM oddDatum ℚ →ₐ[ℚ] Module.End ℚ (A.V s)) (vacuum : A.V s)
    (E : VacuumCornerEvaluation oddDatum params A s raw vacuum) (a : SYM oddDatum ℚ)
    (f : (OddMath.QuiverHecke.pres oddDatum params).obj (OddMath.QuiverHecke.ob oddDatum s) ⟶
      (OddMath.QuiverHecke.pres oddDatum params).obj (OddMath.QuiverHecke.ob oddDatum t')) :
    E.ev t' (A.act s t' ((alpha oddDatum params μ).map f) (raw a vacuum)) =
      (E.K t').mkQ (placementSign oddDatum params s t'
        (sourceCoefficientHom oddDatum params a f)) :=
  E.vacuum_evaluation a f

/-- The vacuum block from moments and a corner evaluation, at the odd datum. -/
example (μ : Bool → ℤ) {t t' : List Bool} {d : ℕ} (A : UpwardModuleAction oddDatum params μ)
    (vacuum : A.V t) (raw : SYM oddDatum ℚ →ₐ[ℚ] Module.End ℚ (A.V t))
    (hm : VacuumMoments bubbles A t raw (probeExponent oddDatum μ t d)
      (reservoirLevel oddDatum μ t d))
    (E : VacuumCornerEvaluation oddDatum params A t raw vacuum)
    (ideal_le : E.K t' ≤ ExtendedAtLeast oddDatum params t t'
      ((vacuumCutoff t d : ℤ) - 2 * t.length.choose 2)) :
    SwappedVacuumBlock oddDatum params bubbles μ t t' d :=
  SwappedVacuumBlock.ofCornerEvaluation bubbles A vacuum raw hm E ideal_le

#print axioms SwappedVacuumBlock.ofCornerEvaluation

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for i in [:env.header.moduleNames.size] do
    if env.header.moduleNames[i]! == `OddMath.QuiverHecke.SwappedVacuumCornerEvaluation then
      for name in env.header.moduleData[i]!.constNames do
        for axiomName in ← Lean.collectAxioms name do
          unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
            throwError "Disallowed axiom {axiomName} in {name}"
        count := count + 1
  if count == 0 then throwError "No owned declarations found"
  logInfo m!"Audited {count} owned declarations: standard axioms only"
