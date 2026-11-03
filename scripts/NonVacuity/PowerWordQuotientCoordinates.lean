import OddMath.QuiverHecke.HalfTurn.PowerWordQuotientCoordinates
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
namespace NonVacuity.PowerWordQuotientCoordinates

namespace TwoOdd
private abbrev D := AsymmetricParameters.datum
private abbrev Sc := AsymmetricParameters.scalars
private def cutoff (_ : Bool) : ℕ := 20
private def L (_ : Bool × ℕ) : ℕ := 20
private abbrev s : List Bool := [false,true]
private theorem canWord_two : Categorification.TypeA.canWord s.length (1 : Equiv.Perm (Fin s.length)) = [] := by
  apply List.length_eq_zero_iff.mp
  rw [Categorification.TypeA.length_canWord, Categorification.TypeA.length_one]
private def identityNF : NFIdx s s := by
  refine ⟨([],1), by simp, by simp, ?_⟩
  simp only [List.map_nil, canWord_two, cw, List.reverse_nil, List.nil_append, pl, SChain]
private def dotNF : NFIdx s s := by
  refine ⟨([1],1), by simp, by simp, ?_⟩
  simp only [List.map_cons, List.map_nil, canWord_two, cw, List.reverse_nil, List.append_nil, pl]
  exact PG.sChain_ld (PG.dot 1) s
private theorem dotNF_par : dotNF.par D = 1 := by
  have hg : dotNF.gens = [PG.dot 1] := by
    change [PG.dot 1] ++ cw (Categorification.TypeA.canWord s.length (1 : Equiv.Perm (Fin s.length))) = _
    rw [canWord_two, cw_nil, List.append_nil]
  rw [NFIdx.par, hg]
  change D.parity true + 0 = 1
  rw [add_zero]
  rfl
private def oddIndex : SKM.SYM.CoefficientIndex D := (0,{⟨false,rfl⟩,⟨true,rfl⟩})
private def rawIndex : SKM.SYM.CoefficientIndex D := (0,{⟨true,rfl⟩})
private def rawCoefficient : SKM.SYM D ℚ := SKM.SYM.coefficientBasis D ℚ rawIndex
private def inhomogeneousCoefficient : SKM.SYM D ℚ := 1 + rawCoefficient
private def occupied : ExtendedAtMost D Sc s s 2 :=
  ⟨extensionBasis D Sc s s (oddIndex,identityNF),
    Submodule.subset_span ⟨(oddIndex,identityNF), by decide, rfl⟩⟩
private def v := powerWordHalfTurnCoordinate D Sc cutoff L s s occupied.val
private theorem powers_high (q : Bool × ℕ) : 16 ≤ L q * SKM.SYM.elementaryWeight D q := by
  have hw : 0 < SKM.SYM.elementaryWeight D q := by
    unfold SKM.SYM.elementaryWeight
    split_ifs <;> omega
  change 16 ≤ 20 * SKM.SYM.elementaryWeight D q
  omega
private theorem v_ne_zero : v ≠ 0 := by
  intro hz
  have hi := powerWordHalfTurnCoordinate_injective_on_extendedAtMost D Sc cutoff L
    (s := s) (t := s) (d := 2) (N := 16) (fun _ => (by decide : 16 ≤ 20)) powers_high (by decide)
  have he : occupied = 0 := hi (by
    change powerWordHalfTurnCoordinate D Sc cutoff L s s occupied.val =
      powerWordHalfTurnCoordinate D Sc cutoff L s s 0
    exact hz.trans (map_zero _).symm)
  exact (extensionBasis D Sc s s).ne_zero (oddIndex,identityNF) (congrArg Subtype.val he)
private abbrev g := sourceCoefficientHom D Sc 1 dotNF.nf

/-- A surviving exterior coefficient vector has its literal source class,
then the actual signed old-Hom dot acts by chronological source composition. -/
example : v ≠ 0 := v_ne_zero
example := PowerWordQuotientCoordinates.quotientEquiv_mk D Sc cutoff L s s occupied.val
example := PowerWordQuotientCoordinates.coordinate_mk D Sc cutoff L s s occupied.val
example := PowerWordQuotientCoordinates.sourceMap_apply_coordinate D Sc cutoff L occupied.val g
example := PowerWordQuotientCoordinates.coordinate_action D Sc cutoff L g v occupied.val
  (PowerWordQuotientCoordinates.coordinate_mk D Sc cutoff L s s occupied.val)
example : (PowerWordQuotientCoordinates.kernel D Sc cutoff L s s).mkQ occupied.val ≠ 0 := by
  intro hz
  have he := congrArg (PowerWordQuotientCoordinates.quotientEquiv D Sc cutoff L s s) hz
  rw [PowerWordQuotientCoordinates.quotientEquiv_mk, map_zero] at he
  exact v_ne_zero he

/-- The independent raw odd coefficient against the odd dot has the
negative source-order sign, rather than a scalar-only normalization. -/
example : reservoirSourceOrder D Sc s s (extensionBasis D Sc s s (rawIndex,dotNF)) =
    -extensionBasis D Sc s s (rawIndex,dotNF) := by
  rw [reservoirSourceOrder_basis, dotNF_par]
  simp [rawIndex, Supercategory.sign]
/-- Actual coefficient insertion includes both parities of the supplied
inhomogeneous coefficient, followed by the actual full old-Hom affine map. -/
example := PowerWordQuotientCoordinates.halfTurnOldHom_coefficient D Sc cutoff s inhomogeneousCoefficient
example := PowerWordQuotientCoordinates.sourceCoefficient_action D Sc cutoff L s inhomogeneousCoefficient
example := PowerWordQuotientCoordinates.coefficient_unit_class D Sc cutoff L s inhomogeneousCoefficient
example := PowerWordQuotientCoordinates.affine_coefficient_class D Sc cutoff L inhomogeneousCoefficient dotNF.nf
/-- Every actual vector, not only the occupied test vector, is a full
source class under the proved quotient equivalence. -/
example := PowerWordQuotientCoordinates.surjective D Sc cutoff L s s
example (w : (powerWordModule D (parameterTwist D Sc) cutoff L s.reverse).obj (OldCategory.mk s.reverse)) :
    PowerWordQuotientCoordinates.quotientEquiv D Sc cutoff L s s
      (PowerWordQuotientCoordinates.coordinate D Sc cutoff L s s w) = w :=
  (PowerWordQuotientCoordinates.quotientEquiv D Sc cutoff L s s).apply_symm_apply w
end TwoOdd

namespace Mixed
private def D : SKM.Datum Bool (Bool → ℤ) :=
  { AsymmetricParameters.datum with
    parity := fun i => if i then 1 else 0
    even_of_odd := fun i j _ => AsymmetricParameters.datum.even_of_odd i j rfl }
private def Sc : SKM.Scalars D ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := by intro _; norm_num
private def cutoff (_ : Bool) : ℕ := 20
private def L (_ : Bool × ℕ) : ℕ := 20
private abbrev s : List Bool := [false,true]
private theorem canWord_two : Categorification.TypeA.canWord s.length (1 : Equiv.Perm (Fin s.length)) = [] := by
  apply List.length_eq_zero_iff.mp
  rw [Categorification.TypeA.length_canWord, Categorification.TypeA.length_one]
private def identityNF : NFIdx s s := by
  refine ⟨([],1), by simp, by simp, ?_⟩
  simp only [List.map_nil, canWord_two, cw, List.reverse_nil, List.nil_append, pl, SChain]
private def dotNF : NFIdx s s := by
  refine ⟨([1],1), by simp, by simp, ?_⟩
  simp only [List.map_cons, List.map_nil, canWord_two, cw, List.reverse_nil, List.append_nil, pl]
  exact PG.sChain_ld (PG.dot 1) s
private theorem dotNF_par : dotNF.par D = 1 := by
  have hg : dotNF.gens = [PG.dot 1] := by
    change [PG.dot 1] ++ cw (Categorification.TypeA.canWord s.length (1 : Equiv.Perm (Fin s.length))) = _
    rw [canWord_two, cw_nil, List.append_nil]
  rw [NFIdx.par, hg]
  change D.parity true + 0 = 1
  rw [add_zero]
  rfl
private def oddIndex : SKM.SYM.CoefficientIndex D := (0,{⟨true,rfl⟩})
private def rawIndex : SKM.SYM.CoefficientIndex D := (0,{⟨true,rfl⟩})
private def rawCoefficient : SKM.SYM D ℚ := SKM.SYM.coefficientBasis D ℚ rawIndex
private def inhomogeneousCoefficient : SKM.SYM D ℚ := 1 + rawCoefficient
private def occupied : ExtendedAtMost D Sc s s 2 :=
  ⟨extensionBasis D Sc s s (oddIndex,identityNF),
    Submodule.subset_span ⟨(oddIndex,identityNF), by decide, rfl⟩⟩
private def v := powerWordHalfTurnCoordinate D Sc cutoff L s s occupied.val
private theorem powers_high (q : Bool × ℕ) : 16 ≤ L q * SKM.SYM.elementaryWeight D q := by
  have hw : 0 < SKM.SYM.elementaryWeight D q := by
    unfold SKM.SYM.elementaryWeight
    split_ifs <;> omega
  change 16 ≤ 20 * SKM.SYM.elementaryWeight D q
  omega
private theorem v_ne_zero : v ≠ 0 := by
  intro hz
  have hi := powerWordHalfTurnCoordinate_injective_on_extendedAtMost D Sc cutoff L
    (s := s) (t := s) (d := 2) (N := 16) (fun _ => (by decide : 16 ≤ 20)) powers_high (by decide)
  have he : occupied = 0 := hi (by
    change powerWordHalfTurnCoordinate D Sc cutoff L s s occupied.val =
      powerWordHalfTurnCoordinate D Sc cutoff L s s 0
    exact hz.trans (map_zero _).symm)
  exact (extensionBasis D Sc s s).ne_zero (oddIndex,identityNF) (congrArg Subtype.val he)
private abbrev g := sourceCoefficientHom D Sc 1 dotNF.nf

/-- A surviving exterior coefficient vector has its literal source class,
then the actual signed old-Hom dot acts by chronological source composition. -/
example : v ≠ 0 := v_ne_zero
example := PowerWordQuotientCoordinates.quotientEquiv_mk D Sc cutoff L s s occupied.val
example := PowerWordQuotientCoordinates.coordinate_mk D Sc cutoff L s s occupied.val
example := PowerWordQuotientCoordinates.sourceMap_apply_coordinate D Sc cutoff L occupied.val g
example := PowerWordQuotientCoordinates.coordinate_action D Sc cutoff L g v occupied.val
  (PowerWordQuotientCoordinates.coordinate_mk D Sc cutoff L s s occupied.val)
example : (PowerWordQuotientCoordinates.kernel D Sc cutoff L s s).mkQ occupied.val ≠ 0 := by
  intro hz
  have he := congrArg (PowerWordQuotientCoordinates.quotientEquiv D Sc cutoff L s s) hz
  rw [PowerWordQuotientCoordinates.quotientEquiv_mk, map_zero] at he
  exact v_ne_zero he

/-- The independent raw odd coefficient against the odd dot has the
negative source-order sign, rather than a scalar-only normalization. -/
example : reservoirSourceOrder D Sc s s (extensionBasis D Sc s s (rawIndex,dotNF)) =
    -extensionBasis D Sc s s (rawIndex,dotNF) := by
  rw [reservoirSourceOrder_basis, dotNF_par]
  simp [rawIndex, Supercategory.sign]
/-- Actual coefficient insertion includes both parities of the supplied
inhomogeneous coefficient, followed by the actual full old-Hom affine map. -/
example := PowerWordQuotientCoordinates.halfTurnOldHom_coefficient D Sc cutoff s inhomogeneousCoefficient
example := PowerWordQuotientCoordinates.sourceCoefficient_action D Sc cutoff L s inhomogeneousCoefficient
example := PowerWordQuotientCoordinates.coefficient_unit_class D Sc cutoff L s inhomogeneousCoefficient
example := PowerWordQuotientCoordinates.affine_coefficient_class D Sc cutoff L inhomogeneousCoefficient dotNF.nf
/-- Every actual vector, not only the occupied test vector, is a full
source class under the proved quotient equivalence. -/
example := PowerWordQuotientCoordinates.surjective D Sc cutoff L s s
example (w : (powerWordModule D (parameterTwist D Sc) cutoff L s.reverse).obj (OldCategory.mk s.reverse)) :
    PowerWordQuotientCoordinates.quotientEquiv D Sc cutoff L s s
      (PowerWordQuotientCoordinates.coordinate D Sc cutoff L s s w) = w :=
  (PowerWordQuotientCoordinates.quotientEquiv D Sc cutoff L s s).apply_symm_apply w
end Mixed

end NonVacuity.PowerWordQuotientCoordinates
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.HalfTurn.PowerWordQuotientCoordinates
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing module: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module: {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} owned declarations in {owner}: standard axioms"
