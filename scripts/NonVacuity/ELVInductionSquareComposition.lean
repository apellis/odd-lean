import OddMath.QuiverHecke.CyclotomicAction.ELVInductionSquareComposition
import OddMath.QuiverHecke.CyclotomicAction.ELVAppendQuotientComparison
import OddMath.QuiverHecke.CyclotomicAction.ELVOldAppendDot
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open ELVOld.BalancedInduction
open CyclotomicAction.AsymmetricParameters
namespace InductionSquareCompositionConsumer
private def D : SKM.Datum Bool (Bool → ℤ) :=
  { datum with
    parity := fun i => if i then 1 else 0
    even_of_odd := fun i j _ => datum.even_of_odd i j rfl }
private def Sc : SKM.Scalars D ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := by intro _; norm_num
private abbrev cut (_ : Bool) : ℕ := 8
private abbrev Q := oldTruncateFunctor D Sc cut 8
private abbrev s : OldCategory D Sc cut := ⟨[false, true]⟩
private def M := induced Q (oldRepresentable D Sc cut s)
private abbrev J (i : Bool) := CyclotomicCrossingTensor.append D Sc cut i
private abbrev T (i : Bool) := truncatedAppend D Sc cut 8 [i]
private abbrev RM := weightedRestriction D Sc cut 8 M

/-- Mixed words and both moving parities keep the two coefficient arrows in order. -/
example (i j : Bool) (v w : OldCategory D Sc cut)
    (a : (J i).obj s ⟶ v) (g : (J j).obj v ⟶ w) (b : M.obj (Q.obj s)) :=
  coendSquareMap_comp_tensor (k := ℚ) (J i) (J j) Q (T i) (T j)
    (oldAppend_truncate D Sc cut 8 i) (oldAppend_truncate D Sc cut 8 j) M s v w a g b

/-- The displayed coefficient comparison also uses the literal, ordered quotient maps. -/
example (i j : Bool) (v w : OldCategory D Sc cut)
    (a : (J i).obj s ⟶ v) (g : (J j).obj v ⟶ w) :=
  coendSquare_comp_coefficient (k := ℚ) (J i) (J j) Q (T i) (T j)
    (oldAppend_truncate D Sc cut 8 i) (oldAppend_truncate D Sc cut 8 j) s v w a g

/-- Two odd dot coefficients exercise the same ordered tensor comparison. -/
example :=
  coendSquareMap_comp_tensor (k := ℚ) (J true) (J true) Q (T true) (T true)
    (oldAppend_truncate D Sc cut 8 true) (oldAppend_truncate D Sc cut 8 true)
    M s ((J true).obj s) ((J true).obj ((J true).obj s))
    (CyclotomicCrossingTensor.oldAppendDotComponent D Sc cut true s)
    (CyclotomicCrossingTensor.oldAppendDotComponent D Sc cut true ((J true).obj s))
    (unit Q (oldRepresentable D Sc cut s).toFunctor s (𝟙 s))

private abbrev vacuum : OldCategory D Sc cut := ⟨[]⟩
private def vacuumM := induced Q (oldRepresentable D Sc cut vacuum)

/-- The source can be vacuum, with both tensor coefficients and the input unit specified. -/
example (i j : Bool) :=
  coendSquareMap_comp_tensor (k := ℚ) (J i) (J j) Q (T i) (T j)
    (oldAppend_truncate D Sc cut 8 i) (oldAppend_truncate D Sc cut 8 j)
    vacuumM vacuum ((J i).obj vacuum) ((J j).obj ((J i).obj vacuum)) (𝟙 _) (𝟙 _)
    (unit Q (oldRepresentable D Sc cut vacuum).toFunctor vacuum (𝟙 vacuum))

end InductionSquareCompositionConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVInductionSquareComposition
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner"
  let names := env.header.moduleData[idx]!.constNames
  unless names.size > 0 do throwError "Empty owner"
  for name in names do
    for ax in (← Lean.collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations"
