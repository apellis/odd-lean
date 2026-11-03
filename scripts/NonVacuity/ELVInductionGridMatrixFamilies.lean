import OddMath.QuiverHecke.CyclotomicAction.ELVInductionGridMatrixFamilies
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeAppendCrossing
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeAppendTensors
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.ELVOld.BalancedInduction
open OddMath.QuiverHecke.ELVOld.WeightedAppendFixture
open OddMath.QuiverHecke.CyclotomicAction OddMath.SKM.SYM
namespace InductionGridMatrixFamiliesConsumer
private abbrev D := datum
private abbrev Sc := scalars
private def m : Bool → ℕ := fun i => if i then 4 else 3
private abbrev cut := probeCutoff D m
private abbrev a : Bool → Polynomial ℚ := probePolynomial (probeDotExponent D) m
private abbrev ν : List Bool := [false,true]
private def M := SuperBimodule.regular (heightParity D Sc a (probePolynomial_parity D m) 2)
private def N := probeOldModule D m Sc ν M
private abbrev hN := probeOldModule_evaluatesCoefficients D m Sc ν M
private def O := probeOrdinaryModuleSuperfunctor D Sc m ν N hN
private abbrev J (μ : List Bool) (i : Bool) := ELVOld.oldContentAppend D Sc cut μ i
private abbrev T (μ : List Bool) (i : Bool) := probeOrdinaryAppend D Sc m μ i
private abbrev Q (μ : List Bool) := probeOldOrdinaryFunctor D Sc m μ
private abbrev h (μ : List Bool) (i : Bool) := probeOldOrdinaryFunctor_append D Sc m μ i

private def M1 := SuperBimodule.regular (heightParity D Sc a (probePolynomial_parity D m) 3)
private def N1 (i : Bool) := probeOldModule D m Sc (i :: ν) M1
private abbrev hN1 (i : Bool) := probeOldModule_evaluatesCoefficients D m Sc (i :: ν) M1
private def O1 (i : Bool) := probeOrdinaryModuleSuperfunctor D Sc m (i :: ν) (N1 i) (hN1 i)


private theorem oldCross (μ : List Bool) (i : Bool) :
    IsSupernatural ℚ (D.parity i) (probeOldContentEqualCross D Sc m μ i) := by
  simpa only [zmod2_mul_self] using probeOldContentEqualCross_supernatural D Sc m μ i
private theorem ordinaryCross (μ : List Bool) (i : Bool) :
    IsSupernatural ℚ (D.parity i) (probeOrdinaryEqualCross D Sc m μ i) := by
  simpa only [zmod2_mul_self] using probeOrdinaryEqualCross_supernatural D Sc m μ i
private abbrev oldDot (μ : List Bool) (i : Bool) := probeOldContentAppendDot_supernatural D Sc m μ i
private abbrev ordinaryDot (μ : List Bool) (i : Bool) := probeOrdinaryAppendDot_supernatural D Sc m μ i

/-- Both moving parities on the literal old changing-content grid. -/
example (i : Bool) (b : ℕ) (r : Option (Fin b)) :=
  gridUnitMatrixEntry_mem (J ν i) (J (i :: ν) i) (oldCross ν i) (oldDot (i :: ν) i) (N1 i) b r
example (i : Bool) (b : ℕ) (r : Option (Fin b)) :=
  gridCapMatrixEntry_mem (J ν i) (J (i :: ν) i) (oldCross ν i) (oldDot ν i) (N1 i) b r

/-- The ordinary changing-content grid uses the same given mate and dotted entries. -/
example (i : Bool) (b : ℕ) (r : Option (Fin b)) :=
  gridUnitMatrixEntry_mem (T ν i) (T (i :: ν) i) (ordinaryCross ν i) (ordinaryDot (i :: ν) i) (O1 i) b r
example (i : Bool) (b : ℕ) (r : Option (Fin b)) :=
  gridCapMatrixEntry_mem (T ν i) (T (i :: ν) i) (ordinaryCross ν i) (ordinaryDot ν i) (O1 i) b r

example (i : Bool) (b : ℕ) (r : Fin b) :=
  gridUnitMatrixEntry_some (J ν i) (J (i :: ν) i) (oldCross ν i) (oldDot (i :: ν) i) (N1 i) b r
example (i : Bool) (b : ℕ) (r : Fin b) :=
  gridCapMatrixEntry_some (J ν i) (J (i :: ν) i) (oldCross ν i) (oldDot ν i) (N1 i) b r

/-- Every slot is computed in the actual canonical source/target coordinates. -/
example (i : Bool) (b : ℕ) (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) :=
  gridUnitMatrixEntry_none_total (J ν i) (J (i :: ν) i) (oldCross ν i) (oldDot (i :: ν) i) (N1 i) b w
example (i : Bool) (b : ℕ) (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) :=
  gridCapMatrixEntry_none_total (J ν i) (J (i :: ν) i) (oldCross ν i) (oldDot ν i) (N1 i) b w
example (i : Bool) (b : ℕ) (r : Fin b) (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) :=
  gridUnitMatrixEntry_some_total (J ν i) (J (i :: ν) i) (oldCross ν i) (oldDot (i :: ν) i) (N1 i) b r w
example (i : Bool) (b : ℕ) (r : Fin b) (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) :=
  gridCapMatrixEntry_some_total (J ν i) (J (i :: ν) i) (oldCross ν i) (oldDot ν i) (N1 i) b r w

/-- Finite assembly retains the actual pointwise superspace grading. -/
example (i : Bool) (b : ℕ) (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) :=
  gridUnitMatrixComponent_mem (J ν i) (J (i :: ν) i) (oldCross ν i) (oldDot (i :: ν) i) (N1 i) b w
example (i : Bool) (b : ℕ) (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) :=
  gridCapMatrixComponent_mem (J ν i) (J (i :: ν) i) (oldCross ν i) (oldDot ν i) (N1 i) b w
example (i : Bool) (b : ℕ) (w : OrdinaryContentCategory D Sc a (i :: ν)) :=
  gridUnitMatrixComponent_mem (T ν i) (T (i :: ν) i) (ordinaryCross ν i) (ordinaryDot (i :: ν) i) (O1 i) b w
example (i : Bool) (b : ℕ) (w : OrdinaryContentCategory D Sc a (i :: ν)) :=
  gridCapMatrixComponent_mem (T ν i) (T (i :: ν) i) (ordinaryCross ν i) (ordinaryDot ν i) (O1 i) b w

/-- These finite components are the given whole module maps. -/
example (i : Bool) (b : ℕ) (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) :=
  gridUnitMatrixModuleMap_total (J ν i) (J (i :: ν) i) (oldCross ν i) (oldDot (i :: ν) i) (N1 i) b w
example (i : Bool) (b : ℕ) (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) :=
  gridCapMatrixModuleMap_total (J ν i) (J (i :: ν) i) (oldCross ν i) (oldDot ν i) (N1 i) b w

/-- Naturality includes the inhomogeneous identity-plus-dot coefficient arrow. -/
example (i : Bool) (b : ℕ) (s : ELVOld.OldContentCategory D Sc cut ν) :=
  (gridUnitMatrixModuleMap (J ν i) (J (i :: ν) i) (oldCross ν i) (oldDot (i :: ν) i) (N1 i) b).toNatTrans.naturality
    (𝟙 ((J ν i).obj s) + probeOldContentAppendDot D Sc m ν i s)
example (i : Bool) (b : ℕ) (s : ELVOld.OldContentCategory D Sc cut ν) :=
  (gridCapMatrixModuleMap (J ν i) (J (i :: ν) i) (oldCross ν i) (oldDot ν i) (N1 i) b).toNatTrans.naturality
    (𝟙 ((J ν i).obj s) + probeOldContentAppendDot D Sc m ν i s)

private def M01 := SuperBimodule.regular (heightParity D Sc a (probePolynomial_parity D m) 1)
private def N01 (i : Bool) := probeOldModule D m Sc [i] M01
private abbrev w0 (i : Bool) : ELVOld.OldContentCategory D Sc cut [i] :=
  ELVOld.oldContentObject D Sc cut [i] ⟨[i],List.Perm.refl [i]⟩

/-- Vacuum includes the zero-size finite family and both matrix directions. -/
example (i : Bool) :=
  gridUnitMatrixComponent_mem (J [] i) (J [i] i)
    (oldCross [] i) (oldDot [i] i) (N01 i) 0 (w0 i)
example (i : Bool) :=
  gridCapMatrixComponent_mem (J [] i) (J [i] i)
    (oldCross [] i) (oldDot [] i) (N01 i) 0 (w0 i)

end InductionGridMatrixFamiliesConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVInductionGridMatrixFamilies
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing owned module {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} declarations in {owner}."
