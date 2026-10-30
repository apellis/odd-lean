import OddMath.QuiverHecke.CyclotomicAction.ELVContentExactness
import Lean.Util.CollectAxioms

/-! The canonical quotient sequence, with unrestricted colours and cutoffs.
These consumers retain off-diagonal matrix entries, both central exponents,
and the empty-content/zero-cutoff cases. -/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

example (i : I) (ν : List I) :
    (contentShortComplex D Sc cutoff i ν).ShortExact :=
  contentShortComplex_shortExact D Sc cutoff i ν

example (i : I) : (contentShortComplex D Sc (fun _ => 0) i []).ShortExact :=
  contentShortComplex_shortExact D Sc (fun _ => 0) i []

example (i : I) (ν : List I) (z : K0 D Sc cutoff i ν) :
    pPolynomialCokernelEquiv D Sc cutoff i ν (Submodule.Quotient.mk z) =
      canonicalAppendPolynomial D Sc cutoff i ν z :=
  pPolynomialCokernelEquiv_mk D Sc cutoff i ν z

example (i : I) (ν : List I) (b : (Polynomial (ContentRing D Sc cutoff ν))ᵐᵒᵖ)
    (z : K0 D Sc cutoff i ν) :
    canonicalAppendPolynomial D Sc cutoff i ν (b • z) =
      b • canonicalAppendPolynomial D Sc cutoff i ν z :=
  (canonicalAppendPolynomial D Sc cutoff i ν).map_smul b z

example (i : I) (ν : List I) (b : (ContentRing D Sc cutoff ν)ᵐᵒᵖ)
    (z : QuotientContent D Sc cutoff i ν)
    (w : ContentWords (i :: ν)) (v : ContentWords ν) :
    (b • z) w v = ∑ t : ContentWords ν,
      quotientPull D Sc cutoff i v.val t.val w.val (b.unop (t, v)) (z w t) :=
  quotientContent_smul_apply D Sc cutoff i ν b z w v

example (i : I) (u v w : List I) (c : hom D Sc cutoff u v)
    (h : hom D Sc cutoff (v ++ [i]) w) :
    quotientPull D Sc cutoff i u v w ((ideal D Sc cutoff u v).mkQ c)
      ((ideal D Sc cutoff (v ++ [i]) w).mkQ h) =
      (ideal D Sc cutoff (u ++ [i]) w).mkQ (rightContext D Sc cutoff [i] u v c ≫ h) :=
  quotientPull_mk D Sc cutoff i c h

example (i : I) (hi : D.parity i = 0) (v w : List I)
    (h : hom D Sc cutoff (v ++ [i]) w) :
    quotientCentral D Sc cutoff i v w ((ideal D Sc cutoff (v ++ [i]) w).mkQ h) =
      (ideal D Sc cutoff (v ++ [i]) w).mkQ (appendMovingPower D Sc cutoff i v 1 ≫ h) := by
  simpa [centralDegree, hi] using quotientCentral_mk D Sc cutoff i v w h

example (i : I) (hi : D.parity i = 1) (v w : List I)
    (h : hom D Sc cutoff (v ++ [i]) w) :
    quotientCentral D Sc cutoff i v w ((ideal D Sc cutoff (v ++ [i]) w).mkQ h) =
      (ideal D Sc cutoff (v ++ [i]) w).mkQ (appendMovingPower D Sc cutoff i v 2 ≫ h) := by
  simpa [centralDegree, hi] using quotientCentral_mk D Sc cutoff i v w h

example (i : I) (ν : List I) (z : QuotientContent D Sc cutoff i ν) :
    MulOpposite.op (Polynomial.X : Polynomial (ContentRing D Sc cutoff ν)) •
      RightCentralPolynomialModule.of (quotientContentCentral D Sc cutoff i ν) z =
      RightCentralPolynomialModule.of _ (quotientContentCentral D Sc cutoff i ν z) :=
  quotientPolynomial_X D Sc cutoff i ν z

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for owner in #[`OddMath.QuiverHecke.CyclotomicAction.ELVQuotientPresheaf,
      `OddMath.QuiverHecke.CyclotomicAction.ELVContentExactness] do
    let some idx := env.header.moduleNames.idxOf? owner
      | throwError "Missing module {owner}"
    let mut count : Nat := 0
    for name in env.header.moduleData[idx]!.constNames do
      let axioms ← Lean.collectAxioms name
      for axiomName in axioms do
        unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
          throwError "Disallowed axiom {axiomName} in {name}"
      count := count + 1
    if count == 0 then throwError "Empty declaration inventory for {owner}"
    logInfo m!"Audited {count} declarations in {owner}; all axioms allowed."
