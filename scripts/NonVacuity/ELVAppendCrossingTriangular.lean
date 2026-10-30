import OddMath.QuiverHecke.CyclotomicAction.ELVAppendCrossingTriangular
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
example (i : I) (v t : List I) (d : ℕ)
    (g : hom D Sc cutoff v t) :
    appendMovingPower D Sc cutoff i v d ≫ rightContext D Sc cutoff [i] v t g =
      rightContext D Sc cutoff [i] v t (twist k (d • D.parity i) g) ≫
        appendMovingPower D Sc cutoff i t d :=
  appendMovingPower_twisted_rightContext D Sc cutoff i v t d g

example (i : I) (v s t : List I) (m : ℕ)
    (r : hom D Sc cutoff v (s ++ [i])) (g : hom D Sc cutoff (s ++ [i]) t) :
    rightContext D Sc cutoff [i] _ _ r ≫
        appendMovingPower D Sc cutoff i (s ++ [i]) m ≫
        affineUnit D Sc cutoff _ _ (crossLast D Sc s i i) ≫
        rightContext D Sc cutoff [i] _ _ g =
      SKM.zsign k (D.parity i * D.parity i) ^ m •
        (rightContext D Sc cutoff [i] _ _ r ≫
          affineUnit D Sc cutoff _ _ (crossLast D Sc s i i) ≫
          rightContext D Sc cutoff [i] _ _ (appendMovingPower D Sc cutoff i s m ≫ g)) +
      rightContext D Sc cutoff [i] _ _ r ≫
        appendOutputPolynomial D Sc cutoff i (s ++ [i]) t
          (appendCrossingCorrection D Sc cutoff i s t m g) :=
  appendCrossing_power_triangular_comp D Sc cutoff i v s t m r g

example (i : I) (v s t : List I) (m : ℕ)
    (r : hom D Sc cutoff v (s ++ [i])) (g : hom D Sc cutoff (s ++ [i]) t) :
    appendProjection D Sc cutoff i v (t ++ [i])
      (rightContext D Sc cutoff [i] _ _ r ≫
        appendMovingPower D Sc cutoff i (s ++ [i]) m ≫
        affineUnit D Sc cutoff _ _ (crossLast D Sc s i i) ≫
        rightContext D Sc cutoff [i] _ _ g) =
      SKM.zsign k (D.parity i * D.parity i) ^ m •
        appendProjection D Sc cutoff i v (t ++ [i])
          (rightContext D Sc cutoff [i] _ _ r ≫
            affineUnit D Sc cutoff _ _ (crossLast D Sc s i i) ≫
            rightContext D Sc cutoff [i] _ _ (appendMovingPower D Sc cutoff i s m ≫ g)) +
      appendProjection D Sc cutoff i v (t ++ [i])
        (rightContext D Sc cutoff [i] _ _ r ≫
          appendOutputPolynomial D Sc cutoff i (s ++ [i]) t
            (appendCrossingCorrection D Sc cutoff i s t m g)) :=
  appendProjection_crossing_power_triangular D Sc cutoff i v s t m r g

example (i : I) (v s t : List I)
    (r : hom D Sc cutoff v s) (f : ℕ →₀ hom D Sc cutoff s t) :
    rightContext D Sc cutoff [i] _ _ r ≫ appendOutputPolynomial D Sc cutoff i s t f =
      appendOutputPolynomial D Sc cutoff i v t
        (Finsupp.lsum k (fun d => (Finsupp.lsingle d).comp (Linear.leftComp k _ r)) f) :=
  appendOutputPolynomial_precomp D Sc cutoff i v s t r f

open Categorification.TypeA in
example (i : I) (v s t u : List I)
    (j : Fin (s.length + 1)) (m : ℕ)
    (h : SChain (s ++ [i])
      (pl (s ++ [i]) (cw (canWord (s.length + 1) (appendRun s.length j).1⁻¹))) t)
    (h' : SChain (s ++ [i] ++ [i])
      (pl (s ++ [i] ++ [i])
        (cw (canWord (s.length + 2) (appendRun (s.length + 1) j.castSucc).1⁻¹))) (t ++ [i]))
    (r : hom D Sc cutoff v (s ++ [i])) (b : hom D Sc cutoff t u) :
    let g := affineUnit D Sc cutoff _ _
      (cl D Sc _ _ (cw (canWord (s.length + 1) (appendRun s.length j).1⁻¹)) h) ≫ b
    rightContext D Sc cutoff [i] _ _ r ≫
        appendMovingPower D Sc cutoff i (s ++ [i]) m ≫
        affineUnit D Sc cutoff _ _
          (cl D Sc _ _ (cw (canWord (s.length + 2)
            (appendRun (s.length + 1) j.castSucc).1⁻¹)) h') ≫
        rightContext D Sc cutoff [i] _ _ b =
      SKM.zsign k (D.parity i * D.parity i) ^ m •
        (rightContext D Sc cutoff [i] _ _ r ≫
          affineUnit D Sc cutoff _ _ (crossLast D Sc s i i) ≫
          rightContext D Sc cutoff [i] _ _ (appendMovingPower D Sc cutoff i s m ≫ g)) +
      rightContext D Sc cutoff [i] _ _ r ≫
        appendOutputPolynomial D Sc cutoff i (s ++ [i]) u
          (appendCrossingCorrection D Sc cutoff i s u m g) :=
  appendRun_castSucc_triangular D Sc cutoff i v s t u j m h h' r b

open Categorification.TypeA in
example (i : I) (v s t u : List I)
    (j : Fin (s.length + 1)) (m : ℕ)
    (h : SChain (s ++ [i])
      (pl (s ++ [i]) (cw (canWord (s.length + 1) (appendRun s.length j).1⁻¹))) t)
    (h' : SChain (s ++ [i] ++ [i])
      (pl (s ++ [i] ++ [i])
        (cw (canWord (s.length + 2) (appendRun (s.length + 1) j.castSucc).1⁻¹))) (t ++ [i]))
    (r : hom D Sc cutoff v (s ++ [i])) (b : hom D Sc cutoff t u) :
    let g := affineUnit D Sc cutoff _ _
      (cl D Sc _ _ (cw (canWord (s.length + 1) (appendRun s.length j).1⁻¹)) h) ≫ b
    appendProjection D Sc cutoff i v (u ++ [i])
      (rightContext D Sc cutoff [i] _ _ r ≫
        appendMovingPower D Sc cutoff i (s ++ [i]) m ≫
        affineUnit D Sc cutoff _ _
          (cl D Sc _ _ (cw (canWord (s.length + 2)
            (appendRun (s.length + 1) j.castSucc).1⁻¹)) h') ≫
        rightContext D Sc cutoff [i] _ _ b) =
    appendProjection D Sc cutoff i v (u ++ [i])
      (SKM.zsign k (D.parity i * D.parity i) ^ m •
        (rightContext D Sc cutoff [i] _ _ r ≫
          affineUnit D Sc cutoff _ _ (crossLast D Sc s i i) ≫
          rightContext D Sc cutoff [i] _ _ (appendMovingPower D Sc cutoff i s m ≫ g)) +
      rightContext D Sc cutoff [i] _ _ r ≫
        appendOutputPolynomial D Sc cutoff i (s ++ [i]) u
          (appendCrossingCorrection D Sc cutoff i s u m g)) :=
  appendProjection_run_castSucc_triangular D Sc cutoff i v s t u j m h h' r b

open Lean in
run_cmd do
  let env ← Lean.getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVAppendCrossingTriangular
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing module {owner}"
  let mut count : Nat := 0
  for name in env.header.moduleData[idx]!.constNames do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
    logInfo m!"AUDIT {owner} {name}: {axioms}"
    count := count + 1
  if count == 0 then throwError "Empty declaration inventory"
  logInfo m!"Audited {count} declarations in {owner}; all axioms allowed."
