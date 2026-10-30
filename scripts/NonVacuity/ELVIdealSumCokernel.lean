import OddMath.QuiverHecke.CyclotomicAction.ELVCokernel

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath OddMath.QuiverHecke ELVOld
open scoped TensorProduct
namespace ELVIdealSumCokernelConsumer
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The former parabolic-term hypothesis is now discharged, with arbitrary coefficients. -/
example (i j : I) (v t w : List I)
    (hN : [j].length + t.length = (v ++ [i]).length) (x : ShIdx hN)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff)
    (b : hom D Sc cutoff (j :: t) w) :
    (affineUnit D Sc cutoff _ _ (shPsi D Sc [j].length x.1.1) ≫
      shuffleParabolic D Sc cutoff x a) ≫ relation D Sc cutoff j t ≫ b ∈
        appendRelations D Sc cutoff i v w ⊔
          LinearMap.range (Linear.leftComp k (obj D Sc cutoff w) (appendW D Sc cutoff i v)) :=
  parabolic_term_mem_appendRelations_sup_range D Sc cutoff i v w j t hN x a b

/-- At empty old word, only the prescribed moving-strand image remains. -/
example (i : I) (w : List I) :
    ideal D Sc cutoff [i] w =
      LinearMap.range (Linear.leftComp k (obj D Sc cutoff w) (appendW D Sc cutoff i [])) := by
  simpa only [List.nil_append, appendRelations_nil, bot_sup_eq] using
    ideal_eq_appendRelations_sup_range D Sc cutoff i [] w

/-- The identification is with the actual enlarged-word quotient, on ambient representatives. -/
example (i : I) (v w : List I) (f : hom D Sc cutoff (v ++ [i]) w) :
    pMapCokernelEquiv D Sc cutoff i v w
      (Submodule.Quotient.mk (appendProjection D Sc cutoff i v w f)) =
        (ideal D Sc cutoff (v ++ [i]) w).mkQ f := by
  rw [pMapCokernelEquiv_mk, canonicalAppendTarget_projection]

example (i : I) (v w : List I) :
    LinearMap.ker (canonicalAppendTarget D Sc cutoff i v w) =
      LinearMap.range (pMap D Sc cutoff i v w) :=
  ker_canonicalAppendTarget D Sc cutoff i v w

/-- Zero cutoff kills the exterior translation itself. -/
example (j : {j : I // D.parity j = 1}) (h : cutoff j.1 = 0) :
    SKM.SYM.elvCoefficientQuotient (k := k) D cutoff (SKM.SYM.delta D k j) = 0 :=
  firstDot_delta_cutoff_zero D cutoff j h

#print axioms firstDot_relation_transport
#print axioms outputParabolic_relation_transport
#print axioms OutputShuffle.short_eq_of_word
#print axioms OutputShuffle.long_eq_of_word
#print axioms ideal_eq_appendRelations_sup_range
#print axioms ker_canonicalAppendTarget
#print axioms pMapCokernelEquiv
end ELVIdealSumCokernelConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for owner in #[`OddMath.QuiverHecke.CyclotomicAction.ELVFirstDotTransport,
      `OddMath.QuiverHecke.CyclotomicAction.ELVParabolicTransport,
      `OddMath.QuiverHecke.OutputShuffle,
      `OddMath.QuiverHecke.CyclotomicAction.ELVIdealSum,
      `OddMath.QuiverHecke.CyclotomicAction.ELVCokernel] do
    let some idx := env.header.moduleNames.idxOf? owner
      | throwError "Module was not imported: {owner}"
    let mut count : Nat := 0
    for name in env.header.moduleData[idx]!.constNames do
      for axiomName in (← Lean.collectAxioms name) do
        unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
          throwError "Disallowed axiom {axiomName} in {name}"
      count := count + 1
    if count == 0 then throwError "Empty declaration inventory: {owner}"
    logInfo m!"Audited {count} declarations in {owner}; all axioms allowed."
