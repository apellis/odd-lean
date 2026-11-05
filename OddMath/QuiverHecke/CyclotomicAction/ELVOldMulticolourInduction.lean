/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVModuleMulticolourBraid
import OddMath.QuiverHecke.CyclotomicAction.ELVOldMulticolourBraid

/-! # Multicolour OLD braids on direct triple induction

Brundan–Ellis (1.9): the independently whiskered positive coefficient
crossings induce the whole direct triple-induction braid. The actual
OLD quotient supplies the source relation; no braid premise is introduced.
The negative equal-colour crossing normalization, rectangular flattening
and repeated-outer ordered correction are separate attachments.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
open BalancedInduction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The append along the prescribed three source colours. -/
abbrev tripleAppend (i j l : I) :=
  (append D Sc cutoff i ⋙ append D Sc cutoff j) ⋙ append D Sc cutoff l

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
