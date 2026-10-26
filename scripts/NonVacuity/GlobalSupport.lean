import OddMath.QuiverHecke.CyclotomicAction.GlobalSupport
import OddMath.QuiverHecke.Examples

/-! Odd rank-one specialization of full content superinduction and its dot. -/
noncomputable section
open CategoryTheory StringDiagrams
open OddMath.QuiverHecke OddMath.QuiverHecke.CyclotomicAction
open OddMath.QuiverHecke.Examples

private theorem hp : CyclotomicPolynomialParity datum (fun _ => (0 : Polynomial ℚ)) := by
  intro i m h
  simp at h

example : Supercategory ℚ (CyclotomicContentModules datum scalars (fun _ => 0) hp 0 {()}) :=
  inferInstance

example : (globalBlockDot datum scalars (fun _ => 0) hp () 0 {()}).IsHomogeneous 1 :=
  globalBlockDot_homogeneous datum scalars (fun _ => 0) hp () 0 {()}

#print axioms OddMath.QuiverHecke.CyclotomicAction.fullSupercategory
#print axioms OddMath.QuiverHecke.CyclotomicAction.fullLiftTrans
#print axioms OddMath.QuiverHecke.CyclotomicAction.globalBlockDot_homogeneous
