import OddMath

/-! Concrete integral consumers of the even nilHecke prerequisites to BE2 Lemma 11.1. -/

open OddMath.EvenNilHecke

example : (1 : Presented 0) ≠ 0 := Examples.one_ne_zero
example : demazure 0 0 ≠ 0 := Examples.demazure_ne_zero
example : zeroHecke 0 0 ≠ 0 := Examples.zeroHecke_ne_zero
example : Examples.matrixMap (demazure 0 0) = !![1, 0; 0, 0] :=
  Examples.matrixMap_demazure
example : demazure 1 0 * demazure 1 1 * demazure 1 0 =
    demazure 1 1 * demazure 1 0 * demazure 1 1 := demazure_braid 0 1 rfl
example : projector 2 * projector 2 = projector 2 := projector_idempotent 2
example : Examples.matrixMap (projector 0) * Examples.matrixMap (projector 0) =
    Examples.matrixMap (projector 0) := map_projector_idempotent Examples.matrixMap
