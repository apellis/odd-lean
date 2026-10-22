import OddMath

/-! # Consumers of the decomposition of maps between words with a common tail `i^e` -/

noncomputable section
open OddMath.QuiverHecke OddMath.QuiverHecke.AlgebraExamples

/-- Maps `[1, 0, 0] → [2, 0, 0]` split into maps `a ⊗ c` with `c ∈ End(0 0)` and maps through
words ending in `0 0 0`. -/
example (n : ℤ) (p : ZMod 2) :
    homPiece datum scalars symmetrizer homogeneous ([1] ++ List.replicate 2 0)
        ([2] ++ List.replicate 2 0) n p ≤
      Submodule.span ℚ (tailParabolic datum scalars symmetrizer homogeneous [1] [2]
          (List.replicate 2 0) n p ∪
        tailThrough datum scalars symmetrizer homogeneous [1] [2] 0 2 n p) :=
  homPiece_le_span_tail (s := [1]) (s' := [2]) rfl 0 2 n p

/-- A shuffle of `1 + 2` letters that keeps the first letter in place is the identity. -/
example (d : Equiv.Perm (Fin 3)) (hd : Categorification.TypeA.IsShuffle (show 1 + 2 = 3 from rfl) d)
    (h : (d⁻¹ 0 : ℕ) < 1) : d = 1 :=
  isShuffle_eq_one hd fun _ => h

#print axioms OddMath.QuiverHecke.homPiece_le_span_tail
