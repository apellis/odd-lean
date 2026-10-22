/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.HomDimension
import OddMath.QuiverHecke.EnvelopeProducts
import OddMath.QuiverHecke.AlgebraExamples

/-!
# Graded pieces of `Hom_H` and products of words: consumers

For the datum with countably many odd colours over `ℚ`: every graded piece of every Hom space
of `H` has dimension the number of normal forms of its degree and parity, and words multiply by
concatenation in `K₀(Ḣ_{q,π})` with BE2's product. The Hom spaces of `H` are bounded below, and
`K₀(Ḣ_{q,π})` is free over `ℤ[q, q⁻¹]`.
-/

noncomputable section
namespace OddMath.QuiverHecke.HomDimensionExamples
open CategoryTheory StringDiagrams AlgebraExamples

example (t t' : List ℕ) (n : ℤ) (p : ZMod 2) :
    Module.finrank ℚ (homPiece datum scalars symmetrizer homogeneous t t' n p) =
      Nat.card {i : NFIdx t t' | i.par datum = p ∧ i.deg datum symmetrizer = n} :=
  finrank_homPiece datum symmetrizer scalars homogeneous t t' n p

example (s t : List ℕ) :
    wordCls datum scalars symmetrizer homogeneous s *
        wordCls datum scalars symmetrizer homogeneous t =
      wordCls datum scalars symmetrizer homogeneous (s ++ t) :=
  wordCls_mul datum scalars symmetrizer homogeneous s t

example : GSKar.HomBoundedBelow (k := ℚ)
    (C := HGr datum scalars symmetrizer homogeneous) :=
  homBoundedBelow datum symmetrizer scalars homogeneous

example :
    letI := K₀.moduleLaurentInt ℚ (GSKar ℚ (HGr datum scalars symmetrizer homogeneous))
    Module.Free (LaurentPolynomial ℤ) (K₀ (GSKar ℚ (HGr datum scalars symmetrizer homogeneous))) :=
  k0_free_laurentInt datum symmetrizer scalars homogeneous

end OddMath.QuiverHecke.HomDimensionExamples
