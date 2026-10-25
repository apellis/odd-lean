import OddMath.QuiverHecke.CyclotomicSeparation

/-! A two-strand, dot-degree-two instance of bounded cyclotomic separation. -/
noncomputable section
open CategoryTheory StringDiagrams OddMath.QuiverHecke

variable {I X k : Type} [AddCommGroup X] [CommRing k]
  (D : OddMath.SKM.Datum I X) (Sc : OddMath.SKM.Scalars D k)

example (i j : I) :
    Function.Injective (fun x : DotAtMost D Sc [i, j] [j, i] 2 =>
      (CyclotomicSpan D Sc [i, j] [j, i] 5).mkQ
        (x : (pres D Sc).obj (ob D [i, j]) ⟶ (pres D Sc).obj (ob D [j, i]))) :=
  cyclotomic_quotient_injective_on_dotAtMost D Sc (by simp) (by change 2 + 2 * (2 : ℕ).choose 2 < 5; decide)

#print axioms permutation_length_le_choose_two
#print axioms nf_firstDotPower_nf_mem
#print axioms cyclotomicSpan_le_dotAtLeast
#print axioms cyclotomic_quotient_injective_on_dotAtMost
