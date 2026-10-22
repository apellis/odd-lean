import OddMath

/-! # The quantum Serre relations in `K₀(Ḣ_{q,π})` (input to BE2 Theorem 11.3)

The rank-two datum of `scripts/NonVacuity/SerreClass.lean` (type `B₂`, `true` odd,
`d_{true,false} = 2`, `d_{false,true} = 1`) with the symmetrizer `d_true = 1`, `d_false = 2`, over
`ℚ`. Both orders of the two colours are exercised, and Lemma 11.1 for an odd colour.
-/

noncomputable section
open OddMath OddMath.QuiverHecke

namespace NonVacuity.EnvelopeSerre

/-- A rank-two datum: `true` is odd, `a_{true,false} = -2`, `a_{false,true} = -1`. -/
def datum : SKM.Datum Bool (Bool → ℤ) where
  cd :=
    { root := fun j i => if i = j then 2 else if i then -2 else -1
      coroot := fun i => LinearMap.proj i
      coroot_root_self := fun i => by simp }
  isGCM :=
    { diag := fun i => by simp [CartanDatum.cartanMatrix_apply]
      offDiag_nonpos := fun i j h => by
        cases i <;> cases j <;> simp_all [CartanDatum.cartanMatrix_apply]
      zero_comm := fun i j => by
        cases i <;> cases j <;> simp [CartanDatum.cartanMatrix_apply] }
  parity := fun i => if i then 1 else 0
  even_of_odd := by
    intro i j hi
    cases i
    · simp at hi
    · cases j <;> simp

def scalars : SKM.Scalars datum ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := fun _ => isUnit_iff_ne_zero.mpr (by norm_num)

theorem dn_true_false : datum.dn true false = 2 := by decide

theorem dn_false_true : datum.dn false true = 1 := by decide

def symmetrizer : SKM.Symmetrizer datum where
  d := fun i => if i then 1 else 2
  pos := fun i => by cases i <;> decide
  symm := by
    intro i j
    cases i <;> cases j <;> simp [SKM.Datum.d, SKM.Datum.h, SKM.Datum.α, datum]

theorem homogeneous : scalars.Homogeneous := fun _ _ _ _ _ _ _ _ h => absurd rfl h

/-- `i` odd, `M = 3`: the Serre relation for the words `i^{3-r} j i^r`. -/
example : ∑ r ∈ Finset.range 4, SerreComplex.serreC symmetrizer true false 3 r •
    wordCls datum scalars symmetrizer homogeneous
      (List.replicate (3 - r) true ++ [false] ++ List.replicate r true) = 0 :=
  serre_words (by decide) (by rw [dn_true_false])

/-- `i` even, `M = 2`. -/
example : ∑ r ∈ Finset.range 3, SerreComplex.serreC symmetrizer false true 2 r •
    wordCls datum scalars symmetrizer homogeneous
      (List.replicate (2 - r) false ++ [true] ++ List.replicate r false) = 0 :=
  serre_words (by decide) (by rw [dn_false_true])

/-- Lemma 11.1 for the odd colour with three strands. -/
example : StringDiagrams.K₀.mk (word datum scalars symmetrizer homogeneous
      (List.replicate 3 true)) =
    (letI := StringDiagrams.K₀.moduleLaurent ℚ (HKar datum scalars symmetrizer homogeneous);
      CoveringQuantum.qpFact (SKM.K0Relations.qUnit (symmetrizer.d true))
          (SKM.K0Relations.piCoeff (datum.parity true)) 3 •
        StringDiagrams.K₀.mk (dpObj datum scalars symmetrizer homogeneous true 3)) :=
  class_word_rep true 3

#print axioms OddMath.QuiverHecke.serre_words
#print axioms OddMath.QuiverHecke.class_word_rep

end NonVacuity.EnvelopeSerre
