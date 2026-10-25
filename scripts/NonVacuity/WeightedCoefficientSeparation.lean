import OddMath.QuiverHecke.WeightedCoefficientSeparation

noncomputable section
open CategoryTheory StringDiagrams OddMath.QuiverHecke
open scoped Classical
variable {I X k : Type} [AddCommGroup X] [CommRing k]
  (D : OddMath.SKM.Datum I X) (Sc : OddMath.SKM.Scalars D k)

/-- The full coefficient extension, including distinct exterior products,
is separated at total weight two by the two-strand cutoff five. -/
example (i j : I) :
    Function.Injective (fun x : ExtendedAtMost D Sc [i, j] [j, i] 2 =>
      (WeightedRelationSpan D Sc [i, j] [j, i] 5).mkQ
        (x : coefficientObj D Sc [i, j] ⟶ coefficientObj D Sc [j, i])) :=
  weighted_quotient_injective_on_extendedAtMost D Sc
    (by change 2 + 2 * (2 : ℕ).choose 2 < 5; decide)

private def coefficients (i j : {i : I // D.parity i = 1})
    (r : Fin 6) : OddMath.SKM.SYM D k :=
  if r.val = 5 then 1 else if r.val = 3 then
    OddMath.SKM.SYM.coefficientBasis D k (0, {i, j}) else 0

/-- A genuine monic deformation with a nonzero two-colour exterior coefficient:
`x^5 + b_{i,j} x^3`. No exterior variable is identified or discarded. -/
example (i j : {i : I // D.parity i = 1}) (hij : i ≠ j) :
    deformedCyclotomic D Sc [i.1, j.1] 5 (coefficients D i j) ∈
      WeightedRelationSpan D Sc [i.1, j.1] [i.1, j.1] 5 := by
  apply deformedCyclotomic_mem_relationSpan D Sc _ _ _ (by simp)
  intro r
  unfold coefficients
  split_ifs with h5 h3
  · rw [h5]
    exact OddMath.SKM.SYM.mem_coefficientAtLeast_zero D k 1
  · apply Submodule.subset_span
    refine ⟨(0, {i, j}), ?_, rfl⟩
    simp [h3, OddMath.SKM.SYM.coefficientWeight, hij]
  · exact Submodule.zero_mem _

#print axioms extendedScore_comp
#print axioms weightedRelationSpan_le_extendedAtLeast
#print axioms weighted_quotient_injective_on_extendedAtMost
#print axioms deformedCyclotomic_mem_relationSpan
#print axioms weighted_quotients_jointly_detect
