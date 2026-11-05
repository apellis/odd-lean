import OddMath.Diagrams.BoxProductCoefficientGraded

/-!
# Non-vacuity: the product `C ⊠ D` over a graded ground ring

`OddMath.Diagrams.BoxProdCoefficient.gradedSupercategory` applied to `I ⊠ I`, for the unit
supercategory `I` over `ℚ` with its grading, `K = R = ℚ`, and `ℚ` graded in degree `0`.
-/

open CategoryTheory StringDiagrams OddMath.Diagrams DirectSum

noncomputable section

example :
    letI := Linear.restrictScalars ℚ ℚ (BoxProd ℚ (BoxUnit.{0, 0} ℚ) (BoxUnit.{0, 0} ℚ))
    letI := Supercategory.restrictScalars ℚ ℚ (BoxProd ℚ (BoxUnit.{0, 0} ℚ) (BoxUnit.{0, 0} ℚ))
    GradedSupercategory ℚ (BoxProd ℚ (BoxUnit.{0, 0} ℚ) (BoxUnit.{0, 0} ℚ)) :=
  letI : Decomposition (BoxUnit.unitDeg (k := ℚ)) :=
    (GradedSuperspace.unit (k := ℚ)).isInternal_deg.chooseDecomposition
  have h : ∀ {X Y : BoxUnit.{0, 0} ℚ} {a n : ℤ} {r : ℚ} {f : X ⟶ Y},
      r ∈ BoxUnit.unitDeg a → f ∈ GradedSupercategory.degree (R := ℚ) X Y n →
      r • f ∈ GradedSupercategory.degree (R := ℚ) X Y (a + n) := by
    intro X Y a n r f hr hf
    rcases BoxUnit.mem_unitDeg.1 hr with ha | hr
    · rcases BoxUnit.mem_degree_iff.1 hf with hn | hf
      · exact BoxUnit.mem_degree_iff.2 (Or.inl (by rw [ha, hn, add_zero]))
      · exact BoxUnit.mem_degree_iff.2 (Or.inr (by rw [hf, smul_zero]))
    · exact BoxUnit.mem_degree_iff.2 (Or.inr (by rw [hr, zero_smul]))
  BoxProdCoefficient.gradedSupercategory h h (fun _ _ _ _ => Iff.rfl) (fun _ _ _ _ => Iff.rfl)

end
