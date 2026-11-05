import OddMath.QuiverHecke.CyclotomicAction.ELVParabolicSpan
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-! # The source presentation of the literal old ELV quotient

SwappedVacuumCoordinates §§5–6. The coefficient quotient has exactly its
specified coefficient-ideal kernel; tensor right exactness is sufficient,
with no flatness assumption. The next comparison identifies the actual
first-boundary old ideal with the image of the full source relation span.
-/
noncomputable section
open scoped Classical TensorProduct
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams Supercategory
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Surjectivity of the actual full-coefficient categorical quotient. -/
theorem elvQuotientMap_surjective (s t : List I) :
    Function.Surjective
      (elvQuotientMap D Sc cutoff (coefficientObj D Sc s) (coefficientObj D Sc t)) :=
  TensorProduct.map_surjective
    ((RingCon.mkₐ_surjective (α := k) (SKM.SYM.elvCoefficientIdeal D k cutoff).ringCon).comp
      (SKM.SYM.polynomialExteriorEquiv D k).symm.surjective) Function.surjective_id

private theorem source_unit_comp_coefficient {s t : List I} (c : SKM.SYM D k)
    (f : (pres D Sc).obj (ob D s) ⟶ (pres D Sc).obj (ob D t)) :
    sourceCoefficientHom D Sc 1 f ≫ sourceCoefficientHom D Sc c (𝟙 _) =
      sourceCoefficientHom D Sc c f := by
  have h1 : SKM.SYM.polynomialExteriorEquiv D k (1 : SKM.SYM D k) ∈
      SKM.SYM.polynomialExteriorParity D k 0 := by
    rw [map_one]; exact SetLike.GradedOne.one_mem
  rw [sourceCoefficientHom_comp D Sc h1 c f (id_mem _)]
  simp only [koszulSign_zero_left, one_smul, mul_one, Category.comp_id]

/-- Every pure coefficient-kernel tensor is in the literal coefficient
arm of the contextual source relations, including nonhomogeneous coefficients. -/
theorem sourceCoefficientHom_mem_coefficientRelationSpan {s t : List I}
    {c : SKM.SYM D k} (hc : c ∈ SKM.SYM.elvCoefficientIdeal D k cutoff)
    (f : (pres D Sc).obj (ob D s) ⟶ (pres D Sc).obj (ob D t)) :
    sourceCoefficientHom D Sc c f ∈ ELVCoefficientRelationSpan D Sc cutoff s t := by
  by_cases hlen : s.length = t.length
  · apply Submodule.subset_span
    refine ⟨t, hlen.symm, c, hc, sourceCoefficientHom D Sc 1 f, 𝟙 _, ?_⟩
    rw [Category.comp_id, source_unit_comp_coefficient]
  · have hf : f = 0 := hom_eq_zero_of_content_ne D Sc (fun h => hlen (by
      have hh := congrArg Multiset.card h
      simpa using hh)) f
    rw [hf, sourceCoefficientHom_zero_right]
    exact Submodule.zero_mem _

/-- Exactness of the full coefficient quotient: its kernel is precisely the
specified two-sided coefficient span, with all exterior coefficients retained. -/
theorem elvQuotientMap_ker_eq_coefficientRelationSpan (s t : List I) :
    LinearMap.ker
      (elvQuotientMap D Sc cutoff (coefficientObj D Sc s) (coefficientObj D Sc t)) =
      ELVCoefficientRelationSpan D Sc cutoff s t := by
  apply le_antisymm
  · let q := (SKM.SYM.elvModelQuotient (k := k) D cutoff).toLinearMap
    let A := (pres D Sc).obj (ob D s) ⟶ (pres D Sc).obj (ob D t)
    have hq : Function.Surjective q :=
      (RingCon.mkₐ_surjective (α := k) (SKM.SYM.elvCoefficientIdeal D k cutoff).ringCon).comp
        (SKM.SYM.polynomialExteriorEquiv D k).symm.surjective
    have hfg : Function.Exact (LinearMap.ker q).subtype q := q.exact_subtype_ker_map
    have he := (rTensor_exact (R := k) (M := LinearMap.ker q) A hfg hq).linearMap_ker_eq
    intro x hx
    have hx' : x ∈ LinearMap.range (LinearMap.rTensor A (LinearMap.ker q).subtype) := by
      rw [← he]
      exact hx
    obtain ⟨y, rfl⟩ := hx'
    clear hx
    induction y using TensorProduct.inductionOn with
    | add y z hy hz => simpa only [map_add] using
        Submodule.add_mem (ELVCoefficientRelationSpan D Sc cutoff s t) hy hz
    | tmul c f =>
      let a := (SKM.SYM.polynomialExteriorEquiv D k).symm c.val
      have ha : a ∈ SKM.SYM.elvCoefficientIdeal D k cutoff := Quotient.exact c.property
      have h := sourceCoefficientHom_mem_coefficientRelationSpan D Sc cutoff ha f
      simpa only [LinearMap.rTensor_tmul, Submodule.subtype_apply,
        sourceCoefficientHom, coefficientHom, a, AlgEquiv.apply_symm_apply,
        BoxProd.tmulHom, SuperalgebraCat.ofElem] using h
  · exact elvQuotientMap_kills_span D Sc cutoff s t

private theorem elvGenerator_image_mem_oldIdeal {v : List I}
    {r : coefficientObj D Sc v ⟶ coefficientObj D Sc v}
    (hr : ELVGenerator D Sc cutoff v r) :
    elvQuotientMap D Sc cutoff _ _ r ∈ ELVOld.ideal D Sc cutoff v v := by
  rcases hr with ⟨a, ha, rfl⟩ | ⟨i, tail, h, rfl⟩ | ⟨i, hi, tail, h, rfl⟩
  · rw [elvQuotientMap_kills D Sc ha]
    exact Submodule.zero_mem _
  · subst v
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    have hrel : elvQuotientMap D Sc cutoff _ _
        (elvCyclotomic D Sc i tail (cutoff i.1)) = ELVOld.relation D Sc cutoff i.1 tail := by
      rw [ELVOld.relation, dite_eq_left i.property]
      rfl
    rw [hrel]
    exact ELVOld.relation_mem D Sc cutoff i.1 tail
  · subst v
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    have hn : D.parity i ≠ 1 := by rw [hi]; exact zero_ne_one
    have hrel : elvQuotientMap D Sc cutoff _ _
        (evenCyclotomic D Sc i tail (cutoff i)) = ELVOld.relation D Sc cutoff i tail := by
      rw [ELVOld.relation, dite_eq_right hn]
      rfl
    rw [hrel]
    exact ELVOld.relation_mem D Sc cutoff i tail

private theorem oldRelation_source_lift (j : I) (tail : List I) :
    ∃ r : coefficientObj D Sc (j :: tail) ⟶ coefficientObj D Sc (j :: tail),
      ELVGenerator D Sc cutoff (j :: tail) r ∧
        elvQuotientMap D Sc cutoff _ _ r = ELVOld.relation D Sc cutoff j tail := by
  by_cases hj : D.parity j = 1
  · refine ⟨elvCyclotomic D Sc ⟨j, hj⟩ tail (cutoff j),
      Or.inr (Or.inl ⟨⟨j, hj⟩, tail, rfl, by simp⟩), ?_⟩
    rw [ELVOld.relation, dite_eq_left hj]
    rfl
  · have hz : D.parity j = 0 := (Supercategory.parity_eq_zero_or_one (D.parity j)).resolve_right hj
    refine ⟨evenCyclotomic D Sc j tail (cutoff j),
      Or.inr (Or.inr ⟨j, hz, tail, rfl, by simp⟩), ?_⟩
    rw [ELVOld.relation, dite_eq_right hj]
    rfl

/-- The source relation span maps onto the literal old cyclotomic ideal.
Every target coefficient and context is lifted through the actual quotient. -/
theorem map_elvRelationSpan_eq_oldIdeal (s t : List I) :
    (ELVRelationSpan D Sc cutoff s t).map
        (elvQuotientMap D Sc cutoff (coefficientObj D Sc s) (coefficientObj D Sc t)) =
      ELVOld.ideal D Sc cutoff s t := by
  apply le_antisymm
  · apply (Submodule.map_le_iff_le_comap).mpr
    apply Submodule.span_le.mpr
    rintro _ ⟨v, _, r, hr, a, b, rfl⟩
    change elvQuotientMap D Sc cutoff _ _ (a ≫ r ≫ b) ∈ ELVOld.ideal D Sc cutoff s t
    rw [elvQuotientMap_comp, elvQuotientMap_comp]
    exact ELVOld.comp_ideal D Sc cutoff _
      (ELVOld.ideal_comp D Sc cutoff (elvGenerator_image_mem_oldIdeal D Sc cutoff hr) _)
  · apply Submodule.span_le.mpr
    rintro _ ⟨j, v, a, b, rfl⟩
    by_cases hlen : (j :: v).length = s.length
    · obtain ⟨a', ha⟩ := elvQuotientMap_surjective D Sc cutoff s (j :: v) a
      obtain ⟨b', hb⟩ := elvQuotientMap_surjective D Sc cutoff (j :: v) t b
      obtain ⟨r, hr, hrel⟩ := oldRelation_source_lift D Sc cutoff j v
      refine ⟨a' ≫ r ≫ b', Submodule.subset_span ⟨j :: v, hlen, r, hr, a', b', rfl⟩, ?_⟩
      rw [elvQuotientMap_comp, elvQuotientMap_comp, ha, hb, hrel]
    · have ha : a = 0 := ELVOld.hom_eq_zero_of_length_ne D Sc cutoff (Ne.symm hlen) a
      rw [ha, Limits.zero_comp]
      exact Submodule.zero_mem _

/-- The actual quotient projection to old cyclotomic Homs. -/
def sourceToOldHom (s t : List I) :=
  (ELVOld.ideal D Sc cutoff s t).mkQ ∘ₗ
    elvQuotientMap D Sc cutoff (coefficientObj D Sc s) (coefficientObj D Sc t)

end OddMath.QuiverHecke
