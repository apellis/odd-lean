import Mathlib.Algebra.Polynomial.Div
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import OddMath.QuiverHecke.CyclotomicAction.ChronologicalTails.CyclotomicShortColumns
import OddMath.QuiverHecke.CyclotomicAction.OutputTransport.OutputBalancedComparison
import OddMath.QuiverHecke.HalfTurn.CoefficientGenerators

/-!
# Append source rows

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # Prescribed source and polynomial long coordinates

The source step of `DeformedMackeyBoundary.md` identifies the range of the
prescribed epsilon-balanced column with the chronological short span. On the
diagonal output this is the kernel of every normalized long extraction.
`sourceCoordinateEquiv` uses the existing decoder and a corrected PBW section,
not an independently chosen complement or an injectivity hypothesis.
The result is ground-ring linear; bimodule and categorical naturality are separate.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory TensorProduct
namespace OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

theorem range_alpha_eq_chronologicalShortSpan (i : I) (v t : List I) :
    LinearMap.range (alpha D Sc cutoff i v t) = chronologicalShortSpan D Sc cutoff i v t := by
  apply le_antisymm
  · have hz : (chronologicalShortSpan D Sc cutoff i v t).mkQ ∘ₗ
        alpha D Sc cutoff i v t = 0 := by
      apply BalancedInduction.hom_ext
      intro s h b
      change (chronologicalShortSpan D Sc cutoff i v t).mkQ
        (alpha D Sc cutoff i v t (pprimeTensor D Sc cutoff i v s.word t h b)) = 0
      obtain ⟨r, rfl⟩ := (ideal D Sc cutoff v (s.word ++ [i])).mkQ_surjective b
      rw [alpha_tensor, alphaPair_mk]
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      exact Submodule.subset_span ⟨s.word, twist k (epsilon D cutoff i v) r, h, rfl⟩
    rintro z ⟨a, rfl⟩
    have h := LinearMap.congr_fun hz a
    exact (Submodule.Quotient.mk_eq_zero _).mp h
  · apply Submodule.span_le.mpr
    rintro z ⟨s, r, h, rfl⟩
    refine ⟨pprimeTensor D Sc cutoff i v s t h
      ((ideal D Sc cutoff v (s ++ [i])).mkQ (twist k (epsilon D cutoff i v) r)), ?_⟩
    rw [alpha_tensor, alphaPair_mk, twist_twist]

theorem ker_outputLongExtraction_eq_range_alpha (p : ZMod 2) (i : I) (v : List I) :
    LinearMap.ker (outputLongExtraction D Sc cutoff p i v) =
      LinearMap.range (alpha D Sc cutoff i v v) := by
  rw [ker_outputLongExtraction_eq_chronologicalShortSpan, range_alpha_eq_chronologicalShortSpan]

@[simp] theorem outputLongExtraction_alpha (p : ZMod 2) (i : I) (v : List I)
    (a : PprimeDomain D Sc cutoff i v v) :
    outputLongExtraction D Sc cutoff p i v (alpha D Sc cutoff i v v a) = 0 := by
  have h : alpha D Sc cutoff i v v a ∈ LinearMap.range (alpha D Sc cutoff i v v) := ⟨a, rfl⟩
  rw [← ker_outputLongExtraction_eq_range_alpha D Sc cutoff p i v] at h
  exact h

/-- The existing long lift corrected by its prescribed short-source coordinate. -/
def sourceLongSection (p : ZMod 2) (i : I) (v : List I) :
    (ℕ →₀ Old D Sc cutoff v v) →ₗ[k] Target D Sc cutoff i v (v ++ [i]) :=
  outputLongSection D Sc cutoff p i v -
    alpha D Sc cutoff i v v ∘ₗ extract D Sc cutoff i v v ∘ₗ outputLongSection D Sc cutoff p i v

@[simp] theorem extract_sourceLongSection (p : ZMod 2) (i : I) (v : List I)
    (f : ℕ →₀ Old D Sc cutoff v v) :
    extract D Sc cutoff i v v (sourceLongSection D Sc cutoff p i v f) = 0 := by
  simp only [sourceLongSection, LinearMap.sub_apply, LinearMap.comp_apply, map_sub,
    extract_alpha, sub_self]

@[simp] theorem outputLongExtraction_sourceLongSection (p : ZMod 2) (i : I) (v : List I)
    (f : ℕ →₀ Old D Sc cutoff v v) :
    outputLongExtraction D Sc cutoff p i v (sourceLongSection D Sc cutoff p i v f) = f := by
  simp only [sourceLongSection, LinearMap.sub_apply, LinearMap.comp_apply, map_sub,
    outputLongExtraction_alpha, outputLongExtraction_section, sub_zero]

theorem source_reconstruction (p : ZMod 2) (i : I) (v : List I)
    (z : Target D Sc cutoff i v (v ++ [i])) :
    alpha D Sc cutoff i v v (extract D Sc cutoff i v v z) +
      sourceLongSection D Sc cutoff p i v (outputLongExtraction D Sc cutoff p i v z) = z := by
  have hz : z - sourceLongSection D Sc cutoff p i v
      (outputLongExtraction D Sc cutoff p i v z) ∈
      LinearMap.ker (outputLongExtraction D Sc cutoff p i v) := by
    simp only [LinearMap.mem_ker, map_sub, outputLongExtraction_sourceLongSection, sub_self]
  rw [ker_outputLongExtraction_eq_range_alpha] at hz
  obtain ⟨a, ha⟩ := hz
  have he := congrArg (extract D Sc cutoff i v v) ha
  simp only [extract_alpha, map_sub, extract_sourceLongSection, sub_zero] at he
  rw [← he, ha]
  exact sub_add_cancel _ _

/-- Coordinates in the prescribed balanced source and the existing polynomial old module. -/
def sourceCoordinateEquiv (p : ZMod 2) (i : I) (v : List I) :
    Target D Sc cutoff i v (v ++ [i]) ≃ₗ[k]
      (PprimeDomain D Sc cutoff i v v × (ℕ →₀ Old D Sc cutoff v v)) where
  toLinearMap := (extract D Sc cutoff i v v).prod (outputLongExtraction D Sc cutoff p i v)
  invFun a := alpha D Sc cutoff i v v a.1 + sourceLongSection D Sc cutoff p i v a.2
  left_inv := source_reconstruction D Sc cutoff p i v
  right_inv a := by
    apply Prod.ext
    · change extract D Sc cutoff i v v (_ + _) = a.1
      simp only [map_add, extract_alpha, extract_sourceLongSection, add_zero]
    · change outputLongExtraction D Sc cutoff p i v (_ + _) = a.2
      simp only [map_add, outputLongExtraction_alpha,
        outputLongExtraction_sourceLongSection, zero_add]

@[simp] theorem sourceCoordinateEquiv_apply (p : ZMod 2) (i : I) (v : List I)
    (z : Target D Sc cutoff i v (v ++ [i])) :
    sourceCoordinateEquiv D Sc cutoff p i v z =
      (extract D Sc cutoff i v v z, outputLongExtraction D Sc cutoff p i v z) := rfl

@[simp] theorem sourceCoordinateEquiv_symm_apply (p : ZMod 2) (i : I) (v : List I)
    (a : PprimeDomain D Sc cutoff i v v) (f : ℕ →₀ Old D Sc cutoff v v) :
    (sourceCoordinateEquiv D Sc cutoff p i v).symm (a, f) =
      alpha D Sc cutoff i v v a + sourceLongSection D Sc cutoff p i v f := rfl

@[simp] theorem sourceCoordinateEquiv_alpha (p : ZMod 2) (i : I) (v : List I)
    (a : PprimeDomain D Sc cutoff i v v) :
    sourceCoordinateEquiv D Sc cutoff p i v (alpha D Sc cutoff i v v a) = (a, 0) := by
  simp only [sourceCoordinateEquiv_apply, extract_alpha, outputLongExtraction_alpha]

end OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
end

end

section

/-!
# Prescribed P on the compatible output lifts

This is the unprojected comparison in `DeformedMackeyBoundary.md` §3: the
actual P applied to the constructed section intertwines corrected output rho
with the actual append moving dot. It does not identify a polynomial projection
against the chronological crossing image. That additional full-ELV append
splitting is necessary before deriving the degree-zero polynomial defect.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped TensorProduct Classical
namespace OddMath.QuiverHecke.ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The literal P-image of the specified compatible long section. -/
def outputLiftBoundary (p : ZMod 2) (j : {j : I // D.parity j = 1}) (v : List I) :
    (ℕ →₀ Old D Sc cutoff v v) →ₗ[k] AppendTarget D Sc cutoff j.1 v (v ++ [j.1]) :=
  (pMap D Sc cutoff j.1 v (v ++ [j.1])).comp (outputLongSection D Sc cutoff p j.1 v)

/-- Actual first-order intertwining before the crossing/polynomial splitting. -/
theorem outputLiftBoundary_rho (p : ZMod 2) (j : {j : I // D.parity j = 1})
    (v : List I) (f : ℕ →₀ Old D Sc cutoff v v) :
    outputLiftBoundary D Sc cutoff p j v (outputCoefficientRho D Sc cutoff p j v f) =
      appendMovingPowerTarget D Sc cutoff j.1 v (v ++ [j.1]) 1
        (outputLiftBoundary D Sc cutoff p j v f) := by
  change pMap D Sc cutoff j.1 v (v ++ [j.1])
    (outputLongSection D Sc cutoff p j.1 v (outputCoefficientRho D Sc cutoff p j v f)) = _
  rw [← boundaryRho_outputLongSection, pMap_boundaryRho]
  rfl

/-- The P-image of every source class differs from that of its specified long
lift by an actual chronological crossing class. This is the needed concrete
factorization statement before constructing the polynomial projection. -/
theorem pMap_sub_outputLiftBoundary_mem (p : ZMod 2) (j : {j : I // D.parity j = 1})
    (v : List I) (z : Target D Sc cutoff j.1 v (v ++ [j.1])) :
    pMap D Sc cutoff j.1 v (v ++ [j.1]) z -
      outputLiftBoundary D Sc cutoff p j v (outputLongExtraction D Sc cutoff p j.1 v z) ∈
        chronologicalCrossingSpan D Sc cutoff j.1 v v := by
  have hs : z - outputLongSection D Sc cutoff p j.1 v
      (outputLongExtraction D Sc cutoff p j.1 v z) ∈
        chronologicalShortSpan D Sc cutoff j.1 v v := by
    rw [← ker_outputLongExtraction_eq_chronologicalShortSpan D Sc cutoff p j.1 v]
    change outputLongExtraction D Sc cutoff p j.1 v _ = 0
    rw [map_sub, outputLongExtraction_section, sub_self]
  have h := pMap_chronologicalShortSpan_le D Sc cutoff j.1 v v
    (Submodule.mem_map.mpr ⟨_, hs, rfl⟩)
  simpa only [map_sub, outputLiftBoundary, LinearMap.comp_apply] using h

end OddMath.QuiverHecke.ELV
end

end

section

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
    elvQuotientMap D Sc cutoff _ _ r ∈ ELV.ideal D Sc cutoff v v := by
  rcases hr with ⟨a, ha, rfl⟩ | ⟨i, tail, h, rfl⟩ | ⟨i, hi, tail, h, rfl⟩
  · rw [elvQuotientMap_kills D Sc ha]
    exact Submodule.zero_mem _
  · subst v
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    have hrel : elvQuotientMap D Sc cutoff _ _
        (elvCyclotomic D Sc i tail (cutoff i.1)) = ELV.relation D Sc cutoff i.1 tail := by
      rw [ELV.relation, dite_eq_left i.property]
      rfl
    rw [hrel]
    exact ELV.relation_mem D Sc cutoff i.1 tail
  · subst v
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    have hn : D.parity i ≠ 1 := by rw [hi]; exact zero_ne_one
    have hrel : elvQuotientMap D Sc cutoff _ _
        (evenCyclotomic D Sc i tail (cutoff i)) = ELV.relation D Sc cutoff i tail := by
      rw [ELV.relation, dite_eq_right hn]
      rfl
    rw [hrel]
    exact ELV.relation_mem D Sc cutoff i tail

private theorem oldRelation_source_lift (j : I) (tail : List I) :
    ∃ r : coefficientObj D Sc (j :: tail) ⟶ coefficientObj D Sc (j :: tail),
      ELVGenerator D Sc cutoff (j :: tail) r ∧
        elvQuotientMap D Sc cutoff _ _ r = ELV.relation D Sc cutoff j tail := by
  by_cases hj : D.parity j = 1
  · refine ⟨elvCyclotomic D Sc ⟨j, hj⟩ tail (cutoff j),
      Or.inr (Or.inl ⟨⟨j, hj⟩, tail, rfl, by simp⟩), ?_⟩
    rw [ELV.relation, dite_eq_left hj]
    rfl
  · have hz : D.parity j = 0 := (Supercategory.parity_eq_zero_or_one (D.parity j)).resolve_right hj
    refine ⟨evenCyclotomic D Sc j tail (cutoff j),
      Or.inr (Or.inr ⟨j, hz, tail, rfl, by simp⟩), ?_⟩
    rw [ELV.relation, dite_eq_right hj]
    rfl

/-- The source relation span maps onto the literal old cyclotomic ideal.
Every target coefficient and context is lifted through the actual quotient. -/
theorem map_elvRelationSpan_eq_oldIdeal (s t : List I) :
    (ELVRelationSpan D Sc cutoff s t).map
        (elvQuotientMap D Sc cutoff (coefficientObj D Sc s) (coefficientObj D Sc t)) =
      ELV.ideal D Sc cutoff s t := by
  apply le_antisymm
  · apply (Submodule.map_le_iff_le_comap).mpr
    apply Submodule.span_le.mpr
    rintro _ ⟨v, _, r, hr, a, b, rfl⟩
    change elvQuotientMap D Sc cutoff _ _ (a ≫ r ≫ b) ∈ ELV.ideal D Sc cutoff s t
    rw [elvQuotientMap_comp, elvQuotientMap_comp]
    exact ELV.comp_ideal D Sc cutoff _
      (ELV.ideal_comp D Sc cutoff (elvGenerator_image_mem_oldIdeal D Sc cutoff hr) _)
  · apply Submodule.span_le.mpr
    rintro _ ⟨j, v, a, b, rfl⟩
    by_cases hlen : (j :: v).length = s.length
    · obtain ⟨a', ha⟩ := elvQuotientMap_surjective D Sc cutoff s (j :: v) a
      obtain ⟨b', hb⟩ := elvQuotientMap_surjective D Sc cutoff (j :: v) t b
      obtain ⟨r, hr, hrel⟩ := oldRelation_source_lift D Sc cutoff j v
      refine ⟨a' ≫ r ≫ b', Submodule.subset_span ⟨j :: v, hlen, r, hr, a', b', rfl⟩, ?_⟩
      rw [elvQuotientMap_comp, elvQuotientMap_comp, ha, hb, hrel]
    · have ha : a = 0 := ELV.hom_eq_zero_of_length_ne D Sc cutoff (Ne.symm hlen) a
      rw [ha, Limits.zero_comp]
      exact Submodule.zero_mem _

/-- The actual quotient projection to old cyclotomic Homs. -/
def sourceToOldHom (s t : List I) :=
  (ELV.ideal D Sc cutoff s t).mkQ ∘ₗ
    elvQuotientMap D Sc cutoff (coefficientObj D Sc s) (coefficientObj D Sc t)

end OddMath.QuiverHecke
end

end
