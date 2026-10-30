/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVBoundaryInputDefect
import OddMath.QuiverHecke.CyclotomicAction.ELVEndpointLeading
/-!
# Output coefficients of the ordered reverse numerator

The coefficient expansion toward `DeformedBoundaryDivision.md` (7) keeps
chronological old composition and the total input-dot twist. All coefficients
belong to the full old ELV quotient, not a commutative scalar replacement.
-/
noncomputable section
namespace OddMath.QuiverHecke.ELVOld
open CategoryTheory StringDiagrams Supercategory
open scoped Classical TensorProduct
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Input exponent translation twists the entire coefficient. -/
def inputCoefficientShift (i : I) (v : List I) (d : ℕ) :
    (ℕ →₀ Old D Sc cutoff v v) →ₗ[k] (ℕ →₀ Old D Sc cutoff v v) :=
  Finsupp.lsum k fun m => (Finsupp.lsingle (d + m)).comp
    (oldTwist D Sc cutoff (d • D.parity i) v v)

/-- Chronological precomposition by an old arrow, coefficient by coefficient. -/
def inputCoefficientComp (v : List I) (c : hom D Sc cutoff v v) :
    (ℕ →₀ Old D Sc cutoff v v) →ₗ[k] (ℕ →₀ Old D Sc cutoff v v) :=
  Finsupp.mapRange.linearMap
    (oldComp D Sc cutoff v v v ((ideal D Sc cutoff v v).mkQ c))

theorem inputCoefficientShift_embedding (i : I) (v : List I) (d : ℕ)
    (f : ℕ →₀ Old D Sc cutoff v v) :
    appendMovingPowerTarget D Sc cutoff i v (v ++ [i]) d
      (appendOutputEmbedding D Sc cutoff i v v f) =
    appendOutputEmbedding D Sc cutoff i v v (inputCoefficientShift D Sc cutoff i v d f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add f g hf hg => simp only [map_add, hf, hg]
  | single m b =>
    obtain ⟨g, rfl⟩ := (ideal D Sc cutoff v v).mkQ_surjective b
    simp only [inputCoefficientShift, Finsupp.lsum_single, LinearMap.comp_apply,
      Finsupp.lsingle_apply]
    change _ = appendOutputEmbedding D Sc cutoff i v v
      (Finsupp.single (d + m) ((ideal D Sc cutoff v v).mkQ (twist k (d • D.parity i) g)))
    rw [appendOutputEmbedding_single, appendMovingPowerTarget_projection,
      appendOutputEmbedding_single, ← Category.assoc,
      appendMovingPower_twisted_rightContext, Category.assoc]
    congr 2
    unfold appendMovingPower
    rw [← affineUnit_comp]
    change affineUnit D Sc cutoff _ _
      (dotE D Sc (v ++ [i]) v.length ^ m * dotE D Sc (v ++ [i]) v.length ^ d) = _
    rw [← pow_add, Nat.add_comm m d]

theorem inputCoefficientComp_embedding (i : I) (v : List I)
    (c : hom D Sc cutoff v v) (f : ℕ →₀ Old D Sc cutoff v v) :
    appendOldSourceTarget D Sc cutoff i v (v ++ [i]) c
      (appendOutputEmbedding D Sc cutoff i v v f) =
    appendOutputEmbedding D Sc cutoff i v v (inputCoefficientComp D Sc cutoff v c f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add f g hf hg => simp only [map_add, hf, hg]
  | single m b =>
    obtain ⟨g, rfl⟩ := (ideal D Sc cutoff v v).mkQ_surjective b
    simp only [inputCoefficientComp, Finsupp.mapRange.linearMap_apply,
      Finsupp.mapRange_single, oldComp_mk, appendOutputEmbedding_single]
    change appendProjection D Sc cutoff i v (v ++ [i])
      (rightContext D Sc cutoff [i] v v c ≫
        (rightContext D Sc cutoff [i] v v g ≫ appendMovingPower D Sc cutoff i v m)) = _
    rw [← Category.assoc, ← rightContext_comp]

/-- Explicit finite endpoint coefficients, including the exterior parity twist. -/
def endpointOutputCoefficients (i : I) (v : List I) : ℕ →₀ Old D Sc cutoff v v :=
  ∑ a : Fin (cutoff i + 1), Finsupp.single a.val
    ((ideal D Sc cutoff v v).mkQ
      (twist k (a.val • D.parity i)
        (ELVPScalar.scalar D Sc cutoff v (singleCoefficient D cutoff i a))))

theorem endpointOutputCoefficients_embedding (i : I) (v : List I) :
    appendProjection D Sc cutoff i v (v ++ [i]) (endpointELV D Sc cutoff i v) =
    appendOutputEmbedding D Sc cutoff i v v (endpointOutputCoefficients D Sc cutoff i v) := by
  unfold endpointELV endpointOutputCoefficients
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [appendOutputEmbedding_single]
  change appendProjection D Sc cutoff i v (v ++ [i])
    (appendCoefficientTerm D Sc cutoff i v (singleCoefficient D cutoff i a) a.val) = _
  rw [append_coefficient_monomial, appendMovingPower_twisted_rightContext]

/-- One literal QP factor on full old output coefficients. The mixed term
precomposes the old dot AFTER shifting the input coefficient. -/
def qpOutputCoefficientStep (i : I) (v : List I) (b : ℕ)
    (f : ℕ →₀ Old D Sc cutoff v v) : ℕ →₀ Old D Sc cutoff v v :=
  let j := v.getD b i
  let O := fun a => inputCoefficientComp D Sc cutoff v (sourceDotPower D Sc cutoff v b a)
  let T := inputCoefficientShift D Sc cutoff i v
  if j = i then
    if D.parity i = 1 then O 2 f + T 2 f else -f
  else if D.d i j = 0 then (Sc.t i j : k) • f
  else (∑ e ∈ Finset.Ioo 0 (D.dn i j), ∑ a ∈ Finset.Ioo 0 (D.dn j i),
      Sc.s i j e a • O a (T e f)) +
    ((Sc.t i j : k) • T (D.dn i j) f + (Sc.t j i : k) • O (D.dn j i) f)

theorem qpOutputCoefficientStep_embedding (i : I) (v : List I) (b : ℕ)
    (hb : b < v.length) (h : hom D Sc cutoff (v ++ [i]) (v ++ [i]))
    (f : ℕ →₀ Old D Sc cutoff v v)
    (hf : appendProjection D Sc cutoff i v (v ++ [i]) h =
      appendOutputEmbedding D Sc cutoff i v v f) :
    appendProjection D Sc cutoff i v (v ++ [i])
      (affineUnit D Sc cutoff _ _ (appendQPFactor D Sc i v (v.getD b i) b) ≫ h) =
    appendOutputEmbedding D Sc cutoff i v v (qpOutputCoefficientStep D Sc cutoff i v b f) := by
  have hm (e : ℕ) : appendProjection D Sc cutoff i v (v ++ [i])
      (affineUnit D Sc cutoff _ _ (dotE D Sc (v ++ [i]) v.length ^ e) ≫ h) =
      appendOutputEmbedding D Sc cutoff i v v (inputCoefficientShift D Sc cutoff i v e f) := by
    change appendMovingPowerTarget D Sc cutoff i v (v ++ [i]) e
      (appendProjection D Sc cutoff i v (v ++ [i]) h) = _
    rw [hf, inputCoefficientShift_embedding]
  have ho (a : ℕ) : appendProjection D Sc cutoff i v (v ++ [i])
      (affineUnit D Sc cutoff _ _ (dotE D Sc (v ++ [i]) b ^ a) ≫ h) =
      appendOutputEmbedding D Sc cutoff i v v
        (inputCoefficientComp D Sc cutoff v (sourceDotPower D Sc cutoff v b a) f) := by
    rw [appendProjection_old_dotPower D Sc cutoff i v _ b a hb, hf,
      inputCoefficientComp_embedding]
  have hmo (e a : ℕ) : appendProjection D Sc cutoff i v (v ++ [i])
      (affineUnit D Sc cutoff _ _
        (dotE D Sc (v ++ [i]) v.length ^ e * dotE D Sc (v ++ [i]) b ^ a) ≫ h) =
      appendOutputEmbedding D Sc cutoff i v v
        (inputCoefficientComp D Sc cutoff v (sourceDotPower D Sc cutoff v b a)
          (inputCoefficientShift D Sc cutoff i v e f)) := by
    rw [End.mul_def, affineUnit_comp, Category.assoc,
      appendProjection_old_dotPower D Sc cutoff i v _ b a hb, hm,
      inputCoefficientComp_embedding]
  unfold qpOutputCoefficientStep
  dsimp only
  split_ifs with hj hp hd
  · rw [hj, appendQPFactor_odd D Sc i hp v b hb hj]
    simp only [map_add, Preadditive.add_comp, ho, hm]
  · simp only [appendQPFactor, hj, hp, ↓reduceIte, map_neg,
      End.one_def, affineUnit_id, Preadditive.neg_comp, Category.id_comp, hf]
  · simp only [appendQPFactor, hj, ↓reduceIte, qPoly, hd, map_smul,
      Linear.smul_comp, End.one_def, affineUnit_id, Category.id_comp, hf]
  · simp only [appendQPFactor, hj, ↓reduceIte, qPoly, hd, map_add, map_sum,
      map_smul, Preadditive.add_comp, Preadditive.sum_comp, Linear.smul_comp, hmo, hm, ho]

/-- Finite ordered expansion: the list order is the actual End-product order. -/
def orderedQPOutputCoefficients (i : I) (v : List I) (l : List ℕ)
    (f : ℕ →₀ Old D Sc cutoff v v) : ℕ →₀ Old D Sc cutoff v v :=
  l.foldl (fun g b => qpOutputCoefficientStep D Sc cutoff i v b g) f

theorem orderedQPOutputCoefficients_embedding (i : I) (v : List I)
    (l : List ℕ) (hl : ∀ b ∈ l, b < v.length)
    (h : hom D Sc cutoff (v ++ [i]) (v ++ [i])) (f : ℕ →₀ Old D Sc cutoff v v)
    (hf : appendProjection D Sc cutoff i v (v ++ [i]) h =
      appendOutputEmbedding D Sc cutoff i v v f) :
    appendProjection D Sc cutoff i v (v ++ [i])
      (affineUnit D Sc cutoff _ _
        ((l.map fun b => appendQPFactor D Sc i v (v.getD b i) b).prod) ≫ h) =
    appendOutputEmbedding D Sc cutoff i v v (orderedQPOutputCoefficients D Sc cutoff i v l f) := by
  induction l generalizing h f with
  | nil => simpa only [List.map_nil, List.prod_nil, End.one_def, affineUnit_id,
      Category.id_comp, orderedQPOutputCoefficients, List.foldl_nil] using hf
  | cons b l ih =>
    simp only [List.map_cons, List.prod_cons, End.mul_def, affineUnit_comp, Category.assoc,
      orderedQPOutputCoefficients, List.foldl_cons]
    exact ih (fun a ha => hl a (List.mem_cons_of_mem b ha)) _ _
      (qpOutputCoefficientStep_embedding D Sc cutoff i v b (hl b List.mem_cons_self) h f hf)

/-- The explicit C₀ polynomial of the ordered reverse numerator at every input power.
No C₀ or boundary map occurs on the coefficient side. -/
theorem appendC0_orderedReverseNumerator (i : I) (v : List I) (d : ℕ) :
    appendC0 D Sc cutoff i v v
      (appendProjection D Sc cutoff i v (v ++ [i])
        (appendMovingPower D Sc cutoff i v d ≫
          affineUnit D Sc cutoff _ _ (appendQPProduct D Sc i v) ≫ endpointELV D Sc cutoff i v)) =
    inputCoefficientShift D Sc cutoff i v d
      (orderedQPOutputCoefficients D Sc cutoff i v (List.range v.length)
        (endpointOutputCoefficients D Sc cutoff i v)) := by
  have H := orderedQPOutputCoefficients_embedding D Sc cutoff i v (List.range v.length)
    (fun _ hb => List.mem_range.mp hb) _ _ (endpointOutputCoefficients_embedding D Sc cutoff i v)
  change appendProjection D Sc cutoff i v (v ++ [i])
    (affineUnit D Sc cutoff _ _ (appendQPProduct D Sc i v) ≫ endpointELV D Sc cutoff i v) = _ at H
  rw [← appendMovingPowerTarget_projection, H, inputCoefficientShift_embedding,
    appendC0_embedding]

/-- Every coefficient of an input shift, including degrees below the shift. -/
theorem inputCoefficientShift_apply (i : I) (v : List I) (d : ℕ)
    (f : ℕ →₀ Old D Sc cutoff v v) (n : ℕ) :
    inputCoefficientShift D Sc cutoff i v d f n =
      ∑ m ∈ f.support, if d + m = n then
        oldTwist D Sc cutoff (d • D.parity i) v v (f m) else 0 := by
  simp only [inputCoefficientShift, Finsupp.lsum_apply, Finsupp.sum,
    LinearMap.comp_apply, Finsupp.lsingle_apply, Finsupp.coe_finsetSum,
    Finset.sum_apply, Finsupp.single_apply]

/-- Input translation at its shifted coefficient is exactly the full old twist. -/
theorem inputCoefficientShift_apply_add (i : I) (v : List I) (d : ℕ)
    (f : ℕ →₀ Old D Sc cutoff v v) (n : ℕ) :
    inputCoefficientShift D Sc cutoff i v d f (d + n) =
      oldTwist D Sc cutoff (d • D.parity i) v v (f n) := by
  rw [inputCoefficientShift_apply]
  simp only [Nat.add_left_cancel_iff]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [Finsupp.notMem_support_iff.mp h, map_zero]

/-- The ordered coefficient expansion gives explicit values of the boundary on
independently defined corrected-rho S evaluations. The moving colour is odd. -/
theorem outputPolynomialBoundary_independentS_coefficients (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I) (d : ℕ) :
    SKM.zsign k (D.parity j.1) ^ v.count j.1 •
      outputPolynomialBoundary D Sc cutoff p j v
        (∑ n ∈ (independentOutputS D Sc cutoff j.1 v).support,
          Finsupp.mapRange.linearMap
            ((oldComp D Sc cutoff v v v).flip (independentOutputS D Sc cutoff j.1 v n))
            ((outputCoefficientRho D Sc cutoff p j v)^[n]
              (outputLongExtraction D Sc cutoff p j.1 v
                (outputCorrectedLift D Sc cutoff p j v d
                  ((ideal D Sc cutoff v v).mkQ (𝟙 _)))))) =
    sign k ((cutoff j.1 • D.parity j.1) * (D.parity j.1 * wordSumParity D v)) •
      inputCoefficientShift D Sc cutoff j.1 v d
        (orderedQPOutputCoefficients D Sc cutoff j.1 v (List.range v.length)
          (endpointOutputCoefficients D Sc cutoff j.1 v)) := by
  rw [outputPolynomialBoundary_independentS, appendC0_orderedReverseNumerator]

end OddMath.QuiverHecke.ELVOld
