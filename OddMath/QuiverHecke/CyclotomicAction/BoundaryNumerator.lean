import OddMath.QuiverHecke.CyclotomicAction.AppendContent
import OddMath.QuiverHecke.CyclotomicAction.AppendSourceRows
import OddMath.QuiverHecke.AppendShuffleRuns
import OddMath.QuiverHecke.ShuffleBasis

/-!
# Boundary numerator

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-!
# Polynomial projection of the prescribed boundary

The factorization in `DeformedMackeyBoundary.md` (5) holds on the original
prepend-old quotient column, not on a replacement crossing-image domain.
The independent S comparison projects the checked reverse-boundary identity
through the constructed C₀. It retains both signs and the ordered numerator.
No monic division or prescribed balanced crossing-column inverse is asserted.
-/
noncomputable section
namespace OddMath.QuiverHecke.ELVOld
open CategoryTheory StringDiagrams Supercategory
open scoped Classical
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The two existing crossing spans have the same arbitrary old-arrow generators. -/
theorem chronologicalCrossingSpan_eq_appendCrossingSpan (i : I) (v t : List I) :
    chronologicalCrossingSpan D Sc cutoff i v t = appendCrossingSpan D Sc cutoff i v t := by
  unfold chronologicalCrossingSpan appendCrossingSpan
  congr 1
  ext z
  constructor
  · rintro ⟨s, r, g, h⟩
    exact ⟨s, r, g, h.symm⟩
  · rintro ⟨s, r, g, h⟩
    exact ⟨s, r, g, h.symm⟩

/-- The boundary on long polynomial coordinates uses the specified PBW section. -/
def outputPolynomialBoundary (p : ZMod 2) (j : {j : I // D.parity j = 1})
    (v : List I) : (ℕ →₀ Old D Sc cutoff v v) →ₗ[k] (ℕ →₀ Old D Sc cutoff v v) :=
  (appendC0 D Sc cutoff j.1 v v).comp (outputLiftBoundary D Sc cutoff p j v)

/-- C₀P factors through the actual long extraction on the original source column. -/
theorem appendC0_pMap (p : ZMod 2) (j : {j : I // D.parity j = 1}) (v : List I)
    (z : Target D Sc cutoff j.1 v (v ++ [j.1])) :
    appendC0 D Sc cutoff j.1 v v (pMap D Sc cutoff j.1 v (v ++ [j.1]) z) =
      outputPolynomialBoundary D Sc cutoff p j v
        (outputLongExtraction D Sc cutoff p j.1 v z) := by
  have h := pMap_sub_outputLiftBoundary_mem D Sc cutoff p j v z
  rw [chronologicalCrossingSpan_eq_appendCrossingSpan, ← appendC0_ker,
    LinearMap.mem_ker, map_sub, sub_eq_zero] at h
  exact h

/-- The independently defined S, evaluated at the corrected coefficient rho,
compares with the ordered reverse numerator after the actual polynomial projection.
The exponent is iterate parity; the moving colour is explicitly odd. -/
theorem outputPolynomialBoundary_independentS (p : ZMod 2)
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
      appendC0 D Sc cutoff j.1 v v
        (appendProjection D Sc cutoff j.1 v (v ++ [j.1])
          (appendMovingPower D Sc cutoff j.1 v d ≫
            affineUnit D Sc cutoff _ _ (appendQPProduct D Sc j.1 v) ≫
            endpointELV D Sc cutoff j.1 v)) := by
  have h := appendC0_pMap D Sc cutoff p j v
    ((boundaryRho D Sc cutoff j v (v ++ [j.1]))^[d]
      (projection D Sc cutoff j.1 v (v ++ [j.1]) (move D Sc cutoff j.1 v)))
  have hp := pMap_boundaryRho_move_iterate D Sc cutoff j v (v ++ [j.1]) d (𝟙 _)
  simp only [Category.comp_id] at hp
  rw [hp, map_smul] at h
  change _ = outputPolynomialBoundary D Sc cutoff p j v
    (outputLongExtraction D Sc cutoff p j.1 v
      ((boundaryRho D Sc cutoff j v (v ++ [j.1]))^[d]
        (projection D Sc cutoff j.1 v (v ++ [j.1])
          (affineUnit D Sc cutoff _ _ (moveHom D Sc j.1 [] v))))) at h
  rw [outputLongExtraction_boundaryRho_move_polynomial, map_smul] at h
  exact h.symm

end OddMath.QuiverHecke.ELVOld
end

end

section

/-!
# Input-dot polynomial boundary defect

The first-order recurrence toward `DeformedBoundaryDivision.md` (8), in the
checked input-oriented convention. Input precomposition twists the entire old
coefficient before exponent shift. Its defect is polynomial-constant on every
append class. This does not identify the input shift with output postcomposition
or assert monic S-division or the prescribed crossing-column inverse.
-/
noncomputable section
namespace OddMath.QuiverHecke.ELVOld
open CategoryTheory StringDiagrams Supercategory
open scoped Classical
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

def appendInputShift (i : I) (v t : List I) :
    (ℕ →₀ Old D Sc cutoff v t) →ₗ[k] (ℕ →₀ Old D Sc cutoff v t) :=
  (appendOutputShift D Sc cutoff v t).comp
    (Finsupp.mapRange.linearMap (oldTwist D Sc cutoff (D.parity i) v t))

theorem appendMovingPowerTarget_embedding_one (i : I) (v t : List I)
    (f : ℕ →₀ Old D Sc cutoff v t) :
    appendMovingPowerTarget D Sc cutoff i v (t ++ [i]) 1
      (appendOutputEmbedding D Sc cutoff i v t f) =
    appendOutputEmbedding D Sc cutoff i v t (appendInputShift D Sc cutoff i v t f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add f g hf hg => simp only [map_add, hf, hg]
  | single m b =>
    obtain ⟨g, rfl⟩ := (ideal D Sc cutoff v t).mkQ_surjective b
    simp only [appendInputShift, LinearMap.comp_apply, Finsupp.mapRange.linearMap_apply,
      Finsupp.mapRange_single, appendOutputShift, Finsupp.lsum_single, Finsupp.lsingle_apply]
    change appendMovingPowerTarget D Sc cutoff i v (t ++ [i]) 1
      (appendOutputEmbedding D Sc cutoff i v t (Finsupp.single m ((ideal D Sc cutoff v t).mkQ g))) =
      appendOutputEmbedding D Sc cutoff i v t
        (Finsupp.single (m + 1) ((ideal D Sc cutoff v t).mkQ (twist k (D.parity i) g)))
    rw [appendOutputEmbedding_single, appendMovingPowerTarget_projection,
      appendOutputEmbedding_single, ← Category.assoc,
      appendMovingPower_twisted_rightContext, one_smul, Category.assoc]
    congr 2
    unfold appendMovingPower
    rw [pow_one, ← affineUnit_comp]
    congr 1

theorem appendMovingPowerTarget_crossing_one (i : I) (v s t : List I)
    (r : hom D Sc cutoff v (s ++ [i])) (g : hom D Sc cutoff (s ++ [i]) t) :
    appendMovingPowerTarget D Sc cutoff i v (t ++ [i]) 1
      (appendCrossingClass D Sc cutoff i v s t r g) =
    SKM.zsign k (D.parity i * D.parity i) •
      appendCrossingClass D Sc cutoff i v s t (twist k (D.parity i) r)
        (appendMovingPower D Sc cutoff i s 1 ≫ g) -
    SKM.zsign k (D.parity i * D.parity i) •
      appendOutputEmbedding D Sc cutoff i v t
        (Finsupp.single 0 ((ideal D Sc cutoff v t).mkQ (twist k (D.parity i) r ≫ g))) := by
  rw [appendCrossingClass, appendMovingPowerTarget_projection,
    ← Category.assoc, appendMovingPower_twisted_rightContext, one_smul, Category.assoc]
  have h := appendCrossing_dot_triangular D Sc cutoff i v s t (twist k (D.parity i) r) g
  have h' : appendMovingPower D Sc cutoff i (s ++ [i]) 1 =
      affineUnit D Sc cutoff _ _ (dotE D Sc (s ++ [i] ++ [i]) (s.length + 1)) := by
    simp only [appendMovingPower, pow_one, List.length_append, List.length_singleton]
  rw [h', h, map_sub, map_smul, map_smul]
  congr 1
  · simp only [appendCrossingClass, appendMovingPower, pow_one]
  · rw [appendOutputEmbedding_single]
    simp only [appendMovingPower, pow_zero, End.one_def, affineUnit_id, Category.comp_id]

def appendC0InputDefect (i : I) (v t : List I) :
    AppendTarget D Sc cutoff i v (t ++ [i]) →ₗ[k] (ℕ →₀ Old D Sc cutoff v t) :=
  (appendC0 D Sc cutoff i v t).comp (appendMovingPowerTarget D Sc cutoff i v (t ++ [i]) 1) -
    (appendInputShift D Sc cutoff i v t).comp (appendC0 D Sc cutoff i v t)

@[simp] theorem appendC0InputDefect_embedding (i : I) (v t : List I)
    (f : ℕ →₀ Old D Sc cutoff v t) :
    appendC0InputDefect D Sc cutoff i v t (appendOutputEmbedding D Sc cutoff i v t f) = 0 := by
  simp only [appendC0InputDefect, LinearMap.sub_apply, LinearMap.comp_apply,
    appendMovingPowerTarget_embedding_one, appendC0_embedding, sub_self]

@[simp] theorem appendC0InputDefect_crossing (i : I) (v s t : List I)
    (r : hom D Sc cutoff v (s ++ [i])) (g : hom D Sc cutoff (s ++ [i]) t) :
    appendC0InputDefect D Sc cutoff i v t (appendCrossingClass D Sc cutoff i v s t r g) =
    -(SKM.zsign k (D.parity i * D.parity i)) •
      Finsupp.single 0 ((ideal D Sc cutoff v t).mkQ (twist k (D.parity i) r ≫ g)) := by
  simp only [appendC0InputDefect, LinearMap.sub_apply, LinearMap.comp_apply,
    appendMovingPowerTarget_crossing_one, map_sub, map_smul, appendC0_crossing,
    appendC0_embedding, map_zero, smul_zero, zero_sub, sub_zero, neg_smul]

theorem appendC0InputDefect_degreeZero (i : I) (v t : List I)
    (z : AppendTarget D Sc cutoff i v (t ++ [i])) :
    appendC0InputDefect D Sc cutoff i v t z =
      Finsupp.single 0 (appendC0InputDefect D Sc cutoff i v t z 0) := by
  have hc : ∀ c ∈ appendCrossingSpan D Sc cutoff i v t,
      appendC0InputDefect D Sc cutoff i v t c =
        Finsupp.single 0 (appendC0InputDefect D Sc cutoff i v t c 0) := by
    intro c hc
    induction hc using Submodule.span_induction with
    | mem c hc =>
      obtain ⟨s, r, g, rfl⟩ := hc
      simp only [appendC0InputDefect_crossing, Finsupp.single_eq_same,
        Finsupp.smul_single]
    | zero => simp only [map_zero, Finsupp.zero_apply, Finsupp.single_zero]
    | add a b _ _ ha hb =>
      simpa only [map_add, Finsupp.add_apply, Finsupp.single_add] using congrArg₂ (· + ·) ha hb
    | smul a b _ hb =>
      simpa only [map_smul, Finsupp.smul_apply, Finsupp.smul_single] using congrArg (a • ·) hb
  have h := hc _ (appendC0_residual_mem D Sc cutoff i v t z)
  simpa only [map_sub, appendC0InputDefect_embedding, sub_zero] using h

/-- First-order polynomial recurrence for the specified boundary and input rho.
The shift twists the entire old coefficient; it is not the output shift. -/
theorem outputPolynomialBoundary_rho (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I) (f : ℕ →₀ Old D Sc cutoff v v) :
    outputPolynomialBoundary D Sc cutoff p j v (outputCoefficientRho D Sc cutoff p j v f) =
      appendInputShift D Sc cutoff j.1 v v (outputPolynomialBoundary D Sc cutoff p j v f) +
      Finsupp.single 0
        (appendC0InputDefect D Sc cutoff j.1 v v (outputLiftBoundary D Sc cutoff p j v f) 0) := by
  have h := appendC0InputDefect_degreeZero D Sc cutoff j.1 v v
    (outputLiftBoundary D Sc cutoff p j v f)
  change appendC0 D Sc cutoff j.1 v v
      (appendMovingPowerTarget D Sc cutoff j.1 v (v ++ [j.1]) 1
        (outputLiftBoundary D Sc cutoff p j v f)) - _ = _ at h
  rw [← outputLiftBoundary_rho] at h
  exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)

end OddMath.QuiverHecke.ELVOld
end

end

section

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
  else (∑ e ∈ Finset.range (D.dn i j), ∑ a ∈ Finset.range (D.dn j i),
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
end

end

section

/-!
# Support of the independent output square product

The degree bound is for the independently defined S of
`DeformedBoundaryDivision.md` §5, not the reverse QP numerator.
-/
noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams Supercategory
open scoped Classical
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The prescribed degree of the square-difference product. This is a bound
also on zero old corners; it is not a claim about `natDegree`. -/
def outputSDegree (i : I) (v : List I) : ℕ :=
  (if D.parity i = 1 then 4 else 2) * v.count i

theorem sourceMovingDegree_le_outputSDegree (i : I) (v : List I)
    (a : ℕ) (c : MoveChoices v) :
    sourceMovingDegree (leadingSourceDots D i 0 a v c) ≤ outputSDegree D i v := by
  induction v generalizing a with
  | nil => simp [leadingSourceDots, sourceMovingDegree, outputSDegree]
  | cons j v ih =>
    rcases c with ⟨b, c⟩
    have h := ih (a + 1) c
    change sourceMovingDegree (leadingSourceBlockDots D i j 0 (a + 1) b ++
      leadingSourceDots D i 0 (a + 1) v c) ≤ _
    rw [sourceMovingDegree_append]
    by_cases hij : i = j
    · subst j
      by_cases hi : D.parity i = 1
      all_goals fin_cases b <;>
        simp [leadingSourceBlockDots, sourceMovingDegree, outputSDegree, hi] at h ⊢ <;>
        omega
    · simpa [leadingSourceBlockDots, hij, sourceMovingDegree, outputSDegree,
        Ne.symm hij] using h

/-- The choice of the highest moving term in every local factor. -/
def outputSTopChoice : (v : List I) → MoveChoices v
  | [] => ()
  | _ :: v => (0, outputSTopChoice v)

theorem outputSTopChoice_data (i : I) (v : List I) (a : ℕ) :
    sourceMovingDegree (leadingSourceDots D i 0 a v (outputSTopChoice v)) =
        outputSDegree D i v ∧
    sourceOldDots (leadingSourceDots D i 0 a v (outputSTopChoice v)) = [] ∧
    leadingMoveCoeff D (k := k) i v (outputSTopChoice v) =
        SKM.zsign k (D.parity i) ^ v.count i := by
  induction v generalizing a with
  | nil => simp [leadingSourceDots, sourceMovingDegree,
      sourceOldDots, outputSDegree, leadingMoveCoeff]
  | cons j v ih =>
    have h := ih (a + 1)
    by_cases hij : i = j
    · subst j
      by_cases hi : D.parity i = 1
      all_goals simp [outputSTopChoice, leadingSourceDots, leadingSourceBlockDots,
        sourceMovingDegree, sourceOldDots, leadingMoveCoeff, leadingBlockCoeff,
        outputSDegree, hi, SKM.zsign, pow_succ, h.1, h.2.1, h.2.2,
        mul_comm, Nat.add_comm]; omega
    · simpa [outputSTopChoice, leadingSourceDots, leadingSourceBlockDots,
        sourceMovingDegree, sourceOldDots, leadingMoveCoeff, leadingBlockCoeff,
        outputSDegree, hij, Ne.symm hij] using h

theorem outputSTopChoice_unique (i : I) (v : List I) (a : ℕ) (c : MoveChoices v)
    (hc : leadingMoveCoeff D (k := k) i v c ≠ 0)
    (hd : sourceMovingDegree (leadingSourceDots D i 0 a v c) = outputSDegree D i v) :
    c = outputSTopChoice v := by
  induction v generalizing a with
  | nil => exact @Subsingleton.elim Unit _ _ _
  | cons j v ih =>
    rcases c with ⟨b, c⟩
    change leadingBlockCoeff D i j b * leadingMoveCoeff D i v c ≠ 0 at hc
    have ht : leadingMoveCoeff D (k := k) i v c ≠ 0 := by
      intro hz
      exact hc (by rw [hz, mul_zero])
    have hb := sourceMovingDegree_le_outputSDegree D i v (a + 1) c
    change sourceMovingDegree (leadingSourceBlockDots D i j 0 (a + 1) b ++
      leadingSourceDots D i 0 (a + 1) v c) = _ at hd
    rw [sourceMovingDegree_append] at hd
    have hzero : b = 0 := by
      by_cases hij : i = j
      · subst j
        by_cases hi : D.parity i = 1
        all_goals fin_cases b <;>
          simp [leadingSourceBlockDots, sourceMovingDegree, outputSDegree, hi] at hd hb ⊢ <;>
          omega
      · by_contra h
        exact hc (by simp [leadingBlockCoeff, hij, h])
    subst b
    have htail : sourceMovingDegree (leadingSourceDots D i 0 (a + 1) v c) =
        outputSDegree D i v := by
      by_cases hij : i = j
      · subst j
        by_cases hi : D.parity i = 1
        all_goals
          simp [leadingSourceBlockDots, sourceMovingDegree, outputSDegree, hi] at hd ⊢
          omega
      · simpa [leadingSourceBlockDots, hij, sourceMovingDegree, outputSDegree,
          Ne.symm hij] using hd
    change (0, c) = (0, outputSTopChoice v)
    rw [ih (a + 1) c ht htail]

namespace ELVOld

theorem independentOutputS_above (i : I) (v : List I) (n : ℕ)
    (hn : outputSDegree D i v < n) : independentOutputS D Sc cutoff i v n = 0 := by
  rw [independentOutputS_apply]
  have h : (∑ c : MoveChoices v,
      if sourceMovingDegree (leadingSourceDots D i 0 0 v c) = n then
        leadingMoveCoeff D (k := k) i v c •
          (ideal D Sc cutoff v v).mkQ (leadingSourceOldArrow D Sc cutoff i v c)
      else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro c _
    rw [ite_eq_right]
    have hc := sourceMovingDegree_le_outputSDegree D i v 0 c
    omega
  rw [h, smul_zero]

theorem independentOutputS_top (i : I) (v : List I) :
    independentOutputS D Sc cutoff i v (outputSDegree D i v) =
      (ideal D Sc cutoff v v).mkQ (𝟙 _) := by
  rw [independentOutputS_apply, Finset.sum_eq_single (outputSTopChoice v)]
  · have h := outputSTopChoice_data D (k := k) i v 0
    rw [h.1, ite_eq_left rfl, h.2.2, smul_smul]
    have hs : (SKM.zsign k (D.parity i) ^ v.count i) *
        (SKM.zsign k (D.parity i) ^ v.count i) = 1 := by
      rw [← mul_pow]
      by_cases hi : D.parity i = 1 <;> simp [SKM.zsign, hi]
    rw [hs, one_smul]
    congr 1
    unfold leadingSourceOldArrow
    rw [h.2.1]
    unfold endpointDotMonomial
    simp only [List.map_nil, cl_nil D Sc v rfl, affineUnit_id]
  · intro c _ hc
    split_ifs with hd
    · have hz : leadingMoveCoeff D (k := k) i v c = 0 := by
        by_contra hz
        exact hc (outputSTopChoice_unique D i v 0 c hz hd)
      rw [hz, zero_smul]
    · rfl
  · simp

theorem independentOutputS_support (i : I) (v : List I) :
    (independentOutputS D Sc cutoff i v).support ⊆
      Finset.range (outputSDegree D i v + 1) := by
  intro n hn
  rw [Finset.mem_range]
  by_contra h
  exact (Finsupp.mem_support_iff.mp hn)
    (independentOutputS_above D Sc cutoff i v n (by omega))

end ELVOld
end OddMath.QuiverHecke
end

end

section

/-!
# Graded coefficient compatibility of the polynomial boundary

The coefficient action on the domain and codomain of C₀P differs by the
long-row balance parity. This is the coefficient bridge needed in
`DeformedBoundaryDivision.md` §5; no centrality of arbitrary ELV coefficients
is asserted.
-/
noncomputable section
namespace OddMath.QuiverHecke.ELVOld
open CategoryTheory StringDiagrams Supercategory
open scoped Classical
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Degree-dependent total twist in output chronological right composition. -/
def outputCoefficientRightAction (i : I) (q : ZMod 2) (v : List I)
    (c : Old D Sc cutoff v v) : (ℕ →₀ Old D Sc cutoff v v) →ₗ[k]
      (ℕ →₀ Old D Sc cutoff v v) :=
  Finsupp.lsum k fun n => (Finsupp.lsingle n).comp
    ((oldComp D Sc cutoff v v v).flip (oldTwist D Sc cutoff (q + n • D.parity i) v v c))

@[simp] theorem outputCoefficientRightAction_single (i : I) (q : ZMod 2)
    (v : List I) (c b : Old D Sc cutoff v v) (n : ℕ) :
    outputCoefficientRightAction D Sc cutoff i q v c (Finsupp.single n b) =
      Finsupp.single n (oldComp D Sc cutoff v v v b
        (oldTwist D Sc cutoff (q + n • D.parity i) v v c)) := by
  simp only [outputCoefficientRightAction, Finsupp.lsum_single, LinearMap.comp_apply,
    Finsupp.lsingle_apply, LinearMap.flip_apply]

theorem outputCoefficientRightAction_apply (i : I) (q : ZMod 2)
    (v : List I) (c : Old D Sc cutoff v v) (f : ℕ →₀ Old D Sc cutoff v v) (n : ℕ) :
    outputCoefficientRightAction D Sc cutoff i q v c f n =
      oldComp D Sc cutoff v v v (f n) (oldTwist D Sc cutoff (q + n • D.parity i) v v c) := by
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero, Finsupp.zero_apply, LinearMap.zero_apply]
  | add f g hf hg => simp only [map_add, Finsupp.add_apply, hf, hg, LinearMap.add_apply]
  | single m b =>
    rw [outputCoefficientRightAction_single]
    by_cases h : m = n
    · subst m; simp only [Finsupp.single_eq_same]
    · simp [Ne.symm h]

/-- Arbitrary output postcomposition on the append quotient. -/
def appendPostcomp (i : I) (v : List I) {w z : List I} (g : hom D Sc cutoff w z) :
    AppendTarget D Sc cutoff i v w →ₗ[k] AppendTarget D Sc cutoff i v z :=
  (appendRelations D Sc cutoff i v w).mapQ (appendRelations D Sc cutoff i v z)
    (Linear.rightComp k _ g) (fun _ hh => appendRelations_comp D Sc cutoff i hh g)

@[simp] theorem appendPostcomp_projection (i : I) (v : List I) {w z : List I}
    (g : hom D Sc cutoff w z) (f : hom D Sc cutoff (v ++ [i]) w) :
    appendPostcomp D Sc cutoff i v g (appendProjection D Sc cutoff i v w f) =
      appendProjection D Sc cutoff i v z (f ≫ g) := rfl

theorem appendPostcomp_embedding (i : I) (v : List I) (g : hom D Sc cutoff v v)
    (f : ℕ →₀ Old D Sc cutoff v v) :
    appendPostcomp D Sc cutoff i v (appendInsert D Sc cutoff i v v g)
      (appendOutputEmbedding D Sc cutoff i v v f) =
    appendOutputEmbedding D Sc cutoff i v v
      (outputCoefficientRightAction D Sc cutoff i 0 v ((ideal D Sc cutoff v v).mkQ g) f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add f h hf hh => simp only [map_add, hf, hh]
  | single m b =>
    obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v v).mkQ_surjective b
    rw [appendOutputEmbedding_single, appendPostcomp_projection,
      outputCoefficientRightAction_single]
    change _ = appendOutputEmbedding D Sc cutoff i v v
      (Finsupp.single m ((ideal D Sc cutoff v v).mkQ (b ≫ twist k (0 + m • D.parity i) g)))
    rw [appendOutputEmbedding_single]
    congr 1
    simp only [appendInsert, Category.assoc, appendMovingPower_twisted_rightContext,
      zero_add, rightContext_comp]

theorem appendPostcomp_crossing (i : I) (v s : List I) (g : hom D Sc cutoff v v)
    (r : hom D Sc cutoff v (s ++ [i])) (h : hom D Sc cutoff (s ++ [i]) v) :
    appendPostcomp D Sc cutoff i v (appendInsert D Sc cutoff i v v g)
      (appendCrossingClass D Sc cutoff i v s v r h) =
    appendCrossingClass D Sc cutoff i v s v r (h ≫ g) := by
  unfold appendCrossingClass
  rw [appendPostcomp_projection]
  simp only [appendInsert, rightContext_comp, Category.assoc]

theorem appendC0_postcomp (i : I) (v : List I) (g : hom D Sc cutoff v v)
    (z : AppendTarget D Sc cutoff i v (v ++ [i])) :
    appendC0 D Sc cutoff i v v
      (appendPostcomp D Sc cutoff i v (appendInsert D Sc cutoff i v v g) z) =
    outputCoefficientRightAction D Sc cutoff i 0 v ((ideal D Sc cutoff v v).mkQ g)
      (appendC0 D Sc cutoff i v v z) := by
  have hpres : ∀ c ∈ appendCrossingSpan D Sc cutoff i v v,
      appendC0 D Sc cutoff i v v
        (appendPostcomp D Sc cutoff i v (appendInsert D Sc cutoff i v v g) c) = 0 := by
    intro c hc
    induction hc using Submodule.span_induction with
    | mem c hc =>
      obtain ⟨s, r, h, rfl⟩ := hc
      rw [appendPostcomp_crossing, appendC0_crossing]
    | zero => simp only [map_zero]
    | add a b _ _ ha hb => simp only [map_add, ha, hb, add_zero]
    | smul a b _ hb => simp only [map_smul, hb, smul_zero]
  have h := hpres _ (appendC0_residual_mem D Sc cutoff i v v z)
  rw [map_sub, map_sub, appendPostcomp_embedding, appendC0_embedding, sub_eq_zero] at h
  exact h

theorem outputLongExtraction_rightAction (p : ZMod 2) (i : I) (v : List I)
    (g : hom D Sc cutoff v v) (z : Target D Sc cutoff i v (v ++ [i])) :
    outputLongExtraction D Sc cutoff p i v
      (act D Sc cutoff i (appendInsert D Sc cutoff i v v g) z) =
    outputCoefficientRightAction D Sc cutoff i (p + D.parity i * wordSumParity D v) v
      ((ideal D Sc cutoff v v).mkQ g) (outputLongExtraction D Sc cutoff p i v z) := by
  ext n
  rw [outputLongExtraction_apply, outputLongCoordinate_outputOld,
    outputCoefficientRightAction_apply, outputLongExtraction_apply]
  have he : p + ((n : ZMod 2) * D.parity i + D.parity i * wordSumParity D v) =
      (p + D.parity i * wordSumParity D v) + n • D.parity i := by
    simp only [nsmul_eq_mul]
    abel
  rw [he]

theorem pMap_postcomp (i : I) (v : List I) {w t : List I}
    (g : hom D Sc cutoff w t) (z : Target D Sc cutoff i v w) :
    pMap D Sc cutoff i v t (act D Sc cutoff i g z) =
      appendPostcomp D Sc cutoff i v g (pMap D Sc cutoff i v w z) := by
  obtain ⟨z, rfl⟩ := projection_surjective D Sc cutoff i v w z
  change appendProjection D Sc cutoff i v t (appendW D Sc cutoff i v ≫ (z ≫ g)) =
    appendProjection D Sc cutoff i v t ((appendW D Sc cutoff i v ≫ z) ≫ g)
  rw [Category.assoc]

/-- Full-coefficient covariance of the actual boundary. The domain parity
shift is essential; this is not ordinary right linearity. -/
theorem outputPolynomialBoundary_rightAction (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I) (c : Old D Sc cutoff v v)
    (f : ℕ →₀ Old D Sc cutoff v v) :
    outputPolynomialBoundary D Sc cutoff p j v
      (outputCoefficientRightAction D Sc cutoff j.1
        (p + D.parity j.1 * wordSumParity D v) v c f) =
    outputCoefficientRightAction D Sc cutoff j.1 0 v c
      (outputPolynomialBoundary D Sc cutoff p j v f) := by
  obtain ⟨g, rfl⟩ := (ideal D Sc cutoff v v).mkQ_surjective c
  have h := appendC0_pMap D Sc cutoff p j v
    (act D Sc cutoff j.1 (appendInsert D Sc cutoff j.1 v v g)
      (outputLongSection D Sc cutoff p j.1 v f))
  rw [outputLongExtraction_rightAction, outputLongExtraction_section] at h
  rw [← h]
  rw [pMap_postcomp, appendC0_postcomp]
  rfl

/-- The independently proved S coefficient parity removes both degree twists
in the full boundary covariance law. It does not make arbitrary coefficients
central or replace the boundary by S. -/
theorem outputPolynomialBoundary_independentS_postcomp (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I) (n : ℕ)
    (f : ℕ →₀ Old D Sc cutoff v v) :
    outputPolynomialBoundary D Sc cutoff p j v
      (Finsupp.mapRange.linearMap ((oldComp D Sc cutoff v v v).flip
        (independentOutputS D Sc cutoff j.1 v n)) f) =
    Finsupp.mapRange.linearMap ((oldComp D Sc cutoff v v v).flip
      (independentOutputS D Sc cutoff j.1 v n))
      (outputPolynomialBoundary D Sc cutoff p j v f) := by
  have he (q : ZMod 2) (h : ℕ →₀ Old D Sc cutoff v v) :
      outputCoefficientRightAction D Sc cutoff j.1 q v
        (independentOutputS D Sc cutoff j.1 v n) h =
      Finsupp.mapRange.linearMap ((oldComp D Sc cutoff v v v).flip
        (independentOutputS D Sc cutoff j.1 v n)) h := by
    ext m
    rw [outputCoefficientRightAction_apply, independentOutputS_oldTwist]
    rfl
  have h := outputPolynomialBoundary_rightAction D Sc cutoff p j v
    (independentOutputS D Sc cutoff j.1 v n) f
  simpa only [he] using h

end OddMath.QuiverHecke.ELVOld
end

end

section

/-!
# Highest coefficient of the ordered reverse numerator

Support bounds and unit times identity at the prescribed degree of the explicit
ordered fold in `DeformedBoundaryDivision.md` (7). These statements allow zero
old endomorphism spaces: no nonzero leading coefficient is asserted.
-/
noncomputable section
namespace OddMath.QuiverHecke.ELVOld
open CategoryTheory StringDiagrams Supercategory
open scoped Classical TensorProduct
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

theorem inputCoefficientShift_above (i : I) (v : List I) (d m n : ℕ)
    (f : ℕ →₀ Old D Sc cutoff v v) (hf : ∀ r, m < r → f r = 0)
    (hn : d + m < n) : inputCoefficientShift D Sc cutoff i v d f n = 0 := by
  rw [inputCoefficientShift_apply]
  apply Finset.sum_eq_zero
  intro r _
  split_ifs with h
  · rw [hf r (by omega), map_zero]
  · rfl

theorem inputCoefficientComp_apply (v : List I) (c : hom D Sc cutoff v v)
    (f : ℕ →₀ Old D Sc cutoff v v) (n : ℕ) :
    inputCoefficientComp D Sc cutoff v c f n =
      oldComp D Sc cutoff v v v ((ideal D Sc cutoff v v).mkQ c) (f n) := rfl

theorem inputCoefficientShift_unit_top (i : I) (v : List I) (d m : ℕ)
    (f : ℕ →₀ Old D Sc cutoff v v) (u : kˣ)
    (hf : f m = (u : k) • (ideal D Sc cutoff v v).mkQ (𝟙 _)) :
    inputCoefficientShift D Sc cutoff i v d f (d + m) =
      (u : k) • (ideal D Sc cutoff v v).mkQ (𝟙 _) := by
  rw [inputCoefficientShift_apply_add, hf, map_smul]
  change (u : k) • (ideal D Sc cutoff v v).mkQ (twist k _ (𝟙 _)) = _
  rw [twist_id]

theorem endpointOutputCoefficients_above (i : I) (v : List I) (n : ℕ)
    (hn : cutoff i < n) : endpointOutputCoefficients D Sc cutoff i v n = 0 := by
  simp only [endpointOutputCoefficients, Finsupp.coe_finsetSum, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro a _
  exact Finsupp.single_eq_of_ne (by omega)

theorem endpointOutputCoefficients_top (i : I) (v : List I) :
    endpointOutputCoefficients D Sc cutoff i v (cutoff i) =
      (ideal D Sc cutoff v v).mkQ (𝟙 _) := by
  unfold endpointOutputCoefficients
  rw [Fin.sum_univ_castSucc]
  simp only [Finsupp.add_apply, Finsupp.coe_finsetSum, Finset.sum_apply]
  have hz : (∑ a : Fin (cutoff i),
      (Finsupp.single a.val ((ideal D Sc cutoff v v).mkQ
        (twist k (a.val • D.parity i)
          (ELVPScalar.scalar D Sc cutoff v (singleCoefficient D cutoff i a.castSucc)))))
      (cutoff i)) = 0 := by
    apply Finset.sum_eq_zero
    intro a _
    exact Finsupp.single_eq_of_ne (by omega)
  simp only [Fin.val_castSucc]
  rw [hz]
  simp only [zero_add, Fin.val_last, Finsupp.single_eq_same, singleCoefficient_top]
  change (ideal D Sc cutoff v v).mkQ (twist k _ (𝟙 _)) = _
  rw [twist_id]

theorem qpOutputCoefficientStep_above (i : I) (v : List I) (b m n : ℕ)
    (f : ℕ →₀ Old D Sc cutoff v v) (hf : ∀ r, m < r → f r = 0)
    (hn : appendQPDegree D i (v.getD b i) + m < n) :
    qpOutputCoefficientStep D Sc cutoff i v b f n = 0 := by
  have ho (a r : ℕ) (hr : m < r) :
      inputCoefficientComp D Sc cutoff v (sourceDotPower D Sc cutoff v b a) f r = 0 := by
    rw [inputCoefficientComp_apply, hf r hr, map_zero]
  have ht (e : ℕ) (he : e + m < n) :=
    inputCoefficientShift_above D Sc cutoff i v e m n f hf he
  unfold qpOutputCoefficientStep
  dsimp only
  split_ifs with hj hp hd
  · simp only [appendQPDegree, hj, hp, ↓reduceIte] at hn
    simp only [Finsupp.add_apply, ho 2 n (by omega), ht 2 hn, add_zero]
  · simp only [appendQPDegree, hj, hp, ↓reduceIte, zero_add] at hn
    simp only [Finsupp.neg_apply, hf n hn, neg_zero]
  · have hd0 : D.dn i (v.getD b i) = 0 := by
      have H := D.dn_cast (Ne.symm hj)
      omega
    simp only [appendQPDegree, hj, ↓reduceIte, hd0, zero_add] at hn
    simp only [Finsupp.smul_apply, hf n hn, smul_zero]
  · simp only [appendQPDegree, hj, ↓reduceIte] at hn
    simp only [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.coe_finsetSum, Finset.sum_apply]
    have hs : (∑ e ∈ Finset.range (D.dn i (v.getD b i)),
        ∑ a ∈ Finset.range (D.dn (v.getD b i) i),
          Sc.s i (v.getD b i) e a •
            inputCoefficientComp D Sc cutoff v (sourceDotPower D Sc cutoff v b a)
              (inputCoefficientShift D Sc cutoff i v e f) n) = 0 := by
      apply Finset.sum_eq_zero
      intro e he
      apply Finset.sum_eq_zero
      intro a _
      rw [inputCoefficientComp_apply, ht e (by have := (Finset.mem_range.mp he); omega),
        map_zero, smul_zero]
    rw [hs, ht _ hn, ho _ n (by omega), smul_zero, smul_zero, add_zero, add_zero]

theorem qpOutputCoefficientStep_unit_top (i : I) (v : List I) (b m : ℕ)
    (f : ℕ →₀ Old D Sc cutoff v v) (u : kˣ)
    (hf : ∀ r, m < r → f r = 0)
    (htop : f m = (u : k) • (ideal D Sc cutoff v v).mkQ (𝟙 _)) :
    qpOutputCoefficientStep D Sc cutoff i v b f (appendQPDegree D i (v.getD b i) + m) =
      ((appendQPUnit D Sc i (v.getD b i) * u : kˣ) : k) •
        (ideal D Sc cutoff v v).mkQ (𝟙 _) := by
  have ho (a n : ℕ) (hn : m < n) :
      inputCoefficientComp D Sc cutoff v (sourceDotPower D Sc cutoff v b a) f n = 0 := by
    rw [inputCoefficientComp_apply, hf n hn, map_zero]
  have ht (e : ℕ) := inputCoefficientShift_unit_top D Sc cutoff i v e m f u htop
  unfold qpOutputCoefficientStep appendQPDegree appendQPUnit
  dsimp only
  split_ifs with hj hp hd
  · simp only [Finsupp.add_apply, ho 2 (2 + m) (by omega), ht, zero_add,
      one_mul]
  · simp only [zero_add, Finsupp.neg_apply, htop, Units.val_neg,
      neg_one_mul, neg_smul]
  · have hd0 : D.dn i (v.getD b i) = 0 := by
      have H := D.dn_cast (Ne.symm hj)
      omega
    simp only [hd0, zero_add, Finsupp.smul_apply, htop, smul_smul, Units.val_mul]
  · have hdpos : 0 < D.dn i (v.getD b i) := by
      have H := D.dn_cast (Ne.symm hj)
      omega
    simp only [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.coe_finsetSum, Finset.sum_apply]
    have hs : (∑ e ∈ Finset.range (D.dn i (v.getD b i)),
        ∑ a ∈ Finset.range (D.dn (v.getD b i) i),
          Sc.s i (v.getD b i) e a •
            inputCoefficientComp D Sc cutoff v (sourceDotPower D Sc cutoff v b a)
              (inputCoefficientShift D Sc cutoff i v e f) (D.dn i (v.getD b i) + m)) = 0 := by
      apply Finset.sum_eq_zero
      intro e he
      apply Finset.sum_eq_zero
      intro a _
      rw [inputCoefficientComp_apply,
        inputCoefficientShift_above D Sc cutoff i v e m _ f hf
          (by have := (Finset.mem_range.mp he); omega), map_zero, smul_zero]
    rw [hs, ht, ho _ _ (by omega), smul_zero, add_zero, zero_add, smul_smul]
    rfl

theorem orderedQPOutputCoefficients_above (i : I) (v : List I)
    (l : List ℕ) (m : ℕ) (f : ℕ →₀ Old D Sc cutoff v v)
    (hf : ∀ r, m < r → f r = 0) (n : ℕ)
    (hn : (l.map (fun b => appendQPDegree D i (v.getD b i))).sum + m < n) :
    orderedQPOutputCoefficients D Sc cutoff i v l f n = 0 := by
  induction l generalizing m f with
  | nil => exact hf n (by simpa using hn)
  | cons b l ih =>
    apply ih (appendQPDegree D i (v.getD b i) + m) _
      (fun r hr => qpOutputCoefficientStep_above D Sc cutoff i v b m r f hf hr)
    simp only [List.map_cons, List.sum_cons] at hn
    omega

theorem orderedQPOutputCoefficients_unit_top (i : I) (v : List I)
    (l : List ℕ) (m : ℕ) (f : ℕ →₀ Old D Sc cutoff v v) (u : kˣ)
    (hf : ∀ r, m < r → f r = 0)
    (htop : f m = (u : k) • (ideal D Sc cutoff v v).mkQ (𝟙 _)) :
    orderedQPOutputCoefficients D Sc cutoff i v l f
      ((l.map (fun b => appendQPDegree D i (v.getD b i))).sum + m) =
      (((l.map (fun b => appendQPUnit D Sc i (v.getD b i))).prod * u : kˣ) : k) •
        (ideal D Sc cutoff v v).mkQ (𝟙 _) := by
  induction l generalizing m f u with
  | nil => simpa only [orderedQPOutputCoefficients, List.foldl_nil, List.map_nil,
      List.sum_nil, List.prod_nil, zero_add, one_mul] using htop
  | cons b l ih =>
    have H := ih (appendQPDegree D i (v.getD b i) + m)
      (qpOutputCoefficientStep D Sc cutoff i v b f) (appendQPUnit D Sc i (v.getD b i) * u)
      (fun r hr => qpOutputCoefficientStep_above D Sc cutoff i v b m r f hf hr)
      (qpOutputCoefficientStep_unit_top D Sc cutoff i v b m f u hf htop)
    simpa only [orderedQPOutputCoefficients, List.foldl_cons, List.map_cons,
      List.sum_cons, List.prod_cons, Nat.add_assoc, Nat.add_left_comm,
      mul_assoc, mul_left_comm] using H

/-- Bounded support of the literal ordered reverse-numerator fold. -/
theorem orderedReverseNumerator_above (i : I) (v : List I) (n : ℕ)
    (hn : endpointQPDegree D cutoff i v < n) :
    orderedQPOutputCoefficients D Sc cutoff i v (List.range v.length)
      (endpointOutputCoefficients D Sc cutoff i v) n = 0 := by
  apply orderedQPOutputCoefficients_above D Sc cutoff i v _ (cutoff i) _
    (endpointOutputCoefficients_above D Sc cutoff i v) n
  simpa only [endpointQPDegree, Nat.add_comm] using hn

/-- The coefficient at the prescribed bound is a scalar unit times the old
identity, even when that identity vanishes. This is not a nonzero-degree claim. -/
theorem orderedReverseNumerator_top (i : I) (v : List I) :
    orderedQPOutputCoefficients D Sc cutoff i v (List.range v.length)
      (endpointOutputCoefficients D Sc cutoff i v) (endpointQPDegree D cutoff i v) =
      (appendQPProductUnit D Sc i v : k) • (ideal D Sc cutoff v v).mkQ (𝟙 _) := by
  have H := orderedQPOutputCoefficients_unit_top D Sc cutoff i v
    (List.range v.length) (cutoff i) (endpointOutputCoefficients D Sc cutoff i v) 1
    (endpointOutputCoefficients_above D Sc cutoff i v)
    (by simpa only [Units.val_one, one_smul] using endpointOutputCoefficients_top D Sc cutoff i v)
  simpa only [endpointQPDegree, appendQPProductUnit, mul_one, Nat.add_comm] using H

/-- The concrete reverse numerator at every input power retains its unit top
coefficient: the total coefficient twist fixes the scalar identity. -/
theorem appendC0_orderedReverseNumerator_top (i : I) (v : List I) (d : ℕ) :
    appendC0 D Sc cutoff i v v
      (appendProjection D Sc cutoff i v (v ++ [i])
        (appendMovingPower D Sc cutoff i v d ≫
          affineUnit D Sc cutoff _ _ (appendQPProduct D Sc i v) ≫ endpointELV D Sc cutoff i v))
      (d + endpointQPDegree D cutoff i v) =
      (appendQPProductUnit D Sc i v : k) • (ideal D Sc cutoff v v).mkQ (𝟙 _) := by
  rw [appendC0_orderedReverseNumerator]
  exact inputCoefficientShift_unit_top D Sc cutoff i v d _ _ _
    (orderedReverseNumerator_top D Sc cutoff i v)

theorem appendC0_orderedReverseNumerator_above (i : I) (v : List I) (d n : ℕ)
    (hn : d + endpointQPDegree D cutoff i v < n) :
    appendC0 D Sc cutoff i v v
      (appendProjection D Sc cutoff i v (v ++ [i])
        (appendMovingPower D Sc cutoff i v d ≫
          affineUnit D Sc cutoff _ _ (appendQPProduct D Sc i v) ≫ endpointELV D Sc cutoff i v)) n = 0 := by
  rw [appendC0_orderedReverseNumerator]
  exact inputCoefficientShift_above D Sc cutoff i v d _ n _
    (orderedReverseNumerator_above D Sc cutoff i v) hn

end OddMath.QuiverHecke.ELVOld
end

end

section

/-!
# Ordered division of the actual boundary numerator by independent S

The quotient is the actual boundary of the corrected source vector. The
remainder is computed by the genuine input-dot defect, not chosen by a
polynomial division interface. This is `DeformedBoundaryDivision.md` (9)–(11)
in the input-oriented full-ELV convention.
-/
noncomputable section
namespace OddMath.QuiverHecke.ELVOld
open CategoryTheory StringDiagrams Supercategory
open scoped Classical
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

private theorem oldTwist_add_apply (a b : ZMod 2) (v : List I)
    (c : Old D Sc cutoff v v) :
    oldTwist D Sc cutoff a v v (oldTwist D Sc cutoff b v v c) =
      oldTwist D Sc cutoff (a + b) v v c := by
  obtain ⟨c, rfl⟩ := (ideal D Sc cutoff v v).mkQ_surjective c
  change (ideal D Sc cutoff v v).mkQ (twist k a (twist k b c)) = _
  rw [← twist_add]
  rfl

private theorem oldTwist_zero_apply (v : List I) (c : Old D Sc cutoff v v) :
    oldTwist D Sc cutoff 0 v v c = c := by
  obtain ⟨c, rfl⟩ := (ideal D Sc cutoff v v).mkQ_surjective c
  change (ideal D Sc cutoff v v).mkQ (twist k 0 c) = _
  rw [twist_zero]

private theorem appendInputShift_apply_succ (i : I) (v : List I)
    (f : ℕ →₀ Old D Sc cutoff v v) (m : ℕ) :
    appendInputShift D Sc cutoff i v v f (m + 1) = oldTwist D Sc cutoff (D.parity i) v v (f m) := by
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero, Finsupp.zero_apply]
  | add f g hf hg => simp only [map_add, Finsupp.add_apply, hf, hg]
  | single n b =>
    simp only [appendInputShift, LinearMap.comp_apply, Finsupp.mapRange.linearMap_apply,
      Finsupp.mapRange_single, appendOutputShift, Finsupp.lsum_single, Finsupp.lsingle_apply]
    by_cases h : m = n
    · subst m; simp only [Finsupp.single_eq_same]
    · rw [Finsupp.single_eq_of_ne (by omega), Finsupp.single_eq_of_ne h, map_zero]

/-- Exact high-coordinate telescoping of the actual input defect. -/
theorem outputPolynomialBoundary_iterate_high (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I) (n m : ℕ)
    (f : ℕ →₀ Old D Sc cutoff v v) :
    outputPolynomialBoundary D Sc cutoff p j v
      ((outputCoefficientRho D Sc cutoff p j v)^[n] f) (n + m) =
    oldTwist D Sc cutoff (n • D.parity j.1) v v
      (outputPolynomialBoundary D Sc cutoff p j v f m) := by
  induction n with
  | zero => simp only [Function.iterate_zero, id_eq, zero_add, zero_smul, oldTwist_zero_apply]
  | succ n ih =>
    rw [Function.iterate_succ_apply', outputPolynomialBoundary_rho]
    have he : n + 1 + m = (n + m) + 1 := by omega
    rw [he, Finsupp.add_apply, Finsupp.single_eq_of_ne (by omega), add_zero,
      appendInputShift_apply_succ, ih, oldTwist_add_apply]
    congr 2
    simp only [add_smul, one_smul, add_comm]

/-- Chronological right multiplication by the independently defined S.
Input shifts retain the entire-coefficient twist; on S support they are even. -/
def independentSRightProduct (i : I) (v : List I) :
    (ℕ →₀ Old D Sc cutoff v v) →ₗ[k] (ℕ →₀ Old D Sc cutoff v v) :=
  ∑ n ∈ (independentOutputS D Sc cutoff i v).support,
    (Finsupp.mapRange.linearMap ((oldComp D Sc cutoff v v v).flip
      (independentOutputS D Sc cutoff i v n))).comp (inputCoefficientShift D Sc cutoff i v n)

/-- The literal S evaluation, retaining the existing corrected coefficient operator. -/
def independentSAtRho (p : ZMod 2) (j : {j : I // D.parity j = 1}) (v : List I) :
    (ℕ →₀ Old D Sc cutoff v v) →ₗ[k] (ℕ →₀ Old D Sc cutoff v v) :=
  ∑ n ∈ (independentOutputS D Sc cutoff j.1 v).support,
    (Finsupp.mapRange.linearMap ((oldComp D Sc cutoff v v v).flip
      (independentOutputS D Sc cutoff j.1 v n))).comp
        ((outputCoefficientRho D Sc cutoff p j v) ^ n)

/-- The actual boundary remainder, before normalization by scalar units. -/
def independentSBoundaryRemainder (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I)
    (f : ℕ →₀ Old D Sc cutoff v v) : ℕ →₀ Old D Sc cutoff v v :=
  outputPolynomialBoundary D Sc cutoff p j v (independentSAtRho D Sc cutoff p j v f) -
    independentSRightProduct D Sc cutoff j.1 v (outputPolynomialBoundary D Sc cutoff p j v f)

theorem independentSBoundaryRemainder_above (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I)
    (f : ℕ →₀ Old D Sc cutoff v v) (m : ℕ) (hm : outputSDegree D j.1 v ≤ m) :
    independentSBoundaryRemainder D Sc cutoff p j v f m = 0 := by
  unfold independentSBoundaryRemainder independentSAtRho independentSRightProduct
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, Module.End.pow_apply, map_sum,
    outputPolynomialBoundary_independentS_postcomp, Finsupp.sub_apply,
    Finsupp.coe_finsetSum, Finset.sum_apply, sub_eq_zero]
  apply Finset.sum_congr rfl
  intro n hn
  have hnm : n ≤ m := by
    have h := independentOutputS_support D Sc cutoff j.1 v hn
    rw [Finset.mem_range] at h
    omega
  have he : m = n + (m - n) := by omega
  rw [he]
  simp only [Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_apply, LinearMap.flip_apply]
  rw [outputPolynomialBoundary_iterate_high, inputCoefficientShift_apply_add]

theorem independentSRightProduct_high (j : {j : I // D.parity j = 1})
    (v : List I) (f : ℕ →₀ Old D Sc cutoff v v) (m : ℕ)
    (hm : outputSDegree D j.1 v ≤ m) :
    independentSRightProduct D Sc cutoff j.1 v f m =
      ∑ n ∈ (independentOutputS D Sc cutoff j.1 v).support,
        oldComp D Sc cutoff v v v (f (m - n)) (independentOutputS D Sc cutoff j.1 v n) := by
  simp only [independentSRightProduct, LinearMap.sum_apply, LinearMap.comp_apply,
    Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.mapRange.linearMap_apply,
    Finsupp.mapRange_apply, LinearMap.flip_apply]
  apply Finset.sum_congr rfl
  intro n hn
  have hnm : n ≤ m := by
    have h := independentOutputS_support D Sc cutoff j.1 v hn
    rw [Finset.mem_range] at h
    omega
  have he : m = n + (m - n) := by omega
  rw [he, inputCoefficientShift_apply_add]
  obtain ⟨q, hq⟩ := independentOutputS_support_even D Sc cutoff j.1 j.2 v hn
  have hp : n • D.parity j.1 = 0 := by
    rw [hq, add_smul, j.2]
    simp only [nsmul_eq_mul, mul_one]
    rw [← two_mul, show (2 : ZMod 2) = 0 from rfl, zero_mul]
  rw [hp, oldTwist_zero_apply]
  simp only [Nat.add_sub_cancel_left]

/-- The leading coefficient of the actual S product is the input coefficient,
with no nonzero-corner hypothesis. -/
theorem independentSRightProduct_top (j : {j : I // D.parity j = 1})
    (v : List I) (f : ℕ →₀ Old D Sc cutoff v v) (M : ℕ)
    (hf : ∀ m, M < m → f m = 0) :
    independentSRightProduct D Sc cutoff j.1 v f (M + outputSDegree D j.1 v) = f M := by
  rw [independentSRightProduct_high D Sc cutoff j v f _ (by omega)]
  rw [Finset.sum_eq_single (outputSDegree D j.1 v)]
  · rw [Nat.add_sub_cancel, independentOutputS_top]
    obtain ⟨b, hb⟩ := (ideal D Sc cutoff v v).mkQ_surjective (f M)
    rw [← hb, oldComp_mk, Category.comp_id]
  · intro n hn hne
    have h := independentOutputS_support D Sc cutoff j.1 v hn
    rw [Finset.mem_range] at h
    rw [hf _ (by omega), map_zero, LinearMap.zero_apply]
  · intro h
    rw [Finsupp.notMem_support_iff.mp h, map_zero]

/-- If the S product vanishes above B, each possible input coefficient above
B-D vanishes, phrased without truncated subtraction or a nonzero hypothesis. -/
theorem independentSRightProduct_detect_bound (j : {j : I // D.parity j = 1})
    (v : List I) (f : ℕ →₀ Old D Sc cutoff v v) (B : ℕ)
    (hf : ∀ m, outputSDegree D j.1 v ≤ m → B < m →
      independentSRightProduct D Sc cutoff j.1 v f m = 0)
    (m : ℕ) (hm : B < m + outputSDegree D j.1 v) : f m = 0 := by
  by_contra h
  have hs : f.support.Nonempty := ⟨m, Finsupp.mem_support_iff.mpr h⟩
  obtain ⟨M, hM, hmax⟩ := f.support.exists_max_image id hs
  have hbound : ∀ n, M < n → f n = 0 := by
    intro n hn
    by_contra hz
    have hh := hmax n (Finsupp.mem_support_iff.mpr hz)
    change n ≤ M at hh
    omega
  have hle := hmax m (Finsupp.mem_support_iff.mpr h)
  change m ≤ M at hle
  have ht := independentSRightProduct_top D Sc cutoff j v f M hbound
  rw [hf _ (by omega) (by omega)] at ht
  exact (Finsupp.mem_support_iff.mp hM) ht.symm

/-- The prescribed boundary value on the corrected source basis. -/
def outputBoundaryPhi (p : ZMod 2) (j : {j : I // D.parity j = 1})
    (v : List I) (d : ℕ) : ℕ →₀ Old D Sc cutoff v v :=
  outputPolynomialBoundary D Sc cutoff p j v
    (outputLongExtraction D Sc cutoff p j.1 v
      (outputCorrectedLift D Sc cutoff p j v d ((ideal D Sc cutoff v v).mkQ (𝟙 _))))

/-- Genuine ordered S quotient/remainder identity for the checked reverse
numerator. The quotient is the actual boundary phi, up to the library sign;
the displayed remainder has support strictly below the independently proved S
bound. No degree-height monicity is assumed. -/
theorem independentS_boundary_division (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I) (d : ℕ) :
    let w := outputLongExtraction D Sc cutoff p j.1 v
      (outputCorrectedLift D Sc cutoff p j v d ((ideal D Sc cutoff v v).mkQ (𝟙 _)))
    let sigma := SKM.zsign k (D.parity j.1) ^ v.count j.1
    sign k ((cutoff j.1 • D.parity j.1) * (D.parity j.1 * wordSumParity D v)) •
      inputCoefficientShift D Sc cutoff j.1 v d
        (orderedQPOutputCoefficients D Sc cutoff j.1 v (List.range v.length)
          (endpointOutputCoefficients D Sc cutoff j.1 v)) =
      independentSRightProduct D Sc cutoff j.1 v (sigma • outputBoundaryPhi D Sc cutoff p j v d) +
        sigma • independentSBoundaryRemainder D Sc cutoff p j v w := by
  dsimp only
  rw [map_smul]
  have h := outputPolynomialBoundary_independentS_coefficients D Sc cutoff p j v d
  rw [← h, ← smul_add]
  congr 1
  unfold outputBoundaryPhi independentSBoundaryRemainder independentSAtRho
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, Module.End.pow_apply]
  abel

/-- High coefficients of the genuine quotient product equal the signed
reverse numerator exactly. -/
theorem independentS_boundary_division_high (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I) (d m : ℕ)
    (hm : outputSDegree D j.1 v ≤ m) :
    independentSRightProduct D Sc cutoff j.1 v
      (SKM.zsign k (D.parity j.1) ^ v.count j.1 • outputBoundaryPhi D Sc cutoff p j v d) m =
    sign k ((cutoff j.1 • D.parity j.1) * (D.parity j.1 * wordSumParity D v)) •
      inputCoefficientShift D Sc cutoff j.1 v d
        (orderedQPOutputCoefficients D Sc cutoff j.1 v (List.range v.length)
          (endpointOutputCoefficients D Sc cutoff j.1 v)) m := by
  have h := congrArg (fun f : ℕ →₀ Old D Sc cutoff v v => f m)
    (independentS_boundary_division D Sc cutoff p j v d)
  simp only [Finsupp.add_apply, Finsupp.smul_apply] at h
  rw [independentSBoundaryRemainder_above D Sc cutoff p j v _ m hm, smul_zero, add_zero] at h
  exact h.symm

/-- The actual boundary quotient has no coefficient beyond the signed
height range. This formulation also covers the negative-height case. -/
theorem outputBoundaryPhi_signed_above (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I) (d m : ℕ)
    (hm : d + endpointQPDegree D cutoff j.1 v < m + outputSDegree D j.1 v) :
    (SKM.zsign k (D.parity j.1) ^ v.count j.1 • outputBoundaryPhi D Sc cutoff p j v d) m = 0 := by
  apply independentSRightProduct_detect_bound D Sc cutoff j v _
    (d + endpointQPDegree D cutoff j.1 v) _ m hm
  intro n hn hN
  rw [independentS_boundary_division_high D Sc cutoff p j v d n hn]
  rw [inputCoefficientShift_above D Sc cutoff j.1 v d (endpointQPDegree D cutoff j.1 v) n _
    (orderedReverseNumerator_above D Sc cutoff j.1 v) hN, smul_zero]

/-- In the nonnegative-height range the actual quotient has the prescribed
scalar unit times identity at its leading bound, including zero old corners. -/
theorem outputBoundaryPhi_signed_top (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I) (d : ℕ)
    (hd : outputSDegree D j.1 v ≤ d + endpointQPDegree D cutoff j.1 v) :
    (SKM.zsign k (D.parity j.1) ^ v.count j.1 • outputBoundaryPhi D Sc cutoff p j v d)
      (d + endpointQPDegree D cutoff j.1 v - outputSDegree D j.1 v) =
    sign k ((cutoff j.1 • D.parity j.1) * (D.parity j.1 * wordSumParity D v)) •
      ((appendQPProductUnit D Sc j.1 v : k) • (ideal D Sc cutoff v v).mkQ (𝟙 _)) := by
  have ht := independentSRightProduct_top D Sc cutoff j v
    (SKM.zsign k (D.parity j.1) ^ v.count j.1 • outputBoundaryPhi D Sc cutoff p j v d)
    (d + endpointQPDegree D cutoff j.1 v - outputSDegree D j.1 v)
    (fun m hm => outputBoundaryPhi_signed_above D Sc cutoff p j v d m (by omega))
  have he : d + endpointQPDegree D cutoff j.1 v - outputSDegree D j.1 v +
      outputSDegree D j.1 v = d + endpointQPDegree D cutoff j.1 v := by omega
  rw [he, independentS_boundary_division_high D Sc cutoff p j v d _ hd,
    inputCoefficientShift_unit_top D Sc cutoff j.1 v d _ _ _
      (orderedReverseNumerator_top D Sc cutoff j.1 v)] at ht
  exact ht.symm

end OddMath.QuiverHecke.ELVOld
end

end

section

/-!
# Coefficient leading maps of the polynomial boundary row

The boundary of each corrected source vector has a prescribed invertible
leading coefficient map. The integer degree difference is the Cartan height.
These are the coefficient-sensitive inputs to row division and then to the
snake-sequence matrix argument; no balanced crossing-column inverse is asserted.
-/
noncomputable section
namespace OddMath.QuiverHecke.ELVOld
open CategoryTheory StringDiagrams Supercategory
open scoped Classical
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

private theorem row_twist_add (a b : ZMod 2) (v : List I) (c : Old D Sc cutoff v v) :
    oldTwist D Sc cutoff a v v (oldTwist D Sc cutoff b v v c) =
      oldTwist D Sc cutoff (a + b) v v c := by
  obtain ⟨c, rfl⟩ := (ideal D Sc cutoff v v).mkQ_surjective c
  change (ideal D Sc cutoff v v).mkQ (twist k a (twist k b c)) = _
  rw [← twist_add]
  rfl

private theorem row_twist_comp (q : ZMod 2) (v : List I) (b c : Old D Sc cutoff v v) :
    oldTwist D Sc cutoff q v v (oldComp D Sc cutoff v v v b c) =
      oldComp D Sc cutoff v v v (oldTwist D Sc cutoff q v v b)
        (oldTwist D Sc cutoff q v v c) := by
  obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v v).mkQ_surjective b
  obtain ⟨c, rfl⟩ := (ideal D Sc cutoff v v).mkQ_surjective c
  change (ideal D Sc cutoff v v).mkQ (twist k q (b ≫ c)) = _
  rw [twist_comp]
  rfl

private theorem row_precomp_comp (v : List I) (a : hom D Sc cutoff v v)
    (b c : Old D Sc cutoff v v) :
    oldPrecomp D Sc cutoff v v a (oldComp D Sc cutoff v v v b c) =
      oldComp D Sc cutoff v v v (oldPrecomp D Sc cutoff v v a b) c := by
  obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v v).mkQ_surjective b
  obtain ⟨c, rfl⟩ := (ideal D Sc cutoff v v).mkQ_surjective c
  change (ideal D Sc cutoff v v).mkQ (a ≫ (b ≫ c)) = _
  rw [← Category.assoc]
  rfl

theorem outputCoefficientRho_rightAction (p q : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I) (c : Old D Sc cutoff v v)
    (f : ℕ →₀ Old D Sc cutoff v v) :
    outputCoefficientRho D Sc cutoff p j v
      (outputCoefficientRightAction D Sc cutoff j.1 q v c f) =
    outputCoefficientRightAction D Sc cutoff j.1 q v c
      (outputCoefficientRho D Sc cutoff p j v f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add f g hf hg => simp only [map_add, hf, hg]
  | single n b =>
    simp only [outputCoefficientRightAction_single, outputCoefficientRho_single,
      map_add, map_smul, row_twist_comp, row_precomp_comp, row_twist_add]
    have he : D.parity j.1 + (q + n • D.parity j.1) = q + (n + 1) • D.parity j.1 := by
      rw [add_smul, one_smul]
      abel
    rw [he]

/-- Corrected source vectors carry the total coefficient twist. -/
theorem outputCorrectedLift_rightAction (p q : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I) (d : ℕ)
    (c : Old D Sc cutoff v v) :
    outputCoefficientRightAction D Sc cutoff j.1 q v c
      (outputLongExtraction D Sc cutoff p j.1 v
        (outputCorrectedLift D Sc cutoff p j v d ((ideal D Sc cutoff v v).mkQ (𝟙 _)))) =
    outputLongExtraction D Sc cutoff p j.1 v
      (outputCorrectedLift D Sc cutoff p j v d (oldTwist D Sc cutoff q v v c)) := by
  simp only [outputLongExtraction_correctedLift]
  induction d with
  | zero =>
    simp only [Function.iterate_zero, id_eq, outputCoefficientRightAction_single,
      zero_smul, add_zero]
    congr 1
    obtain ⟨c, rfl⟩ := (ideal D Sc cutoff v v).mkQ_surjective c
    change (ideal D Sc cutoff v v).mkQ (𝟙 _ ≫ twist k q c) = _
    rw [Category.id_comp]
    rfl
  | succ d ih =>
    rw [Function.iterate_succ_apply', ← outputCoefficientRho_rightAction, ih,
      Function.iterate_succ_apply']

/-- Full coefficient formula for the boundary of the corrected lift. -/
theorem outputBoundary_corrected_coefficient (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I) (d n : ℕ)
    (c : Old D Sc cutoff v v) :
    outputPolynomialBoundary D Sc cutoff p j v
      (outputLongExtraction D Sc cutoff p j.1 v (outputCorrectedLift D Sc cutoff p j v d c)) n =
    oldComp D Sc cutoff v v v (outputBoundaryPhi D Sc cutoff p j v d n)
      (oldTwist D Sc cutoff
        (n • D.parity j.1 + (p + D.parity j.1 * wordSumParity D v)) v v c) := by
  have h := outputPolynomialBoundary_rightAction D Sc cutoff p j v
    (oldTwist D Sc cutoff (p + D.parity j.1 * wordSumParity D v) v v c)
    (outputLongExtraction D Sc cutoff p j.1 v
      (outputCorrectedLift D Sc cutoff p j v d ((ideal D Sc cutoff v v).mkQ (𝟙 _))))
  rw [outputCorrectedLift_rightAction, oldTwist_twice] at h
  rw [h, outputCoefficientRightAction_apply, zero_add, row_twist_add]
  rfl

/-- The row degree is the Cartan height, with integer subtraction. -/
theorem endpointQPDegree_sub_outputSDegree (i : I) (v : List I) :
    (endpointQPDegree D cutoff i v : ℤ) - outputSDegree D i v =
      (cutoff i : ℤ) - (v.map (fun j => D.h i (D.α j))).sum := by
  have hr : ∀ w : List I, (List.range w.length).map (fun b => w.getD b i) = w := by
    intro w
    induction w with
    | nil => rfl
    | cons a w ih =>
      simp only [List.length_cons, List.range_succ_eq_map, List.map_cons, List.getD_cons_zero,
        List.map_map]
      exact congrArg (List.cons a) ih
  have he : endpointQPDegree D cutoff i v = cutoff i + (v.map (appendQPDegree D i)).sum := by
    unfold endpointQPDegree
    conv_rhs => rw [← hr v, List.map_map]
    rfl
  rw [he, Nat.cast_add]
  suffices hs : ((v.map (appendQPDegree D i)).sum : ℤ) - outputSDegree D i v =
      -(v.map (fun j => D.h i (D.α j))).sum by omega
  clear he hr
  induction v with
  | nil => simp [outputSDegree]
  | cons a v ih =>
    simp only [List.map_cons, List.sum_cons, Nat.cast_add]
    by_cases h : a = i
    · subst a
      simp [outputSDegree, appendQPDegree, D.cd.coroot_root_self] at ih ⊢
      split_ifs at ih ⊢ <;> omega
    · have hni : i ≠ a := Ne.symm h
      simp [outputSDegree, h, appendQPDegree, D.dn_cast hni,
        SKM.Datum.d] at ih ⊢
      omega

/-- Coefficients above the integer height bound vanish for every old coefficient. -/
theorem outputBoundary_corrected_above (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I) (d n : ℕ)
    (c : Old D Sc cutoff v v)
    (hn : d + endpointQPDegree D cutoff j.1 v < n + outputSDegree D j.1 v) :
    outputPolynomialBoundary D Sc cutoff p j v
      (outputLongExtraction D Sc cutoff p j.1 v (outputCorrectedLift D Sc cutoff p j v d c)) n = 0 := by
  rw [outputBoundary_corrected_coefficient]
  have h := outputBoundaryPhi_signed_above D Sc cutoff p j v d n hn
  have h' := congrArg (fun b : Old D Sc cutoff v v =>
    SKM.zsign k (D.parity j.1) ^ v.count j.1 • b) h
  simp only [Finsupp.smul_apply, smul_smul, ← mul_pow, SKM.zsign_mul_self',
    one_pow, one_smul, smul_zero] at h'
  rw [h', map_zero, LinearMap.zero_apply]

/-- The leading coefficient map is the specified scalar times total parity twist. -/
theorem outputBoundary_corrected_signed_top (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I) (d n : ℕ)
    (c : Old D Sc cutoff v v)
    (hn : n + outputSDegree D j.1 v = d + endpointQPDegree D cutoff j.1 v) :
    SKM.zsign k (D.parity j.1) ^ v.count j.1 •
      outputPolynomialBoundary D Sc cutoff p j v
        (outputLongExtraction D Sc cutoff p j.1 v (outputCorrectedLift D Sc cutoff p j v d c)) n =
    sign k ((cutoff j.1 • D.parity j.1) * (D.parity j.1 * wordSumParity D v)) •
      ((appendQPProductUnit D Sc j.1 v : k) • oldTwist D Sc cutoff
        (n • D.parity j.1 + (p + D.parity j.1 * wordSumParity D v)) v v c) := by
  rw [outputBoundary_corrected_coefficient, ← LinearMap.smul_apply, ← map_smul]
  have he : n = d + endpointQPDegree D cutoff j.1 v - outputSDegree D j.1 v := by omega
  have ht := outputBoundaryPhi_signed_top D Sc cutoff p j v d (by omega)
  rw [← he] at ht
  simp only [Finsupp.smul_apply] at ht
  rw [ht, map_smul, map_smul, LinearMap.smul_apply, LinearMap.smul_apply]
  congr 2
  obtain ⟨b, hb⟩ := (ideal D Sc cutoff v v).mkQ_surjective
    (oldTwist D Sc cutoff (n • D.parity j.1 + (p + D.parity j.1 * wordSumParity D v)) v v c)
  rw [← hb, oldComp_mk, Category.id_comp]

/-- The unit prescribed by the signed numerator and the independent S top. -/
def outputBoundaryLeadingUnit (j : {j : I // D.parity j = 1}) (v : List I) : kˣ :=
  (⟨SKM.zsign k (D.parity j.1), SKM.zsign k (D.parity j.1),
    SKM.zsign_mul_self' _, SKM.zsign_mul_self' _⟩ : kˣ) ^ v.count j.1 *
  (⟨sign k ((cutoff j.1 • D.parity j.1) * (D.parity j.1 * wordSumParity D v)),
    sign k ((cutoff j.1 • D.parity j.1) * (D.parity j.1 * wordSumParity D v)),
    Supercategory.sign_mul_self _, Supercategory.sign_mul_self _⟩ : kˣ) * appendQPProductUnit D Sc j.1 v

/-- The complete coefficient leading map, including total parity, is invertible. -/
def outputBoundaryLeadingEquiv (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I) (n : ℕ) :
    Old D Sc cutoff v v ≃ₗ[k] Old D Sc cutoff v v :=
  (LinearEquiv.ofInvolutive
    (oldTwist D Sc cutoff (n • D.parity j.1 + (p + D.parity j.1 * wordSumParity D v)) v v)
    (oldTwist_twice D Sc cutoff _ v v)).trans
      (LinearEquiv.smulOfUnit (outputBoundaryLeadingUnit D Sc cutoff j v))

/-- The leading equivalence is the coefficient of the boundary itself. -/
theorem outputBoundary_corrected_top (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I) (d n : ℕ)
    (c : Old D Sc cutoff v v)
    (hn : n + outputSDegree D j.1 v = d + endpointQPDegree D cutoff j.1 v) :
    outputPolynomialBoundary D Sc cutoff p j v
      (outputLongExtraction D Sc cutoff p j.1 v (outputCorrectedLift D Sc cutoff p j v d c)) n =
    outputBoundaryLeadingEquiv D Sc cutoff p j v n c := by
  have h := outputBoundary_corrected_signed_top D Sc cutoff p j v d n c hn
  have h' := congrArg (fun b : Old D Sc cutoff v v =>
    SKM.zsign k (D.parity j.1) ^ v.count j.1 • b) h
  rw [smul_smul, ← mul_pow, SKM.zsign_mul_self', one_pow, one_smul] at h'
  exact h'.trans (by
    change _ = (SKM.zsign k (D.parity j.1) ^ v.count j.1 *
      sign k ((cutoff j.1 • D.parity j.1) * (D.parity j.1 * wordSumParity D v)) *
      (appendQPProductUnit D Sc j.1 v : k)) •
      oldTwist D Sc cutoff (n • D.parity j.1 + (p + D.parity j.1 * wordSumParity D v)) v v c
    rw [mul_smul, mul_smul])

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Output-last shuffle words

The output-last PBW expansion in `DeformedActionAssembly.md` §2 uses the
shuffle itself, rather than its inverse from the input-side append basis.
Its canonical word is the descending run. This distinction is needed to
move a first-position ELV relation past every nonlong output shuffle.
-/

noncomputable section
open Categorification.TypeA Equiv
namespace OddMath.QuiverHecke

/-- Output-last shuffles use descending words; input append tails use their
inverse ascending words. -/
theorem canWord_appendRun_forward (n : ℕ) (r : Fin (n + 1)) :
    canWord (n + 1) (appendRun n r).1 = descRun r.val (n - r.val) := by
  change canWord (n + 1) (runPerm n r.val)⁻¹ = _
  rw [runPerm, ← wordProd_reverse]
  change canWord (n + 1) (wordProd (n + 1) (descRun r.val (n - r.val))) = _
  cases n with
  | zero =>
    simpa only [Nat.zero_sub, descRun_zero, codeWord_nil] using
      (canWord_wordProd_codeWord (m := 1) (c := []) isCode_nil (by decide))
  | succ n =>
    have hc : IsCode (r.val :: idCode n) :=
      ⟨by rw [length_idCode]; omega, isCode_idCode n⟩
    have hw : codeWord (r.val :: idCode n) = descRun r.val (n + 1 - r.val) := by
      simp only [codeWord_cons, codeWord_idCode, length_idCode, List.nil_append]
    rw [← hw]
    exact canWord_wordProd_codeWord hc (by simp only [List.length_cons, length_idCode]; omega)

theorem cw_descRun (r n : ℕ) :
    cw (descRun r n) = (List.range' r n).map PG.cross := by
  simp only [cw, descRun, List.reverse_reverse]

/-- The long output-last shuffle moves the first colour to the last slot. -/
theorem outputLast_long_target {I : Type*} (i : I) (v : List I) :
    tgt (i :: v) (cw (descRun 0 v.length)) = v ++ [i] := by
  rw [cw_descRun]
  induction v with
  | nil => rfl
  | cons j v ih =>
    rw [List.length_cons, List.range'_succ, List.map_cons, tgt_cons]
    change tgt (j :: i :: v) ((List.range' 1 v.length).map PG.cross) = _
    have hs : (List.range' 1 v.length).map PG.cross =
        ((List.range' 0 v.length).map PG.cross).map (PG.shift 1) := by
      rw [show (1 : ℕ) = 0 + 1 from rfl, List.range'_succ_left]
      simp only [List.map_map]
      apply List.map_congr_left
      intro x _
      exact congrArg PG.cross (Nat.add_comm x 1)
    rw [hs]
    change tgt ([j] ++ (i :: v))
      (((List.range' 0 v.length).map PG.cross).map (PG.shift [j].length)) = _
    rw [tgt_shift, ih]
    rfl

theorem outputLast_last_block {I : Type*} {s t : List I} {j : I}
    {hlen : t.length + [j].length = s.length} (x : ShIdx hlen) :
    shR s t.length x.1.1 = [j] := by
  have hs : (shR s t.length x.1.1).length = 1 := by
    rw [length_shR]
    simp only [List.length_singleton] at hlen
    omega
  have hc : code (shR s t.length x.1.1).length x.2.2.1.2 = [] :=
    List.length_eq_zero_iff.mp (by rw [length_code, hs])
  have hp := x.2.2.tgt_cw
  simpa only [canWord, hc, codeWord_nil, cw_nil, tgt_nil] using hp

/-- Every admissible mixed output-last shuffle is a word on the tail after
the first strand. The first strand is a spectator throughout, not merely at
the two endpoints. -/
theorem outputLast_tail_word {I : Type*} {i j : I} (hij : i ≠ j) (v : List I)
    (n : ℕ) (hn : n + 1 = (i :: v).length) (d : Shuffle hn)
    (hj : shR (i :: v) n d.1 = [j]) :
    ∃ L : List ℕ, ValidWord v.length L ∧
      cw (canWord (i :: v).length d.1) = (cw L).map (PG.shift 1) := by
  have hnv : n = v.length := by simpa only [List.length_cons, Nat.add_right_cancel_iff] using hn
  subst n
  obtain ⟨r, rfl⟩ := (appendRunEquiv v.length).surjective d
  simp only [appendRunEquiv_apply] at hj ⊢
  have hword : canWord (i :: v).length (appendRun v.length r).1 =
      descRun r.val (v.length - r.val) := canWord_appendRun_forward v.length r
  have hr : 0 < r.val := by
    by_contra h
    have hr0 : r.val = 0 := by omega
    rw [shR, shTop, hword, hr0, Nat.sub_zero, outputLast_long_target,
      List.drop_left] at hj
    exact hij (List.singleton_inj.mp hj)
  refine ⟨descRun (r.val - 1) (v.length - r.val), ?_, ?_⟩
  · intro a ha
    rw [mem_descRun] at ha
    have hrv := r.isLt
    omega
  · have hshift := List.range'_succ_left (s := r.val - 1) (n := v.length - r.val) (step := 1)
    rw [show r.val - 1 + 1 = r.val from by omega] at hshift
    rw [hword, cw_descRun, cw_descRun, hshift]
    simp only [List.map_map]
    apply List.map_congr_left
    intro a _
    exact congrArg PG.cross (Nat.add_comm a 1)

/-- The two output blocks of a mixed shuffle have a first-colour spectator
factorization, with the actual lower word of the tail retained. -/
theorem outputLast_tail_factor {I : Type*} {i j : I} (hij : i ≠ j) (v : List I)
    (n : ℕ) (hn : n + 1 = (i :: v).length) (d : Shuffle hn)
    (hj : shR (i :: v) n d.1 = [j]) :
    ∃ (s : List I) (L : List ℕ), ValidWord v.length L ∧
      shL (i :: v) n d.1 = i :: s ∧ tgt v (cw L) = s ++ [j] ∧
      cw (canWord (i :: v).length d.1) = (cw L).map (PG.shift 1) := by
  obtain ⟨L, hL, hw⟩ := outputLast_tail_word hij v n hn d hj
  have ht : shL (i :: v) n d.1 ++ [j] = i :: tgt v (cw L) := by
    rw [← hj, shL_append_shR, shTop, hw]
    exact tgt_shift [i] v (cw L)
  cases hs : shL (i :: v) n d.1 with
  | nil =>
    simp only [hs, List.nil_append] at ht
    exact (hij (List.cons.inj ht).1.symm).elim
  | cons c s =>
    simp only [hs, List.cons_append] at ht
    have hhead : c = i := (List.cons.inj ht).1
    have htail : s ++ [j] = tgt v (cw L) := (List.cons.inj ht).2
    subst c
    exact ⟨s, L, hL, rfl, htail.symm, hw⟩

end OddMath.QuiverHecke
end

end
