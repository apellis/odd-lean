/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVBoundaryPolynomial
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
