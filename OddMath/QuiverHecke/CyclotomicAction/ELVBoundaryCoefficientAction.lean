/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVOutputSLeading

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
