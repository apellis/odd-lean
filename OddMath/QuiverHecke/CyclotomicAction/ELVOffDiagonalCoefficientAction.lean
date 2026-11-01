import OddMath.QuiverHecke.CyclotomicAction.ELVBoundaryCoefficientAction

/-! # Arbitrary-output covariance of the actual polynomial projection

The degree-dependent total twist acts on arbitrary old Hom coefficients.
The existing append quotient is postcomposed by an actual affine old arrow.
Its polynomial projection is covariant with the prescribed twist; no
diagonal-corner sufficiency or module-level inverse is asserted.
-/
noncomputable section
namespace OddMath.QuiverHecke.ELVOld
open CategoryTheory StringDiagrams Supercategory
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The full output-arrow action, including the degree-dependent total twist. -/
def offDiagonalCoefficientRightAction (i : I) (q : ZMod 2) (v s t : List I)
    (c : Old D Sc cutoff s t) :
    (ℕ →₀ Old D Sc cutoff v s) →ₗ[k] (ℕ →₀ Old D Sc cutoff v t) :=
  Finsupp.lsum k fun n => (Finsupp.lsingle n).comp
    ((oldComp D Sc cutoff v s t).flip
      (oldTwist D Sc cutoff (q + n • D.parity i) s t c))

@[simp] theorem offDiagonalCoefficientRightAction_single (i : I) (q : ZMod 2)
    (v s t : List I) (c : Old D Sc cutoff s t) (b : Old D Sc cutoff v s) (n : ℕ) :
    offDiagonalCoefficientRightAction D Sc cutoff i q v s t c (Finsupp.single n b) =
      Finsupp.single n (oldComp D Sc cutoff v s t b
        (oldTwist D Sc cutoff (q + n • D.parity i) s t c)) := by
  simp only [offDiagonalCoefficientRightAction, Finsupp.lsum_single,
    LinearMap.comp_apply, Finsupp.lsingle_apply, LinearMap.flip_apply]

theorem offDiagonalCoefficientRightAction_apply (i : I) (q : ZMod 2)
    (v s t : List I) (c : Old D Sc cutoff s t)
    (f : ℕ →₀ Old D Sc cutoff v s) (n : ℕ) :
    offDiagonalCoefficientRightAction D Sc cutoff i q v s t c f n =
      oldComp D Sc cutoff v s t (f n)
        (oldTwist D Sc cutoff (q + n • D.parity i) s t c) := by
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero, Finsupp.zero_apply, LinearMap.zero_apply]
  | add f g hf hg => simp only [map_add, Finsupp.add_apply, hf, hg, LinearMap.add_apply]
  | single m b =>
    rw [offDiagonalCoefficientRightAction_single]
    by_cases h : m = n
    · subst m; simp only [Finsupp.single_eq_same]
    · simp [Ne.symm h]

theorem appendPostcomp_embedding_general (i : I) (v s t : List I)
    (g : hom D Sc cutoff s t) (f : ℕ →₀ Old D Sc cutoff v s) :
    appendPostcomp D Sc cutoff i v (appendInsert D Sc cutoff i s t g)
      (appendOutputEmbedding D Sc cutoff i v s f) =
    appendOutputEmbedding D Sc cutoff i v t
      (offDiagonalCoefficientRightAction D Sc cutoff i 0 v s t
        ((ideal D Sc cutoff s t).mkQ g) f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add f h hf hh => simp only [map_add, hf, hh]
  | single m b =>
    obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v s).mkQ_surjective b
    rw [appendOutputEmbedding_single, appendPostcomp_projection,
      offDiagonalCoefficientRightAction_single]
    change _ = appendOutputEmbedding D Sc cutoff i v t
      (Finsupp.single m ((ideal D Sc cutoff v t).mkQ
        (b ≫ twist k (0 + m • D.parity i) g)))
    rw [appendOutputEmbedding_single]
    congr 1
    simp only [appendInsert, Category.assoc, appendMovingPower_twisted_rightContext,
      zero_add, rightContext_comp]

theorem appendPostcomp_crossing_general (i : I) (v u s t : List I)
    (g : hom D Sc cutoff s t) (r : hom D Sc cutoff v (u ++ [i]))
    (h : hom D Sc cutoff (u ++ [i]) s) :
    appendPostcomp D Sc cutoff i v (appendInsert D Sc cutoff i s t g)
      (appendCrossingClass D Sc cutoff i v u s r h) =
    appendCrossingClass D Sc cutoff i v u t r (h ≫ g) := by
  unfold appendCrossingClass
  rw [appendPostcomp_projection]
  simp only [appendInsert, rightContext_comp, Category.assoc]

/-- Covariance is proved on the actual quotient using its exact crossing kernel. -/
theorem appendC0_postcomp_general (i : I) (v s t : List I)
    (g : hom D Sc cutoff s t) (z : AppendTarget D Sc cutoff i v (s ++ [i])) :
    appendC0 D Sc cutoff i v t
      (appendPostcomp D Sc cutoff i v (appendInsert D Sc cutoff i s t g) z) =
    offDiagonalCoefficientRightAction D Sc cutoff i 0 v s t
      ((ideal D Sc cutoff s t).mkQ g) (appendC0 D Sc cutoff i v s z) := by
  have hpres : ∀ c ∈ appendCrossingSpan D Sc cutoff i v s,
      appendC0 D Sc cutoff i v t
        (appendPostcomp D Sc cutoff i v (appendInsert D Sc cutoff i s t g) c) = 0 := by
    intro c hc
    induction hc using Submodule.span_induction with
    | mem c hc =>
      obtain ⟨u, r, h, rfl⟩ := hc
      rw [appendPostcomp_crossing_general, appendC0_crossing]
    | zero => simp only [map_zero]
    | add a b _ _ ha hb => simp only [map_add, ha, hb, add_zero]
    | smul a b _ hb => simp only [map_smul, hb, smul_zero]
  have h := hpres _ (appendC0_residual_mem D Sc cutoff i v s z)
  rw [map_sub, map_sub, appendPostcomp_embedding_general, appendC0_embedding,
    sub_eq_zero] at h
  exact h

end OddMath.QuiverHecke.ELVOld
