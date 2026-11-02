/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVIdealSum
import OddMath.QuiverHecke.CyclotomicAction.ELVAppendCrossingTriangular
import OddMath.QuiverHecke.CyclotomicAction.ELVOutputLastShuffle

/-! # The output-old ideal in distinct last-colour corners

Advances `DeformedActionAssembly.md` §2, the full-ELV extension of KKO I
equality (9.3). The output-old span retains the last colour as a spectator.
First-position relations move only past tail arrows, with their full total
parity. No relation is commuted through the first crossing.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped TensorProduct Classical
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Relations imposed on the old output word, keeping the last colour fixed. -/
def outputOldRelations (j : I) (v t : List I) :
    Submodule k (hom D Sc cutoff v (t ++ [j])) :=
  Submodule.span k {z | ∃ s, ∃ r : hom D Sc cutoff s t,
    r ∈ ideal D Sc cutoff s t ∧ ∃ c : hom D Sc cutoff v (s ++ [j]),
      c ≫ rightContext D Sc cutoff [j] s t r = z}

theorem outputOldRelations_le_ideal (j : I) (v t : List I) :
    outputOldRelations D Sc cutoff j v t ≤ ideal D Sc cutoff v (t ++ [j]) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨s, r, hr, c, rfl⟩
  exact comp_ideal D Sc cutoff c (ideal_rightContext D Sc cutoff [j] hr)

theorem outputOldRelations_precomp (j : I) {v w t : List I}
    (c : hom D Sc cutoff v w) {z : hom D Sc cutoff w (t ++ [j])}
    (hz : z ∈ outputOldRelations D Sc cutoff j w t) :
    c ≫ z ∈ outputOldRelations D Sc cutoff j v t := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨s, r, hr, b, rfl⟩ := hz
    exact Submodule.subset_span ⟨s, r, hr, c ≫ b, Category.assoc _ _ _⟩
  | zero => simpa only [Limits.comp_zero] using
      (outputOldRelations D Sc cutoff j v t).zero_mem
  | add a b _ _ ha hb =>
    simpa only [Preadditive.comp_add] using Submodule.add_mem _ ha hb
  | smul a z _ hz =>
    simpa only [Linear.comp_smul] using Submodule.smul_mem _ a hz

/-- Reverse tail transport uses the total relation parity. The first strand
is untouched throughout the tail arrow. -/
theorem relation_comp_tail (i : I) {v w : List I}
    (f : (pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w)) :
    relation D Sc cutoff i v ≫ affineUnit D Sc cutoff _ _ (affineInsert D Sc i v w f) =
      affineUnit D Sc cutoff _ _
        (affineInsert D Sc i v w (twist k ((cutoff i : ZMod 2) * D.parity i) f)) ≫
          relation D Sc cutoff i w := by
  induction f using Supercategory.induction_on (R := k) (C := (pres D Sc).Presented) with
  | zero => simp only [map_zero, Limits.comp_zero, Limits.zero_comp]
  | add f g hf hg =>
    simp only [map_add, Preadditive.comp_add, Preadditive.add_comp, hf, hg]
  | hom q f hf =>
    rw [twist_of_mem _ hf, map_smul, map_smul, Linear.smul_comp, ← koszulSign_smul]
    have h := congrArg (koszulSign ((cutoff i : ZMod 2) * D.parity i) q • ·)
      (tail_relation_homogeneous D Sc cutoff i f hf)
    simpa only [smul_smul, koszulSign_mul_self, one_smul] using h.symm

/-- A first-position relation followed by a last-dot power remains an
output-old relation. The parity involution acts on the whole old Hom. -/
theorem relation_lastPower_outputOldRelations (i j : I) (s t : List I)
    (m : ℕ) (b : hom D Sc cutoff (i :: s) t) :
    relation D Sc cutoff i (s ++ [j]) ≫ appendMovingPower D Sc cutoff j (i :: s) m ≫
        rightContext D Sc cutoff [j] (i :: s) t b ∈
      outputOldRelations D Sc cutoff j ((i :: s) ++ [j]) t := by
  have hmove := appendMovingPower_twisted_rightContext D Sc cutoff j (i :: s) (i :: s) m
    (twist k (m • D.parity j) (relation D Sc cutoff i s))
  rw [twist_twist] at hmove
  rw [← rightContext_relation D Sc cutoff [j] i s, ← Category.assoc, ← hmove,
    Category.assoc, ← rightContext_comp]
  exact Submodule.subset_span ⟨i :: s,
    twist k (m • D.parity j) (relation D Sc cutoff i s) ≫ b,
    ideal_comp D Sc cutoff (twist_ideal D Sc cutoff _ (relation_mem D Sc cutoff i s)) b,
    appendMovingPower D Sc cutoff j (i :: s) m, rfl⟩

private theorem relation_tail_parabolic_mem (i j : I) (v s t l r : List I)
    (hl : l = i :: s) (hr : r = [j])
    (f : (pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D (s ++ [j])))
    (F : (pres D Sc).obj (ob D (i :: v)) ⟶ (pres D Sc).obj (ob D (l ++ r)))
    (hF : HEq F (affineInsert D Sc i v (s ++ [j]) f))
    (b : NFIdx l t) (c : NFIdx r [j])
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    relation D Sc cutoff i v ≫ affineUnit D Sc cutoff _ _ F ≫
        (a ⊗ₜ[k] (((pres D Sc).obj (ob D l) ◁ c.nf) ≫
          (b.nf ▷ (pres D Sc).obj (ob D [j]))) :
            hom D Sc cutoff (l ++ r) (t ++ [j])) ∈
      outputOldRelations D Sc cutoff j (i :: v) t := by
  subst l
  subst r
  have hF' : F = affineInsert D Sc i v (s ++ [j]) f := eq_of_heq hF
  subst F
  let P : hom D Sc cutoff ((i :: s) ++ [j]) (t ++ [j]) :=
    a ⊗ₜ[k] (((pres D Sc).obj (ob D (i :: s)) ◁ c.nf) ≫
      (b.nf ▷ (pres D Sc).obj (ob D [j])))
  change relation D Sc cutoff i v ≫
    affineUnit D Sc cutoff _ _ (affineInsert D Sc i v (s ++ [j]) f) ≫ P ∈ _
  rw [← Category.assoc, relation_comp_tail D Sc cutoff i f, Category.assoc]
  apply outputOldRelations_precomp
  obtain ⟨m, rfl⟩ := (singleNFIndex_bijective j).surjective c
  have hp : P =
      appendMovingPower D Sc cutoff j (i :: s) m ≫
        rightContext D Sc cutoff [j] (i :: s) t (a ⊗ₜ[k] b.nf) := by
    dsimp only [P]
    rw [singleNFIndex_nf, appendMovingPower_whisker, rightContext_tmul]
    exact (affineUnit_comp_coefficient D Sc cutoff _ _ a).symm
  rw [hp]
  exact relation_lastPower_outputOldRelations D Sc cutoff i j s t m (a ⊗ₜ[k] b.nf)

private theorem relation_outputLast_term_mem (i j : I) (hij : i ≠ j) (v t : List I)
    (hlen : t.length + [j].length = (i :: v).length) (x : ShIdx hlen)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    relation D Sc cutoff i v ≫
        (affineUnit D Sc cutoff _ _ (shPsi D Sc t.length x.1.1) ≫
          shuffleParabolic D Sc cutoff x a) ∈
      outputOldRelations D Sc cutoff j (i :: v) t := by
  have hr := outputLast_last_block x
  obtain ⟨s, L, hL, hl, ht, hw⟩ :=
    outputLast_tail_factor hij v t.length hlen x.1 hr
  let f : (pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D (s ++ [j])) :=
    cl D Sc v (s ++ [j]) (cw L) (by rw [← ht]; exact sChain_pl v (cw L))
  have hF : HEq (shPsi D Sc t.length x.1.1) (affineInsert D Sc i v (s ++ [j]) f) := by
    change HEq (shPsi D Sc t.length x.1.1) ((pres D Sc).obj (ob D [i]) ◁ f)
    dsimp only [f]
    rw [cl_whiskerLeft]
    exact OutputShuffle.cl_heq D Sc _ _ hw
  exact relation_tail_parabolic_mem D Sc cutoff i j v s t
    (shL (i :: v) t.length x.1.1) (shR (i :: v) t.length x.1.1)
    hl hr f (shPsi D Sc t.length x.1.1) hF x.2.1 x.2.2 a

/-- In a distinct last-colour corner, the first-position relation lands in
the old output ideal. The long output-last shuffle is absent by support. -/
theorem relation_comp_outputOldRelations (i j : I) (hij : i ≠ j) (v t : List I)
    (h : hom D Sc cutoff (i :: v) (t ++ [j])) :
    relation D Sc cutoff i v ≫ h ∈ outputOldRelations D Sc cutoff j (i :: v) t := by
  by_cases hlen : t.length + [j].length = (i :: v).length
  · let S := (outputOldRelations D Sc cutoff j (i :: v) t).comap
      (Linear.leftComp k _ (relation D Sc cutoff i v))
    exact hom_mem_of_shuffle_parabolic D Sc cutoff hlen S
      (relation_outputLast_term_mem D Sc cutoff i j hij v t hlen) h
  · have hh : h = 0 := hom_eq_zero_of_length_ne D Sc cutoff (by
      intro he
      apply hlen
      simpa only [List.length_append] using he.symm) h
    rw [hh, Limits.comp_zero]
    exact Submodule.zero_mem _

/-- The moving-strand summand of the one-sided ideal decomposition is
already an output-old relation in every distinct-colour corner. -/
theorem appendW_range_le_outputOldRelations (i j : I) (hij : i ≠ j) (v t : List I) :
    LinearMap.range (Linear.leftComp k (obj D Sc cutoff (t ++ [j]))
      (appendW D Sc cutoff i v)) ≤ outputOldRelations D Sc cutoff j (v ++ [i]) t := by
  rintro _ ⟨h, rfl⟩
  change appendW D Sc cutoff i v ≫ h ∈ _
  rw [appendW, Category.assoc]
  exact outputOldRelations_precomp D Sc cutoff j _
    (relation_comp_outputOldRelations D Sc cutoff i j hij v t h)

/-- The word-corner form of KKO I (9.3) for the noncentral full-ELV relation.
Both old ideals remain literal; empty words and zero cutoffs are included. -/
theorem ideal_eq_appendRelations_sup_outputOldRelations
    (i j : I) (hij : i ≠ j) (v t : List I) :
    ideal D Sc cutoff (v ++ [i]) (t ++ [j]) =
      appendRelations D Sc cutoff i v (t ++ [j]) ⊔
        outputOldRelations D Sc cutoff j (v ++ [i]) t := by
  apply le_antisymm
  · rw [ideal_eq_appendRelations_sup_range]
    exact sup_le_sup_left (appendW_range_le_outputOldRelations D Sc cutoff i j hij v t) _
  · exact sup_le (appendRelations_le_ideal D Sc cutoff i v (t ++ [j]))
      (outputOldRelations_le_ideal D Sc cutoff j (v ++ [i]) t)

end OddMath.QuiverHecke.ELVOld
