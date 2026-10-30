/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVAppendCrossingTriangular
import OddMath.QuiverHecke.CyclotomicAction.ELVAppendDescent

/-!
# Output polynomials and the append crossing dot defect

The output maps in `DeformedMackeyBoundary.md` (4) and the local dot identity
preceding (8), over the full ELV old quotient. These use postcomposition by
the output moving dot, not the input moving-dot operator. The crossing
formula retains total old-Hom parity, including exterior coefficients.
This module does not assert the global corrected polynomial projection.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Output polynomial reconstruction with coefficients in the old quotient. -/
def appendOutputEmbedding (i : I) (v t : List I) :
    (ℕ →₀ Old D Sc cutoff v t) →ₗ[k] AppendTarget D Sc cutoff i v (t ++ [i]) :=
  Finsupp.lsum k fun m => appendPair D Sc cutoff 0 i
    (appendMovingPower D Sc cutoff i t m)

@[simp] theorem appendOutputEmbedding_single (i : I) (v t : List I)
    (m : ℕ) (g : hom D Sc cutoff v t) :
    appendOutputEmbedding D Sc cutoff i v t
      (Finsupp.single m ((ideal D Sc cutoff v t).mkQ g)) =
    appendProjection D Sc cutoff i v (t ++ [i])
      (rightContext D Sc cutoff [i] v t g ≫ appendMovingPower D Sc cutoff i t m) := by
  simp only [appendOutputEmbedding, Finsupp.lsum_single, appendPair_mk, twist_zero]

/-- The prescribed output polynomial map descends coefficientwise. -/
theorem appendOutputEmbedding_map (i : I) (v t : List I)
    (f : ℕ →₀ hom D Sc cutoff v t) :
    appendOutputEmbedding D Sc cutoff i v t
      (Finsupp.mapRange.linearMap (ideal D Sc cutoff v t).mkQ f) =
    appendProjection D Sc cutoff i v (t ++ [i]) (appendOutputPolynomial D Sc cutoff i v t f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add f g hf hg => simp only [map_add, hf, hg]
  | single m g =>
    simp only [Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single,
      appendOutputEmbedding_single, appendOutputPolynomial_single]

private theorem append_postcomp_relations (i : I) (v w z : List I)
    (a : hom D Sc cutoff w z) :
    appendRelations D Sc cutoff i v w ≤
      (appendRelations D Sc cutoff i v z).comap (Linear.rightComp k _ a) := by
  intro h hh
  exact appendRelations_comp D Sc cutoff i hh a

/-- Output postcomposition preserves all append-old relations. -/
def appendOutputDot (i : I) (v t : List I) :
    AppendTarget D Sc cutoff i v (t ++ [i]) →ₗ[k]
      AppendTarget D Sc cutoff i v (t ++ [i]) :=
  (appendRelations D Sc cutoff i v (t ++ [i])).mapQ
    (appendRelations D Sc cutoff i v (t ++ [i]))
    (Linear.rightComp k _ (appendMovingPower D Sc cutoff i t 1))
    (append_postcomp_relations D Sc cutoff i v _ _ _)

@[simp] theorem appendOutputDot_projection (i : I) (v t : List I)
    (h : hom D Sc cutoff (v ++ [i]) (t ++ [i])) :
    appendOutputDot D Sc cutoff i v t (appendProjection D Sc cutoff i v (t ++ [i]) h) =
      appendProjection D Sc cutoff i v (t ++ [i])
        (h ≫ appendMovingPower D Sc cutoff i t 1) := rfl

/-- Exponent translation on output coefficients. -/
def appendOutputShift (v t : List I) :
    (ℕ →₀ Old D Sc cutoff v t) →ₗ[k] (ℕ →₀ Old D Sc cutoff v t) :=
  Finsupp.lsum k fun m => Finsupp.lsingle (m + 1)

/-- The output polynomial map intertwines the specified output dot. -/
theorem appendOutputDot_embedding (i : I) (v t : List I)
    (f : ℕ →₀ Old D Sc cutoff v t) :
    appendOutputDot D Sc cutoff i v t (appendOutputEmbedding D Sc cutoff i v t f) =
      appendOutputEmbedding D Sc cutoff i v t (appendOutputShift D Sc cutoff v t f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add f g hf hg => simp only [map_add, hf, hg]
  | single m b =>
    obtain ⟨g, rfl⟩ := (ideal D Sc cutoff v t).mkQ_surjective b
    rw [appendOutputEmbedding_single, appendOutputDot_projection]
    simp only [appendOutputShift, Finsupp.lsum_single, Finsupp.lsingle_apply,
      appendOutputEmbedding_single]
    congr 1
    rw [Category.assoc]
    congr 1
    unfold appendMovingPower
    rw [pow_one, ← affineUnit_comp]
    congr 1
    exact (pow_succ' (dotE D Sc (t ++ [i]) t.length) m).symm

/-- The crossing generator with arbitrary old input and output arrows. -/
def appendCrossingClass (i : I) (v s t : List I)
    (r : hom D Sc cutoff v (s ++ [i])) (g : hom D Sc cutoff (s ++ [i]) t) :
    AppendTarget D Sc cutoff i v (t ++ [i]) :=
  appendProjection D Sc cutoff i v (t ++ [i])
    (rightContext D Sc cutoff [i] _ _ r ≫ affineUnit D Sc cutoff _ _
      (crossLast D Sc s i i) ≫ rightContext D Sc cutoff [i] _ _ g)

/-- Crossing followed by the output moving dot, before the old quotient. -/
theorem appendCrossing_output_dot (i : I) (s : List I) :
    affineUnit D Sc cutoff _ _ (crossLast D Sc s i i) ≫
        appendMovingPower D Sc cutoff i (s ++ [i]) 1 =
      SKM.zsign k (D.parity i * D.parity i) •
        (rightContext D Sc cutoff [i] _ _ (appendMovingPower D Sc cutoff i s 1) ≫
          affineUnit D Sc cutoff _ _ (crossLast D Sc s i i)) -
      SKM.zsign k (D.parity i * D.parity i) • 𝟙 _ := by
  have hd : rightContext D Sc cutoff [i] _ _ (appendMovingPower D Sc cutoff i s 1) =
      affineUnit D Sc cutoff _ _ (dotE D Sc (s ++ [i] ++ [i]) s.length) := by
    simp only [appendMovingPower, pow_one, rightContext_affineUnit]
    congr 1
    exact dotE_whiskerRight D Sc (s ++ [i]) [i] s.length (by simp)
  rw [hd, ← affineUnit_comp, dotE_comp_crossLast_self, map_add, map_smul,
    affineUnit_comp, affineUnit_id, smul_add, zsign_smul_zsign_smul,
    add_sub_cancel_right]
  simp only [appendMovingPower, pow_one, List.length_append, List.length_singleton]

/-- The full-coefficient output-dot defect on every crossing generator.
For odd moving colour the constant term has positive sign. -/
theorem appendOutputDot_crossingClass (i : I) (v s t : List I)
    (r : hom D Sc cutoff v (s ++ [i])) (g : hom D Sc cutoff (s ++ [i]) t) :
    appendOutputDot D Sc cutoff i v t (appendCrossingClass D Sc cutoff i v s t r g) =
      SKM.zsign k (D.parity i * D.parity i) •
        appendCrossingClass D Sc cutoff i v s t
          (r ≫ appendMovingPower D Sc cutoff i s 1) (twist k (D.parity i) g) -
      SKM.zsign k (D.parity i * D.parity i) •
        appendOutputEmbedding D Sc cutoff i v t
          (Finsupp.single 0 ((ideal D Sc cutoff v t).mkQ (r ≫ twist k (D.parity i) g))) := by
  have ht := appendMovingPower_twisted_rightContext D Sc cutoff i (s ++ [i]) t 1
    (twist k (D.parity i) g)
  simp only [one_smul, twist_twist] at ht
  simp only [appendCrossingClass, appendOutputDot_projection, Category.assoc]
  rw [← ht, ← Category.assoc (affineUnit D Sc cutoff _ _ _), appendCrossing_output_dot]
  simp only [Preadditive.sub_comp, Preadditive.comp_sub, Linear.smul_comp,
    Linear.comp_smul, Category.assoc, Category.id_comp, ← rightContext_comp,
    map_sub, map_smul, appendOutputEmbedding_single, appendMovingPower,
    pow_zero, End.one_def, affineUnit_id, Category.comp_id]
  simp only [rightContext_comp, Category.assoc]

/-- At an odd moving colour, the defect is the positive degree-zero output term. -/
theorem appendOutputDot_crossingClass_odd (i : I) (hi : D.parity i = 1)
    (v s t : List I) (r : hom D Sc cutoff v (s ++ [i]))
    (g : hom D Sc cutoff (s ++ [i]) t) :
    appendOutputDot D Sc cutoff i v t (appendCrossingClass D Sc cutoff i v s t r g) =
      -appendCrossingClass D Sc cutoff i v s t
        (r ≫ appendMovingPower D Sc cutoff i s 1) (twist k 1 g) +
      appendOutputEmbedding D Sc cutoff i v t
        (Finsupp.single 0 ((ideal D Sc cutoff v t).mkQ (r ≫ twist k 1 g))) := by
  rw [appendOutputDot_crossingClass, hi, mul_one]
  simp only [SKM.zsign, ite_true, neg_one_smul, sub_neg_eq_add]

end OddMath.QuiverHecke.ELVOld
