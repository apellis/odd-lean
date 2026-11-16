import OddMath.SKM.SameColourSourceCoordinates

/-! Source principal columns with upward cap dots. Both inverse-block and
sliding corrections are retained with their isolated cap indices. -/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Presentation
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k}
namespace SameColourSourceFrame
variable {P Q Z : List (Letter I)} {i : I} (F : SameColourSourceFrame P Q Z i)
  (cs : CScalars Sc) (μ : X)

def sourceLoopLift (r : F.residual.Labels)
    (z : End ((pres D Sc).obj (ob D (wt D μ Q) []))) : F.residual.Labels →₀ SYM D k :=
  (F.residual.expansion_surjective cs μ
    (plcAt μ (P ++ Q) (P ++ Q) P Q z ≫ xev cs μ (P ++ Q) Z (F.residual.layers r))).choose

theorem sourceLoopLift_eval (r : F.residual.Labels)
    (z : End ((pres D Sc).obj (ob D (wt D μ Q) []))) :
    F.residual.expansion cs μ (F.sourceLoopLift cs μ r z) =
      plcAt μ (P ++ Q) (P ++ Q) P Q z ≫ xev cs μ (P ++ Q) Z (F.residual.layers r) :=
  (F.residual.expansion_surjective cs μ _).choose_spec

def sourceNegativeColumn (N b : ℕ) (r : F.residual.Labels) :
    (F.residual.Labels × ℕ) →₀ SYM D k :=
  if b < N then 0 else
    ((zsign k (D.parity i)) ^ (b - N) * (↑(cs.c (wt D μ Q) i)⁻¹ : k)) •
      Finsupp.single (r, b - N) 1 +
    ∑ s ∈ Finset.range (b - N), (zsign k (D.parity i)) ^ s •
      F.capResidualColumn s (F.sourceLoopLift cs μ r
        (hLM D Sc i (wt D μ Q) (b - 1 - s) ≫ epsP cs i (wt D μ Q)))

def sourceNonnegativeColumn (N b : ℕ) (r : F.residual.Labels) :
    (F.residual.Labels × ℕ) →₀ SYM D k :=
  (-((zsign k (D.parity i)) ^ b *
    (-(zsign k (D.parity i * (D.h i (wt D μ Q) : ZMod 2)) *
      (↑(cs.c (wt D μ Q) i)⁻¹ : k))))) • Finsupp.single (r, b + N) 1 +
  (∑ j ∈ Finset.range N,
    ((zsign k (D.parity i)) ^ b *
      (-(zsign k (D.parity i * (D.h i (wt D μ Q) : ZMod 2)) *
        (↑(cs.c (wt D μ Q) i)⁻¹ : k)))) •
      F.capResidualColumn (b + j) (F.sourceLoopLift cs μ r
        (dcM D Sc i (wt D μ Q) j ≫ eLM D Sc i (wt D μ Q) N))) +
  ∑ s ∈ Finset.range b, (zsign k (D.parity i)) ^ s •
    F.capResidualColumn s (F.sourceLoopLift cs μ r
      (hLM D Sc i (wt D μ Q) (b - 1 - s) ≫ epsP cs i (wt D μ Q)))

theorem source_cap_loop (r : F.residual.Labels)
    (z : End ((pres D Sc).obj (ob D (wt D μ Q) []))) (b : ℕ) :
    F.residual.preRowsExpansion cs μ (sourceCapRows (Sc := Sc) μ P Q i)
      (F.capResidualColumn b (F.sourceLoopLift cs μ r z)) =
    plcW μ (P ++ up i :: dn i :: Q) (P ++ Q) P Q [up i, dn i] []
      (eLM D Sc i (wt D μ Q) b ≫ z) ≫ xev cs μ (P ++ Q) Z (F.residual.layers r) := by
  rw [capResidualColumn, F.residual.preRowsExpansion_residualRow cs μ _ b _
    (sourceCapRows_mem_parity μ P Q i b), F.sourceLoopLift_eval, ← Category.assoc]
  congr 1
  exact sourcePlcW_comp_at μ _ _ (P ++ Q) P Q [up i, dn i] [] [] (by simp) _ _

theorem sourceNegativeColumn_eval (N b : ℕ) (r : F.residual.Labels)
    (hN : -D.h i (wt D μ Q) = (N : ℤ)) (hpos : 0 < N) :
    F.residual.preRowsExpansion cs μ (sourceCapRows (Sc := Sc) μ P Q i)
      (F.sourceNegativeColumn cs μ N b r) =
    plcW μ (P ++ up i :: dn i :: Q) (P ++ Q) P Q [up i, dn i] []
      (sgM D Sc i (wt D μ Q) ≫ cpow (uRM D Sc i (wt D μ Q)) b ≫
        epsP cs i (wt D μ Q)) ≫ xev cs μ (P ++ Q) Z (F.residual.layers r) := by
  by_cases hb : b < N
  · rw [sourceNegativeColumn, ite_eq_left hb, map_zero,
      paired_source_below cs i (wt D μ Q) b (by omega), map_zero, Limits.zero_comp]
  · have he : N + (b - N) = b := by omega
    have H := paired_source_leading_neg cs i (wt D μ Q) N (b - N) hN hpos
    rw [he] at H
    rw [H, sourceNegativeColumn, ite_eq_right hb]
    simp only [map_add, map_smul, map_sum, Preadditive.add_comp,
      Linear.smul_comp, Preadditive.sum_comp, F.source_cap_loop]
    rw [F.residual.preRowsExpansion_single]
    simp only [map_one, End.one_def, bubAt_id, Category.id_comp, sourceCapRows]

theorem sourceNonnegativeColumn_eval (N b : ℕ) (r : F.residual.Labels)
    (hN : D.h i (wt D μ Q) = (N : ℤ)) :
    F.residual.preRowsExpansion cs μ (sourceCapRows (Sc := Sc) μ P Q i)
      (F.sourceNonnegativeColumn cs μ N b r) =
    plcW μ (P ++ up i :: dn i :: Q) (P ++ Q) P Q [up i, dn i] []
      (sgM D Sc i (wt D μ Q) ≫ cpow (uRM D Sc i (wt D μ Q)) b ≫
        epsP cs i (wt D μ Q)) ≫ xev cs μ (P ++ Q) Z (F.residual.layers r) := by
  rw [paired_source_leading_nonneg cs i (wt D μ Q) N b hN, sourceNonnegativeColumn]
  simp only [map_add, map_smul, map_sum, Preadditive.add_comp,
    Linear.smul_comp, Preadditive.sum_comp, F.source_cap_loop]
  rw [F.residual.preRowsExpansion_single]
  simp only [map_one, End.one_def, bubAt_id, Category.id_comp, sourceCapRows]

theorem capResidualColumn_apply_ne (m n : ℕ) (hn : n ≠ m)
    (v : F.residual.Labels →₀ SYM D k) (t : F.residual.Labels) :
    F.capResidualColumn m v (t, n) = 0 :=
  F.residual.residualRow_apply_ne m n hn _ t

theorem sourceNegativeColumn_above (N b m : ℕ) (r t : F.residual.Labels)
    (hb : N ≤ b) (hm : b - N ≤ m) :
    F.sourceNegativeColumn cs μ N b r (t, m) =
      ((zsign k (D.parity i)) ^ (b - N) * (↑(cs.c (wt D μ Q) i)⁻¹ : k)) •
        (Finsupp.single (r, b - N) (1 : SYM D k) (t, m)) := by
  classical
  rw [sourceNegativeColumn, ite_eq_right (by omega)]
  simp only [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.finsetSum_apply]
  suffices H : (∑ s ∈ Finset.range (b - N), (zsign k (D.parity i)) ^ s •
      (F.capResidualColumn s (F.sourceLoopLift cs μ r
        (hLM D Sc i (wt D μ Q) (b - 1 - s) ≫ epsP cs i (wt D μ Q)))) (t, m)) = 0 by
    rw [H, add_zero]
  apply Finset.sum_eq_zero
  intro s hs
  rw [F.capResidualColumn_apply_ne s m (by have := Finset.mem_range.mp hs; omega), smul_zero]

theorem sourceNonnegativeColumn_above (N b m : ℕ) (r t : F.residual.Labels)
    (hm : b + N ≤ m) :
    F.sourceNonnegativeColumn cs μ N b r (t, m) =
      (-((zsign k (D.parity i)) ^ b *
        (-(zsign k (D.parity i * (D.h i (wt D μ Q) : ZMod 2)) *
          (↑(cs.c (wt D μ Q) i)⁻¹ : k))))) •
        (Finsupp.single (r, b + N) (1 : SYM D k) (t, m)) := by
  classical
  rw [sourceNonnegativeColumn]
  simp only [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.finsetSum_apply]
  have hfirst : (∑ j ∈ Finset.range N,
      ((zsign k (D.parity i)) ^ b *
        (-(zsign k (D.parity i * (D.h i (wt D μ Q) : ZMod 2)) *
          (↑(cs.c (wt D μ Q) i)⁻¹ : k)))) •
        (F.capResidualColumn (b + j) (F.sourceLoopLift cs μ r
          (dcM D Sc i (wt D μ Q) j ≫ eLM D Sc i (wt D μ Q) N))) (t, m)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [F.capResidualColumn_apply_ne (b + j) m (by have := Finset.mem_range.mp hj; omega), smul_zero]
  have hsecond : (∑ s ∈ Finset.range b, (zsign k (D.parity i)) ^ s •
      (F.capResidualColumn s (F.sourceLoopLift cs μ r
        (hLM D Sc i (wt D μ Q) (b - 1 - s) ≫ epsP cs i (wt D μ Q)))) (t, m)) = 0 := by
    apply Finset.sum_eq_zero
    intro s hs
    rw [F.capResidualColumn_apply_ne s m (by have := Finset.mem_range.mp hs; omega), smul_zero]
  rw [hfirst, hsecond, add_zero, add_zero]

end SameColourSourceFrame
end OddMath.SKM
