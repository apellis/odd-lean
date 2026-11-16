import OddMath.SKM.ResidualCoefficientLift
import OddMath.SKM.SameColourCupRows

/-! Finite coefficient lifts for the paired target rows. Residual loops are
expanded at the unchanged external weight, with arbitrary left and right
contexts; no bubble-slide formula or residual independence is used. -/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Presentation
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k}
namespace MatchingBasisChoice
variable {a P Q : List (Letter I)} (B : MatchingBasisChoice a (P ++ Q))
  (cs : CScalars Sc) (μ : X) (i : I)

/-- A finite lift of the residual loop composed after a residual representative. -/
def targetLoopLift (r : B.Labels)
    (z : End ((pres D Sc).obj (ob D (wt D μ Q) []))) : B.Labels →₀ SYM D k :=
  (B.expansion_surjective cs μ
    (xev cs μ a (P ++ Q) (B.layers r) ≫ plcAt μ (P ++ Q) (P ++ Q) P Q z)).choose

theorem targetLoopLift_eval (r : B.Labels)
    (z : End ((pres D Sc).obj (ob D (wt D μ Q) []))) :
    B.expansion cs μ (B.targetLoopLift cs μ r z) =
      xev cs μ a (P ++ Q) (B.layers r) ≫ plcAt μ (P ++ Q) (P ++ Q) P Q z :=
  (B.expansion_surjective cs μ _).choose_spec

/-- Finite unit-input column at positive height. Low dot rows have zero
principal column; they will be detected by the inversion matrix's cap rows. -/
def targetPositiveColumn (N b : ℕ) (r : B.Labels) : (B.Labels × ℕ) →₀ SYM D k :=
  if b < N then 0 else
    (-((zsign k (D.parity i)) ^ (b - N + 1)) * (cs.c (wt D μ Q) i : k)) •
      Finsupp.single (r, b - N) 1 +
    ∑ s ∈ Finset.range (b - N), (-((zsign k (D.parity i)) ^ (s + 1))) •
      B.residualRow s (B.targetLoopLift cs μ r
        (etaP cs i (wt D μ Q) ≫ eLM D Sc i (wt D μ Q) (b - 1 - s)))

/-- Finite unit-input column at nonpositive height. Both inverse-block and
dot-slide corrections keep their strictly smaller isolated cup indices. -/
def targetNonpositiveColumn (N b : ℕ) (r : B.Labels) : (B.Labels × ℕ) →₀ SYM D k :=
  (-((zsign k (D.parity i)) ^ b *
    (zsign k (ipar D i (wt D μ Q)) * (cs.c (wt D μ Q) i : k)))) •
      Finsupp.single (r, N + b) 1 +
  (∑ j ∈ Finset.range N,
    ((zsign k (D.parity i)) ^ b *
      (zsign k (ipar D i (wt D μ Q)) * (cs.c (wt D μ Q) i : k))) •
        B.residualRow (j + b) (B.targetLoopLift cs μ r
          (hLM D Sc i (wt D μ Q) N ≫ dkM D Sc i (wt D μ Q) j))) +
  ∑ s ∈ Finset.range b, (-((zsign k (D.parity i)) ^ (s + 1))) •
    B.residualRow s (B.targetLoopLift cs μ r
      (etaP cs i (wt D μ Q) ≫ eLM D Sc i (wt D μ Q) (b - 1 - s)))

/-- Place the isolated right cup in its contextual target boundary. -/
def targetCupRows (P Q : List (Letter I)) (i : I) (b : ℕ) :
    (pres D Sc).obj (ob D μ (P ++ Q)) ⟶
      (pres D Sc).obj (ob D μ (P ++ dn i :: up i :: Q)) :=
  plcW μ (P ++ Q) (P ++ dn i :: up i :: Q) P Q [] [dn i, up i]
    (hLM D Sc i (wt D μ Q) b)

private theorem residual_loop_cup (r : B.Labels)
    (z : End ((pres D Sc).obj (ob D (wt D μ Q) []))) (b : ℕ) :
    B.postRowsExpansion cs μ (targetCupRows (Sc := Sc) μ P Q i)
      (B.residualRow b (B.targetLoopLift cs μ r z)) =
    xev cs μ a (P ++ Q) (B.layers r) ≫
      plcW μ (P ++ Q) (P ++ dn i :: up i :: Q) P Q [] [dn i, up i]
        (z ≫ hLM D Sc i (wt D μ Q) b) := by
  rw [B.postRowsExpansion_residualRow, B.targetLoopLift_eval]
  dsimp only [targetCupRows, plcAt]
  have C : cl D Sc μ (P ++ [] ++ Q) (P ++ Q) [] ≫
      cl D Sc μ (P ++ Q) (P ++ [] ++ Q) [] = 𝟙 _ := by
    rw [cl_comp (show SChain (P ++ [] ++ Q) [] (P ++ Q) from by
      change P ++ [] ++ Q = P ++ Q; simp)
      (show SChain (P ++ Q) [] (P ++ [] ++ Q) from by
        change P ++ Q = P ++ [] ++ Q; simp), List.nil_append, cl_nil]
  simp only [plcW_apply, plcL_comp, Category.assoc]
  rw [← Category.assoc (cl D Sc μ (P ++ [] ++ Q) (P ++ Q) []), C, Category.id_comp]

/-- Evaluation of every positive-height principal coefficient column. -/
theorem targetPositiveColumn_eval (N b : ℕ) (r : B.Labels)
    (hN : D.h i (wt D μ Q) = (N : ℤ)) (hpos : 0 < N) :
    B.postRowsExpansion cs μ (targetCupRows (Sc := Sc) μ P Q i)
      (B.targetPositiveColumn cs μ i N b r) =
    xev cs μ a (P ++ Q) (B.layers r) ≫
      plcW μ (P ++ Q) (P ++ dn i :: up i :: Q) P Q [] [dn i, up i]
        (etaP cs i (wt D μ Q) ≫ cpow (uLM D Sc i (wt D μ Q)) b ≫
          sgM D Sc i (wt D μ Q)) := by
  by_cases hb : b < N
  · rw [targetPositiveColumn, ite_eq_left hb, map_zero,
      paired_target_below cs i (wt D μ Q) b (by omega), map_zero, Limits.comp_zero]
  · have he : N + (b - N) = b := by omega
    have H := paired_target_leading_pos cs i (wt D μ Q) N (b - N) hN hpos
    rw [he] at H
    rw [H, targetPositiveColumn, ite_eq_right hb]
    simp only [map_add, map_smul, map_sum, Preadditive.comp_add,
      Linear.comp_smul, Preadditive.comp_sum, B.residual_loop_cup]
    rw [B.postRowsExpansion_single]
    simp only [map_one, End.one_def, bubAt_id, Category.id_comp, targetCupRows, Category.assoc]

/-- Evaluation of every nonpositive-height principal coefficient column. -/
theorem targetNonpositiveColumn_eval (N b : ℕ) (r : B.Labels)
    (hN : -D.h i (wt D μ Q) = (N : ℤ)) :
    B.postRowsExpansion cs μ (targetCupRows (Sc := Sc) μ P Q i)
      (B.targetNonpositiveColumn cs μ i N b r) =
    xev cs μ a (P ++ Q) (B.layers r) ≫
      plcW μ (P ++ Q) (P ++ dn i :: up i :: Q) P Q [] [dn i, up i]
        (etaP cs i (wt D μ Q) ≫ cpow (uLM D Sc i (wt D μ Q)) b ≫
          sgM D Sc i (wt D μ Q)) := by
  rw [paired_target_leading_nonpos cs i (wt D μ Q) N b hN, targetNonpositiveColumn]
  simp only [map_add, map_smul, map_sum, Preadditive.comp_add,
    Linear.comp_smul, Preadditive.comp_sum, B.residual_loop_cup]
  rw [B.postRowsExpansion_single]
  simp only [map_one, End.one_def, bubAt_id, Category.id_comp, targetCupRows, Category.assoc]

/-- At or above its leading cup index, the positive-height column has only
its displayed diagonal. Residual lifts cannot create a different cup row. -/
theorem targetPositiveColumn_above (N b m : ℕ) (r t : B.Labels)
    (hb : N ≤ b) (hm : b - N ≤ m) :
    B.targetPositiveColumn cs μ i N b r (t, m) =
      (-((zsign k (D.parity i)) ^ (b - N + 1)) * (cs.c (wt D μ Q) i : k)) •
        (Finsupp.single (r, b - N) (1 : SYM D k) (t, m)) := by
  classical
  rw [targetPositiveColumn, ite_eq_right (by omega)]
  simp only [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.finsetSum_apply]
  suffices H : (∑ s ∈ Finset.range (b - N),
      (-((zsign k (D.parity i)) ^ (s + 1))) •
        (B.residualRow s (B.targetLoopLift cs μ r
          (etaP cs i (wt D μ Q) ≫ eLM D Sc i (wt D μ Q) (b - 1 - s)))) (t, m)) = 0 by
    rw [H, add_zero]
  apply Finset.sum_eq_zero
  intro s hs
  rw [B.residualRow_apply_ne s m (by have := Finset.mem_range.mp hs; omega), smul_zero]

/-- At or above the shifted pivot the nonpositive-height column has only
its diagonal; both finite correction sums are strictly lower. -/
theorem targetNonpositiveColumn_above (N b m : ℕ) (r t : B.Labels)
    (hm : N + b ≤ m) :
    B.targetNonpositiveColumn cs μ i N b r (t, m) =
      (-((zsign k (D.parity i)) ^ b *
        (zsign k (ipar D i (wt D μ Q)) * (cs.c (wt D μ Q) i : k)))) •
          (Finsupp.single (r, N + b) (1 : SYM D k) (t, m)) := by
  classical
  rw [targetNonpositiveColumn]
  simp only [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.finsetSum_apply]
  have hfirst : (∑ j ∈ Finset.range N,
      ((zsign k (D.parity i)) ^ b *
        (zsign k (ipar D i (wt D μ Q)) * (cs.c (wt D μ Q) i : k))) •
          (B.residualRow (j + b) (B.targetLoopLift cs μ r
            (hLM D Sc i (wt D μ Q) N ≫ dkM D Sc i (wt D μ Q) j))) (t, m)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [B.residualRow_apply_ne (j + b) m (by have := Finset.mem_range.mp hj; omega), smul_zero]
  have hsecond : (∑ s ∈ Finset.range b, (-((zsign k (D.parity i)) ^ (s + 1))) •
      (B.residualRow s (B.targetLoopLift cs μ r
        (etaP cs i (wt D μ Q) ≫ eLM D Sc i (wt D μ Q) (b - 1 - s)))) (t, m)) = 0 := by
    apply Finset.sum_eq_zero
    intro s hs
    rw [B.residualRow_apply_ne s m (by have := Finset.mem_range.mp hs; omega), smul_zero]
  rw [hfirst, hsecond, add_zero, add_zero]

end MatchingBasisChoice
end OddMath.SKM
