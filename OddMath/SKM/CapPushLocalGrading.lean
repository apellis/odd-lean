import OddMath.SKM.TableIsotopy
import OddMath.SKM.SpanCapTrack

/-!
Numerical cap-block and zigzag calculations supporting the choice-independence
step of Brundan–Ellis, arXiv:1701.04133v2, Theorem 10.3. These concern the existing
generator-table sum and parity, not equality inferred from a lower-term relation.
-/

namespace OddMath.SKM
open StringDiagrams StringDiagrams.Chord
variable {I X : Type*} [AddCommGroup X] (D : Datum I X) (sy : Symmetrizer D)

@[simp] theorem tableDegree_cap (μ : X) (a : Letter I) :
    tableDegree D sy μ (xCapL a) =
      sy.d a.2 * (1 + if a.1 then D.h a.2 μ else -D.h a.2 μ) := by
  obtain ⟨_ | _, i⟩ := a <;> simp [xCapL, tableDegree, gdeg, sub_eq_add_neg]

@[simp] theorem xpar_cap (μ : X) (a : Letter I) :
    xpar D μ (xCapL a) = cupPar D μ a := by
  obtain ⟨_ | _, i⟩ := a <;> simp [xCapL, xpar, xlpar, cupPar, Shape.parity]

@[simp] theorem tableDegree_capBlk_zero (μ : X) (S : List (Letter I)) (a : Letter I) :
    tableDegree D sy μ (capBlk S a 0) = tableDegree D sy μ (lmLc S a) +
      tableDegree D sy (wt D μ S) (xCapL a) := by
  simp [capBlk, xDotsL, tableDegree_append]

@[simp] theorem xpar_capBlk_zero (μ : X) (S : List (Letter I)) (a : Letter I) :
    xpar D μ (capBlk S a 0) = xpar D μ (lmLc S a) + cupPar D μ a := by
  simp [capBlk, xDotsL, xpar_append]

/-- Both source U-turns cancel numerically, including both orientations. -/
theorem tableDegree_xpar_zigL (μ : X) (a : Letter I) :
    tableDegree D sy μ ((xCupL a).map (xwhL [] [a]) ++
      (xCapL a).map (xwhL [a] [])) = 0 ∧
    xpar D μ ((xCupL a).map (xwhL [] [a]) ++
      (xCapL a).map (xwhL [a] [])) = 0 := by
  constructor
  · simp only [tableDegree_append, tableDegree_whisk, tableDegree_cup, tableDegree_cap]
    obtain ⟨_ | _, i⟩ := a <;> simp [wt, sh, Datum.α, D.cd.coroot_root_self] <;> ring
  · simp only [xpar_append, xpar_map_xwhL, xpar_cup, xpar_cap]
    exact CharTwo.add_self_eq_zero _

theorem tableDegree_xpar_zigR (μ : X) (a : Letter I) :
    tableDegree D sy μ ((xCupL a).map (xwhL [flipL a] []) ++
      (xCapL a).map (xwhL [] [flipL a])) = 0 ∧
    xpar D μ ((xCupL a).map (xwhL [flipL a] []) ++
      (xCapL a).map (xwhL [] [flipL a])) = 0 := by
  constructor
  · simp only [tableDegree_append, tableDegree_whisk, tableDegree_cup, tableDegree_cap]
    obtain ⟨_ | _, i⟩ := a <;> simp [wt, sh, flipL, Datum.α, D.cd.coroot_root_self] <;> ring
  · simp only [xpar_append, xpar_map_xwhL, xpar_cup, xpar_cap]
    exact CharTwo.add_self_eq_zero _

/-- Moving a final letter to the front does not change the region weight. -/
theorem wt_append_singleton_table (μ : X) (S : List (Letter I)) (a : Letter I) :
    wt D μ (S ++ [a]) = wt D μ (a :: S) := by
  induction S with
  | nil => rfl
  | cons s S ih => simp [wt, ih, add_left_comm]

/-- The left zigzag branch of cap-push for an arbitrary intervening block. -/
theorem tableDegree_xpar_capBlk_cupAleft0 (μ : X) (S : List (Letter I)) (a : Letter I) :
    tableDegree D sy μ ((xCupL a).map (xwhL [] (S ++ [a])) ++
      (capBlk S a 0).map (xwhL [a] [])) = tableDegree D sy μ (lmLc S a) ∧
    xpar D μ ((xCupL a).map (xwhL [] (S ++ [a])) ++
      (capBlk S a 0).map (xwhL [a] [])) = xpar D μ (lmLc S a) := by
  constructor
  · simp only [tableDegree_append, tableDegree_whisk, tableDegree_capBlk_zero,
      tableDegree_cup, tableDegree_cap, wt_append_singleton_table]
    obtain ⟨_ | _, i⟩ := a <;> simp [wt, sh, Datum.α, D.cd.coroot_root_self] <;> ring
  · simp only [xpar_append, xpar_map_xwhL, xpar_cup, xpar_capBlk_zero]
    have h := CharTwo.add_self_eq_zero (cupPar D μ a)
    linear_combination h

@[simp] theorem tableDegree_lmLc (μ : X) (S : List (Letter I)) (a : Letter I) :
    tableDegree D sy μ (lmLc S a) =
      (S.map fun s => if s.1 = a.1 then sy.d s.2 * D.d s.2 a.2 else 0).sum := by
  induction S with
  | nil => simp [lmLc, tableDegree]
  | cons s S ih => simp [lmLc, ih, add_comm]

@[simp] theorem tableDegree_lmRc (μ : X) (S : List (Letter I)) (a : Letter I) :
    tableDegree D sy μ (lmRc a S) =
      (S.map fun s => if a.1 = s.1 then sy.d a.2 * D.d a.2 s.2 else 0).sum := by
  induction S with
  | nil => simp [lmRc, tableDegree]
  | cons s S ih => simp [lmRc, ih]

@[simp] theorem xpar_lmLc (μ : X) (S : List (Letter I)) (a : Letter I) :
    xpar D μ (lmLc S a) = (S.map fun s => D.parity s.2 * D.parity a.2).sum := by
  induction S with
  | nil => simp [lmLc]
  | cons s S ih => simp [lmLc, xpar_append, ih, add_comm]

@[simp] theorem xpar_lmRc (μ : X) (S : List (Letter I)) (a : Letter I) :
    xpar D μ (lmRc a S) = (S.map fun s => D.parity a.2 * D.parity s.2).sum := by
  induction S with
  | nil => simp [lmRc]
  | cons s S ih => simp [lmRc, xpar_append, ih]

/-- Numerical cap pitchfork: no scalar relation or nonzero quotient hypothesis. -/
theorem tableDegree_xpar_capPF (μ : X) (a e : Letter I) :
    tableDegree D sy μ ((xCrL (flipL a) e).map (xwhL [] [a]) ++
      (xCapL a).map (xwhL [e] [])) =
      tableDegree D sy μ ((xCrL e a).map (xwhL [flipL a] []) ++
        (xCapL a).map (xwhL [] [e])) ∧
    xpar D μ ((xCrL (flipL a) e).map (xwhL [] [a]) ++
      (xCapL a).map (xwhL [e] [])) =
      xpar D μ ((xCrL e a).map (xwhL [flipL a] []) ++
        (xCapL a).map (xwhL [] [e])) := by
  constructor
  · simp only [tableDegree_append, tableDegree_whisk, tableDegree_cross, tableDegree_cap]
    obtain ⟨_ | _, i⟩ := a <;> obtain ⟨_ | _, j⟩ := e <;>
      (have hs := sy.symm i j; simp only [Datum.d] at hs
       simp [flipL, wt, Datum.d]; nlinarith [hs])
  · simp [xpar_append, flipL, mul_comm]

/-- The right zigzag branch, with arbitrarily many intervening strands. -/
theorem tableDegree_xpar_capBlk_cupBright0 (μ : X) (S : List (Letter I)) (a : Letter I) :
    tableDegree D sy μ ((xCupL a).map (xwhL ([flipL a] ++ S) []) ++
      (capBlk S a 0).map (xwhL [] [flipL a])) = tableDegree D sy μ (lmRc (flipL a) S) ∧
    xpar D μ ((xCupL a).map (xwhL ([flipL a] ++ S) []) ++
      (capBlk S a 0).map (xwhL [] [flipL a])) = xpar D μ (lmRc (flipL a) S) := by
  constructor
  · simp only [tableDegree_append, tableDegree_whisk, tableDegree_capBlk_zero,
      tableDegree_cup, tableDegree_cap, tableDegree_lmLc, tableDegree_lmRc]
    induction S with
    | nil =>
      obtain ⟨_ | _, i⟩ := a <;>
        simp [wt, flipL, sh, Datum.α, D.cd.coroot_root_self] <;> ring
    | cons s S ih =>
      rw [← wt_append, wt_append_singleton_table] at ih ⊢
      obtain ⟨_ | _, i⟩ := a <;> obtain ⟨_ | _, j⟩ := s <;>
        (have hs := sy.symm i j; simp only [Datum.d] at hs
         simp [wt, flipL, Datum.d] at ih ⊢; nlinarith [hs])
  · simp only [xpar_append, xpar_map_xwhL, xpar_cup, xpar_capBlk_zero,
      xpar_lmLc, xpar_lmRc]
    simp only [flipL, mul_comm]
    have h := CharTwo.add_self_eq_zero (cupPar D μ a)
    linear_combination h

/-- Numerical equalities extend through a common layered context. -/
theorem tableDegree_xpar_context (μ : X) (pre post L R : List (XLayer I))
    (u v : List (Letter I))
    (hd : tableDegree D sy (wt D μ v) L = tableDegree D sy (wt D μ v) R)
    (hp : xpar D (wt D μ v) L = xpar D (wt D μ v) R) :
    tableDegree D sy μ (pre ++ L.map (xwhL u v) ++ post) =
      tableDegree D sy μ (pre ++ R.map (xwhL u v) ++ post) ∧
    xpar D μ (pre ++ L.map (xwhL u v) ++ post) =
      xpar D μ (pre ++ R.map (xwhL u v) ++ post) := by
  rw [xpar_wt, xpar_wt] at hp
  exact ⟨by simp only [tableDegree_append, tableDegree_whisk, hd],
    by simp only [xpar_append, xpar_map_xwhL, hp]⟩

/-- A strand entering from the left: the numeric counterpart of `capBlk_enterL0`. -/
theorem tableDegree_xpar_capBlk_enterL0 (μ : X) (S : List (Letter I)) (e a : Letter I) :
    tableDegree D sy μ ((xCrL (flipL a) e).map (xwhL [] (S ++ [a])) ++
      (capBlk S a 0).map (xwhL [e] [])) = tableDegree D sy μ (capBlk (e :: S) a 0) ∧
    xpar D μ ((xCrL (flipL a) e).map (xwhL [] (S ++ [a])) ++
      (capBlk S a 0).map (xwhL [e] [])) = xpar D μ (capBlk (e :: S) a 0) := by
  obtain ⟨hd, hp⟩ := tableDegree_xpar_capPF D sy (wt D μ S) a e
  constructor
  · simp only [tableDegree_append, tableDegree_whisk, tableDegree_cross,
      tableDegree_cap, wt_nil] at hd
    simp only [tableDegree_append, tableDegree_whisk, tableDegree_cross,
      tableDegree_capBlk_zero, tableDegree_cap, tableDegree_lmLc, wt_nil,
      List.map_cons, List.sum_cons, wt_cons]
    simp only [wt_cons, wt_nil] at hd
    linear_combination hd
  · simp [xpar_append, flipL, mul_comm, add_comm, add_left_comm]

/-- The internal braid step of the cap block is numerical, without `R3Rel`. -/
theorem tableDegree_xpar_capBlk_crossS (μ : X) (S₁ S₂ : List (Letter I))
    (a b l : Letter I) :
    tableDegree D sy μ ((xCrL a b).map (xwhL ([flipL l] ++ S₁) (S₂ ++ [l])) ++
      capBlk (S₁ ++ [b, a] ++ S₂) l 0) =
      tableDegree D sy μ (capBlk (S₁ ++ [a, b] ++ S₂) l 0 ++
        (xCrL a b).map (xwhL S₁ S₂)) ∧
    xpar D μ ((xCrL a b).map (xwhL ([flipL l] ++ S₁) (S₂ ++ [l])) ++
      capBlk (S₁ ++ [b, a] ++ S₂) l 0) =
      xpar D μ (capBlk (S₁ ++ [a, b] ++ S₂) l 0 ++
        (xCrL a b).map (xwhL S₁ S₂)) := by
  constructor
  · simp only [tableDegree_append, tableDegree_whisk, tableDegree_cross,
      tableDegree_capBlk_zero, tableDegree_lmLc, List.map_append, List.map_cons,
      List.map_nil, List.sum_append, List.sum_cons, List.sum_nil,
      wt_append, List.cons_append, List.nil_append]
    rw [wt_pair_swap_table D (wt D μ S₂) b a]
    ring
  · simp [xpar_append, add_comm, add_left_comm]

end OddMath.SKM
