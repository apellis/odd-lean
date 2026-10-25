import OddMath.SKM.ContextualCrossFamily

/-! Transport existing distinguished points and literal serializers through
one terminal crossing, placing every dot before that crossing. -/
noncomputable section
namespace OddMath.SKM
open StringDiagrams StringDiagrams.Chord DTMove
variable {I : Type*}

@[simp] theorem tRen_append_cross (k : ℕ) (p : ℕ) (T : TState (Letter I))
    (R : List (TMove (Letter I))) (x : ℕ) :
    tRen k T (R ++ [.mv (.cross p)]) x = tRen k T R x := by
  induction R generalizing T x with
  | nil => rfl
  | cons m R ih => exact ih _ _

@[simp] theorem dotPts_append_tm (ds : List (DTMove I)) (m : TMove (Letter I)) :
    dotPts (ds ++ [.tm m]) = dotPts ds := by
  induction ds with
  | nil => rfl
  | cons d ds ih => cases d <;> simp only [List.cons_append, dotPts, ih]

/-- A bounded point on the old matching stays on the transposed strand. -/
theorem onStrand_append_cross {a P Q : List (Letter I)} {x y : Letter I}
    {R : List (TMove (Letter I))} (hR : IsMatching₂ a (P ++ x :: y :: Q) R)
    {j : ℕ} {q : ℕ × ℕ} (hq : q.1 ≤ R.length) (hj : OnStrand₂ a R j q) :
    OnStrand₂ a (R ++ [TMove.mv (.cross P.length)]) (tau (a.length + P.length) j) q := by
  have ht : (R ++ [TMove.mv (.cross P.length)]).take q.1 = R.take q.1 :=
    List.take_append_of_le_length hq
  have hd : (R ++ [TMove.mv (.cross P.length)]).drop q.1 =
      R.drop q.1 ++ [.mv (.cross P.length)] := List.drop_append_of_le_length hq
  constructor
  · simpa only [ht] using hj.1
  · rw [ht, hd, tRen_append_cross, pairing_append_cross]
    simpa only [idD, idAt_swapAt (target_pair_bound hR), tau_tau] using hj.2

/-- Literal serializer layers append the actual contextual mixed crossing. -/
theorem dLay_append_terminal_cross {a P Q : List (Letter I)} {x y : Letter I}
    {R : List (TMove (Letter I))} (hR : IsMatching₂ a (P ++ x :: y :: Q) R)
    {ds : List (DTMove I)} (hd : tmoves ds = R) :
    dLay a (ds ++ [.tm (.mv (.cross P.length))]) =
      dLay a ds ++ (xCrL x y).map (xwhL P Q) := by
  rw [dLay_append, hd, hR.2]
  simp only [dLay, tmLay, moveLay_cross, List.append_nil]

theorem leftEnds_append_cross_perm {a P Q : List (Letter I)} {x y : Letter I}
    {R : List (TMove (Letter I))} (hR : IsMatching₂ a (P ++ x :: y :: Q) R)
    (hn : ¬ Same (pairing₂ a R) (a.length + P.length) (a.length + P.length + 1)) :
    (leftEnds₂ a (R ++ [.mv (.cross P.length)])).Perm
      ((leftEnds₂ a R).map (tau (a.length + P.length))) := by
  apply (List.perm_ext_iff_of_nodup (nodup_leftEnds₂ _ _)
    ((nodup_leftEnds₂ a R).map (fun _ _ h => tau_inj.mp h))).mpr
  intro j
  constructor
  · intro hj
    let z := (terminalCrossStrandEquiv hR hn).symm ⟨j, hj⟩
    refine List.mem_map.mpr ⟨z.val, z.property, ?_⟩
    exact congrArg Subtype.val ((terminalCrossStrandEquiv hR hn).apply_symm_apply ⟨j, hj⟩)
  · intro hj
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
    exact (terminalCrossStrandEquiv hR hn ⟨i, hi⟩).property

/-- Existing decoration points and counts are reindexed by the actual endpoint
transposition. Appending the crossing leaves the literal dot list unchanged. -/
theorem decorates_append_cross {a P Q : List (Letter I)} {x y : Letter I}
    {R : List (TMove (Letter I))} (hR : IsMatching₂ a (P ++ x :: y :: Q) R)
    (hn : ¬ Same (pairing₂ a R) (a.length + P.length) (a.length + P.length + 1))
    {q : ℕ → ℕ × ℕ} {n : ℕ → ℕ} {ds : List (DTMove I)} (hd : Decorates₂ a R q n ds) :
    Decorates₂ a (R ++ [.mv (.cross P.length)])
      (fun j => q (tau (a.length + P.length) j))
      (fun j => n (tau (a.length + P.length) j)) (ds ++ [.tm (.mv (.cross P.length))]) := by
  constructor
  · rw [tmoves_append, hd.1]; rfl
  · rw [dotPts_append_tm]
    apply hd.2.trans
    have hp := (leftEnds_append_cross_perm hR hn).flatMap_right
      (fun j => List.replicate (n (tau (a.length + P.length) j))
        (q (tau (a.length + P.length) j)))
    simpa only [List.flatMap_map, Function.comp_def, tau_tau] using hp.symm

end OddMath.SKM
