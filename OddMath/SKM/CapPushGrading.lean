import OddMath.SKM.CapPushCrossingGrading

/-!
# Numerical cap-push through cups and the reverse-list induction

Supporting Brundan–Ellis, arXiv:1701.04133v2, Theorem 10.3, choice independence.
The original cup/crossing construction retains fit, pairing and crossing bounds.
Zigzags preserve the numerical tables; curls and double crossings strictly lower
the bound and hence cannot occur under the equality premise. A cup joining its
own two ends is excluded by the unequal-ID premise.

This proves the one-cap existential, not two-sided normalization or Claim 2.
-/

namespace OddMath.SKM
open StringDiagrams
open StringDiagrams.Chord (Move Fits run Iso rl rlId mvL mvR rl_of_ne rl_of_eq)
variable {I X : Type*} [AddCommGroup X] {D : Datum I X} {sy : Symmetrizer D} {μ : X}

theorem wt_cap_remove (μ : X) (S Q : List (Letter I)) (a : Letter I) :
    wt D μ (flipL a :: (S ++ a :: Q)) = wt D μ (S ++ Q) := by
  induction S with
  | nil => simpa using wt_pair_cancel_table D μ (flipL a) Q
  | cons s S ih =>
    simp only [List.cons_append]
    rw [wt_pair_swap_table D μ (flipL a) s, wt_cons, ih, wt_cons]

theorem numericCapPush_cup {E : List (Move (Letter I))} (ih : NumericCapPush D sy μ E) (hfE : Fits 0 E) {g : ℕ}
    (hg : g ≤ (run flipL E).length) (a : Letter I) : NumericCapPush D sy μ (E ++ [.cup g a]) := by
  intro P S Q A B ht hl hne
  obtain ⟨u, w, ht₀, hu⟩ := exists_split_cup hg
  set n := (run flipL E).length with hn
  have hfr : ∀ x ∈ run flipL E, x.1 < n := (Chord.inv_run (d := flipL) hfE).2
  have hncr : ncr (E ++ [.cup g a]) = ncr E := by rw [ncr_append]; rfl
  have hlay : chordLay [] (E ++ [.cup g a]) =
      chordLay [] E ++ (xCupL a).map (xwhL (u.map Prod.snd) (w.map Prod.snd)) := by
    rw [chordLay_snoc, ht₀]
    exact congrArg _ (moveLay_cup_eq a (by simp) (by simp [hu]))
  rw [run_snoc] at ht
  change Chord.insAt (run flipL E) g (n, a) (n, flipL a) = _ at ht
  rw [ht₀, ← hu] at ht
  simp only [Chord.insAt, List.take_left', List.drop_left'] at ht
  have hcE : ∀ F, chordLay [] (E ++ F) = chordLay [] E ++ chordLay ((run flipL E).map Prod.snd) F :=
    fun F => by rw [chordLay_append, foldl_chStep_eq]
  unfold NumericCapPushRes
  rw [hncr, hlay]
  rcases posPair (show u ++ [(n, a), (n, flipL a)] ++ w = P ++ [A] ++ S ++ [B] ++ Q by
      simpa using ht) with
    ⟨R, hP, hw⟩ | ⟨hP, h1, hv⟩ | ⟨hu', h2, S', hS, hv⟩ | ⟨hu', h2, hS, h1, hv⟩ |
    ⟨S₁, S₂, hS, hu', hv⟩ | ⟨S', hS, h1, hu', hv⟩ | ⟨hu', h2, hQ⟩ | ⟨R, hQ, hu'⟩
  · -- a cup to the left of the block
    subst hP hw
    have hAB : A.1 < n ∧ B.1 < n := ⟨hfr A (by rw [ht₀]; simp), hfr B (by rw [ht₀]; simp)⟩
    obtain ⟨E', hf', hiso, hle, hxl⟩ := ih (u ++ R) S Q A B (by rw [ht₀]; simp) hl hne
    refine ⟨E' ++ [.cup u.length a], fits_snoc'.2 ⟨hf', by
        rw [hiso.length_eq]; show _ ≤ _; simp only [List.length_map, List.length_append]; omega⟩,
      iso_snoc_cup hf' hiso (f := rl B.1 A.1) (u := u) (w := R ++ S ++ Q) (by lsimp) (by lsimp)
        rfl (rl_of_ne (by simp; omega)) (rl_of_ne (by simp; omega))
        (fresh_map_rl (fun x hx => hfr x (by rw [ht₀]; simp at hx ⊢; tauto)) hAB.1),
      by nomega, fun h => ?_⟩
    have I := hxl (by nomega)
    have H := numeric_snoc hiso (l := ((u ++ R ++ S ++ Q).map Prod.snd)) (by simp) I
      (m := .cup u.length a)
      (moveLay_cup_eq (u := u.map Prod.snd) (w := (R ++ S ++ Q).map Prod.snd) a (by simp) (by simp))
    have hwgt : wt D μ ((R ++ [A] ++ S ++ [B] ++ Q).map Prod.snd) =
        wt D μ ((R ++ S ++ Q).map Prod.snd) := by
      simp only [List.map_append, List.map_cons, List.append_assoc,
        List.cons_append, List.nil_append, hl]
      rw [wt_append, wt_append, wt_cap_remove]
    obtain ⟨Hd, Hp⟩ := H
    constructor
    · simp only [tableDegree_append, tableDegree_whisk] at Hd ⊢
      rw [hwgt]
      linear_combination Hd
    · simpa only [xpar_append, xpar_map_xwhL,
        add_assoc, add_comm, add_left_comm] using Hp
  · -- the cup creates `A` and the strand to its left: a zigzag
    subst hP hv
    obtain rfl : (n, flipL a) = A := h1
    have ha : a = B.2 := flipL_inj hl
    subst ha
    have hrun : run flipL (E ++ mvL u.length S.length) = u ++ [B] ++ S ++ Q := by
      rw [run_append_foldl, ht₀,
        show u ++ (S ++ [B] ++ Q) = u ++ S ++ [B] ++ Q by simp,
        Chord.foldl_mvL (Chord.step flipL) (fun _ _ => rfl)]
    have hfB : ∀ x ∈ u ++ [B] ++ S ++ Q, x.1 < n := fun x hx => hfr x (by
      rw [ht₀]; simp at hx ⊢; tauto)
    refine ⟨E ++ mvL u.length S.length, fits_append_run hfE (Chord.fits_mvL _ _ (by
        rw [ht₀]; simp)), ?_, by rw [ncr_append, Chord.ncr_mvL], fun _ => ?_⟩
    · rw [hrun]
      have e : (u ++ [(n, B.2)] ++ S ++ Q).map (rl B.1 n) = (u ++ [B] ++ S ++ Q).map (rl B.1 n) := by
        simp [rl_of_ne (show (n, B.2).1 ≠ B.1 by simp; have := hfB B (by simp); omega),
          rl_of_eq (show B.1 = B.1 from rfl)]
      rw [show (n, B.2).1 = n from rfl, e]
      exact (Chord.iso_map_rl_of_fresh fun x hx => (hfB x hx).ne).symm
    · have hR : chordLay [] (E ++ mvL u.length S.length) = chordLay [] E ++
          (lmLc (S.map Prod.snd) B.2).map (xwhL (u.map Prod.snd) (Q.map Prod.snd)) := by
        rw [hcE, ht₀, show u ++ (S ++ [B] ++ Q) = u ++ S ++ [B] ++ Q by simp,
          show u.length = (u.map Prod.snd).length by simp,
          show S.length = (S.map Prod.snd).length by simp]
        simp only [List.map_append, List.map_cons, List.map_nil]
        rw [chordLay_mvL]
      rw [hR]
      have H := tableDegree_xpar_capBlk_cupAleft0 D sy (wt D μ (Q.map Prod.snd))
        (S.map Prod.snd) B.2
      have H' := tableDegree_xpar_context D sy μ (chordLay [] E) [] _ _
        (u.map Prod.snd) (Q.map Prod.snd) H.1 H.2
      simpa using H'
  · -- the cup creates `A` and the first strand of the block: a curl, lower
    subst hu' hS hv
    obtain rfl : (n, a) = A := h2
    have ha : flipL a = B.2 := by rw [← flipL_flipL B.2, ← hl]
    have hrun : run flipL (E ++ mvL u.length S'.length) = u ++ [B] ++ S' ++ Q := by
      rw [run_append_foldl, ht₀,
        show u ++ (S' ++ [B] ++ Q) = u ++ S' ++ [B] ++ Q by simp,
        Chord.foldl_mvL (Chord.step flipL) (fun _ _ => rfl)]
    have hfB : ∀ x ∈ u ++ [B] ++ S' ++ Q, x.1 < n := fun x hx => hfr x (by
      rw [ht₀]; simp at hx ⊢; tauto)
    refine ⟨E ++ mvL u.length S'.length, fits_append_run hfE (Chord.fits_mvL _ _ (by
        rw [ht₀]; simp)), ?_, by rw [ncr_append, Chord.ncr_mvL]; simp,
        fun h => absurd h (by rw [ncr_append, Chord.ncr_mvL]; simp)⟩
    rw [hrun]
    have e : (u ++ (n, flipL a) :: S' ++ Q).map (rl B.1 n) =
        (u ++ [B] ++ S' ++ Q).map (rl B.1 n) := by
      have hB' : rl B.1 n (n, B.2) = (n, B.2) :=
        rl_of_ne (show (n, B.2).1 ≠ B.1 by simp; have := hfB B (by simp); omega)
      simp [rl_of_eq (show B.1 = B.1 from rfl), ha, hB']
    rw [show (n, a).1 = n from rfl, e]
    exact (Chord.iso_map_rl_of_fresh fun x hx => (hfB x hx).ne).symm
  · -- the cup creates `A` and `B`: excluded
    exact absurd (by rw [← h2, ← h1]) hne
  · -- a cup inside the block: a double crossing, lower
    subst hS hu' hv
    have hAB : A.1 < n ∧ B.1 < n := ⟨hfr A (by rw [ht₀]; simp), hfr B (by rw [ht₀]; simp)⟩
    obtain ⟨E', hf', hiso, hle, -⟩ := ih P (S₁ ++ S₂) Q A B (by rw [ht₀]; simp) hl hne
    refine ⟨E' ++ [.cup (P.length + S₁.length) a], fits_snoc'.2 ⟨hf', by
        rw [hiso.length_eq]; show _ ≤ _; simp only [List.length_map, List.length_append]; omega⟩,
      iso_snoc_cup hf' hiso (f := rl B.1 A.1) (u := P ++ S₁) (w := S₂ ++ Q) (by lsimp) (by lsimp)
        (by simp) (rl_of_ne (by simp; omega)) (rl_of_ne (by simp; omega))
        (fresh_map_rl (fun x hx => hfr x (by rw [ht₀]; simp at hx ⊢; tauto)) hAB.1),
      by nomega, fun h => absurd h (by nomega)⟩
  · -- the cup creates `B` and the last strand of the block: a curl, lower
    subst hS hu' hv
    obtain rfl : (n, flipL a) = B := h1
    have ha : A.2 = a := by rw [hl, flipL_flipL]
    have hrun : run flipL (E ++ mvR P.length S'.length) = P ++ S' ++ [A] ++ w := by
      rw [run_append_foldl, ht₀,
        show P ++ [A] ++ S' ++ w = P ++ [A] ++ S' ++ w from rfl]
      have := Chord.foldl_mvR (Chord.step flipL) (fun _ _ => rfl) P S' w A
      simpa using this
    have hfA : ∀ x ∈ P ++ S' ++ w, x.1 ≠ n := fun x hx => (hfr x (by
      rw [ht₀]; simp at hx ⊢; tauto)).ne
    refine ⟨E ++ mvR P.length S'.length, fits_append_run hfE (Chord.fits_mvR _ _ (by
        rw [ht₀]; simp)), ?_, by rw [ncr_append, Chord.ncr_mvR]; simp,
        fun h => absurd h (by rw [ncr_append, Chord.ncr_mvR]; simp)⟩
    rw [hrun]
    have e : (P ++ (S' ++ [(n, a)]) ++ w).map (rl n A.1) = P ++ S' ++ [A] ++ w := by
      have h1 : P.map (rl n A.1) = P := Chord.map_rl_of_forall_ne fun x hx => hfA x (by simp [hx])
      have h2 : S'.map (rl n A.1) = S' :=
        Chord.map_rl_of_forall_ne fun x hx => hfA x (by simp [hx])
      have h3 : w.map (rl n A.1) = w := Chord.map_rl_of_forall_ne fun x hx => hfA x (by simp [hx])
      simp only [List.map_append, List.map_cons, List.map_nil, h1, h2, h3,
        rl_of_eq (show (n, a).1 = n from rfl)]
      rw [show (A.1, (n, a).2) = A by rw [← ha]]
      simp
    rw [show (n, flipL a).1 = n from rfl, e]
    exact Chord.Iso.refl _
  · -- the cup creates `B` and the strand to its right: a zigzag
    subst hu' hQ
    obtain rfl : (n, a) = B := h2
    have ha : A.2 = flipL a := hl
    have hrun : run flipL (E ++ mvR P.length S.length) = P ++ S ++ [A] ++ w := by
      rw [run_append_foldl, ht₀]
      have := Chord.foldl_mvR (Chord.step flipL) (fun _ _ => rfl) P S w A
      simpa using this
    have hfA : ∀ x ∈ P ++ S ++ w, x.1 ≠ n := fun x hx => (hfr x (by
      rw [ht₀]; simp at hx ⊢; tauto)).ne
    refine ⟨E ++ mvR P.length S.length, fits_append_run hfE (Chord.fits_mvR _ _ (by
        rw [ht₀]; simp)), ?_, by rw [ncr_append, Chord.ncr_mvR], fun _ => ?_⟩
    · rw [hrun]
      have e : (P ++ S ++ (n, flipL a) :: w).map (rl n A.1) = P ++ S ++ [A] ++ w := by
        have h1 : P.map (rl n A.1) = P :=
          Chord.map_rl_of_forall_ne fun x hx => hfA x (by simp [hx])
        have h2 : S.map (rl n A.1) = S :=
          Chord.map_rl_of_forall_ne fun x hx => hfA x (by simp [hx])
        have h3 : w.map (rl n A.1) = w :=
          Chord.map_rl_of_forall_ne fun x hx => hfA x (by simp [hx])
        simp only [List.map_append, List.map_cons, h1, h2, h3,
          rl_of_eq (show (n, flipL a).1 = n from rfl)]
        rw [show (A.1, (n, flipL a).2) = A by rw [← ha]]
        simp
      rw [show (n, a).1 = n from rfl, e]
      exact Chord.Iso.refl _
    · have hR : chordLay [] (E ++ mvR P.length S.length) = chordLay [] E ++
          (lmRc (flipL a) (S.map Prod.snd)).map (xwhL (P.map Prod.snd) (w.map Prod.snd)) := by
        rw [hcE, ht₀, show P.length = (P.map Prod.snd).length by simp,
          show S.length = (S.map Prod.snd).length by simp]
        simp only [List.map_append, List.map_cons, List.map_nil, ha]
        rw [← chordLay_mvR]
      rw [hR]
      have H := tableDegree_xpar_capBlk_cupBright0 D sy (wt D μ (w.map Prod.snd))
        (S.map Prod.snd) a
      have H' := tableDegree_xpar_context D sy μ (chordLay [] E) [] _ _
        (P.map Prod.snd) (w.map Prod.snd) H.1 H.2
      simpa [ha] using H'
  · -- a cup to the right of the block
    subst hQ hu'
    have hAB : A.1 < n ∧ B.1 < n := ⟨hfr A (by rw [ht₀]; simp), hfr B (by rw [ht₀]; simp)⟩
    obtain ⟨E', hf', hiso, hle, hxl⟩ := ih P S (R ++ w) A B (by rw [ht₀]; simp) hl hne
    refine ⟨E' ++ [.cup (P.length + S.length + R.length) a], fits_snoc'.2 ⟨hf', by
        rw [hiso.length_eq]; show _ ≤ _; simp only [List.length_map, List.length_append]; omega⟩,
      iso_snoc_cup hf' hiso (f := rl B.1 A.1) (u := P ++ S ++ R) (w := w) (by lsimp) (by lsimp)
        (by simp; omega) (rl_of_ne (by simp; omega)) (rl_of_ne (by simp; omega))
        (fresh_map_rl (fun x hx => hfr x (by rw [ht₀]; simp at hx ⊢; tauto)) hAB.1),
      by nomega, fun h => ?_⟩
    have I := hxl (by nomega)
    have H := numeric_snoc hiso (l := ((P ++ S ++ R ++ w).map Prod.snd)) (by simp) I
      (m := .cup (P.length + S.length + R.length) a)
      (moveLay_cup_eq (u := (P ++ S ++ R).map Prod.snd) (w := w.map Prod.snd) a (by simp)
        (by simp; omega))
    obtain ⟨Hd, Hp⟩ := H
    constructor
    · simp only [tableDegree_append, tableDegree_whisk, List.map_append, List.map_cons,
        List.map_nil, wt_append, wt_pair_cancel_table, wt_nil] at Hd ⊢
      linear_combination Hd
    · simpa only [xpar_append, xpar_map_xwhL,
        add_assoc, add_comm, add_left_comm] using Hp

/-- A cap block can be pushed through any fitting cup/crossing list. The output has
its two cap strands joined, no more crossings than the source, and the same table
degree and parity if the bound is attained. No scalar or span relation is assumed. -/
theorem numericCapPush (D : Datum I X) (sy : Symmetrizer D) (μ : X) :
    ∀ E : List (Move (Letter I)), Fits 0 E → NumericCapPush D sy μ E := by
  intro E
  induction E using List.reverseRecOn with
  | nil =>
    intro _ P S Q A B ht
    simp [Chord.run] at ht
  | append_singleton E m ih =>
    intro hf
    obtain ⟨hfE, hm⟩ := fits_snoc'.1 hf
    cases m with
    | cross p => exact numericCapPush_cross (ih hfE) hfE hm
    | cup g a => exact numericCapPush_cup (ih hfE) hfE hm a

end OddMath.SKM
