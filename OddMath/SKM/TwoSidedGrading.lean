import OddMath.SKM.CapPushGrading
import OddMath.SKM.CupAttachmentReduced

/-!
# Numerical comparison of reduced two-sided matchings

Supporting Brundan–Ellis, arXiv:1701.04133v2, Theorem 10.3, representative
independence and Claim 2; compare Khovanov–Lauda, arXiv:0807.3250v1,
§2.2 degree independence and Lemma 2.9. The constructive cap-push witnesses
preserve the generator-table degree and parity when their crossing bounds are
sharp. Crossing-minimality forces sharpness; one-sided chord equivalence then
compares both bent diagrams with the same canonical diagram. Cancelling the
common initial cup sum gives the two-sided comparison.

Only `Reduced₂` is needed, not the extra critical-point bound of `StrictReduced₂`.
No numeric conclusion is inferred from a span relation or from a quotient morphism.
This is undecorated comparison, not yet the decorated-series/form identity.
-/

namespace OddMath.SKM
open StringDiagrams
open StringDiagrams.Chord (Move Fits run Iso rl rlId TMove TState tStep tRun TFits TInv ncr₂ jn canon)
variable {I X : Type*} [AddCommGroup X] (D : Datum I X) (sy : Symmetrizer D)

theorem numericTPush (μ : X) {k : ℕ} {T : TState (Letter I)} (I₀ : TInv T)
    {E : List (Move (Letter I))} (hf : Fits 0 E) (hiso : Iso (run flipL E) T.st)
    {u l : List (Letter I)} (hu : u.length = k) (hl : T.st.map Prod.snd = u ++ l)
    {m : TMove (Letter I)} (hm : m.Ok flipL k T.st) :
    (tStep flipL k T m).st.map Prod.snd = u ++ tLet l m ∧ XChain l (tmLay l m) (tLet l m) ∧
      xcnt (tmLay l m) = ncr₂ [m] ∧
      ∃ E', Fits 0 E' ∧ Iso (run flipL E') (tStep flipL k T m).st ∧
        ncr E' ≤ ncr E + ncr₂ [m] ∧
        (ncr E' = ncr E + ncr₂ [m] → tableDegree D sy μ (chordLay [] E ++ (tmLay l m).map (xwhL u [])) =
          tableDegree D sy μ (chordLay [] E') ∧
          xpar D μ (chordLay [] E ++ (tmLay l m).map (xwhL u [])) =
          xpar D μ (chordLay [] E')) := by
  have hlen : T.st.length = u.length + l.length := by
    have := congrArg List.length hl; simpa using this
  have hrun : (run flipL E).map Prod.snd = u ++ l := by rw [hiso.1, hl]
  rcases m with (⟨g, a⟩ | p) | g
  · -- a cup
    simp only [TMove.Ok] at hm
    have hg : g ≤ l.length := by omega
    have hok : (Move.cup g a).Ok l.length := hg
    obtain ⟨hlay, hstep⟩ := moveLay_shift u [] hok
    simp only [List.append_nil] at hlay hstep
    rw [hu] at hlay hstep
    simp only [shiftM] at hlay hstep
    have hm' : (Move.cup (k + g) a).Ok (run flipL E).length := by
      show k + g ≤ _; rw [hiso.length_eq]; exact hm
    refine ⟨?_, xChain_moveLay hok, by rw [tmLay, xcnt_moveLay hok]; rfl,
      E ++ [.cup (k + g) a], fits_snoc'.2 ⟨hf, hm'⟩, ?_, ?_, fun _ => ?_⟩
    · obtain ⟨v, w, rfl, rfl⟩ := exists_split_cup hg
      obtain ⟨U, W, hT, hU⟩ := exists_split_cup (l := T.st) (g := k + v.length) hm
      rw [hT] at hl
      simp only [List.map_append] at hl
      obtain ⟨h1, h2⟩ := List.append_inj (s₁ := U.map Prod.snd) (t₁ := W.map Prod.snd)
        (s₂ := u ++ v) (t₂ := w) (by simpa using hl) (by simp [hU, hu])
      simp only [tStep, tLet, chStep_cup, hT]
      rw [← hU]
      simp [Chord.insAt, h1, h2]
    · rw [run_snoc]
      exact hiso.insAt hm' (fun x hx => ((Chord.inv_run (d := flipL) hf).2 x hx).ne)
        (fun x hx => (I₀.fresh x hx).ne) a (flipL a)
    · simp [ncr_append, ncr₂]
    · rw [chordLay_snoc, hrun, hlay]
      exact ⟨rfl, rfl⟩
  · -- a crossing
    simp only [TMove.Ok] at hm
    have hp : p + 1 < l.length := by omega
    have hok : (Move.cross (α := Letter I) p).Ok l.length := hp
    obtain ⟨hlay, hstep⟩ := moveLay_shift u [] hok
    simp only [List.append_nil] at hlay hstep
    rw [hu] at hlay hstep
    simp only [shiftM] at hlay hstep
    have hm' : (Move.cross (α := Letter I) (k + p)).Ok (run flipL E).length := by
      show k + p + 1 < _; rw [hiso.length_eq]; exact hm
    refine ⟨?_, xChain_moveLay hok, by rw [tmLay, xcnt_moveLay hok]; rfl,
      E ++ [.cross (k + p)], fits_snoc'.2 ⟨hf, hm'⟩, ?_, ?_, fun _ => ?_⟩
    · obtain ⟨U, X, Y, W, v, x, y, w, hT, hU, rfl, rfl, hX, hY, h1, h2⟩ := split_state hl hp
      simp only [tStep, tLet, hT, chStep_cross]
      rw [← hu, ← hU, swapAt_mid]
      simp [h1, h2, hX, hY]
    · rw [run_snoc]
      exact hiso.swapAt (k + p)
    · simp [ncr_append, ncr₂]
    · rw [chordLay_snoc, hrun, hlay]
      exact ⟨rfl, rfl⟩
  · -- a cap
    obtain ⟨A, B, hA, hB, hAB, hne⟩ := hm
    have hr : k + g + 1 < T.st.length := by
      by_contra h; rw [List.getElem?_eq_none (by omega)] at hB; cases hB
    have hg : g + 1 < l.length := by omega
    obtain ⟨U, X, Y, W, v, x, y, w, hT, hU, rfl, rfl, hX, hY, h1, h2⟩ := split_state hl hg
    have hXA : X = A := by
      rw [hT, show k + v.length = U.length by omega] at hA; simpa using hA
    have hYB : Y = B := by
      rw [hT, show k + v.length + 1 = U.length + 1 by omega] at hB; simpa using hB
    subst hXA hYB
    have hxy : x = flipL y := by rw [← hX, ← hY]; exact hAB
    obtain ⟨hcap, hlet⟩ := tmLay_cap v w x y
    have hrE : U.length + 1 < (run flipL E).length := by
      rw [hiso.length_eq, hT]; simp
    obtain ⟨U', X', Y', W', hE, hU'⟩ := exists_split_cross hrE
    have hsnd := hiso.1
    rw [hE, hT] at hsnd
    simp only [List.map_append, List.map_cons] at hsnd
    obtain ⟨e1, e2⟩ := List.append_inj hsnd (by simp [hU'])
    simp only [List.cons.injEq] at e2
    obtain ⟨eX, eY, eW⟩ := e2
    have hne' : X'.1 ≠ Y'.1 := by
      intro e
      have hs : Chord.Same (run flipL E) U.length (U.length + 1) := by
        refine ⟨by omega, ?_, ?_⟩
        · rw [Chord.idAt_ne_none_iff]; omega
        · rw [hE, ← hU']; simp [Chord.idAt, e]
      have := ((hiso.2 _ _).1 hs).2.2
      rw [hT] at this
      apply hne
      simpa [Chord.idAt] using this
    obtain ⟨E', hf', hiso', hle, hxl⟩ := numericCapPush D sy μ E hf U' [] W' X' Y'
      (by rw [hE]; simp) (by rw [eX, eY, hX, hY]; exact hxy) hne'
    have hjnE : jn (run flipL E) U.length = (U' ++ [] ++ W').map (rl Y'.1 X'.1) := by
      rw [hE, ← hU', List.append_nil]
      have := Chord.jn_mid U' W' X' Y'
      simpa using this
    have hkg : k + v.length = U.length := by omega
    have hstst : (tStep flipL k T (.cap v.length)).st = jn T.st U.length := by
      simp only [tStep]; rw [hkg]
    have hjnT : jn T.st U.length = (U ++ W).map (rl Y.1 X.1) := by
      rw [hT]; have := Chord.jn_mid U W X Y; simpa using this
    refine ⟨?_, ?_, ?_, E', hf', ?_, by simpa [ncr₂] using hle, fun h => ?_⟩
    · rw [hstst, hjnT, Chord.map_snd_map_rl, hlet]
      simp [h1, h2]
    · rw [hcap, hlet, hxy]
      have := (xChain_xCapL y).whisk v w
      simpa using this
    · rw [hcap]; simp [ncr₂]
    · rw [hstst]
      exact hiso'.trans (hjnE ▸ hiso.jn (by rw [hiso.length_eq.symm] at hr; omega))
    · have H := hxl (by simpa [ncr₂] using h)
      simp only [List.map_nil, capBlk_nil] at H
      rw [e1, eW, eY, hY, h1, h2] at H
      rw [hcap, map_xwhL_xwhL]
      simpa using H


theorem numericTProcess (μ : X) {k : ℕ} {u : List (Letter I)} (hu : u.length = k) :
    ∀ (R : List (TMove (Letter I))) (T : TState (Letter I)) (l : List (Letter I))
      (E : List (Move (Letter I))), TInv T → Fits 0 E → Iso (run flipL E) T.st →
      T.st.map Prod.snd = u ++ l → TFits flipL k T R →
      (tRun flipL k T R).st.map Prod.snd = u ++ R.foldl tLet l ∧
      XChain l (tLay l R) (R.foldl tLet l) ∧ xcnt (tLay l R) = ncr₂ R ∧
      ∃ E', Fits 0 E' ∧ Iso (run flipL E') (tRun flipL k T R).st ∧ ncr E' ≤ ncr E + ncr₂ R ∧
        (ncr E' = ncr E + ncr₂ R →
          tableDegree D sy μ (chordLay [] E ++ (tLay l R).map (xwhL u [])) =
            tableDegree D sy μ (chordLay [] E') ∧
          xpar D μ (chordLay [] E ++ (tLay l R).map (xwhL u [])) =
            xpar D μ (chordLay [] E'))
  | [], T, l, E, _, hf, hiso, hl, _ =>
    ⟨hl, rfl, rfl, E, hf, hiso, by simp [ncr₂], fun _ => by simp [tLay]⟩
  | m :: R, T, l, E, I₀, hf, hiso, hl, ⟨hm, hR⟩ => by
    obtain ⟨hl₁, hc₁, hx₁, E₁, hf₁, hiso₁, hle₁, hxl₁⟩ :=
      numericTPush D sy μ I₀ hf hiso hu hl hm
    obtain ⟨hl₂, hc₂, hx₂, E', hf', hiso', hle', hxl'⟩ :=
      numericTProcess μ hu R _ _ E₁ (I₀.step hm) hf₁ hiso₁ hl₁ hR
    have hn := ncr₂_cons m R
    refine ⟨hl₂, hc₁.append hc₂, by rw [tLay, xcnt_append, hx₁, hx₂, hn], E', hf', hiso',
      by omega, fun h => ?_⟩
    have H₁ := hxl₁ (by omega)
    have H₂ := hxl' (by omega)
    constructor
    · simpa only [tLay, List.map_append, tableDegree_append, ← H₁.1, add_assoc] using H₂.1
    · simpa only [tLay, List.map_append, xpar_append, ← H₁.2, add_assoc] using H₂.2

/-- Minimal crossing count makes every numerical cap-push bound sharp. -/
theorem reduced₂_bent_degree_parity (μ : X) {a b : List (Letter I)}
    {R : List (TMove (Letter I))} (hR : IsMatching₂ a b R) (hred : Reduced₂ a R) :
    tableDegree D sy μ (cupA (dualW a) ++ (tLay a R).map (xwhL (dualW a) [])) =
      tableDegree D sy μ (chordLay [] (canon (pairing₂ a R))) ∧
    xpar D μ (cupA (dualW a) ++ (tLay a R).map (xwhL (dualW a) [])) =
      xpar D μ (chordLay [] (canon (pairing₂ a R))) := by
  obtain ⟨hf₀, hn₀, hc₀, _⟩ := cupMoves_spec (dualW a)
  obtain ⟨_, _, _, E', hf', hiso', hle, hnum⟩ := numericTProcess D sy μ
    (length_dualW a) R (tStart a) a (cupMoves (dualW a))
    (tInv_tStart a) hf₀ (Iso.refl _) (tStart_letters a) hR.1
  have hbound := Chord.length_xs_le_cr ((tInv_tStart a).run hR.1) hred.1 hred.2
  rw [Chord.length_xs_tRun, show (tStart a).xs.length = 0 from rfl, zero_add] at hbound
  change ncr₂ R ≤ Chord.cr (pairing₂ a R) at hbound
  have hcr : Chord.cr (run flipL E') = Chord.cr (pairing₂ a R) :=
    le_antisymm (Chord.cr_le_of_iso hiso') (Chord.cr_le_of_iso hiso'.symm)
  have hcr' := Chord.cr_run_le_ncr flipL hf'
  rw [hn₀, zero_add] at hle hnum
  have heq : ncr E' = ncr₂ R := by omega
  have hredE : Chord.Reduced flipL E' := (Chord.reduced_iff flipL hf').2 (by omega)
  have hcanon := tableDegree_xpar_equiv D sy μ
    (Chord.equiv_canon_of_reduced flipL hf' hredE) [] hf'
  rw [Chord.canon_eq_of_iso hiso'] at hcanon
  have H := hnum heq
  rw [hc₀] at H
  exact ⟨H.1.trans hcanon.1, H.2.trans hcanon.2⟩

/-- Crossing-minimal representatives of the same boundary pairing have equal table invariants. -/
theorem reduced₂_degree_parity_of_iso (μ : X) {a b : List (Letter I)}
    {R S : List (TMove (Letter I))} (hR : IsMatching₂ a b R) (hrR : Reduced₂ a R)
    (hS : IsMatching₂ a b S) (hrS : Reduced₂ a S)
    (hi : Iso (pairing₂ a R) (pairing₂ a S)) :
    tableDegree D sy μ (tLay a R) = tableDegree D sy μ (tLay a S) ∧
      xpar D μ (tLay a R) = xpar D μ (tLay a S) := by
  have HR := reduced₂_bent_degree_parity D sy μ hR hrR
  have HS := reduced₂_bent_degree_parity D sy μ hS hrS
  rw [Chord.canon_eq_of_iso hi] at HR
  have hd := HR.1.trans HS.1.symm
  have hp := HR.2.trans HS.2.symm
  simp only [tableDegree_append, tableDegree_whisk, wt_nil, add_right_inj,
    xpar_append, xpar_map_xwhL] at hd hp
  exact ⟨hd, hp⟩

/-- The undecorated right-cup target, with crossing-minimality only. -/
theorem cupAttach_normalized_degree_parity (μ : X) {i : I} {a b : List (Letter I)}
    {R S : List (TMove (Letter I))}
    (hR : IsMatching₂ ((true, i) :: a) b R) (hrR : Reduced₂ ((true, i) :: a) R)
    (hS : IsMatching₂ a ((false, i) :: b) S) (hrS : Reduced₂ a S)
    (hi : Iso (pairing₂ a S) (pairing₂ ((true, i) :: a) R)) :
    tableDegree D sy μ (tLay a S) = tableDegree D sy μ (tLay a (cupAttachMatching i R)) ∧
      xpar D μ (tLay a S) = xpar D μ (tLay a (cupAttachMatching i R)) := by
  obtain ⟨hm, hc⟩ := cupAttach_matching_iso hR
  exact reduced₂_degree_parity_of_iso D sy μ hS hrS hm (reduced₂_cupAttach hR hrR)
    (hi.trans hc.symm)

end OddMath.SKM
