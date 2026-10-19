import OddMath.SKM.PositivePointGrading

/-! Raw right-cup attachment supporting BE2 v2 Theorem 10.3 Claim 2.
This proves literal layer realization and numerical grading, not representative-family
correspondence or transport of distinguished strand points. -/

namespace OddMath.SKM
open StringDiagrams StringDiagrams.Chord DTMove

variable {I X : Type*} [AddCommGroup X]

/-- Shifting a valid decorated move list left-whiskers its layers. -/
theorem dLay_shift_of_fits {k : ℕ} {v : List (Letter I)} (hv : v.length = k)
    (u : List (Letter I)) (ds : List (DTMove I)) (T : TState (Letter I))
    (l : List (Letter I)) (hl : T.st.map Prod.snd = v ++ l)
    (hf : TFits flipL k T (tmoves ds)) :
    dLay (u ++ l) (ds.map (shiftD u.length)) = (dLay l ds).map (xwhL u []) := by
  induction ds generalizing T l with
  | nil => rfl
  | cons d ds ih =>
    cases d with
    | tm m =>
      obtain ⟨hm, hf⟩ := hf
      have hlen : T.st.length = k + l.length := by
        have h := congrArg List.length hl
        simpa [hv] using h
      have hm' : ∀ mm, m = .mv mm → mm.Ok l.length := by
        intro mm he
        subst he
        cases mm with
        | cup g x =>
          show g ≤ l.length
          have : k + g ≤ T.st.length := hm
          omega
        | cross p =>
          show p + 1 < l.length
          have : k + p + 1 < T.st.length := hm
          omega
      have hn := letters_tRun hv [m] T l hl ⟨hm, trivial⟩
      simp only [tRun, List.foldl_cons, List.foldl_nil] at hn
      obtain ⟨he, ht⟩ := tmLay_shift u hm'
      simp only [List.map_cons, shiftD, dLay]
      rw [← ht, ih _ _ hn hf, ← he, List.map_append]
    | dt p =>
      simp only [List.map_cons, shiftD, dLay]
      rw [dotOn_append_left, ih _ _ hl hf, List.map_append]

/-- The literal decorated move list after attaching the right cup. -/
def cupAttachMoves (i : I) (ds : List (DTMove I)) : List (DTMove I) :=
  .tm (.mv (.cup 0 (false, i))) :: ds.map (shiftD 1)

/-- The corresponding ordinary layers, with no normalization. -/
def cupAttachLayers (i : I) (a : List (Letter I)) (L : List (LayerData I)) :
    List (LayerData I) :=
  ([], Shape.cup i, a) :: L.map (whL [(false, i)] [])

theorem sChain_cupAttach {i : I} {a b : List (Letter I)} {L : List (LayerData I)}
    (hL : SChain ((true, i) :: a) L b) :
    SChain a (cupAttachLayers i a L) ((false, i) :: b) := by
  refine ⟨rfl, ?_⟩
  simpa [Shape.cod] using hL.whisk [(false, i)] []

theorem dLay_cupAttach {i : I} {a b : List (Letter I)}
    {R : List (TMove (Letter I))} (hR : IsMatching₂ ((true, i) :: a) b R)
    {ds : List (DTMove I)} (hd : tmoves ds = R) :
    dLay a (cupAttachMoves i ds) =
      [ofL ([], Shape.cup i, a)] ++
        (dLay ((true, i) :: a) ds).map (xwhL [(false, i)] []) := by
  have hs := dLay_shift_of_fits (length_dualW ((true, i) :: a)) [(false, i)] ds
    (tStart ((true, i) :: a)) ((true, i) :: a) (tStart_letters _) (by rw [hd]; exact hR.1)
  have hc : tLet a (.mv (.cup 0 (false, i))) = (false, i) :: (true, i) :: a := by
    simpa [tLet, flipL] using chStep_cup ([] : List (Letter I)) a (false, i)
  have hm : tmLay a (.mv (.cup 0 (false, i))) = [ofL ([], Shape.cup i, a)] := by
    have h := moveLay_cup ([] : List (Letter I)) a (false, i)
    simpa [tmLay, xCupL, xwhL, ofL, etaL] using h
  simpa only [cupAttachMoves, dLay, hc, hm, List.length_singleton,
    List.singleton_append] using congrArg
    (fun z => [ofL ([], Shape.cup i, a)] ++ z) hs

/-- Literal right-cup attachment has the source cup degree and no parity change.
The supplied ordinary realization is not a grading-preservation assumption. -/
theorem cup_attach_up_degree_parity (D : Datum I X) (sy : Symmetrizer D) (μ : X)
    {i : I} {a b : List (Letter I)} {R : List (TMove (Letter I))}
    (hR : IsMatching₂ ((true, i) :: a) b R)
    {ds : List (DTMove I)} (hd : tmoves ds = R)
    (L : List (LayerData I)) (hL : SChain ((true, i) :: a) L b)
    (he : L.map ofL = dLay ((true, i) :: a) ds) :
    ∃ hLB : SChain a (cupAttachLayers i a L) ((false, i) :: b),
      (cupAttachLayers i a L).map ofL = dLay a (cupAttachMoves i ds) ∧
      Diagram.degree (gdeg D sy) (mkD D μ (cupAttachLayers i a L) hLB) =
        Diagram.degree (gdeg D sy) (mkD D μ L hL) +
          sy.d i * (1 + D.h i (wt D μ a)) ∧
      xpar D μ (dLay a (cupAttachMoves i ds)) = xpar D μ (dLay ((true, i) :: a) ds) := by
  refine ⟨sChain_cupAttach hL, ?_, ?_, ?_⟩
  · rw [dLay_cupAttach hR hd, ← he, map_xwhL_map_ofL]
    rfl
  · rw [degree_gdeg_mkD, degree_gdeg_mkD]
    simp [cupAttachLayers, List.map_map, Function.comp_def, whL, gdeg, add_comm]
  · rw [dLay_cupAttach hR hd, xpar_append, xpar_map_xwhL]
    simp [xpar, xlpar, ofL, Shape.parity]

end OddMath.SKM
