/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.SpanDotStrands

/-!
# Decorated reduced matchings span (Theorem 8.1, general bottom boundary)

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Theorem 8.1, whose
proof the paper omits, referring to M. Khovanov, A. Lauda, *A categorification of quantum
`sl(n)`*, arXiv:0807.3250v1, Proposition 3.11.

An `(a, b)`-matching is a generic layering `R : List (TMove (Letter I))` of cups, crossings and
caps (`IsMatching₂ a b R`), with pairing `pairing₂ a R` on the letters `a* b` (the bottom
endpoints first, in reverse order). A decorated matching `ds : List (DTMove I)` adds dots at
positions between the moves, and is evaluated by `dLay a ds : E_a 1_λ → E_b 1_λ`. A strand is
named by its left endpoint `j` in the pairing (`leftEnds₂`); a distinguished point of it is a
height and a position at that height (`OnStrand₂`): the strand ids of the two-sided matchings
(`Chord.TState`) followed up through the later caps (`tRen`) identify the strand.

## Main results

* `theorem_8_1_of_pairings`: **[BE2] Theorem 8.1 for any bottom boundary**, for any set of
  reduced matchings that contains a representative of every pairing, any distinguished points
  and any order of the dots at one height.
* `canon_dots_mem_decorated₂`: the triangular step: the canonical chord diagrams of the bent
  pairings, with dots, lie in the span of the bent decorated matchings (given the diagrams with
  fewer crossings).

The proof bends the bottom boundary up (`bendF`, `bendG`) and follows KL III: the canonical
diagram of a pairing agrees up to sign, modulo diagrams with fewer crossings, with a reduced
representative (`reduced₂_bent_normal_form`); dots move to the left ends of their arcs
(`dots_to_lEnd`) and along the strands of the matching (`DotBase.dots_up`), modulo diagrams with
fewer crossings or fewer dots.
-/

noncomputable section

namespace OddMath.SKM

open CategoryTheory StringDiagrams Presentation
open StringDiagrams.Chord (Move Iso TMove TState tStep tRun TFits ncr₂ idD Same Valid Lettered canon
  idAt)

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]
  {Sc : Scalars D k} {cs : CScalars Sc}

/-! ## Decorated matchings bent up -/

section Shift

open DTMove

/-- A move of a decorated matching shifted `n` positions to the right. -/
def shiftD (n : ℕ) : DTMove I → DTMove I
  | .tm m => .tm (shiftT n m)
  | .dt i => .dt (n + i)

theorem tmoves_map_shiftD (n : ℕ) : ∀ ds : List (DTMove I),
    tmoves (ds.map (shiftD n)) = (tmoves ds).map (shiftT n)
  | [] => rfl
  | .tm m :: ds => by simp [tmoves, shiftD, tmoves_map_shiftD n ds]
  | .dt i :: ds => by simp [tmoves, shiftD, tmoves_map_shiftD n ds]

theorem lOk_unshift (u : List (Letter I)) {l : List (Letter I)} {m : TMove (Letter I)}
    (h : LOk (u ++ l) (shiftT u.length m)) : LOk l m := by
  rcases m with (⟨g, a⟩ | p) | g
  · have : u.length + g ≤ (u ++ l).length := h
    show g ≤ l.length
    simp at this; omega
  · have : u.length + p + 1 < (u ++ l).length := h
    show p + 1 < l.length
    simp at this; omega
  · obtain ⟨v, y, w, hl, hv⟩ := h
    rcases List.append_eq_append_iff.1 hl with ⟨v', rfl, rfl⟩ | ⟨c', rfl, hc⟩
    · exact ⟨v', y, w, rfl, by simp at hv; omega⟩
    · simp only [List.length_append] at hv
      have : c' = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst this
      exact ⟨[], y, w, by simpa using hc.symm, by simp; omega⟩

theorem xChain_tmLay_of_lOk {l : List (Letter I)} {m : TMove (Letter I)} (h : LOk l m) :
    XChain l (tmLay l m) (tLet l m) := by
  rcases m with mm | g
  · exact xChain_moveLay (show mm.Ok l.length from h)
  · obtain ⟨v, y, w, rfl, rfl⟩ := h
    obtain ⟨hcap, hlet⟩ := tmLay_cap v w (flipL y) y
    rw [hcap, hlet]; simpa using (xChain_xCapL y).whisk v w

theorem dotOn_append_left (u l : List (Letter I)) (i : ℕ) :
    dotOn (u ++ l) (u.length + i) = (dotOn l i).map (xwhL u []) := by
  have e1 : (u ++ l).drop (u.length + i) = l.drop i := by
    rw [List.drop_append, List.drop_eq_nil_of_le (by omega)]; simp
  have e2 : (u ++ l).take (u.length + i) = u ++ l.take i := by
    rw [List.take_append]; simp
  unfold dotOn
  rw [e1, e2]
  rcases l.drop i with _ | ⟨x, w⟩
  · rfl
  · simp [List.map_map, Function.comp_def, xwhL]

/-- **A decorated matching bent up**: shifting it past the strands `u` on the left whiskers its
layers by `u`. -/
theorem shiftD_spec (u : List (Letter I)) (n : ℕ) (hu : u.length = n) :
    ∀ (ds : List (DTMove I)) {T : TState (Letter I)} {l : List (Letter I)},
    T.st.map Prod.snd = u ++ l → TFits flipL 0 T (tmoves (ds.map (shiftD n))) →
    dLay (u ++ l) (ds.map (shiftD n)) = (dLay l ds).map (xwhL u []) ∧
      XChain l (dLay l ds) ((tmoves ds).foldl tLet l) ∧
      (tmoves (ds.map (shiftD n))).foldl tLet (u ++ l) = u ++ (tmoves ds).foldl tLet l ∧
      (DOk₂ (u ++ l) (ds.map (shiftD n)) ↔ DOk₂ l ds)
  | [], _, _, _, _ => ⟨rfl, rfl, rfl, Iff.rfl⟩
  | .tm m :: ds, T, l, hl, hf => by
    subst hu
    have hf' : (shiftT u.length m).Ok flipL 0 T.st ∧
        TFits flipL 0 (tStep flipL 0 T (shiftT u.length m)) (tmoves (ds.map (shiftD u.length))) :=
      hf
    have hL := lOk_unshift u (lOk_of_ok hl hf'.1)
    obtain ⟨e1, e2⟩ := tmLay_shift u (l := l) (m := m) (fun mm h => by subst h; exact hL)
    have hl' : (tStep flipL 0 T (shiftT u.length m)).st.map Prod.snd = u ++ tLet l m := by
      rw [(tStep_spec hl hf'.1).1, e2]
    obtain ⟨h1, h2, h3, h4⟩ := shiftD_spec u u.length rfl ds hl' hf'.2
    refine ⟨?_, (xChain_tmLay_of_lOk hL).append h2, ?_, ?_⟩
    · show tmLay (u ++ l) (shiftT u.length m) ++
        dLay (tLet (u ++ l) (shiftT u.length m)) (ds.map (shiftD u.length)) = _
      rw [← e1, ← e2, h1, dLay, List.map_append]
    · show (tmoves (ds.map (shiftD u.length))).foldl tLet (tLet (u ++ l) (shiftT u.length m)) = _
      rw [← e2, h3]; rfl
    · show DOk₂ (tLet (u ++ l) (shiftT u.length m)) _ ↔ DOk₂ (tLet l m) ds
      rw [← e2, h4]
  | .dt i :: ds, T, l, hl, hf => by
    subst hu
    obtain ⟨h1, h2, h3, h4⟩ := shiftD_spec u u.length rfl ds hl hf
    refine ⟨?_, (xChain_dotOn' l i).append h2, h3, ?_⟩
    · show dotOn (u ++ l) (u.length + i) ++ dLay (u ++ l) (ds.map (shiftD u.length)) = _
      rw [dotOn_append_left, h1, dLay, List.map_append]
    · show (u.length + i < (u ++ l).length ∧ _) ↔ (i < l.length ∧ _)
      rw [h4, List.length_append]
      exact and_congr_left' ⟨fun h => by omega, fun h => by omega⟩

/-- The strand ids reached by the dots of a shifted decorated matching. -/
theorem dotIds_shiftD (n : ℕ) : ∀ (ds : List (DTMove I)) (T : TState (Letter I)),
    dotIds T (ds.map (shiftD n)) = (dotPts ds).map fun p =>
      tRen n (tRun flipL n T ((tmoves ds).take p.1)) ((tmoves ds).drop p.1)
        (idD (tRun flipL n T ((tmoves ds).take p.1)).st (n + p.2))
  | [], _ => rfl
  | .tm m :: ds, T => by
    show dotIds (tStep flipL 0 T (shiftT n m)) (ds.map (shiftD n)) = _
    rw [← tStep_shift, dotIds_shiftD n ds]
    simp only [dotPts, tmoves, List.map_map, Function.comp_def, List.take_succ_cons,
      List.drop_succ_cons]
    rfl
  | .dt i :: ds, T => by
    show tRen 0 T (tmoves (ds.map (shiftD n))) (idD T.st (n + i)) :: dotIds T (ds.map (shiftD n)) = _
    rw [tmoves_map_shiftD, ← tRen_shift, dotIds_shiftD n ds]
    simp [dotPts, tmoves, Chord.tRun]

theorem dOk₂_of_dotPts : ∀ (ds : List (DTMove I)) (l : List (Letter I)),
    (∀ p ∈ dotPts ds, p.2 < (((tmoves ds).take p.1).foldl tLet l).length) → DOk₂ l ds
  | [], _, _ => trivial
  | .tm m :: ds, l, h => dOk₂_of_dotPts ds (tLet l m) fun p hp => by
      have := h (p.1 + 1, p.2) (List.mem_map.2 ⟨p, hp, rfl⟩)
      simpa [tmoves] using this
  | .dt i :: ds, l, h => ⟨by simpa using h (0, i) List.mem_cons_self,
      dOk₂_of_dotPts ds l fun p hp => by
        have := h p (List.mem_cons_of_mem _ hp); simpa [tmoves] using this⟩

theorem tStart_letters (a : List (Letter I)) : (tStart a).st.map Prod.snd = dualW a ++ a := by
  obtain ⟨-, -, -, hw₀⟩ := cupMoves_spec (dualW a)
  rw [dualW_dualW] at hw₀
  rw [tStart]; dsimp only; rw [← foldl_chStep_eq, hw₀]

theorem length_dualW (a : List (Letter I)) : (dualW a).length = a.length := by simp [dualW]

/-- **An `(a, b)`-matching bent up** by the nested cups `cupA a*`. -/
theorem matching_bent_spec {a b : List (Letter I)} {R : List (TMove (Letter I))}
    (hR : IsMatching₂ a b R) :
    TFits flipL 0 (tStart a) (R.map (shiftT a.length)) ∧
      (R.map (shiftT a.length)).foldl tLet (dualW a ++ a) = dualW a ++ b ∧
      tLay (dualW a ++ a) (R.map (shiftT a.length)) = (tLay a R).map (xwhL (dualW a) []) ∧
      XChain a (tLay a R) b ∧
      (tRun flipL 0 (tStart a) (R.map (shiftT a.length))).st = pairing₂ a R ∧
      ncr₂ (R.map (shiftT a.length)) = ncr₂ R := by
  have hfit := (tFits_shift a.length _ R).1 hR.1
  have e : (R.map DTMove.tm).map (shiftD a.length) = (R.map (shiftT a.length)).map DTMove.tm := by
    simp [List.map_map, Function.comp_def, shiftD]
  obtain ⟨h1, h2, h3, -⟩ := shiftD_spec (dualW a) a.length (length_dualW a) (R.map .tm)
    (tStart_letters a) (by rw [e, tmoves_map_tm]; exact hfit)
  rw [e, dLay_map_tm, dLay_map_tm] at h1
  rw [e, tmoves_map_tm, tmoves_map_tm, hR.2] at h3
  rw [dLay_map_tm, tmoves_map_tm, hR.2] at h2
  exact ⟨hfit, h3, h1, h2, by rw [← tRun_shift]; rfl, ncr₂_shift _ R⟩

end Shift

/-! ## Decorated matchings with dots at distinguished points -/

section Decorated

open DTMove

open scoped Classical in
/-- The strands of an `(a, b)`-matching, named by their left endpoints in the pairing on `a* b`. -/
def leftEnds₂ (a : List (Letter I)) (R : List (TMove (Letter I))) : List ℕ :=
  (List.range (pairing₂ a R).length).filter fun j => decide (IsLeftEnd (pairing₂ a R) j)

theorem mem_leftEnds₂ {a : List (Letter I)} {R : List (TMove (Letter I))} {j : ℕ} :
    j ∈ leftEnds₂ a R ↔ IsLeftEnd (pairing₂ a R) j := by
  classical
  simp only [leftEnds₂, List.mem_filter, List.mem_range, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩

theorem nodup_leftEnds₂ (a : List (Letter I)) (R : List (TMove (Letter I))) :
    (leftEnds₂ a R).Nodup :=
  (List.nodup_range).filter _

/-- The point `q` (height `q.1`, the number of moves below it, and position `q.2` among the strands
of the matching at that height) lies on the strand of the `(a, b)`-matching `R` with left endpoint
`j`: its strand id, followed up through the later caps, is the id of `j`. -/
def OnStrand₂ (a : List (Letter I)) (R : List (TMove (Letter I))) (j : ℕ) (q : ℕ × ℕ) : Prop :=
  q.2 < ((R.take q.1).foldl tLet a).length ∧
    tRen a.length (tRun flipL a.length (tStart a) (R.take q.1)) (R.drop q.1)
      (idD (tRun flipL a.length (tStart a) (R.take q.1)).st (a.length + q.2)) =
        idD (pairing₂ a R) j

/-- **Decorated matchings with dots at the distinguished points**: `ds` is the matching `R` with
`n j` dots at the distinguished point `q j` of the strand with left endpoint `j`, for every strand
`j` (the dots at one height in any order). -/
def Decorates₂ (a : List (Letter I)) (R : List (TMove (Letter I))) (q : ℕ → ℕ × ℕ) (n : ℕ → ℕ)
    (ds : List (DTMove I)) : Prop :=
  tmoves ds = R ∧ (dotPts ds).Perm ((leftEnds₂ a R).flatMap fun j => List.replicate (n j) (q j))

/-- The decorated matchings of a choice: for each chosen matching `R ∈ M` and counts `n`, the
decorated matching `σ R n`, as a diagram `E_a 1_λ → E_b 1_λ`. -/
def decoratedFamily₂ (a : List (Letter I)) (M : Set (List (TMove (Letter I))))
    (σ : List (TMove (Letter I)) → (ℕ → ℕ) → List (DTMove I)) : Set (List (XLayer I)) :=
  {L | ∃ R ∈ M, ∃ n : ℕ → ℕ, L = dLay a (σ R n)}

theorem decSpan_mono {μ : X} {l₀ : List (Letter I)} {B₀ : List (XLayer I)}
    {R : List (TMove (Letter I))} {t : List (Letter I)} {N N' : ℕ} (h : N ≤ N') :
    DecSpan cs μ l₀ B₀ R t N ≤ DecSpan cs μ l₀ B₀ R t N' :=
  Submodule.span_mono fun _ ⟨ds, Z, β, h1, h2, h3, h4, h5, h6⟩ =>
    ⟨ds, Z, β, h1, h2, h3, by omega, h5, h6⟩

theorem decSpan_comp_bubAt {μ : X} {l₀ : List (Letter I)} {B₀ : List (XLayer I)}
    {R : List (TMove (Letter I))} {t : List (Letter I)} {N : ℕ}
    {β : (pres D Sc).obj (ob D μ []) ⟶ (pres D Sc).obj (ob D μ [])} (hβ : IsBubbleProd cs μ β)
    {x} (hx : x ∈ DecSpan cs μ l₀ B₀ R t N) :
    x ≫ bubAt D Sc μ t β ∈ DecSpan cs μ l₀ B₀ R t N := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨ds, Z, γ, h1, h2, h3, h4, h5, rfl⟩ := hx
    rw [Category.assoc, ← bubAt_comp]
    exact Submodule.subset_span ⟨ds, Z, γ ≫ β, h1, h2, h3, h4, h5.comp hβ, rfl⟩
  | zero => rw [Limits.zero_comp]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [Preadditive.add_comp]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [Linear.smul_comp]; exact Submodule.smul_mem _ r hx

theorem fewerDots_comp_bubAt_mem {μ : X} {s : List (ℕ × Letter I)} {m : ℕ}
    {T : Submodule k ((pres D Sc).obj (ob D μ []) ⟶ (pres D Sc).obj (ob D μ (s.map Prod.snd)))}
    {β : (pres D Sc).obj (ob D μ []) ⟶ (pres D Sc).obj (ob D μ [])} (hβ : IsBubbleProd cs μ β)
    (h : ∀ (js : List ℕ), (∀ i ∈ js, i < s.length) → js.length < m → ∀ {γ}, IsBubbleProd cs μ γ →
      xev cs μ [] (s.map Prod.snd) (chordLay [] (canon s) ++ dotsOn (s.map Prod.snd) js) ≫
        bubAt D Sc μ (s.map Prod.snd) γ ∈ T)
    {x} (hx : x ∈ FewerDots cs μ s m) : x ≫ bubAt D Sc μ (s.map Prod.snd) β ∈ T := by
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨js, γ, hjs, hlen, hγ, rfl⟩ := hz
    rw [Category.assoc, ← bubAt_comp]
    exact h js hjs hlen (hγ.comp hβ)
  | zero => rw [Limits.zero_comp]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [Preadditive.add_comp]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [Linear.smul_comp]; exact Submodule.smul_mem _ a hx

/-- A strand of a pairing isomorphic to a valid `s` is named by the left end of its arc in `s`. -/
theorem lEnd_eq_of_idD {P s : List (ℕ × Letter I)} (hv : Valid s) (hiso : Iso P s) {y j : ℕ}
    (hy : y < P.length) (hj : IsLeftEnd s j) (h : idD P y = idD P j) : lEnd s y = j := by
  have hjP : j < P.length := by rw [hiso.length_eq]; exact hj.1
  have h' : idAt P y = idAt P j := by
    rw [Chord.idAt_eq_idD hy, Chord.idAt_eq_idD hjP, h]
  refine lEnd_eq_of_isLeftEnd hv hj ?_
  rcases eq_or_same_of_idAt hy h' with h | h
  · exact Or.inl h
  · exact Or.inr ((hiso.2 _ _).1 h)

end Decorated

/-! ## The triangular step -/

section Step

open DTMove

variable (μ : X) (a b : List (Letter I)) (M : Set (List (TMove (Letter I))))
  (hM : ∀ R ∈ M, IsMatching₂ a b R ∧ Reduced₂ a R)
  (hrep : ∀ s : List (ℕ × Letter I), Valid s → Lettered flipL s →
    s.map Prod.snd = dualW a ++ b → ∃ R ∈ M, Iso (pairing₂ a R) s)
  (q : List (TMove (Letter I)) → ℕ → ℕ × ℕ)
  (hq : ∀ R ∈ M, ∀ j ∈ leftEnds₂ a R, OnStrand₂ a R j (q R j))
  (σ : List (TMove (Letter I)) → (ℕ → ℕ) → List (DTMove I))
  (hσ : ∀ R ∈ M, ∀ n, Decorates₂ a R (q R) n (σ R n))
  (v : List (Letter I)) (hvab : dualW a ++ b = v)
  (T : Submodule k ((pres D Sc).obj (ob D μ []) ⟶ (pres D Sc).obj (ob D μ v)))
  (hfam : ∀ R ∈ M, ∀ n, ∀ {β : (pres D Sc).obj (ob D μ []) ⟶ (pres D Sc).obj (ob D μ [])},
    IsBubbleProd cs μ β → xev cs μ [] v (cupA (dualW a) ++
      dLay (dualW a ++ a) ((σ R n).map (shiftD a.length))) ≫ bubAt D Sc μ v β ∈ T)
  (c : ℕ) (hlow : LtL D Sc cs μ [] v c ≤ T)

include hM hrep hq hσ hvab hfam hlow in
/-- **The canonical diagrams with dots, step**: given the canonical diagrams with fewer than `N`
dots and the bent decorated diagrams with fewer than `N` dots, the canonical diagrams with `N`
dots lie in `T`. -/
theorem canon_dots_mem_step (N : ℕ)
    (hC : ∀ {s : List (ℕ × Letter I)}, Valid s → Lettered flipL s → s.map Prod.snd = v →
      ncr (canon s) = c → ∀ (is : List ℕ), (∀ i ∈ is, i < s.length) → is.length < N →
      ∀ {β : (pres D Sc).obj (ob D μ []) ⟶ (pres D Sc).obj (ob D μ [])}, IsBubbleProd cs μ β →
      xev cs μ [] v (chordLay [] (canon s) ++ dotsOn v is) ≫ bubAt D Sc μ v β ∈ T)
    (hA : ∀ {s : List (ℕ × Letter I)}, Valid s → Lettered flipL s → s.map Prod.snd = v →
      ncr (canon s) = c → ∀ R ∈ M, Iso (pairing₂ a R) s →
      DecSpan cs μ (dualW a ++ a) (cupA (dualW a)) (R.map (shiftT a.length)) v N ≤ T) :
    ∀ {s : List (ℕ × Letter I)}, Valid s → Lettered flipL s → s.map Prod.snd = v →
      ncr (canon s) = c → ∀ (is : List ℕ), (∀ i ∈ is, i < s.length) → is.length ≤ N →
      ∀ {β : (pres D Sc).obj (ob D μ []) ⟶ (pres D Sc).obj (ob D μ [])}, IsBubbleProd cs μ β →
      xev cs μ [] v (chordLay [] (canon s) ++ dotsOn v is) ≫ bubAt D Sc μ v β ∈ T := by
  intro s hv hl hsv hc is his hN β hβ
  subst hsv
  obtain ⟨R, hRM, hiso⟩ := hrep s hv hl hvab.symm
  obtain ⟨hR, hred⟩ := hM R hRM
  obtain ⟨-, hnc, hNF⟩ := reduced₂_bent_normal_form cs μ hR hred
  rw [Chord.canon_eq_of_iso hiso, hc] at hnc
  rw [Chord.canon_eq_of_iso hiso, hnc, hvab] at hNF
  obtain ⟨hfitb, hfoldb, htLayb, hXb, hstb, hncrb⟩ := matching_bent_spec hR
  set P := pairing₂ a R with hPdef
  set Rb := R.map (shiftT a.length) with hRb
  -- the decoration with the multiplicities of the left ends of the dots `is`
  set n : ℕ → ℕ := fun j => (is.map (lEnd s)).count j with hn
  obtain ⟨hmv, hperm⟩ := hσ R hRM n
  set ds := σ R n with hds
  set ds' := ds.map (shiftD a.length) with hds'
  have htm : tmoves ds' = Rb := by rw [hds', tmoves_map_shiftD, hmv]
  have hfit' : TFits flipL 0 (tStart a) (tmoves ds') := by rw [htm]; exact hfitb
  obtain ⟨hd1, hd2, hd3, hd4⟩ := shiftD_spec (dualW a) a.length (length_dualW a) ds
    (tStart_letters a) hfit'
  have hdok : DOk₂ a ds := dOk₂_of_dotPts ds a fun p hp => by
    obtain ⟨j, hj, hp'⟩ := List.mem_flatMap.1 (hperm.subset hp)
    rw [List.eq_of_mem_replicate hp', hmv]; exact (hq R hRM j hj).1
  -- all dots move up to the top
  obtain ⟨Y', hY1, hY2, hY3, hY4⟩ := (dotBase_tStart cs μ a).dots_up ds' [] []
    (s.map Prod.snd) (by rw [List.nil_append, htm, hfoldb, hvab]) (by simpa using hfit')
    (by simpa using (hd4).2 hdok) (by simp)
  simp only [List.nil_append, htm, hstb] at hY2 hY3 hY4
  have hlenP : P.length = s.length := hiso.length_eq
  -- the strands reached are those of the left ends of the dots `is`
  have hY3' : (Y'.map (idD P)).Perm
      ((leftEnds₂ a R).flatMap fun j => List.replicate (n j) (idD P j)) := by
    have e1 : dotIds (tRun flipL 0 (tStart a) []) ds' = (dotPts ds).map fun p =>
        tRen a.length (tRun flipL a.length (tStart a) (R.take p.1)) (R.drop p.1)
          (idD (tRun flipL a.length (tStart a) (R.take p.1)).st (a.length + p.2)) := by
      rw [← hmv]; exact dotIds_shiftD a.length ds (tStart a)
    rw [e1] at hY3
    refine hY3.trans ((hperm.map _).trans ?_)
    rw [List.map_flatMap]
    refine List.Perm.of_eq (List.flatMap_congr fun j hj => ?_)
    rw [List.map_replicate, (hq R hRM j hj).2]
  classical
  let f : ℕ → ℕ := fun x => if h : ∃ j, IsLeftEnd s j ∧ idD P j = x then Classical.choose h else 0
  have hf : ∀ y, y < P.length → (∃ j, IsLeftEnd s j ∧ idD P j = idD P y) →
      f (idD P y) = lEnd s y := by
    intro y hy hex
    simp only [f, hex, ↓reduceDIte]
    have := Classical.choose_spec hex
    exact (lEnd_eq_of_idD hv hiso hy this.1 this.2.symm).symm
  have hLj : ∀ j ∈ leftEnds₂ a R, IsLeftEnd s j := fun j hj =>
    (isLeftEnd_iso hiso).1 (mem_leftEnds₂.1 hj)
  have hYl : (Y'.map (lEnd s)).Perm (is.map (lEnd s)) := by
    have e2 : Y'.map (lEnd s) = (Y'.map (idD P)).map f := by
      rw [List.map_map]
      refine List.map_congr_left fun y hy => ?_
      have hm := hY3'.subset (List.mem_map_of_mem hy)
      obtain ⟨j, hj, hj'⟩ := List.mem_flatMap.1 hm
      exact (hf y (hY2 y hy) ⟨j, hLj j hj, (List.eq_of_mem_replicate hj').symm⟩).symm
    have e3 : ((leftEnds₂ a R).flatMap fun j => List.replicate (n j) (idD P j)).map f =
        (leftEnds₂ a R).flatMap fun j => List.replicate (n j) j := by
      rw [List.map_flatMap]
      refine List.flatMap_congr fun j hj => ?_
      have hjP : j < P.length := by rw [hlenP]; exact (hLj j hj).1
      rw [List.map_replicate, hf j hjP ⟨j, hLj j hj, rfl⟩,
        lEnd_eq_of_isLeftEnd hv (hLj j hj) (Or.inl rfl)]
    rw [e2]
    refine ((hY3'.map f).trans (List.Perm.of_eq e3)).trans ?_
    refine (perm_flatMap_count (nodup_leftEnds₂ a R) ?_).symm
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    exact mem_leftEnds₂.2 ((isLeftEnd_iso hiso).2 (isLeftEnd_lEnd hv (his i hi)))
  have hYlen : Y'.length = is.length := by simpa using hYl.length_eq
  have hYb : ∀ y ∈ Y', y < s.length := fun y hy => hlenP ▸ hY2 y hy
  -- the chain of moves
  set t := s.map Prod.snd with ht
  set S := LtL D Sc cs μ [] t c ⊔ (FewerDots cs μ s is.length ⊔
    DecSpan cs μ (dualW a ++ a) (cupA (dualW a)) Rb t N)
  have hP := xChain_chordLay_canon hv hl
  have hLF : LtL D Sc cs μ [] t c ≤ S := le_sup_left
  have hFD : FewerDots cs μ s is.length ≤ S := le_sup_left.trans le_sup_right
  have hDS : DecSpan cs μ (dualW a ++ a) (cupA (dualW a)) Rb t N ≤ S :=
    le_sup_right.trans le_sup_right
  have h01 : SignRel S (xev cs μ [] t (chordLay [] (canon s) ++ dotsOn t is))
      (xev cs μ [] t (chordLay [] (canon s) ++ dotsOn t (is.map (lEnd s)))) := by
    have := dots_to_lEnd (cs := cs) μ hv hl is [] (by simpa using his)
    simp only [List.append_nil, List.length_nil, add_zero, hc] at this
    exact this.mono (sup_le hLF hFD)
  have h12 : SignRel S (xev cs μ [] t (chordLay [] (canon s) ++ dotsOn t (is.map (lEnd s))))
      (xev cs μ [] t (chordLay [] (canon s) ++ dotsOn t (Y'.map (lEnd s)))) := by
    have := dotsOn_perm (cs := cs) (ν := μ) (t₀ := t) (n := c) (t := t) hYl.symm
      (by intro x hx; obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
          simpa [t] using lEnd_lt (his i hi))
      (chordLay [] (canon s)) [] hP
    simpa only [List.append_nil] using this.signRel.mono hLF
  have h23 : SignRel S (xev cs μ [] t (chordLay [] (canon s) ++ dotsOn t (Y'.map (lEnd s))))
      (xev cs μ [] t (chordLay [] (canon s) ++ dotsOn t Y')) := by
    have := dots_to_lEnd (cs := cs) μ hv hl Y' [] (by simpa using hYb)
    simp only [List.append_nil, List.length_nil, add_zero, hc, hYlen] at this
    exact this.symm.mono (sup_le hLF hFD)
  have hXB : XChain [] (cupA (dualW a) ++ (tLay a R).map (xwhL (dualW a) [])) t := by
    have := xChain_bendF hXb; rwa [hvab] at this
  have h34 : SignRel S (xev cs μ [] t (chordLay [] (canon s) ++ dotsOn t Y'))
      (xev cs μ [] t (cupA (dualW a) ++ (tLay a R).map (xwhL (dualW a) []) ++ dotsOn t Y')) := by
    have := hNF.append_right (t := t) hXB hP (dotsOn t Y')
    rw [xcnt_dotsOn, add_zero] at this
    exact this.symm.signRel.mono hLF
  have h45 : SignRel S
      (xev cs μ [] t (cupA (dualW a) ++ (tLay a R).map (xwhL (dualW a) []) ++ dotsOn t Y'))
      (xev cs μ [] t (cupA (dualW a) ++ dLay (dualW a ++ a) ds')) := by
    have := hY4.symm
    simp only [tLay, List.append_nil, List.foldl_nil, dotsOn_nil, List.length_nil, add_zero,
      xcnt_cupA, zero_add, hncrb, hnc, htLayb] at this
    refine this.mono (sup_le hLF (le_trans (decSpan_mono ?_) hDS))
    omega
  have hchain := h01.trans (h12.trans (h23.trans (h34.trans h45)))
  refine hchain.comp_mem ?_ (hfam R hRM n hβ)
  intro x hx
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
  obtain ⟨z₁, hz₁, z₂, hz₂, rfl⟩ := Submodule.mem_sup.1 hz
  rw [Preadditive.add_comp, Preadditive.add_comp]
  refine Submodule.add_mem _ (hlow (ltL_comp_bubAt hy hβ)) (Submodule.add_mem _ ?_ ?_)
  · exact fewerDots_comp_bubAt_mem hβ (fun js hjs hlt _ hγ =>
      hC hv hl rfl hc js hjs (by omega) hγ) hz₁
  · exact hA hv hl rfl hc R hRM hiso (decSpan_comp_bubAt hβ hz₂)

include hM hvab hlow in
/-- **The bent decorated diagrams with dots, step**: given the canonical diagrams with at most `N`
dots and the bent decorated diagrams with fewer than `N` dots, the bent decorated diagrams with
at most `N` dots lie in `T`. -/
theorem decSpan_le_step (N : ℕ)
    (hC : ∀ {s : List (ℕ × Letter I)}, Valid s → Lettered flipL s → s.map Prod.snd = v →
      ncr (canon s) = c → ∀ (is : List ℕ), (∀ i ∈ is, i < s.length) → is.length ≤ N →
      ∀ {β : (pres D Sc).obj (ob D μ []) ⟶ (pres D Sc).obj (ob D μ [])}, IsBubbleProd cs μ β →
      xev cs μ [] v (chordLay [] (canon s) ++ dotsOn v is) ≫ bubAt D Sc μ v β ∈ T)
    (hA : ∀ {s : List (ℕ × Letter I)}, Valid s → Lettered flipL s → s.map Prod.snd = v →
      ncr (canon s) = c → ∀ R ∈ M, Iso (pairing₂ a R) s →
      DecSpan cs μ (dualW a ++ a) (cupA (dualW a)) (R.map (shiftT a.length)) v N ≤ T) :
    ∀ {s : List (ℕ × Letter I)}, Valid s → Lettered flipL s → s.map Prod.snd = v →
      ncr (canon s) = c → ∀ R ∈ M, Iso (pairing₂ a R) s →
      DecSpan cs μ (dualW a ++ a) (cupA (dualW a)) (R.map (shiftT a.length)) v (N + 1) ≤ T := by
  intro s hv hl hsv hc R hRM hiso
  refine Submodule.span_le.2 ?_
  rintro _ ⟨ds, Z, β, hmv, hok, hZ, hcnt, hβ, rfl⟩
  subst hsv
  obtain ⟨hR, hred⟩ := hM R hRM
  obtain ⟨-, hnc, hNF⟩ := reduced₂_bent_normal_form cs μ hR hred
  rw [Chord.canon_eq_of_iso hiso, hc] at hnc
  rw [Chord.canon_eq_of_iso hiso, hnc, hvab] at hNF
  obtain ⟨hfitb, hfoldb, htLayb, hXb, hstb, hncrb⟩ := matching_bent_spec hR
  set t := s.map Prod.snd with ht
  obtain ⟨Y', hY1, hY2, -, hY4⟩ := (dotBase_tStart cs μ a).dots_up ds [] Z t
    (by rw [List.nil_append, hmv, hfoldb, hvab]) (by rw [List.nil_append, hmv]; exact hfitb)
    (by simpa using hok) hZ
  simp only [List.nil_append, hmv, hstb] at hY2 hY4
  have hlenP : (pairing₂ a R).length = s.length := hiso.length_eq
  set S := LtL D Sc cs μ [] t c ⊔
    DecSpan cs μ (dualW a ++ a) (cupA (dualW a)) (R.map (shiftT a.length)) t N
  have hXB : XChain [] (cupA (dualW a) ++ (tLay a R).map (xwhL (dualW a) [])) t := by
    have := xChain_bendF hXb; rwa [hvab] at this
  have h1 : SignRel S (xev cs μ [] t (cupA (dualW a) ++ dLay (dualW a ++ a) ds ++ dotsOn t Z))
      (xev cs μ [] t (cupA (dualW a) ++ (tLay a R).map (xwhL (dualW a) []) ++
        dotsOn t (Y' ++ Z))) := by
    simp only [tLay, List.append_nil, List.foldl_nil, xcnt_cupA, zero_add, hncrb, hnc,
      htLayb] at hY4
    exact hY4.mono (sup_le_sup le_rfl (decSpan_mono (by omega)))
  have h2 : SignRel S (xev cs μ [] t (cupA (dualW a) ++ (tLay a R).map (xwhL (dualW a) []) ++
        dotsOn t (Y' ++ Z)))
      (xev cs μ [] t (chordLay [] (canon s) ++ dotsOn t (Y' ++ Z))) := by
    have := hNF.append_right (t := t) hXB (xChain_chordLay_canon hv hl) (dotsOn t (Y' ++ Z))
    rw [xcnt_dotsOn, add_zero] at this
    exact this.signRel.mono le_sup_left
  refine (h1.trans h2).comp_mem ?_ (hC hv hl rfl hc (Y' ++ Z) ?_ ?_ hβ)
  · intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    rw [Preadditive.add_comp]
    exact Submodule.add_mem _ (hlow (ltL_comp_bubAt hy hβ))
      (hA hv hl rfl hc R hRM hiso (decSpan_comp_bubAt hβ hz))
  · intro y hy
    rcases List.mem_append.1 hy with hy | hy
    · exact hlenP ▸ hY2 y hy
    · simpa [t] using hZ y hy
  · rw [List.length_append, hY1]; omega

include hM hrep hq hσ hvab hfam hlow in
/-- **The triangular step of [BE2] Theorem 8.1** (KL III, proof of Proposition 3.11): if `T`
contains the bent decorated matchings and the diagrams with fewer than `c` crossings, then it
contains the canonical diagrams with `c` crossings and any dots, and the bent decorated diagrams
with their moves, by induction on the number of dots. -/
theorem canon_dots_mem_decorated₂ : ∀ N : ℕ,
    (∀ {s : List (ℕ × Letter I)}, Valid s → Lettered flipL s → s.map Prod.snd = v →
      ncr (canon s) = c → ∀ (is : List ℕ), (∀ i ∈ is, i < s.length) → is.length < N →
      ∀ {β : (pres D Sc).obj (ob D μ []) ⟶ (pres D Sc).obj (ob D μ [])}, IsBubbleProd cs μ β →
      xev cs μ [] v (chordLay [] (canon s) ++ dotsOn v is) ≫ bubAt D Sc μ v β ∈ T) ∧
    (∀ {s : List (ℕ × Letter I)}, Valid s → Lettered flipL s → s.map Prod.snd = v →
      ncr (canon s) = c → ∀ R ∈ M, Iso (pairing₂ a R) s →
      DecSpan cs μ (dualW a ++ a) (cupA (dualW a)) (R.map (shiftT a.length)) v N ≤ T)
  | 0 => ⟨fun _ _ _ _ _ _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ _ _ _ _ =>
      Submodule.span_le.2 fun _ ⟨_, _, _, _, _, _, h, _⟩ => absurd h (Nat.not_lt_zero _)⟩
  | N + 1 => by
    obtain ⟨hC, hA⟩ := canon_dots_mem_decorated₂ N
    exact ⟨fun hv hl hsv hc is his hlt _ hβ => canon_dots_mem_step μ a b M hM hrep q hq σ hσ v
        hvab T hfam c hlow N hC hA hv hl hsv hc is his (by omega) hβ,
      decSpan_le_step μ a b M hM v hvab T c hlow N (fun hv hl hsv hc is his hle _ hβ =>
        canon_dots_mem_step μ a b M hM hrep q hq σ hσ v hvab T hfam c hlow N hC hA hv hl hsv hc is
          his hle hβ) hA⟩

end Step

/-! ## Theorem 8.1 -/

section Theorem

open DTMove

/-- **A bent decorated matching lies in the span, bent back.** -/
theorem bendF_mem_comap_bendG (μ : X) (a b : List (Letter I)) {𝒞 : Set (List (XLayer I))}
    {A : List (XLayer I)} (hA𝒞 : A ∈ 𝒞) (hA : XChain a A b)
    {β : (pres D Sc).obj (ob D μ []) ⟶ (pres D Sc).obj (ob D μ [])} (hβ : IsBubbleProd cs μ β) :
    xev cs μ [] (dualW a ++ b) (cupA (dualW a) ++ A.map (xwhL (dualW a) [])) ≫
        bubAt D Sc μ (dualW a ++ b) β ∈
      (diagBubSpan D Sc cs μ a b 𝒞).comap (bendG cs μ a b) := by
  obtain ⟨p, hp⟩ := hβ.exists_mem
  have hC := xChain_bendF hA
  rw [Submodule.mem_comap, bendG_xev_comp_bubAt cs μ hC hp]
  have e : xev cs μ a b (bendL a b (cupA (dualW a) ++ A.map (xwhL (dualW a) []))) =
      zsign k (pairPar D μ (dualW a) + cupsPar D μ (dualW a) * xpar D μ A) • xev cs μ a b A := by
    rw [← bendG_bendF_xev cs μ hA, bendF_xev cs μ hA, bendG_xev cs μ hC]
    rfl
  rw [e, Linear.smul_comp]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _
    (Submodule.subset_span ⟨A, hA𝒞, β, hβ.isBub, rfl⟩))

variable (μ : X) (a b : List (Letter I)) (M : Set (List (TMove (Letter I))))
  (hM : ∀ R ∈ M, IsMatching₂ a b R ∧ Reduced₂ a R)
  (hrep : ∀ s : List (ℕ × Letter I), Valid s → Lettered flipL s →
    s.map Prod.snd = dualW a ++ b → ∃ R ∈ M, Iso (pairing₂ a R) s)
  (q : List (TMove (Letter I)) → ℕ → ℕ × ℕ)
  (hq : ∀ R ∈ M, ∀ j ∈ leftEnds₂ a R, OnStrand₂ a R j (q R j))
  (σ : List (TMove (Letter I)) → (ℕ → ℕ) → List (DTMove I))
  (hσ : ∀ R ∈ M, ∀ n, Decorates₂ a R (q R) n (σ R n))

include hM hrep hq hσ in
/-- **[BE2] Theorem 8.1, for any bottom boundary**, for any set of reduced matchings representing
every pairing, any distinguished points, and any order of the dots at one height.

Let `M` be a set of reduced `(a, b)`-matchings (`IsMatching₂ a b R`, `Reduced₂ a R`) such that
every pairing of `a* b` (a valid lettered chord state, `Valid`, `Lettered flipL`) is the pairing of
some `R ∈ M` (`Iso`). For each `R ∈ M` let `q R j` be a distinguished point on the strand with left
endpoint `j` (`OnStrand₂`), and for counts `n` let `σ R n` be a decorated matching with `n j` dots
at `q R j` (`Decorates₂`). Then the 2-morphisms `dLay a (σ R n) : E_a 1_λ → E_b 1_λ` generate
`Hom(E_a 1_λ, E_b 1_λ)` as a right `SYM`-module, `SYM` acting through `β_λ` in the rightmost
region (`diagBubSpan`).

Matchings are encoded by generic layerings (a sequence of cups, crossings and caps); every planar
matching has such layerings, and they differ by the super interchange law, i.e. by signs.

Compared with the printed statement:
* `Reduced₂` asks that no strand crosses itself and two strands cross at most once, but not that
  every strand has exactly one critical point; this allows more matchings in `M` (the statement is
  more general).
* The hypothesis on `M` is that it represents every *pairing* of `a* b`, rather than every
  equivalence class of reduced matchings; the form of the paper is `theorem_8_1`, using that every
  pairing is the pairing of a reduced matching (`exists_reduced_matching`).
* `M` need not consist of pairwise inequivalent matchings, and for each `R` and `n` any decorated
  matching with the prescribed dots may be chosen, in particular with the dots at one height in any
  order (both only make the statement more general); `wt(a) = wt(b)` is not needed. -/
theorem theorem_8_1_of_pairings :
    diagBubSpan D Sc cs μ a b (decoratedFamily₂ a M σ) = ⊤ := by
  set T := diagBubSpan D Sc cs μ a b (decoratedFamily₂ a M σ)
  have hfam : ∀ R ∈ M, ∀ n, ∀ {β : (pres D Sc).obj (ob D μ []) ⟶ (pres D Sc).obj (ob D μ [])},
      IsBubbleProd cs μ β → xev cs μ [] (dualW a ++ b) (cupA (dualW a) ++
        dLay (dualW a ++ a) ((σ R n).map (shiftD a.length))) ≫
          bubAt D Sc μ (dualW a ++ b) β ∈ T.comap (bendG cs μ a b) := by
    intro R hRM n β hβ
    obtain ⟨hR, -⟩ := hM R hRM
    obtain ⟨hmv, -⟩ := hσ R hRM n
    obtain ⟨hfitb, -⟩ := matching_bent_spec hR
    obtain ⟨h1, h2, -, -⟩ := shiftD_spec (dualW a) a.length (length_dualW a) (σ R n)
      (tStart_letters a) (by rw [tmoves_map_shiftD, hmv]; exact hfitb)
    rw [h1]
    rw [hmv, hR.2] at h2
    exact bendF_mem_comap_bendG μ a b (𝒞 := decoratedFamily₂ a M σ) ⟨R, hRM, n, rfl⟩ h2 hβ
  have hT' : T.comap (bendG cs μ a b) = ⊤ :=
    eq_top_of_canon_dots_mem cs μ (dualW a ++ b) _ fun c hlow _ hv hl hsv hc is his _ hβ =>
      (canon_dots_mem_decorated₂ μ a b M hM hrep q hq σ hσ (dualW a ++ b) rfl _ hfam c hlow
        (is.length + 1)).1 hv hl hsv hc is his (Nat.lt_succ_self _) hβ
  exact eq_top_of_cl_mem fun L _ => Submodule.map_comap_le _ _
    (mem_map_bendG_of_bendF_mem cs μ (cl_mem_homPar' μ a b L) (by rw [hT']; trivial))

end Theorem

end OddMath.SKM
