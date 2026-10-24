import OddMath.SKM.Nondegeneracy

/-!
# Finite open-dot normalization for a chosen matching family

Supporting calculation for the BE2 nondegeneracy conjecture. The filtered image
retains finite abstract-SYM source coefficients with strictly smaller crossing
count or equal crossing count and strictly fewer open dots. The decorated-error
clause concerns skeletons belonging to the chosen family. This does not construct
a signed comparison between two families or an inverse coefficient transition.
-/

noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Presentation
open StringDiagrams.Chord (Move Iso TMove TState tStep tRun TFits ncr₂ idD Same Valid Lettered canon idAt)
open DTMove
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]
  {Sc : Scalars D k} {cs : CScalars Sc}

theorem strand_count_sum {a : List (Letter I)} {R : List (TMove (Letter I))}
    {s : List (ℕ × Letter I)} (hv : Valid s) (hiso : Iso (pairing₂ a R) s)
    (is : List ℕ) (his : ∀ i ∈ is, i < s.length) :
    (∑ j : MatchingStrand a R, (is.map (lEnd s)).count j.val) = is.length := by
  classical
  rw [← Finset.sum_subtype (leftEnds₂ a R).toFinset (by intro j; exact List.mem_toFinset)
    (fun j => (is.map (lEnd s)).count j)]
  have hm : ∀ j ∈ (is.map (lEnd s) : Multiset ℕ), j ∈ (leftEnds₂ a R).toFinset := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hj
    exact List.mem_toFinset.2 (mem_leftEnds₂.2
      ((isLeftEnd_iso hiso).2 (isLeftEnd_lEnd hv (his i hi))))
  simpa using Multiset.sum_count_eq_card hm

section Bounded
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
  (c : ℕ)
  (N : ℕ)
  (hfam : ∀ R ∈ M, ncr₂ R = c → ∀ n, (∑ j : MatchingStrand a R, n j) ≤ N →
    ∀ {β : (pres D Sc).obj (ob D μ []) ⟶ (pres D Sc).obj (ob D μ [])},
    IsBubbleProd cs μ β → xev cs μ [] v (cupA (dualW a) ++
      dLay (dualW a ++ a) ((σ R n).map (shiftD a.length))) ≫ bubAt D Sc μ v β ∈ T)
  (hlow : LtL D Sc cs μ [] v c ≤ T)

include hM hrep hq hσ hvab hfam hlow in
theorem canon_dots_mem_step_bounded
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
  obtain ⟨-, hnc, -⟩ := reduced₂_bent_normal_form cs μ hR hred
  rw [Chord.canon_eq_of_iso hiso, hc] at hnc
  have hchain := canon_dots_signRel_decorated₂ (cs := cs) μ a b R hR hred
    (q R) (hq R hRM) (σ R) (hσ R hRM) hvab c hv hl hc hiso is his
  refine hchain.comp_mem ?_ (hfam R hRM hnc _ (by rw [strand_count_sum hv hiso is his]; exact hN) hβ)
  intro x hx
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
  obtain ⟨z₁, hz₁, z₂, hz₂, rfl⟩ := Submodule.mem_sup.1 hz
  rw [Preadditive.add_comp, Preadditive.add_comp]
  refine Submodule.add_mem _ (hlow (ltL_comp_bubAt hy hβ)) (Submodule.add_mem _ ?_ ?_)
  · exact fewerDots_comp_bubAt_mem hβ (fun js hjs hlt _ hγ =>
      hC hv hl rfl hc js hjs (by omega) hγ) hz₁
  · exact hA hv hl rfl hc R hRM hiso (decSpan_mono hN (decSpan_comp_bubAt hβ hz₂))
end Bounded

section Recursion
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
  (c : ℕ)
  (K : ℕ)
  (hfam : ∀ R ∈ M, ncr₂ R = c → ∀ n, (∑ j : MatchingStrand a R, n j) < K →
    ∀ {β : (pres D Sc).obj (ob D μ []) ⟶ (pres D Sc).obj (ob D μ [])},
    IsBubbleProd cs μ β → xev cs μ [] v (cupA (dualW a) ++
      dLay (dualW a ++ a) ((σ R n).map (shiftD a.length))) ≫ bubAt D Sc μ v β ∈ T)
  (hlow : LtL D Sc cs μ [] v c ≤ T)
include hM hrep hq hσ hvab hfam hlow in
theorem canon_dots_mem_bounded : ∀ N : ℕ, N ≤ K →
    (∀ {s : List (ℕ × Letter I)}, Valid s → Lettered flipL s → s.map Prod.snd = v →
      ncr (canon s) = c → ∀ (is : List ℕ), (∀ i ∈ is, i < s.length) → is.length < N →
      ∀ {β : (pres D Sc).obj (ob D μ []) ⟶ (pres D Sc).obj (ob D μ [])}, IsBubbleProd cs μ β →
      xev cs μ [] v (chordLay [] (canon s) ++ dotsOn v is) ≫ bubAt D Sc μ v β ∈ T) ∧
    (∀ {s : List (ℕ × Letter I)}, Valid s → Lettered flipL s → s.map Prod.snd = v →
      ncr (canon s) = c → ∀ R ∈ M, Iso (pairing₂ a R) s →
      DecSpan cs μ (dualW a ++ a) (cupA (dualW a)) (R.map (shiftT a.length)) v N ≤ T)
  | 0, _ => ⟨fun _ _ _ _ _ _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ _ _ _ _ =>
      Submodule.span_le.2 fun _ ⟨_, _, _, _, _, _, h, _⟩ => absurd h (Nat.not_lt_zero _)⟩
  | N + 1, hNK => by
    obtain ⟨hC, hA⟩ := canon_dots_mem_bounded N (by omega)
    exact ⟨fun hv hl hsv hc is his hlt _ hβ => canon_dots_mem_step_bounded μ a b M hM hrep q hq σ hσ v
        hvab T c N (fun R hR hc n hn => hfam R hR hc n (by omega)) hlow hC hA hv hl hsv hc is his (by omega) hβ,
      decSpan_le_step μ a b M hM v hvab T c hlow N (fun hv hl hsv hc is his hle _ hβ =>
        canon_dots_mem_step_bounded μ a b M hM hrep q hq σ hσ v hvab T c N (fun R hR hc n hn => hfam R hR hc n (by omega)) hlow hC hA hv hl hsv hc is
          his hle hβ) hA⟩
end Recursion

namespace MatchingBasisChoice
variable {a b : List (Letter I)} (cs : CScalars Sc) (μ : X)

def openDots (F : MatchingBasisChoice a b) (t : F.Labels) : ℕ := ∑ j, t.2 j

def dotBound (F : MatchingBasisChoice a b) (c N : ℕ) (t : F.Labels) : Prop :=
  ncr₂ t.1.val < c ∨ (ncr₂ t.1.val = c ∧ F.openDots t < N)

theorem filtered_span_le (F : MatchingBasisChoice a b) (P : F.Labels → Prop) :
    diagBubSpan D Sc cs μ a b {L | ∃ t, P t ∧ F.layers t = L} ≤
      (Finsupp.supported (SYM D k) k {t | P t}).map (F.expansion cs μ) := by
  classical
  refine Submodule.span_le.2 ?_
  rintro _ ⟨_, ⟨t, ht, rfl⟩, β, hβ, rfl⟩
  obtain ⟨γ, hγ, eγ⟩ := bubble_swap cs μ (xev_mem_homPar cs μ a b (F.layers t)) hβ
  rw [eγ]
  have hγ' : (γ : End _) ∈ (betaSYM cs μ).range := by
    rw [betaSYM_range]
    exact hγ
  obtain ⟨p, rfl⟩ := hγ'
  exact ⟨Finsupp.single t p, Finsupp.single_mem_supported k p ht,
    F.expansion_single cs μ t p⟩

/-- Simultaneous strict open-dot normalization, after bending back to the original boundary.
The same-crossing stratum has strictly fewer than N actual open dots; lower crossings
have no dot restriction. The target family remains complete throughout the recursion. -/
theorem bounded_errors_mem (F : MatchingBasisChoice a b) (c N : ℕ) :
    let T := ((Finsupp.supported (SYM D k) k {t | F.dotBound c N t}).map
      (F.expansion cs μ)).comap (bendG cs μ a b)
    (∀ {s : List (ℕ × Letter I)}, Valid s → Lettered flipL s →
      s.map Prod.snd = dualW a ++ b → ncr (canon s) = c →
      ∀ is : List ℕ, (∀ i ∈ is, i < s.length) → is.length < N →
      ∀ {β : End ((pres D Sc).obj (ob D μ []))}, IsBubbleProd cs μ β →
      xev cs μ [] (dualW a ++ b)
        (chordLay [] (canon s) ++ dotsOn (dualW a ++ b) is) ≫
        bubAt D Sc μ (dualW a ++ b) β ∈ T) ∧
    (∀ {s : List (ℕ × Letter I)}, Valid s → Lettered flipL s →
      s.map Prod.snd = dualW a ++ b → ncr (canon s) = c →
      ∀ R ∈ F.members, Iso (pairing₂ a R) s →
      DecSpan cs μ (dualW a ++ a) (cupA (dualW a))
        (R.map (shiftT a.length)) (dualW a ++ b) N ≤ T) := by
  classical
  let P := F.dotBound c N
  let S := (Finsupp.supported (SYM D k) k {t | P t}).map (F.expansion cs μ)
  let T := S.comap (bendG cs μ a b)
  have hlow : LtL D Sc cs μ [] (dualW a ++ b) c ≤ T := by
    intro f hf
    obtain ⟨z, hz, hs⟩ := F.exists_expansion_of_mem_ltL cs μ (bendG_mem_ltL μ hf)
    exact ⟨z, (Finsupp.mem_supported k z).2 (fun t ht => Or.inl (hs t ht)), hz⟩
  have hfam : ∀ R ∈ F.members, ncr₂ R = c → ∀ n : ℕ → ℕ,
      (∑ j : MatchingStrand a R, n j) < N →
      ∀ {β : End ((pres D Sc).obj (ob D μ []))}, IsBubbleProd cs μ β →
      xev cs μ [] (dualW a ++ b) (cupA (dualW a) ++
        dLay (dualW a ++ a) ((F.ambientSerializer R n).map (shiftD a.length))) ≫
        bubAt D Sc μ (dualW a ++ b) β ∈ T := by
    intro R hRM hc n hn β hβ
    let t : F.Labels := ⟨⟨R, hRM⟩, fun j => n j⟩
    have ht : P t := Or.inr ⟨hc, hn⟩
    obtain ⟨hR, -⟩ := F.matching R hRM
    obtain ⟨hmv, -⟩ := F.ambient_decorates R hRM n
    obtain ⟨hfitb, -⟩ := matching_bent_spec hR
    obtain ⟨h1, h2, -, -⟩ := shiftD_spec (dualW a) a.length (length_dualW a)
      (F.ambientSerializer R n) (tStart_letters a)
      (by rw [tmoves_map_shiftD, hmv]; exact hfitb)
    rw [h1]
    rw [hmv, hR.2] at h2
    apply F.filtered_span_le cs μ P
    apply bendF_mem_comap_bendG μ a b
      (𝒞 := {L | ∃ t, P t ∧ F.layers t = L}) ?_ h2 hβ
    exact ⟨t, ht, by simp [t, layers, ambientSerializer, hRM]⟩
  exact canon_dots_mem_bounded μ a b F.members
    (fun R hR => ⟨(F.matching R hR).1, (F.matching R hR).2.1⟩)
    (fun s hv hl hs => by
      obtain ⟨R', hR', hred, hiso⟩ := exists_strictReduced_matching hv hl hs
      obtain ⟨R, hRM, hR⟩ := F.complete R' hR' hred
      exact ⟨R, hRM, hR.trans hiso⟩)
    F.ambientPoints
    (fun R hR j hj => by
      simpa only [ambientPoints, dite_eq_left hR] using F.onStrand ⟨R, hR⟩ j hj)
    F.ambientSerializer F.ambient_decorates (dualW a ++ b) rfl T c N hfam hlow N le_rfl
end MatchingBasisChoice
end OddMath.SKM
#print axioms OddMath.SKM.MatchingBasisChoice.bounded_errors_mem
