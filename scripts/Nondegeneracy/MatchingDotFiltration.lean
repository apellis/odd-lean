import OddMath.SKM.Nondegeneracy

/-!
# Finite open-dot normalization for a chosen matching family

Supporting calculation for the BE2 nondegeneracy conjecture. The filtered image
retains finite abstract-SYM source coefficients with strictly smaller crossing
count or equal crossing count and strictly fewer open dots. The original simultaneous
recursion treats the chosen family; a second induction extends the decorated-error
bound to every reduced skeleton. This does not construct a signed comparison
between two families or an inverse coefficient transition.
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

/-- Realize every strand multiplicity by dots placed at canonical left endpoints. -/
theorem exists_canonical_strand_dots {a : List (Letter I)}
    {R : List (TMove (Letter I))} {s : List (ℕ × Letter I)}
    (hv : Valid s) (hi : Iso (pairing₂ a R) s) (n : MatchingStrand a R → ℕ) :
    ∃ is : List ℕ, (∀ i ∈ is, i < s.length) ∧
      (∀ j : MatchingStrand a R, (is.map (lEnd s)).count j.val = n j) ∧
      is.length = ∑ j, n j := by
  classical
  let is := (leftEnds₂ a R).flatMap fun j => List.replicate (strandCounts n j) j
  have hmem : ∀ i ∈ is, i ∈ leftEnds₂ a R := by
    intro i h
    obtain ⟨j, hj, hij⟩ := List.mem_flatMap.mp h
    exact (List.eq_of_mem_replicate hij) ▸ hj
  have hleft : ∀ j ∈ leftEnds₂ a R, IsLeftEnd s j := fun j hj =>
    (isLeftEnd_iso hi).mp (mem_leftEnds₂.mp hj)
  have hvalid : ∀ i ∈ is, i < s.length := fun i hi => (hleft i (hmem i hi)).1
  have hmap : is.map (lEnd s) = is := by
    calc
      is.map (lEnd s) = is.map id := List.map_congr_left fun i hi =>
        lEnd_eq_of_isLeftEnd hv (hleft i (hmem i hi)) (Or.inl rfl)
      _ = is := List.map_id is
  have hcount : ∀ (K : List ℕ), K.Nodup → ∀ j,
      (K.flatMap fun i => List.replicate (strandCounts n i) i).count j =
        if j ∈ K then strandCounts n j else 0 := by
    intro K hK j
    induction K with
    | nil => simp
    | cons i K ih =>
      rw [List.flatMap_cons, List.count_append, ih (List.nodup_cons.mp hK).2,
        List.count_replicate]
      by_cases hij : i = j
      · subst i
        simp [(List.nodup_cons.mp hK).1]
      · simp [hij, Ne.symm hij]
  have hn : ∀ j : MatchingStrand a R, (is.map (lEnd s)).count j.val = n j := by
    intro j
    rw [hmap, hcount _ (nodup_leftEnds₂ a R)]
    simp [j.property]
  refine ⟨is, hvalid, hn, ?_⟩
  rw [← strand_count_sum hv hi is hvalid]
  exact Finset.sum_congr rfl fun j _ => hn j

/-- Retain the canonical leading sign while absorbing all three error sectors
into a specified target submodule. The target may come from another family. -/
theorem canon_dots_signRel_of_bounds
    (μ : X) (a b : List (Letter I)) (R : List (TMove (Letter I)))
    (hR : IsMatching₂ a b R) (hred : Reduced₂ a R)
    (q : ℕ → ℕ × ℕ) (hq : ∀ j ∈ leftEnds₂ a R, OnStrand₂ a R j (q j))
    (σ : (ℕ → ℕ) → List (DTMove I)) (hσ : ∀ n, Decorates₂ a R q n (σ n))
    (v : List (Letter I)) (hvab : dualW a ++ b = v)
    (T : Submodule k ((pres D Sc).obj (ob D μ []) ⟶ (pres D Sc).obj (ob D μ v)))
    (c : ℕ) {s : List (ℕ × Letter I)} (hv : Valid s) (hl : Lettered flipL s)
    (hs : s.map Prod.snd = v) (hc : ncr (canon s) = c) (hi : Iso (pairing₂ a R) s)
    (is : List ℕ) (his : ∀ i ∈ is, i < s.length)
    (hlo : LtL D Sc cs μ [] v c ≤ T)
    (hC : ∀ js : List ℕ, (∀ i ∈ js, i < s.length) → js.length < is.length →
      ∀ {β : End ((pres D Sc).obj (ob D μ []))}, IsBubbleProd cs μ β →
      xev cs μ [] v (chordLay [] (canon s) ++ dotsOn v js) ≫ bubAt D Sc μ v β ∈ T)
    (hD : DecSpan cs μ (dualW a ++ a) (cupA (dualW a))
      (R.map (shiftT a.length)) v is.length ≤ T) :
    SignRel T (xev cs μ [] v (chordLay [] (canon s) ++ dotsOn v is))
      (xev cs μ [] v (cupA (dualW a) ++ dLay (dualW a ++ a)
        ((σ (fun j => (is.map (lEnd s)).count j)).map (shiftD a.length)))) := by
  subst hs
  apply (canon_dots_signRel_decorated₂ μ a b R hR hred q hq σ hσ hvab c hv hl hc hi is his).mono
  refine sup_le hlo (sup_le ?_ hD)
  refine Submodule.span_le.mpr ?_
  rintro x ⟨js, β, hjs, hlen, hβ, rfl⟩
  exact hC js hjs hlen hβ

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

/-- The unique representative of a source matching class in another complete choice. -/
def representativeIn (F G : MatchingBasisChoice a b) (R : F.members) : G.members :=
  ⟨(G.complete R.val (F.matching R.val R.property).1
    (F.matching R.val R.property).2).choose,
    (G.complete R.val (F.matching R.val R.property).1
      (F.matching R.val R.property).2).choose_spec.1⟩

theorem representativeIn_iso (F G : MatchingBasisChoice a b) (R : F.members) :
    Iso (pairing₂ a R.val) (pairing₂ a (F.representativeIn G R).val) :=
  (G.complete R.val (F.matching R.val R.property).1
    (F.matching R.val R.property).2).choose_spec.2.symm

/-- Choices have the same finite-endpoint matching classes, without identifying serializers. -/
def representativesEquiv (F G : MatchingBasisChoice a b) : F.members ≃ G.members where
  toFun := F.representativeIn G
  invFun := G.representativeIn F
  left_inv R := Subtype.ext (F.unique _ (G.representativeIn F _).property _ R.property
    ((G.representativeIn_iso F _).symm.trans (F.representativeIn_iso G R).symm))
  right_inv R := Subtype.ext (G.unique _ (F.representativeIn G _).property _ R.property
    ((F.representativeIn_iso G _).symm.trans (G.representativeIn_iso F R).symm))

/-- Reindex actual matching labels by endpoint-preserving strand transport. -/
def labelsEquiv (F G : MatchingBasisChoice a b) : F.Labels ≃ G.Labels :=
  Equiv.sigmaCongr (F.representativesEquiv G) fun R =>
    Equiv.arrowCongr (matchingStrandEquivOfIso (F.representativeIn_iso G R)) (Equiv.refl ℕ)

theorem labelsEquiv_openDots (F G : MatchingBasisChoice a b) (t : F.Labels) :
    G.openDots (F.labelsEquiv G t) = F.openDots t := by
  change (∑ j, t.2 ((matchingStrandEquivOfIso (F.representativeIn_iso G t.1)).symm j)) = _
  exact (matchingStrandEquivOfIso (F.representativeIn_iso G t.1)).symm.sum_comp t.2

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
/-- Lower-dot decorations on any reduced matching normalize into the chosen family's
strict filtered image. The skeleton need not belong to the chosen family. -/
theorem bounded_arbitrary_errors_mem (F : MatchingBasisChoice a b) (c N : ℕ) :
    let T := ((Finsupp.supported (SYM D k) k {t | F.dotBound c N t}).map
      (F.expansion cs μ)).comap (bendG cs μ a b)
    ∀ {s : List (ℕ × Letter I)}, Valid s → Lettered flipL s →
      s.map Prod.snd = dualW a ++ b → ncr (canon s) = c →
      ∀ R, IsMatching₂ a b R → Reduced₂ a R → Iso (pairing₂ a R) s →
      DecSpan cs μ (dualW a ++ a) (cupA (dualW a))
        (R.map (shiftT a.length)) (dualW a ++ b) N ≤ T := by
  classical
  let T := ((Finsupp.supported (SYM D k) k {t | F.dotBound c N t}).map
    (F.expansion cs μ)).comap (bendG cs μ a b)
  let M : Set (List (TMove (Letter I))) := {R | IsMatching₂ a b R ∧ Reduced₂ a R}
  have hlow : LtL D Sc cs μ [] (dualW a ++ b) c ≤ T := by
    intro f hf
    obtain ⟨z, hz, hs⟩ := F.exists_expansion_of_mem_ltL cs μ (bendG_mem_ltL μ hf)
    exact ⟨z, (Finsupp.mem_supported k z).2 (fun t ht => Or.inl (hs t ht)), hz⟩
  have hA : ∀ n : ℕ, n ≤ N →
      ∀ {s : List (ℕ × Letter I)}, Valid s → Lettered flipL s →
        s.map Prod.snd = dualW a ++ b → ncr (canon s) = c →
        ∀ R ∈ M, Iso (pairing₂ a R) s →
        DecSpan cs μ (dualW a ++ a) (cupA (dualW a))
          (R.map (shiftT a.length)) (dualW a ++ b) n ≤ T := by
    intro n
    induction n with
    | zero =>
      intro _ s hv hl hs hc R hR hi
      exact Submodule.span_le.2 fun _ ⟨_, _, _, _, _, _, h, _⟩ =>
        absurd h (Nat.not_lt_zero _)
    | succ n ih =>
      intro hn
      exact decSpan_le_step μ a b M (fun R hR => hR) (dualW a ++ b) rfl T c
        hlow n (fun hv hl hs hc is his hlen _ hβ =>
          (F.bounded_errors_mem cs μ c N).1 hv hl hs hc is his (by omega) hβ)
        (ih (by omega))
  dsimp only
  intro s hv hl hs hc R hR hr hi
  exact hA N le_rfl hv hl hs hc R ⟨hR, hr⟩ hi

/-- Canonical comparison with the lower terms expanded in an arbitrary fixed
complete choice. In particular the compared skeleton need not belong to F. -/
theorem canonical_filtered_signRel (F : MatchingBasisChoice a b) (c : ℕ)
    (R : List (TMove (Letter I))) (hR : IsMatching₂ a b R) (hred : Reduced₂ a R)
    (q : ℕ → ℕ × ℕ) (hq : ∀ j ∈ leftEnds₂ a R, OnStrand₂ a R j (q j))
    (σ : (ℕ → ℕ) → List (DTMove I)) (hσ : ∀ n, Decorates₂ a R q n (σ n))
    {s : List (ℕ × Letter I)} (hv : Valid s) (hl : Lettered flipL s)
    (hs : s.map Prod.snd = dualW a ++ b) (hc : ncr (canon s) = c)
    (hi : Iso (pairing₂ a R) s) (is : List ℕ) (his : ∀ i ∈ is, i < s.length) :
    SignRel (((Finsupp.supported (SYM D k) k {t | F.dotBound c is.length t}).map
        (F.expansion cs μ)).comap (bendG cs μ a b))
      (xev cs μ [] (dualW a ++ b) (chordLay [] (canon s) ++ dotsOn (dualW a ++ b) is))
      (xev cs μ [] (dualW a ++ b) (cupA (dualW a) ++ dLay (dualW a ++ a)
        ((σ (fun j => (is.map (lEnd s)).count j)).map (shiftD a.length)))) := by
  apply canon_dots_signRel_of_bounds μ a b R hR hred q hq σ hσ
    (dualW a ++ b) rfl _ c hv hl hs hc hi is his
  · intro f hf
    obtain ⟨z, hz, hzlo⟩ := F.exists_expansion_of_mem_ltL cs μ (bendG_mem_ltL μ hf)
    exact ⟨z, (Finsupp.mem_supported k z).mpr (fun t ht => Or.inl (hzlo t ht)), hz⟩
  · exact (F.bounded_errors_mem cs μ c is.length).1 hv hl hs hc
  · exact F.bounded_arbitrary_errors_mem cs μ c is.length hv hl hs hc R hR hred hi

theorem layers_chain (F : MatchingBasisChoice a b) (t : F.Labels) :
    XChain a (F.layers t) b := by
  obtain ⟨hR, -⟩ := F.matching t.1.val t.1.property
  obtain ⟨hmv, -⟩ := F.decorates t.1 t.2
  obtain ⟨hfit, -⟩ := matching_bent_spec hR
  obtain ⟨-, hchain, -, -⟩ := shiftD_spec (dualW a) a.length (length_dualW a)
    (F.serialize t.1 t.2) (tStart_letters a)
    (by rw [tmoves_map_shiftD, hmv]; exact hfit)
  simpa only [hmv, hR.2, layers] using hchain

theorem bendF_layers (F : MatchingBasisChoice a b) (t : F.Labels) :
    bendF cs μ a b (xev cs μ a b (F.layers t)) =
      xev cs μ [] (dualW a ++ b) (cupA (dualW a) ++ dLay (dualW a ++ a)
        ((F.serialize t.1 t.2).map (shiftD a.length))) := by
  obtain ⟨hR, -⟩ := F.matching t.1.val t.1.property
  obtain ⟨hmv, -⟩ := F.decorates t.1 t.2
  obtain ⟨hfit, -⟩ := matching_bent_spec hR
  obtain ⟨hshift, -, -, -⟩ := shiftD_spec (dualW a) a.length (length_dualW a)
    (F.serialize t.1 t.2) (tStart_letters a)
    (by rw [tmoves_map_shiftD, hmv]; exact hfit)
  rw [bendF_xev cs μ (F.layers_chain t), hshift]
  rfl

/-- The signed canonical comparison evaluates the actual chosen serializer,
with every lower term expressed in the independently chosen target family G. -/
theorem label_canonical_filtered_signRel (F G : MatchingBasisChoice a b)
    (t : F.Labels) (c : ℕ) {s : List (ℕ × Letter I)}
    (hv : Valid s) (hl : Lettered flipL s) (hs : s.map Prod.snd = dualW a ++ b)
    (hc : ncr (canon s) = c) (hi : Iso (pairing₂ a t.1.val) s)
    (is : List ℕ) (his : ∀ i ∈ is, i < s.length)
    (hn : ∀ j : MatchingStrand a t.1.val, (is.map (lEnd s)).count j.val = t.2 j) :
    SignRel (((Finsupp.supported (SYM D k) k {u | G.dotBound c is.length u}).map
        (G.expansion cs μ)).comap (bendG cs μ a b))
      (xev cs μ [] (dualW a ++ b) (chordLay [] (canon s) ++ dotsOn (dualW a ++ b) is))
      (bendF cs μ a b (xev cs μ a b (F.layers t))) := by
  have hser : F.ambientSerializer t.1.val (fun j => (is.map (lEnd s)).count j) =
      F.serialize t.1 t.2 := by
    simp only [ambientSerializer, dite_eq_left t.1.property]
    congr 1
    exact funext hn
  have h := G.canonical_filtered_signRel cs μ c t.1.val
    (F.matching t.1.val t.1.property).1 (F.matching t.1.val t.1.property).2.1
    (F.ambientPoints t.1.val)
    (fun j hj => by simpa only [ambientPoints, dite_eq_left t.1.property] using F.onStrand t.1 j hj)
    (F.ambientSerializer t.1.val) (F.ambient_decorates t.1.val t.1.property)
    hv hl hs hc hi is his
  rw [hser, ← F.bendF_layers cs μ t] at h
  exact h

/-- Actual evaluations of two independently chosen decorated representatives
have the same signed leading term after bending, with strictly filtered errors. -/
theorem labels_bent_filtered_signRel (F G : MatchingBasisChoice a b) (t : F.Labels) :
    SignRel (((Finsupp.supported (SYM D k) k
        {u | G.dotBound (ncr₂ t.1.val) (F.openDots t) u}).map
        (G.expansion cs μ)).comap (bendG cs μ a b))
      (bendF cs μ a b (xev cs μ a b (F.layers t)))
      (bendF cs μ a b (xev cs μ a b (G.layers (F.labelsEquiv G t)))) := by
  let s := pairing₂ a t.1.val
  obtain ⟨hR, hred⟩ := F.matching t.1.val t.1.property
  have hv : Valid s := ((tInv_tStart a).run hR.1).valid
  have hl : Lettered flipL s := by
    obtain ⟨hf₀, -, -, -⟩ := cupMoves_spec (dualW a)
    exact lettered_tRun t.1.val _ (tInv_tStart a) (Chord.lettered_run flipL_involutive hf₀) hR.1
  have hs : s.map Prod.snd = dualW a ++ b := by
    dsimp only [s, pairing₂]
    rw [letters_tRun (length_dualW a) t.1.val _ a (tStart_letters a) hR.1, hR.2]
  have hc : ncr (canon s) = ncr₂ t.1.val :=
    (reduced₂_bent_normal_form cs μ hR hred.1).2.1.symm
  obtain ⟨is, his, hn, hlen⟩ := exists_canonical_strand_dots hv (Iso.refl _) t.2
  have h1 := F.label_canonical_filtered_signRel cs μ G t _ hv hl hs hc (Iso.refl _) is his hn
  have h2 := G.label_canonical_filtered_signRel cs μ G (F.labelsEquiv G t) _ hv hl hs hc
    (F.representativeIn_iso G t.1).symm is his (fun j =>
      hn ((matchingStrandEquivOfIso (F.representativeIn_iso G t.1)).symm j))
  have h := h1.symm.trans h2
  rw [hlen] at h
  exact h

/-- The signed unit-column comparison, in the original oriented hom space. -/
theorem labels_filtered_signRel (F G : MatchingBasisChoice a b) (t : F.Labels) :
    SignRel ((Finsupp.supported (SYM D k) k
        {u | G.dotBound (ncr₂ t.1.val) (F.openDots t) u}).map (G.expansion cs μ))
      (xev cs μ a b (F.layers t))
      (xev cs μ a b (G.layers (F.labelsEquiv G t))) := by
  obtain ⟨p, hp⟩ := F.labels_bent_filtered_signRel cs μ G t
  simp only [Submodule.mem_comap, map_sub, map_smul,
    bendG_bendF_xev cs μ (F.layers_chain t),
    bendG_bendF_xev cs μ (G.layers_chain (F.labelsEquiv G t))] at hp
  let pF := pairPar D μ (dualW a) + cupsPar D μ (dualW a) * xpar D μ (F.layers t)
  let pG := pairPar D μ (dualW a) + cupsPar D μ (dualW a) * xpar D μ (G.layers (F.labelsEquiv G t))
  refine ⟨pF + (p + pG), ?_⟩
  have h := Submodule.smul_mem _ (zsign k pF) hp
  simpa only [pF, pG, smul_sub, smul_smul, zsign_mul_self', one_smul, ← zsign_add] using h

end MatchingBasisChoice
end OddMath.SKM
#print axioms OddMath.SKM.MatchingBasisChoice.bounded_errors_mem

#print axioms OddMath.SKM.MatchingBasisChoice.bounded_arbitrary_errors_mem

#print axioms OddMath.SKM.MatchingBasisChoice.canonical_filtered_signRel

#print axioms OddMath.SKM.MatchingBasisChoice.labels_filtered_signRel
