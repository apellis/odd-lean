/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.QuiverHecke.UTurnSpanning
import OddMath.QuiverHecke.Label

/-!
# Split diagrams factor into an upward and a downward diagram

Brundan–Ellis, arXiv:1701.04133v2, proof of Theorem 11.7, surjectivity (cf. Khovanov–Lauda,
arXiv:0807.3250v1, §3.2.4). A split diagram on `E_𝐢 F_𝐢′ 1_μ` (dots and crossings inside the
blocks of upward and downward strands; `SplitMoves`) is, up to a sign, an upward quiver Hecke
diagram on the left block placed next to a downward one on the right block. The downward
diagrams are the images under `ω` (`omegaL`) of upward quiver Hecke diagrams, so the two
factors are images of `α_{n,λ}` and of `α′_{n′,λ}`.

* `udLayers V U' M N`: the upward diagram `M` whiskered by `V` on the right, followed by the
  image of the downward diagram `N` under `omegaL`, whiskered by `U'` on the left.
* `UDFactor`: a layer list equals a multiple of such a product.
* `udFactor_dLay`: every split diagram factors.
* `UDSpan μ s t b`: the span of products of an upward diagram, a downward diagram and a bubble;
  `udSpan_sup_shortSpan`: together with the composites through shorter words it is everything.
-/

noncomputable section

namespace OddMath.SKM

open CategoryTheory StringDiagrams Presentation StringDiagrams.Chord DTMove
open QuiverHecke (upWord upLayers)

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]
  (Sc : Scalars D k)

/-- The downward word `F_t`: the letters of `t`, all pointing down. -/
abbrev dnWord (t : List I) : List (Letter I) := flipW (upWord t)

@[simp] theorem dnWord_append (s t : List I) : dnWord (s ++ t) = dnWord s ++ dnWord t := by
  simp [dnWord]

/-- An upward layer, as a layer of `𝔘(𝔤)`. -/
def upL (x : QuiverHecke.LayerData I) : LayerData I := (upWord x.1, x.2.1.toSKM, upWord x.2.2)

theorem upLayers_singleton (x : QuiverHecke.LayerData I) : upLayers [x] = [upL x] := rfl

/-- The upward diagram `M` placed left of `V`, followed by the image of `N` under `omegaL`
placed right of `U'`. -/
def udLayers (V U' : List (Letter I)) (M N : List (QuiverHecke.LayerData I)) :
    List (LayerData I) :=
  (upLayers M).map (whL [] V) ++ (omegaL (upLayers N)).map (whL U' [])

theorem sChain_udLayers {s s' t t' : List I} {M N : List (QuiverHecke.LayerData I)}
    (hM : QuiverHecke.SChain s M s') (hN : QuiverHecke.SChain t' N t) :
    SChain (upWord s ++ dnWord t) (udLayers (dnWord t) (upWord s') M N)
      (upWord s' ++ dnWord t') := by
  have h₁ := hM.up.whisk [] (dnWord t)
  have h₂ := (sChain_omegaL hN.up).whisk (upWord s') []
  simp only [List.nil_append, List.append_nil] at h₁ h₂
  exact h₁.append h₂

/-- `L` from `E_s F_t 1_μ` to `E_{s'} F_{t'} 1_μ` is a multiple of an upward diagram followed by a
downward one. -/
def UDFactor (μ : X) (s t s' t' : List I) (L : List (LayerData I)) : Prop :=
  SChain (upWord s ++ dnWord t) L (upWord s' ++ dnWord t') ∧
    ∃ (M N : List (QuiverHecke.LayerData I)) (c : k), QuiverHecke.SChain s M s' ∧
      QuiverHecke.SChain t' N t ∧
      cl D Sc μ (upWord s ++ dnWord t) (upWord s' ++ dnWord t') L =
        c • cl D Sc μ (upWord s ++ dnWord t) (upWord s' ++ dnWord t')
          (udLayers (dnWord t) (upWord s') M N)

theorem UDFactor.nil (μ : X) (s t : List I) : UDFactor Sc μ s t s t [] :=
  ⟨rfl, [], [], 1, rfl, rfl, by simp [udLayers, upLayers]⟩

/-- Appending an upward layer. -/
theorem UDFactor.append_up {μ : X} {s t s' t' s'' : List I} {L : List (LayerData I)}
    (h : UDFactor Sc μ s t s' t' L) (x : QuiverHecke.LayerData I)
    (hx : QuiverHecke.SChain s' [x] s'') :
    UDFactor Sc μ s t s'' t' (L ++ [whL [] (dnWord t') (upL x)]) := by
  have hy : SChain (upWord s' ++ dnWord t') [whL [] (dnWord t') (upL x)]
      (upWord s'' ++ dnWord t') := by
    simpa only [List.nil_append, upLayers_singleton, List.map_singleton] using
      hx.up.whisk [] (dnWord t')
  refine ⟨h.1.append hy, ?_⟩
  obtain ⟨M, N, c, hM, hN, he⟩ := h.2
  refine ⟨M ++ [x], N, zsign k (parsum D [upL x] * parsum D (omegaL (upLayers N))) * c,
    hM.append hx, hN, ?_⟩
  rw [← cl_comp h.1 hy, he, Linear.smul_comp, cl_comp (sChain_udLayers hM hN) hy]
  have E := cl_interchange (D := D) (Sc := Sc) (μ := μ)
    (S := upWord s ++ dnWord t) (T := upWord s'' ++ dnWord t')
    ((upLayers M).map (whL [] (dnWord t))) [] (s := upWord s') (s' := upWord s'')
    (A := [upL x]) (B := omegaL (upLayers N))
    (by simpa only [upLayers_singleton] using hx.up) (sChain_omegaL hN.up)
  simp only [List.append_nil] at E
  have e₁ : udLayers (dnWord t) (upWord s') M N ++ [whL [] (dnWord t') (upL x)] =
      (upLayers M).map (whL [] (dnWord t)) ++
        (omegaL (upLayers N)).map (whL (upWord s') []) ++ [upL x].map (whL [] (dnWord t')) := by
    simp [udLayers]
  have e₂ : udLayers (dnWord t) (upWord s'') (M ++ [x]) N =
      (upLayers M).map (whL [] (dnWord t)) ++ [upL x].map (whL [] (dnWord t)) ++
        (omegaL (upLayers N)).map (whL (upWord s'') []) := by
    simp [udLayers, upLayers_singleton]
  rw [e₁, e₂, E, smul_smul, mul_right_comm, zsign_mul_self, one_mul]

/-- Appending a downward layer, the image under `omegaL` of an upward one. -/
theorem UDFactor.append_dn {μ : X} {s t s' t' t'' : List I} {L : List (LayerData I)}
    (h : UDFactor Sc μ s t s' t' L) (x : QuiverHecke.LayerData I)
    (hx : QuiverHecke.SChain t'' [x] t') :
    UDFactor Sc μ s t s' t'' (L ++ (omegaL [upL x]).map (whL (upWord s') [])) := by
  have hy : SChain (upWord s' ++ dnWord t') ((omegaL [upL x]).map (whL (upWord s') []))
      (upWord s' ++ dnWord t'') := by
    simpa only [List.append_nil, upLayers_singleton] using
      (sChain_omegaL hx.up).whisk (upWord s') []
  refine ⟨h.1.append hy, ?_⟩
  obtain ⟨M, N, c, hM, hN, he⟩ := h.2
  refine ⟨M, x :: N, c, hM, hx.append hN, ?_⟩
  rw [← cl_comp h.1 hy, he, Linear.smul_comp, cl_comp (sChain_udLayers hM hN) hy]
  have e : omegaL (upLayers (x :: N)) = omegaL (upLayers N) ++ omegaL [upL x] := by
    rw [show upLayers (x :: N) = [upL x] ++ upLayers N from rfl, omegaL_append]
  simp only [udLayers, e, List.map_append, List.append_assoc]

/-! ### Split diagrams -/

theorem exists_split_one {β : Type*} {l : List β} {i : ℕ} (h : i < l.length) :
    ∃ u x w, l = u ++ x :: w ∧ u.length = i := by
  obtain ⟨u, w', rfl, hu⟩ := exists_split_cup (l := l) (g := i) h.le
  match w', h with
  | x :: w, _ => exact ⟨u, x, w, rfl, hu⟩
  | [], h => simp at h; omega

theorem dotOn_mid (u w : List (Letter I)) (x : Letter I) :
    dotOn (u ++ x :: w) u.length = (xDotL x).map (xwhL u w) := by
  simp [dotOn]

theorem moveLay_cross_of_le {l : List (Letter I)} {p : ℕ} (h : l.length ≤ p + 1) :
    moveLay l (.cross p) = [] := by
  rcases hd : l.drop p with _ | ⟨x, _ | ⟨y, r⟩⟩
  · simp [moveLay, hd]
  · simp [moveLay, hd]
  · have := congrArg List.length hd
    simp at this; omega

theorem chStep_cross_of_le {l : List (Letter I)} {p : ℕ} (h : l.length ≤ p + 1) :
    chStep l (.cross p) = l := by
  simp only [chStep, lstep, swapAt]
  split_ifs with h'
  · omega
  · rfl

theorem length_ud (s t : List I) : (upWord s ++ dnWord t).length = s.length + t.length := by
  simp [upWord, dnWord, flipW]

/-- One more move of a split diagram. -/
theorem UDFactor.step {μ : X} {s t s' t' : List I} {L : List (LayerData I)}
    (h : UDFactor Sc μ s t s' t' L) (d : DTMove I)
    (hd : ∀ m ∈ tmoves [d], ∃ p, m = .mv (.cross p))
    (hs : LSorted ((tmoves [d]).foldl tLet (upWord s' ++ dnWord t'))) :
    ∃ s'' t'' L', dLay (upWord s' ++ dnWord t') [d] = L'.map ofL ∧
      (tmoves [d]).foldl tLet (upWord s' ++ dnWord t') = upWord s'' ++ dnWord t'' ∧
      UDFactor Sc μ s t s'' t'' (L ++ L') := by
  cases d with
  | dt i =>
    simp only [tmoves, List.foldl_nil] at hs ⊢
    simp only [dLay, List.append_nil]
    by_cases h₁ : i < s'.length
    · obtain ⟨α, j, β, rfl, rfl⟩ := exists_split_one h₁
      refine ⟨α ++ j :: β, t', [whL [] (dnWord t') (upL (α, .dot j, β))], ?_, rfl,
        h.append_up Sc _ ⟨by simp [QuiverHecke.Shape.dom],
          by simp [QuiverHecke.SChain, QuiverHecke.Shape.cod]⟩⟩
      have e : upWord (α ++ j :: β) ++ dnWord t' =
          upWord α ++ up j :: (upWord β ++ dnWord t') := by simp [upWord]
      rw [e, show α.length = (upWord α).length by simp [upWord], dotOn_mid]
      simp [xDotL, xwhL, ofL, whL, upL, QuiverHecke.Shape.toSKM]
    by_cases h₂ : i < s'.length + t'.length
    · obtain ⟨α, j, β, rfl, hα⟩ := exists_split_one (l := t') (i := i - s'.length) (by omega)
      refine ⟨s', α ++ j :: β, (omegaL [upL (α, .dot j, β)]).map (whL (upWord s') []), ?_, rfl,
        h.append_dn Sc _ ⟨by simp [QuiverHecke.Shape.dom],
          by simp [QuiverHecke.SChain, QuiverHecke.Shape.cod]⟩⟩
      have e : upWord s' ++ dnWord (α ++ j :: β) =
          (upWord s' ++ dnWord α) ++ dn j :: dnWord β := by simp [upWord, dnWord]
      rw [e, show i = (upWord s' ++ dnWord α).length by simp [upWord, dnWord, flipW]; omega,
        dotOn_mid]
      simp [xDotL, dn, upL, omegaL, chevL, QuiverHecke.Shape.toSKM, List.map_map,
        Function.comp_def, upWord, dnWord, flipW]
    · refine ⟨s', t', [], ?_, rfl, by simpa using h⟩
      rw [dotOn_of_le (by rw [length_ud]; omega)]; rfl
  | tm m =>
    obtain ⟨p, rfl⟩ := hd m (by simp [tmoves])
    simp only [tmoves, List.foldl_cons, List.foldl_nil, tLet] at hs ⊢
    simp only [dLay, tmLay, List.append_nil]
    by_cases h₁ : p + 1 < s'.length
    · obtain ⟨α, i, j, β, rfl, rfl⟩ := exists_split_cross h₁
      have e : upWord (α ++ i :: j :: β) ++ dnWord t' =
          upWord α ++ up i :: up j :: (upWord β ++ dnWord t') := by simp [upWord]
      have hp : α.length = (upWord α).length := by simp [upWord]
      refine ⟨α ++ j :: i :: β, t', [whL [] (dnWord t') (upL (α, .cross i j, β))], ?_, ?_,
        h.append_up Sc _ ⟨by simp [QuiverHecke.Shape.dom], by simp [QuiverHecke.Shape.cod]⟩⟩
      · rw [e, hp, moveLay_cross]
        simp [xCrL, xwhL, ofL, whL, upL, QuiverHecke.Shape.toSKM]
      · rw [e, hp, chStep_cross]; simp [upWord]
    by_cases h₂ : p + 1 < s'.length + t'.length
    · by_cases h₃ : p < s'.length
      · -- a crossing between the two blocks would leave the word unsorted
        exfalso
        obtain ⟨α, i, β', rfl, hα⟩ := exists_split_one h₃
        have hβ' : β' = [] := by
          rcases β' with _ | ⟨b, β'⟩
          · rfl
          · simp at h₁; omega
        subst hβ'
        obtain ⟨j, β, rfl⟩ : ∃ j β, t' = j :: β := by
          rcases t' with _ | ⟨j, β⟩
          · simp at h₂; omega
          · exact ⟨j, β, rfl⟩
        have e : upWord (α ++ [i]) ++ dnWord (j :: β) =
            upWord α ++ up i :: dn j :: dnWord β := by simp [upWord, dnWord]
        rw [e, ← hα, show α.length = (upWord α).length by simp [upWord], chStep_cross] at hs
        have := hs (upWord α).length ((upWord α).length + 1) (by omega) (dn j) (up i)
          (by simp) (by simp)
        simp at this
      · obtain ⟨α, i, j, β, rfl, hα⟩ := exists_split_cross (l := t') (p := p - s'.length)
          (by omega)
        have e : upWord s' ++ dnWord (α ++ i :: j :: β) =
            (upWord s' ++ dnWord α) ++ dn i :: dn j :: dnWord β := by simp [upWord, dnWord]
        have hp : p = (upWord s' ++ dnWord α).length := by
          simp [upWord, dnWord, flipW]; omega
        refine ⟨s', α ++ j :: i :: β,
          (omegaL [upL (α, .cross j i, β)]).map (whL (upWord s') []), ?_, ?_,
          h.append_dn Sc _ ⟨by simp [QuiverHecke.Shape.dom], by simp [QuiverHecke.Shape.cod]⟩⟩
        · rw [e, hp, moveLay_cross]
          simp [xCrL, dn, upL, omegaL, chevL, QuiverHecke.Shape.toSKM, List.map_map,
            Function.comp_def, upWord, dnWord, flipW]
        · rw [e, hp, chStep_cross]; simp [upWord, dnWord]
    · refine ⟨s', t', [], ?_, ?_, by simpa using h⟩
      · rw [moveLay_cross_of_le (by rw [length_ud]; omega)]; rfl
      · rw [chStep_cross_of_le (by rw [length_ud]; omega)]

/-- **Split diagrams factor** into an upward diagram followed by a downward one. -/
theorem udFactor_dLay (μ : X) (s t : List I) (ds : List (DTMove I))
    (h : SplitMoves (upWord s ++ dnWord t) ds) :
    ∃ s' t' L, dLay (upWord s ++ dnWord t) ds = L.map ofL ∧
      (tmoves ds).foldl tLet (upWord s ++ dnWord t) = upWord s' ++ dnWord t' ∧
      UDFactor Sc μ s t s' t' L := by
  induction ds using List.reverseRecOn with
  | nil => exact ⟨s, t, [], rfl, rfl, UDFactor.nil Sc μ s t⟩
  | append_singleton ds d ih =>
    have hpre : SplitMoves (upWord s ++ dnWord t) ds := by
      refine ⟨fun m hm => h.1 m (by rw [tmoves_append]; exact List.mem_append_left _ hm),
        fun R₀ R₁ hR => h.2 R₀ (R₁ ++ tmoves [d]) ?_⟩
      rw [tmoves_append, hR, List.append_assoc]
    obtain ⟨s', t', L, hL, hl, hf⟩ := ih hpre
    have hd : ∀ m ∈ tmoves [d], ∃ p, m = .mv (.cross p) := fun m hm =>
      h.1 m (by rw [tmoves_append]; exact List.mem_append_right _ hm)
    have hs : LSorted ((tmoves [d]).foldl tLet (upWord s' ++ dnWord t')) := by
      rw [← hl, ← List.foldl_append, ← tmoves_append]
      exact h.2 _ [] (List.append_nil _).symm
    obtain ⟨s'', t'', L', hL', hl', hf'⟩ := hf.step Sc d hd hs
    refine ⟨s'', t'', L ++ L', ?_, ?_, hf'⟩
    · rw [dLay_append, hl, hL', hL, List.map_append]
    · rw [tmoves_append, List.foldl_append, hl, hl']

variable (cs : CScalars Sc)

/-- The products of an upward diagram, a downward diagram and a bubble in the rightmost
region, `E_s F_t 1_μ → b`. -/
def UDSpan (μ : X) (s t : List I) (b : List (Letter I)) :
    Submodule k ((pres D Sc).obj (ob D μ (upWord s ++ dnWord t)) ⟶ (pres D Sc).obj (ob D μ b)) :=
  Submodule.span k {f | ∃ (s' t' : List I) (M N : List (QuiverHecke.LayerData I)),
    QuiverHecke.SChain s M s' ∧ QuiverHecke.SChain t' N t ∧ upWord s' ++ dnWord t' = b ∧
    ∃ β, IsBub cs μ β ∧
      f = cl D Sc μ (upWord s ++ dnWord t) b (udLayers (dnWord t) (upWord s') M N) ≫
        bubAt D Sc μ b β}

/-- **Split diagrams followed by bubbles are products of upward and downward diagrams and
bubbles.** -/
theorem splitSpan_le_udSpan (μ : X) (s t : List I) (b : List (Letter I)) :
    SplitSpan Sc cs μ (upWord s ++ dnWord t) b ≤ UDSpan Sc cs μ s t b := by
  refine Submodule.span_le.mpr ?_
  rintro f ⟨ds, hds, β, hβ, rfl⟩
  obtain ⟨s', t', L, hL, -, hf⟩ := udFactor_dLay Sc μ s t ds hds
  rw [hL, xev_map_ofL]
  by_cases hb : upWord s' ++ dnWord t' = b
  · subst hb
    obtain ⟨M, N, c, hM, hN, he⟩ := hf.2
    rw [he, Linear.smul_comp]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨s', t', M, N, hM, hN, rfl, β, hβ, rfl⟩)
  · rw [cl_of_not (fun h => hb (hf.1.eq_target h)), Limits.zero_comp]
    exact Submodule.zero_mem _

theorem dnWord_eq_map (t : List I) : dnWord t = t.map dn := by
  simp [dnWord, flipW, upWord, Function.comp_def]

/-- **Endomorphisms of `E_s F_t 1_μ`** (BE2, proof of Theorem 11.7): every 2-morphism from
`E_s F_t 1_μ` to a sorted word of the same length is a combination of products of an upward
diagram, a downward diagram and a bubble, plus composites through words with two letters fewer. -/
theorem udSpan_sup_shortSpan (μ : X) (s t : List I) {b : List (Letter I)} (hb : LSorted b)
    (hab : (upWord s ++ dnWord t).length = b.length) :
    UDSpan Sc cs μ s t b ⊔ ShortSpan Sc μ (upWord s ++ dnWord t) b = ⊤ := by
  have ha : LSorted (upWord s ++ dnWord t) :=
    lSorted_of_sorted ⟨s, t, by rw [dnWord_eq_map]; rfl⟩
  refine eq_top_iff.mpr ?_
  rw [← splitSpan_sup_shortSpan Sc cs μ ha hb hab]
  exact sup_le_sup_right (splitSpan_le_udSpan Sc cs μ s t b) _

end OddMath.SKM
