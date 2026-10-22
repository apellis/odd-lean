/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.SKM.Nondegeneracy
import OddMath.SKM.MixedRealization
import OddMath.QuiverHecke.SortedSummands

/-!
# Endomorphisms of sorted words modulo U-turns

Brundan–Ellis, arXiv:1701.04133v2, proof of Theorem 11.7, surjectivity: the composite
`γ_{n,n',λ} = β_{n,n',λ} ∘ α_{n,n',λ}` is surjective, where `β_{n,n',λ}` is the quotient of
`H_{n,n',λ}` by the ideal `I_{n,n',λ}` spanned by the string diagrams with a U-turn (cf.
Khovanov–Lauda, arXiv:0807.3250v1, Proposition 3.17). The input is Theorem 8.1: a diagram
between words of the same length has a U-turn on its bottom edge if and only if it has one on
its top edge, and we choose the reduced matchings of Theorem 8.1 so that

* a matching with a U-turn passes through a word with two letters fewer (it factors through a
  shorter word);
* a matching without U-turns between sorted words (all upward letters to the left of all
  downward letters) consists of crossings, each between two upward or two downward strands
  (`exists_strictReduced_matching_shape`).

So every 2-morphism `E_a 1_μ → E_b 1_μ` between sorted words of the same length is a linear
combination of *split* diagrams (dots and crossings inside the blocks of upward and downward
strands) followed by bubbles in the rightmost region, plus composites through words of length
at most `|a| - 2` (`splitSpan_sup_shortSpan`).

## Main declarations

* `ShortSpan μ a b`: the span of the composites `E_a 1_μ → E_u 1_μ → E_b 1_μ` with
  `|u| + 2 ≤ |a|`.
* `SplitMoves a ds`: a decorated matching of dots and crossings whose words are all sorted.
* `SplitSpan μ a b`: the span of split diagrams followed by bubbles.
* `splitSpan_sup_shortSpan`: their sum is everything, for sorted `a`, `b` of the same length.
-/

noncomputable section

namespace OddMath.SKM

open CategoryTheory StringDiagrams Presentation StringDiagrams.Chord DTMove

universe u v w

variable {I : Type u}

/-! ### Arcs on the two edges -/

/-- **A pairing of `a* b` with `|b| = |a|` has an arc on the top edge only if it has one on the
bottom edge**: otherwise the bottom endpoints are joined injectively to the top endpoints, hence
bijectively. -/
theorem not_topArc_of_not_botArc {a : List (Letter I)} {s : List (ℕ × Letter I)} (hv : Valid s)
    (hl : s.length = 2 * a.length) (hb : ¬ BotArc a s) : ¬ TopArc a s := by
  classical
  rintro ⟨r, t, hr, ht, hS⟩
  let f : (i : ℕ) → i ∈ Finset.range a.length → ℕ := fun i hi =>
    Classical.choose (hv.exists (show i < s.length by simp at hi; omega))
  have hf : ∀ i hi, Same s i (f i hi) := fun i hi =>
    Classical.choose_spec (hv.exists (show i < s.length by simp at hi; omega))
  have hmaps : ∀ i hi, f i hi ∈ Finset.Ico a.length s.length := by
    intro i hi
    have h1 := hf i hi
    simp only [Finset.mem_range] at hi
    simp only [Finset.mem_Ico]
    refine ⟨?_, h1.lt_right⟩
    by_contra c
    exact hb ⟨i, f i (by simpa using hi), hi, by omega, h1⟩
  obtain ⟨i, hi, e⟩ := Finset.surj_on_of_inj_on_of_card_le f hmaps
    (fun i j hi hj e => by
      have h1 := hf i hi
      have h2 := hf j hj
      rw [e] at h1
      exact hv.unique h1.symm h2.symm)
    (by simp; omega) r (by simp only [Finset.mem_Ico]; exact ⟨hr, hS.lt_left⟩)
  have h1 := hf i hi
  rw [← e] at h1
  have := hv.unique hS h1.symm
  simp at hi
  omega

/-- Sorted words in the sense of `Sorted` (upward letters, then downward letters) are sorted in
the positional sense `LSorted`. -/
theorem lSorted_of_sorted {w : List (Letter I)} (h : Sorted w) : LSorted w := by
  obtain ⟨x, y, rfl⟩ := h
  intro i j hij l l' hl hl' hl1
  rcases Nat.lt_or_ge i x.length with hi | hi
  · rw [List.getElem?_append_left (by simpa using hi), List.getElem?_map] at hl
    obtain ⟨c, -, rfl⟩ := Option.map_eq_some_iff.1 hl
    simp at hl1
  · rw [List.getElem?_append_right (by simp; omega), List.getElem?_map] at hl'
    obtain ⟨c, -, rfl⟩ := Option.map_eq_some_iff.1 hl'
    rfl

/-! ### Splitting decorated matchings -/

theorem exists_split_of_tmoves : ∀ (ds : List (DTMove I)) (R₀ R₁ : List (TMove (Letter I))),
    tmoves ds = R₀ ++ R₁ → ∃ ds₀ ds₁, ds = ds₀ ++ ds₁ ∧ tmoves ds₀ = R₀ ∧ tmoves ds₁ = R₁
  | ds, [], R₁, h => ⟨[], ds, rfl, rfl, h⟩
  | [], _ :: _, _, h => by simp [tmoves] at h
  | .tm m :: ds, m' :: R₀, R₁, h => by
    simp only [tmoves, List.cons_append, List.cons.injEq] at h
    obtain ⟨rfl, h⟩ := h
    obtain ⟨ds₀, ds₁, rfl, h₀, h₁⟩ := exists_split_of_tmoves ds R₀ R₁ h
    exact ⟨.tm m :: ds₀, ds₁, rfl, by simp [tmoves, h₀], h₁⟩
  | .dt i :: ds, m' :: R₀, R₁, h => by
    simp only [tmoves] at h
    obtain ⟨ds₀, ds₁, rfl, h₀, h₁⟩ := exists_split_of_tmoves ds (m' :: R₀) R₁ h
    exact ⟨.dt i :: ds₀, ds₁, rfl, by simp [tmoves, h₀], h₁⟩

/-! ### The spans -/

section Spans

variable {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]
  (Sc : Scalars D k) (cs : CScalars Sc)

/-- The span of the composites `E_a 1_μ → E_u 1_μ → E_b 1_μ` through words `u` with at least two
letters fewer than `a`. -/
def ShortSpan (μ : X) (a b : List (Letter I)) :
    Submodule k ((pres D Sc).obj (ob D μ a) ⟶ (pres D Sc).obj (ob D μ b)) :=
  Submodule.span k {f | ∃ (u : List (Letter I)) (_ : u.length + 2 ≤ a.length)
    (g : (pres D Sc).obj (ob D μ a) ⟶ (pres D Sc).obj (ob D μ u))
    (h : (pres D Sc).obj (ob D μ u) ⟶ (pres D Sc).obj (ob D μ b)), f = g ≫ h}

/-- **Split decorated matchings** on the letters `a`: dots and crossings only, with every word
crossed sorted. A crossing between two sorted words joins two upward or two downward strands. -/
def SplitMoves (a : List (Letter I)) (ds : List (DTMove I)) : Prop :=
  (∀ m ∈ tmoves ds, ∃ p, m = .mv (.cross p)) ∧
    ∀ R₀ R₁, tmoves ds = R₀ ++ R₁ → LSorted (R₀.foldl tLet a)

/-- The span of split diagrams `E_a 1_μ → E_b 1_μ` followed by bubbles in the rightmost
region. -/
def SplitSpan (μ : X) (a b : List (Letter I)) :
    Submodule k ((pres D Sc).obj (ob D μ a) ⟶ (pres D Sc).obj (ob D μ b)) :=
  Submodule.span k {f | ∃ ds, SplitMoves a ds ∧ ∃ β, IsBub cs μ β ∧
    f = xev cs μ a b (dLay a ds) ≫ bubAt D Sc μ b β}

/-- The reduced matchings used: those through a shorter word, and the split ones. -/
def UTurnGood (a : List (Letter I)) (R : List (TMove (Letter I))) : Prop :=
  (∃ R₀ R₁, R = R₀ ++ R₁ ∧ (R₀.foldl tLet a).length + 2 ≤ a.length) ∨
    ((∀ m ∈ R, ∃ p, m = .mv (.cross p)) ∧ ∀ R₀ R₁, R = R₀ ++ R₁ → LSorted (R₀.foldl tLet a))

/-- **Proof of BE2 Theorem 11.7, surjectivity of `γ_{n,n',λ}`**: every 2-morphism
`E_a 1_μ → E_b 1_μ` between sorted words of the same length is a combination of split diagrams
followed by bubbles, modulo composites through words with two letters fewer. -/
theorem splitSpan_sup_shortSpan (μ : X) {a b : List (Letter I)} (ha : LSorted a)
    (hb : LSorted b) (hab : a.length = b.length) :
    SplitSpan Sc cs μ a b ⊔ ShortSpan Sc μ a b = ⊤ := by
  classical
  let M : Set (List (TMove (Letter I))) :=
    {R | IsMatching₂ a b R ∧ StrictReduced₂ a R ∧ UTurnGood a R}
  -- distinguished points and decorated matchings
  have hpts : ∀ R, ∃ q : ℕ → ℕ × ℕ, IsMatching₂ a b R → ∀ j ∈ leftEnds₂ a R,
      (q j).1 ≤ R.length ∧ OnStrand₂ a R j (q j) := fun R => by
    by_cases hR : IsMatching₂ a b R
    · obtain ⟨q, hq⟩ := matching_bounded_points hR
      exact ⟨q, fun _ => hq⟩
    · exact ⟨fun _ => (0, 0), fun h => absurd h hR⟩
  choose q hq using hpts
  have hdec : ∀ R (n : ℕ → ℕ), ∃ ds, IsMatching₂ a b R → Decorates₂ a R (q R) n ds := by
    intro R n
    by_cases hR : IsMatching₂ a b R
    · obtain ⟨ds, hd, -⟩ := exists_decorates₂_of_bounded_points a R (q R)
        (fun j hj => (hq R hR j hj).2) (fun j hj => (hq R hR j hj).1) (fun j => n j)
      exact ⟨ds, fun _ => (decorates₂_strandCounts_iff _ n _).mp hd⟩
    · exact ⟨[], fun h => absurd h hR⟩
  choose σ hσ using hdec
  have h81 := theorem_8_1 (cs := cs) μ a b M (fun R hR => ⟨hR.1, hR.2.1⟩)
    (fun R' hR' _ => by
      have hv := ((tInv_tStart a).run hR'.1).valid
      obtain ⟨hf₀, -, -, -⟩ := cupMoves_spec (dualW a)
      have hl := lettered_tRun R' _ (tInv_tStart a) (Chord.lettered_run flipL_involutive hf₀) hR'.1
      have hs : (pairing₂ a R').map Prod.snd = dualW a ++ b := by
        rw [pairing₂, letters_tRun (length_dualW a) R' _ a (tStart_letters a) hR'.1, hR'.2]
      obtain ⟨R, hR, hred, hiso, h1, h2⟩ := exists_strictReduced_matching_shape hv hl hs
      refine ⟨R, ⟨hR, hred, ?_⟩, hiso⟩
      by_cases hba : BotArc a (pairing₂ a R')
      · exact Or.inl (h1 hba)
      · have hlen : (pairing₂ a R').length = 2 * a.length := by
          have := congrArg List.length hs
          simp only [List.length_map, List.length_append, length_dualW] at this
          omega
        exact Or.inr ((h2 hba (not_topArc_of_not_botArc hv hlen hba)).imp_right
          fun h => h ha hb))
    q (fun R hR j hj => (hq R hR.1 j hj).2) σ (fun R hR n => hσ R n hR.1)
  rw [eq_top_iff, ← h81]
  refine Submodule.span_le.2 ?_
  rintro g ⟨C, ⟨R, ⟨hR, -, hgood⟩, n, rfl⟩, β, hβ, rfl⟩
  have hd := hσ R n hR
  rcases hgood with ⟨R₀, R₁, e, hlen⟩ | ⟨hx, hsrt⟩
  · refine Submodule.mem_sup_right (Submodule.subset_span ?_)
    obtain ⟨ds₀, ds₁, hds, h₀, -⟩ := exists_split_of_tmoves _ R₀ R₁ (hd.1.trans e)
    have hfit : TFits flipL a.length (tStart a) R₀ := by
      have := hR.1; rw [e] at this; exact ((tFits_append_at _ _ _ _).1 this).1
    have hch := matching_dLay_chain (b := R₀.foldl tLet a) ⟨hfit, rfl⟩ ds₀ h₀
    refine ⟨R₀.foldl tLet a, hlen, xev cs μ a _ (dLay a ds₀),
      xev cs μ _ b (dLay (R₀.foldl tLet a) ds₁) ≫ bubAt D Sc μ b β, ?_⟩
    rw [hds, dLay_append, h₀, xev_append cs _ hch, Category.assoc]
  · refine Submodule.mem_sup_left (Submodule.subset_span ⟨σ R n, ⟨?_, ?_⟩, β, hβ, rfl⟩)
    · rw [hd.1]; exact hx
    · rw [hd.1]; exact hsrt

end Spans

end OddMath.SKM
