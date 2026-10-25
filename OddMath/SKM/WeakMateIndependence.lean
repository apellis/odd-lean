import OddMath.SKM.WeakMateLayers
import OddMath.SKM.WeakMatchingTargetExpansion
import OddMath.SKM.ClosureCoefficientExpansion
import OddMath.SKM.PositiveClosureDetector
import OddMath.SKM.TopMatchingChoiceList
import OddMath.SKM.MatchingChoiceCast
import OddMath.SKM.MatchingEndpointSupport

/-!
# Closure of complete weak inverse-mate families

Actual full-SYM coefficient identities used in the sorted-boundary
upward-to-oriented implication of BE2 §8.
-/
noncomputable section
namespace OddMath.SKM.WeakMate
open CategoryTheory StringDiagrams Presentation StringDiagrams.Chord DTMove
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} (cs : CScalars Sc) (μ : X)

/-- Closure with the dual-word source convention of literal matchings. -/
def closure (l r : List I) (a b : List (Letter I)) :
    ((pres D Sc).obj (ob D (wt D μ (ups r)) (a ++ dualW (ups r))) ⟶
      (pres D Sc).obj (ob D (wt D μ (ups r)) (dns l ++ b))) →ₗ[k]
    ((pres D Sc).obj (ob D μ (ups l ++ a)) ⟶ (pres D Sc).obj (ob D μ (b ++ ups r))) :=
  (rightClosure D Sc μ l r a b).comp
    (wordCast (wt D μ (ups r)) (by rw [dualW_ups]) rfl)

theorem closure_decorated_coefficient {l r : List I} {a b : List (Letter I)}
    {R : List (TMove (Letter I))} (hR : IsMatching₂ (ups l ++ a) (b ++ ups r) R)
    (q : ℕ → ℕ × ℕ)
    (hq : ∀ j ∈ leftEnds₂ (ups l ++ a) R,
      (q j).1 ≤ R.length ∧ OnStrand₂ (ups l ++ a) R j (q j))
    (n : MatchingStrand (ups l ++ a) R → ℕ) {ds : List (DTMove I)}
    (hd : Decorates₂ (ups l ++ a) R q (strandCounts n) ds)
    {L : List (LayerData I)} (hL : SChain (ups l ++ a) L (b ++ ups r))
    (he : L.map ofL = dLay (ups l ++ a) ds) (p : SYM D k) :
    ∃ z : PositiveWordDots (b ++ ups r) →₀ SYM D k,
      closure (D := D) (Sc := Sc) μ l r a b
        (xev cs (wt D μ (ups r)) (a ++ dualW (ups r)) (dns l ++ b)
          (dLay (a ++ dualW (ups r)) (moves l b (ups r) ds)) ≫
            bubAt D Sc (wt D μ (ups r)) (dns l ++ b) (betaSYM cs (wt D μ (ups r)) p)) =
      xev cs μ (ups l ++ a) (b ++ ups r) (dLay (ups l ++ a) ds) ≫
        bubAt D Sc μ (b ++ ups r) (betaSYM cs μ p) +
      xev cs μ (ups l ++ a) (b ++ ups r) (dLay (ups l ++ a) ds) ≫
        positiveWordExpansion cs μ (b ++ ups r) z := by
  have hmate := dLay_moves hR q hq n hd he
  have hm : dLay (a ++ dualW (ups r)) (moves l b (ups r) ds) =
      (partialRightMateL l r a b L).map ofL := by
    simpa only [dualW_ups] using hmate
  have H := rightClosure_partialMate_betaSYM_expansion cs μ l r a b hL p
  obtain ⟨z, hz⟩ := H
  have hw : b ++ [] ++ ups r = b ++ ups r := by simp
  let z' : PositiveWordDots (b ++ ups r) →₀ SYM D k := hw ▸ z
  have hez : wordCast (D := D) (Sc := Sc) μ hw hw
      (positiveWordExpansion cs μ (b ++ [] ++ ups r) z) =
      positiveWordExpansion cs μ (b ++ ups r) z' := by
    have aux (v w : List (Letter I)) (h : v = w) (v' : PositiveWordDots v →₀ SYM D k) :
        wordCast (D := D) (Sc := Sc) μ h h (positiveWordExpansion cs μ v v') =
          positiveWordExpansion cs μ w (h ▸ v') := by subst w; rfl
    exact aux _ _ hw z
  rw [hez] at hz
  refine ⟨z', ?_⟩
  change rightClosure D Sc μ l r a b (wordCast _ _ _ _) = _
  rw [wordCast_comp _ _ rfl rfl, wordCast_xev, wordCast_self,
    hm, xev_map_ofL, ← he, xev_map_ofL]
  exact hz


/-- Closure proves independence of the literal weak family, then finite
surjective normalization transfers it to the strict target choice. The two
extra top-serializer premises are discharged by `atTopSplit` below. -/
theorem strict_injective_of_top_data {l r : List I} {a b : List (Letter I)}
    (U : MatchingBasisChoice (ups l ++ a) (b ++ ups r))
    (F : MatchingBasisChoice (a ++ dualW (ups r)) (dns l ++ b))
    (hq : ∀ R : U.members, ∀ j ∈ leftEnds₂ (ups l ++ a) R.val,
      (U.points R j).1 ≤ R.val.length)
    (hOrd : ∀ t : U.Labels, ∃ L : List (LayerData I),
      SChain (ups l ++ a) L (b ++ ups r) ∧ L.map ofL = U.layers t)
    (hpos : ∀ (t : U.Labels) (z : PositiveWordDots (b ++ ups r) →₀ SYM D k),
      ∃ v : U.Labels →₀ SYM D k,
        (∀ u ∈ v.support, U.openDots t < U.openDots u) ∧
        U.targetExpansion cs μ v = xev cs μ (ups l ++ a) (b ++ ups r) (U.layers t) ≫
          positiveWordExpansion cs μ (b ++ ups r) z)
    (hU : Function.Injective (U.expansion cs μ)) :
    Function.Injective (F.expansion cs (wt D μ (ups r))) := by
  classical
  let W := weakChoice U F hq
  let e := sourceLabelsEquiv U F hq
  let E : (F.Labels →₀ SYM D k) ≃ₗ[k] (U.Labels →₀ SYM D k) := Finsupp.domLCongr e
  let strong := (U.targetExpansion cs μ).comp E.toLinearMap
  have hstrong : Function.Injective strong :=
    ((U.expansion_injective_iff_target cs μ).mp hU).comp E.injective
  apply W.strict_expansion_injective cs (wt D μ (ups r))
  apply (W.expansion_injective_iff_target cs (wt D μ (ups r))).mpr
  apply OrientedReduction.injective_of_positive_closure F.openDots
    (W.targetExpansion cs (wt D μ (ups r))) strong (closure μ l r a b) hstrong
  intro t p
  obtain ⟨L, hL, he⟩ := hOrd (e t)
  have hc := closure_decorated_coefficient cs μ
    (U.matching (e t).1.val (e t).1.property).1 (U.points (e t).1)
    (fun j hj => ⟨hq _ j hj, U.onStrand _ j hj⟩) (e t).2
    (U.decorates (e t).1 (e t).2) hL he p
  obtain ⟨z, hz⟩ := hc
  obtain ⟨v, hv, hev⟩ := hpos (e t) z
  refine ⟨E.symm v, ?_, ?_⟩
  · intro u hu
    have hu' : v (e u) ≠ 0 := by
      have h := Finsupp.mem_support_iff.mp hu
      simpa only [E, Finsupp.domLCongr_apply, Finsupp.domLCongr_symm,
        Finsupp.domCongr_apply, Finsupp.equivMapDomain_apply, Equiv.symm_symm] using h
    have h := hv (e u) (Finsupp.mem_support_iff.mpr hu')
    simpa only [e, sourceLabelsEquiv_openDots] using h
  · rw [W.targetExpansion_single]
    change closure μ l r a b (xev cs (wt D μ (ups r)) _ _ (W.layers t) ≫ _) = _
    rw [weakChoice_layers U F hq t]
    change closure μ l r a b _ = U.targetExpansion cs μ (E (Finsupp.single t p + E.symm v))
    rw [map_add, E.apply_symm_apply, map_add, hev]
    have hs : E (Finsupp.single t p) = Finsupp.single (e t) p := by simp [E]
    rw [hs, U.targetExpansion_single]
    exact hz


/-- Full upward independence, with exactly the equal-weight restriction in
BE2's nondegeneracy conjecture and unrestricted abstract-SYM coefficients. -/
def UpwardIndependence : Prop :=
  ∀ (a b : List I), wt D 0 (ups a) = wt D 0 (ups b) →
    ∀ (ν : X) (U : MatchingBasisChoice (ups a) (ups b)),
      Function.Injective (U.expansion cs ν)

private theorem upward_injective (h : UpwardIndependence cs)
    (a b : List I) (ν : X) (U : MatchingBasisChoice (ups a) (ups b)) :
    Function.Injective (U.expansion cs ν) := by
  classical
  by_cases hn : Nonempty U.members
  · obtain ⟨R⟩ := hn
    exact h a b ((U.matching R.val R.property).1.wt_eq D 0) ν U
  · intro v w _
    ext t
    exact False.elim (hn ⟨t.1⟩)

private theorem wt_translate (ν : X) (a : List (Letter I)) :
    wt D ν a = wt D 0 a + ν := by
  induction a with
  | nil => simp
  | cons x a ih => simp only [wt_cons, ih]; abel

/-- Full upward independence implies independence for every sorted oriented
boundary pair, at every external weight and every strict matching choice.
No bubble faithfulness, separate serializer input, or strictness of inverse
mates is assumed. General boundary sorting is a separate step. -/
theorem sorted_independence (hUp : UpwardIndependence cs)
    (l a b r : List I) (ξ : X)
    (F : MatchingBasisChoice (ups a ++ dns r) (dns l ++ ups b)) :
    Function.Injective (F.expansion cs ξ) := by
  let ν := ξ - wt D 0 (ups r)
  have hν : wt D ν (ups r) = ξ := by rw [wt_translate]; dsimp [ν]; abel
  let U₀ : MatchingBasisChoice (ups l ++ ups a) (ups b ++ ups r) :=
    Classical.choice (MatchingBasisChoice.nonempty _ _)
  let U := U₀.atTopSplit l a b r
  have hU : Function.Injective (U.expansion cs ν) := by
    have hs : ups l ++ ups a = ups (l ++ a) := (ups_append l a).symm
    have ht : ups b ++ ups r = ups (b ++ r) := (ups_append b r).symm
    exact (U.cast_expansion_injective_iff cs ν hs ht).mp
      (upward_injective cs hUp (l ++ a) (b ++ r) ν (U.cast hs ht))
  have hs : ups a ++ dns r = ups a ++ dualW (ups r) := by rw [dualW_ups]
  have H := strict_injective_of_top_data cs ν U (F.cast hs rfl)
    (fun R j _ => U₀.atTopSplit_bounded l a b r R j)
    (U₀.atTopSplit_ordinary l a b r)
    (U₀.atTopSplit_positiveExpansion_lift cs l a b r ν) hU
  have H' := (F.cast_expansion_injective_iff cs (wt D ν (ups r)) hs rfl).mp H
  exact hν ▸ H'

end OddMath.SKM.WeakMate
