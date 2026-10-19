import OddMath.SKM.TwoSidedGrading
import OddMath.SKM.MixedDotGrading

/-! # Decorated reduced-representative comparison

BE2, arXiv:1701.04133v2, §8 and Theorem 10.3,
choice independence and the numerical right-cup step of Claim 2.
Finite labels use the existing left endpoints, not raw count-function quotients.
Points and valid serializations may be chosen independently before any grading.
-/
namespace OddMath.SKM
open StringDiagrams StringDiagrams.Chord DTMove
open scoped BigOperators
variable {I X : Type*} [AddCommGroup X]

/-- Extend the endpoint-preserving correspondence of `cupAttachStrandEquiv`
to an arbitrary isomorphism of the existing boundary pairings. -/
def matchingStrandEquivOfIso {a b : List (Letter I)} {R S : List (TMove (Letter I))}
    (hi : Iso (pairing₂ a R) (pairing₂ b S)) : MatchingStrand a R ≃ MatchingStrand b S where
  toFun j := ⟨j.val, mem_leftEnds₂.mpr ((isLeftEnd_iso hi).mp (mem_leftEnds₂.mp j.property))⟩
  invFun j := ⟨j.val, mem_leftEnds₂.mpr ((isLeftEnd_iso hi).mpr (mem_leftEnds₂.mp j.property))⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem matchingStrandEquivOfIso_val {a b : List (Letter I)}
    {R S : List (TMove (Letter I))} (hi : Iso (pairing₂ a R) (pairing₂ b S))
    (j : MatchingStrand a R) : (matchingStrandEquivOfIso hi j).val = j.val := rfl

/-- Colour is preserved by the actual letter equality in `Iso.1`. -/
theorem matchingStrandColour_iso {a b : List (Letter I)}
    {R S : List (TMove (Letter I))} (hi : Iso (pairing₂ a R) (pairing₂ b S))
    (j : MatchingStrand a R) :
    matchingStrandColour b S (matchingStrandEquivOfIso hi j) = matchingStrandColour a R j := by
  have he := congrArg (fun l : List (Letter I) => l[j.val]?) hi.1
  have hj := (mem_leftEnds₂.mp j.property).1
  have hk : j.val < (pairing₂ b S).length :=
    (mem_leftEnds₂.mp (matchingStrandEquivOfIso hi j).property).1
  simp only [List.getElem?_map, List.getElem?_eq_getElem hj,
    List.getElem?_eq_getElem hk, Option.map_some, Option.some.injEq] at he
  exact (congrArg Prod.snd he).symm

/-- Reindex finite strand contributions by the endpoint-preserving equivalence. -/
theorem matchingStrand_sum_transport {a b : List (Letter I)}
    {R S : List (TMove (Letter I))} (hi : Iso (pairing₂ a R) (pairing₂ b S))
    (c : MatchingStrand a R → ℕ) {M : Type*} [AddCommMonoid M] (f : ℕ → I → M) :
    (∑ j, f ((c ∘ (matchingStrandEquivOfIso hi).symm) j) (matchingStrandColour b S j)) =
      ∑ j, f (c j) (matchingStrandColour a R j) := by
  classical
  rw [← (matchingStrandEquivOfIso hi).sum_comp]
  simp only [Function.comp_apply, Equiv.symm_apply_apply, matchingStrandColour_iso]

/-- Independently chosen strand points and valid serializers give the same degree
and parity on two crossing-minimal representatives of one boundary pairing. -/
theorem mixed_decorated_degree_parity_of_iso (D : Datum I X) (sy : Symmetrizer D) (μ : X)
    {a b : List (Letter I)} {R S : List (TMove (Letter I))}
    (hR : IsMatching₂ a b R) (hrR : Reduced₂ a R)
    (hS : IsMatching₂ a b S) (hrS : Reduced₂ a S)
    (hi : Iso (pairing₂ a R) (pairing₂ a S))
    (q r : ℕ → ℕ × ℕ)
    (hq : ∀ j ∈ leftEnds₂ a R, OnStrand₂ a R j (q j))
    (hr : ∀ j ∈ leftEnds₂ a S, OnStrand₂ a S j (r j))
    (c : MatchingStrand a R → ℕ) (ds es : List (DTMove I))
    (hd : Decorates₂ a R q (strandCounts c) ds)
    (he : Decorates₂ a S r (strandCounts (c ∘ (matchingStrandEquivOfIso hi).symm)) es) :
    tableDegree D sy μ (dLay a ds) = tableDegree D sy μ (dLay a es) ∧
      xpar D μ (dLay a ds) = xpar D μ (dLay a es) := by
  obtain ⟨hdR, hpR⟩ := mixed_decorated_degree_parity D sy μ hR q hq c ds hd
  obtain ⟨hdS, hpS⟩ := mixed_decorated_degree_parity D sy μ hS r hr _ es he
  obtain ⟨hb, hp⟩ := reduced₂_degree_parity_of_iso D sy μ hR hrR hS hrS hi
  rw [matchingStrand_sum_transport hi c (fun n i => (n : ℤ) * (2 * sy.d i))] at hdS
  rw [matchingStrand_sum_transport hi c (fun n i => (n : ZMod 2) * D.parity i)] at hpS
  exact ⟨by rw [hdR, hdS, hb], by rw [hpR, hpS, hp]⟩

/-- Literal attachment evaluated from the existing layer identity, before normalization. -/
theorem cupAttach_table_degree_parity (D : Datum I X) (sy : Symmetrizer D) (μ : X)
    {i : I} {a b : List (Letter I)} {R : List (TMove (Letter I))}
    (hR : IsMatching₂ ((true, i) :: a) b R) {ds : List (DTMove I)} (hd : tmoves ds = R) :
    tableDegree D sy μ (dLay a (cupAttachMoves i ds)) =
      tableDegree D sy μ (dLay ((true, i) :: a) ds) + sy.d i * (1 + D.h i (wt D μ a)) ∧
    xpar D μ (dLay a (cupAttachMoves i ds)) = xpar D μ (dLay ((true, i) :: a) ds) := by
  rw [dLay_cupAttach hR hd]
  constructor
  · rw [tableDegree_append, tableDegree_whisk, wt_nil]
    simp [tableDegree, ofL, gdeg, add_comm]
  · rw [xpar_append, xpar_map_xwhL]
    simp [xpar, xlpar, ofL, Shape.parity]

/-- The normalized right cup has the source degree shift and no parity shift.
Both reduced representatives, their matching hypotheses, the pairing isomorphism,
and independently chosen valid point decorations remain explicit. -/
theorem cupAttach_normalized_decorated_degree_parity
    (D : Datum I X) (sy : Symmetrizer D) (μ : X)
    {i : I} {a b : List (Letter I)} {R S : List (TMove (Letter I))}
    (hR : IsMatching₂ ((true, i) :: a) b R) (hrR : Reduced₂ ((true, i) :: a) R)
    (hS : IsMatching₂ a ((false, i) :: b) S) (hrS : Reduced₂ a S)
    (hi : Iso (pairing₂ ((true, i) :: a) R) (pairing₂ a S))
    (q r : ℕ → ℕ × ℕ)
    (hq : ∀ j ∈ leftEnds₂ ((true, i) :: a) R,
      (q j).1 ≤ R.length ∧ OnStrand₂ ((true, i) :: a) R j (q j))
    (hr : ∀ j ∈ leftEnds₂ a S, OnStrand₂ a S j (r j))
    (c : MatchingStrand ((true, i) :: a) R → ℕ) (ds es : List (DTMove I))
    (hd : Decorates₂ ((true, i) :: a) R q (strandCounts c) ds)
    (he : Decorates₂ a S r (strandCounts (c ∘ (matchingStrandEquivOfIso hi).symm)) es) :
    tableDegree D sy μ (dLay a es) = tableDegree D sy μ (dLay ((true, i) :: a) ds) +
      sy.d i * (1 + D.h i (wt D μ a)) ∧
    xpar D μ (dLay a es) = xpar D μ (dLay ((true, i) :: a) ds) := by
  obtain ⟨hm, hc⟩ := cupAttach_matching_iso hR
  let hi' := hc.trans hi
  have hq' : ∀ j ∈ leftEnds₂ a (cupAttachMatching i R),
      OnStrand₂ a (cupAttachMatching i R) j ((cupAttachPoint ∘ q) j) := by
    intro j hj
    rw [leftEnds₂_cupAttach hR] at hj
    exact (onStrand₂_cupAttach hR (hq j hj).1 (hq j hj).2).2
  have hcounts : (c ∘ (cupAttachStrandEquiv hR).symm) ∘
      (matchingStrandEquivOfIso hi').symm = c ∘ (matchingStrandEquivOfIso hi).symm := by
    funext j
    rfl
  have he' : Decorates₂ a S r
      (strandCounts ((c ∘ (cupAttachStrandEquiv hR).symm) ∘
        (matchingStrandEquivOfIso hi').symm)) es := by rw [hcounts]; exact he
  obtain ⟨hdeg, hpar⟩ := mixed_decorated_degree_parity_of_iso D sy μ
    hm (reduced₂_cupAttach hR hrR) hS hrS hi' (cupAttachPoint ∘ q) r hq' hr
    (c ∘ (cupAttachStrandEquiv hR).symm) (cupAttachMoves i ds) es
    (decorates₂_cupAttach hR q c hd) he'
  obtain ⟨hraw, hpraw⟩ := cupAttach_table_degree_parity D sy μ hR hd.1
  exact ⟨hdeg.symm.trans hraw, hpar.symm.trans hpraw⟩

end OddMath.SKM
