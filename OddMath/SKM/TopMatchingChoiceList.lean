import OddMath.SKM.TopClosureCoefficients

/-! Top serializers transported to literal list boundaries. -/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Presentation
universe u v w
variable {I : Type u} {c d : ℕ} (α : Fin c → I) (β : Fin d → I)
namespace MatchingBasisChoice
variable {a b : List (Letter I)}

def atTopAlong (ha : (List.ofFn fun j => (true, α j)) = a)
    (hb : (List.ofFn fun j => (true, β j)) = b)
    (F : MatchingBasisChoice a b) : MatchingBasisChoice a b := by
  subst a b
  exact F.atTop α β

theorem atTopAlong_bounded (ha : (List.ofFn fun j => (true, α j)) = a)
    (hb : (List.ofFn fun j => (true, β j)) = b)
    (F : MatchingBasisChoice a b) (R : (F.atTopAlong α β ha hb).members) (j : ℕ) :
    ((F.atTopAlong α β ha hb).points R j).1 ≤ R.val.length := by
  subst a b
  exact F.atTop_bounded α β R j

theorem atTopAlong_valid (ha : (List.ofFn fun j => (true, α j)) = a)
    (hb : (List.ofFn fun j => (true, β j)) = b)
    (F : MatchingBasisChoice a b) (R : (F.atTopAlong α β ha hb).members)
    (n : MatchingStrand a R.val → ℕ) :
    DOk₂ a ((F.atTopAlong α β ha hb).serialize R n) := by
  subst a b
  exact F.atTop_valid α β R n

theorem atTopAlong_ordinary (ha : (List.ofFn fun j => (true, α j)) = a)
    (hb : (List.ofFn fun j => (true, β j)) = b)
    (F : MatchingBasisChoice a b) (t : (F.atTopAlong α β ha hb).Labels) :
    ∃ L : List (LayerData I), SChain a L b ∧ L.map ofL = (F.atTopAlong α β ha hb).layers t := by
  subst a b
  exact F.atTop_ordinary α β t

variable {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} (cs : CScalars Sc)
theorem atTopAlong_positiveExpansion_lift
    (ha : (List.ofFn fun j => (true, α j)) = a)
    (hb : (List.ofFn fun j => (true, β j)) = b)
    (F : MatchingBasisChoice a b) (μ : X)
    (t : (F.atTopAlong α β ha hb).Labels) (z : PositiveWordDots b →₀ SYM D k) :
    ∃ r : (F.atTopAlong α β ha hb).Labels →₀ SYM D k,
      (∀ u ∈ r.support, (F.atTopAlong α β ha hb).openDots t <
        (F.atTopAlong α β ha hb).openDots u) ∧
      (F.atTopAlong α β ha hb).targetExpansion cs μ r =
        xev cs μ a b ((F.atTopAlong α β ha hb).layers t) ≫
          positiveWordExpansion cs μ b z := by
  subst a b
  exact F.top_positiveExpansion_lift cs α β μ t z

end MatchingBasisChoice

/-- Every literal upward list has the standard finite-function presentation. -/
theorem ofFn_up_get (a : List I) :
    (List.ofFn fun j : Fin a.length => (true, a.get j)) = ups a := by
  simpa only [List.map_ofFn, Function.comp_def, ups, up] using
    congrArg (List.map (fun i : I => (true, i))) (List.ofFn_get a)

/-- The source split used in the oriented closure argument. -/
theorem ofFn_up_get_append (a b : List I) :
    (List.ofFn fun j : Fin (a ++ b).length => (true, (a ++ b).get j)) =
      ups a ++ ups b := by
  rw [ofFn_up_get, ups_append]

namespace MatchingBasisChoice

def atTopList (a b : List I) (F : MatchingBasisChoice (ups a) (ups b)) :
    MatchingBasisChoice (ups a) (ups b) :=
  F.atTopAlong a.get b.get (ofFn_up_get a) (ofFn_up_get b)

def atTopSplit (l a b r : List I)
    (F : MatchingBasisChoice (ups l ++ ups a) (ups b ++ ups r)) :
    MatchingBasisChoice (ups l ++ ups a) (ups b ++ ups r) :=
  F.atTopAlong (l ++ a).get (b ++ r).get (ofFn_up_get_append l a) (ofFn_up_get_append b r)

theorem atTopSplit_bounded (l a b r : List I)
    (F : MatchingBasisChoice (ups l ++ ups a) (ups b ++ ups r))
    (R : (F.atTopSplit l a b r).members) (j : ℕ) :
    ((F.atTopSplit l a b r).points R j).1 ≤ R.val.length :=
  F.atTopAlong_bounded (l ++ a).get (b ++ r).get _ _ R j

theorem atTopSplit_ordinary (l a b r : List I)
    (F : MatchingBasisChoice (ups l ++ ups a) (ups b ++ ups r))
    (t : (F.atTopSplit l a b r).Labels) :
    ∃ L : List (LayerData I), SChain (ups l ++ ups a) L (ups b ++ ups r) ∧
      L.map ofL = (F.atTopSplit l a b r).layers t :=
  F.atTopAlong_ordinary (l ++ a).get (b ++ r).get _ _ t

variable {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} (cs : CScalars Sc)

theorem atTopSplit_positiveExpansion_lift (l a b r : List I)
    (F : MatchingBasisChoice (ups l ++ ups a) (ups b ++ ups r)) (μ : X)
    (t : (F.atTopSplit l a b r).Labels) (z : PositiveWordDots (ups b ++ ups r) →₀ SYM D k) :
    ∃ v : (F.atTopSplit l a b r).Labels →₀ SYM D k,
      (∀ u ∈ v.support, (F.atTopSplit l a b r).openDots t <
        (F.atTopSplit l a b r).openDots u) ∧
      (F.atTopSplit l a b r).targetExpansion cs μ v =
        xev cs μ (ups l ++ ups a) (ups b ++ ups r) ((F.atTopSplit l a b r).layers t) ≫
          positiveWordExpansion cs μ (ups b ++ ups r) z :=
  F.atTopAlong_positiveExpansion_lift (l ++ a).get (b ++ r).get cs _ _ μ t z

end MatchingBasisChoice
end OddMath.SKM
