import OddMath.SKM.PositivePointGrading

/-! Strand-point and dot-order tests for positive decorated degree/parity. -/

namespace OddMath.SKM.PositivePointGradingExamples
open StringDiagrams StringDiagrams.Chord DTMove
open scoped BigOperators

private def word {I : Type*} (i j : I) : Fin 2 → I := ![i, j]
private def crossing {I : Type*} : List (TMove (Letter I)) := [.mv (.cross 0)]

private theorem matching {I : Type*} (i j : I) :
    IsMatching₂ (List.ofFn fun r => (true, word i j r))
      (List.ofFn fun r => (true, word j i r)) crossing := by
  constructor
  · change 3 < 4 ∧ True
    decide
  · rfl

private theorem reduced {I : Type*} (i j : I) :
    StrictReduced₂ (List.ofFn fun r => (true, word i j r)) crossing := by
  refine ⟨⟨List.nodup_singleton _, ?_⟩, List.nodup_nil⟩
  intro z hz
  change z ∈ [_] at hz
  obtain rfl := List.mem_singleton.mp hz
  change ¬ (s(2, 0) : Sym2 ℕ).IsDiag
  decide

private def position {I : Type*} (i j : I) :
    MatchingStrand (List.ofFn fun r => (true, word i j r)) crossing ≃ Fin 2 where
  toFun x := ⟨x.val, (positive_mem_leftEnds₂ (word i j) (word j i) (matching i j) x).mp x.property⟩
  invFun x := ⟨x.val, (positive_mem_leftEnds₂ (word i j) (word j i) (matching i j) x).mpr x.isLt⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem top_point {I : Type*} (i j : I)
    (x : MatchingStrand (List.ofFn fun r => (true, word i j r)) crossing) :
    OnStrand₂ (List.ofFn fun r => (true, word i j r)) crossing x.val
      (1, (position i j x).val) := by
  rcases x with ⟨x, hx⟩
  have h := (positive_mem_leftEnds₂ (word i j) (word j i) (matching i j) x).mp hx
  interval_cases x
  · change 0 < 2 ∧ 0 = 0
    decide
  · change 1 < 2 ∧ 2 = 2
    decide

private theorem endpoints {I : Type*} (i j : I) : ∀ r : Fin 2,
    Same (pairing₂ (List.ofFn fun r => (true, word i j r)) crossing)
      (2 - 1 - r.val) (2 + ((Equiv.swap 0 1) r).val) := by
  intro r
  fin_cases r
  · change 1 ≠ 3 ∧ (some 2 : Option ℕ) ≠ none ∧ (some 2 : Option ℕ) = some 2
    decide
  · change 0 ≠ 2 ∧ (some 0 : Option ℕ) ≠ none ∧ (some 0 : Option ℕ) = some 0
    decide

/-- A dot on the first bottom strand is on the second top strand after crossing.
The statement works for distinct or repeated colours, and both placements use the headline. -/
theorem crossing_dot_points {I X : Type*} [AddCommGroup X]
    (D : Datum I X) (sy : Symmetrizer D) (μ : X) (i j : I) :
    ∀ ds ∈ [[.dt 0, .tm (.mv (.cross 0))], [.tm (.mv (.cross 0)), .dt 1]],
    ∃ (L : List (LayerData I))
      (hL : SChain [(true, i), (true, j)] L [(true, j), (true, i)]),
      L.map ofL = dLay [(true, i), (true, j)] ds ∧
      Diagram.degree (gdeg D sy) (mkD D μ L hL) = sy.d i * D.d i j + 2 * sy.d i ∧
      xpar D μ (dLay [(true, i), (true, j)] ds) = D.parity i * D.parity j + D.parity i := by
  let A := List.ofFn fun r => (true, word i j r)
  have hl : leftEnds₂ A crossing = [0, 1] := by
    have hh (x : ℕ) : IsLeftEnd (pairing₂ A crossing) x ↔ x < 2 :=
      mem_leftEnds₂.symm.trans
        (positive_mem_leftEnds₂ (word i j) (word j i) (matching i j) x)
    unfold leftEnds₂
    simp only [show (pairing₂ A crossing).length = 4 from rfl, hh]
    decide
  have hbelow : ∀ x ∈ leftEnds₂ A crossing, OnStrand₂ A crossing x (0, 1 - x) := by
    intro x hx
    rw [hl] at hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · change 1 < 2 ∧ 0 = 0
      decide
    · change 0 < 2 ∧ 2 = 2
      decide
  have htop : ∀ x ∈ leftEnds₂ A crossing, OnStrand₂ A crossing x (1, x) := by
    intro x hx
    exact top_point i j ⟨x, hx⟩
  have h1 : 1 ∈ leftEnds₂ [(true, word i j 0), (true, word i j 1)] crossing := by
    change 1 ∈ leftEnds₂ A crossing
    rw [hl]
    simp
  have hb : Decorates₂ A crossing (fun x => (0, 1 - x))
      (strandCounts fun x => (![0, 1] : Fin 2 → ℕ) (position i j x))
      [.dt 0, .tm (.mv (.cross 0))] := by
    constructor
    · rfl
    · simp only [dotPts, hl, List.flatMap_cons, List.flatMap_nil, strandCounts]
      simp [position, h1]
  have ht : Decorates₂ A crossing (fun x => (1, x))
      (strandCounts fun x => (![0, 1] : Fin 2 → ℕ) (position i j x))
      [.tm (.mv (.cross 0)), .dt 1] := by
    constructor
    · rfl
    · simp only [dotPts, hl, List.flatMap_cons, List.flatMap_nil, strandCounts]
      simp [position, h1]
  intro ds hds
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hds
  rcases hds with rfl | rfl
  · simpa [word, Finset.sum_filter, Fin.sum_univ_two] using
      positive_point_decorated_degree_parity D sy μ (word i j) (word j i)
        (matching i j) (reduced i j) (Equiv.swap 0 1) (endpoints i j)
        (position i j) (top_point i j) (fun x => (0, 1 - x)) hbelow ![0, 1] _ hb
  · simpa [word, Finset.sum_filter, Fin.sum_univ_two] using
      positive_point_decorated_degree_parity D sy μ (word i j) (word j i)
        (matching i j) (reduced i j) (Equiv.swap 0 1) (endpoints i j)
        (position i j) (top_point i j) (fun x => (1, x)) htop ![0, 1] _ ht

/-- Two orders of dots at the same height have the same numerical grading;
they are not identified as lists of layers. -/
theorem identity_dot_orders {I X : Type*} [AddCommGroup X]
    (D : Datum I X) (sy : Symmetrizer D) (μ : X) (i j : I) :
    ∀ ds ∈ [[.dt 0, .dt 1], [.dt 1, .dt 0]],
    ∃ (L : List (LayerData I))
      (hL : SChain [(true, i), (true, j)] L [(true, i), (true, j)]),
      L.map ofL = dLay [(true, i), (true, j)] ds ∧
      Diagram.degree (gdeg D sy) (mkD D μ L hL) = 2 * sy.d i + 2 * sy.d j ∧
      xpar D μ (dLay [(true, i), (true, j)] ds) = D.parity i + D.parity j := by
  let a := word i j
  let A := List.ofFn fun r => (true, a r)
  have hm : IsMatching₂ A A [] := ⟨trivial, rfl⟩
  have hr : StrictReduced₂ A [] :=
    ⟨⟨List.nodup_nil, by simp [tRun, tStart]⟩, List.nodup_nil⟩
  have he : ∀ r : Fin 2, Same (pairing₂ A [])
      (2 - 1 - r.val) (2 + ((Equiv.refl _) r).val) := by
    intro r
    fin_cases r
    · change 1 ≠ 2 ∧ (some 2 : Option ℕ) ≠ none ∧ (some 2 : Option ℕ) = some 2
      decide
    · change 0 ≠ 3 ∧ (some 0 : Option ℕ) ≠ none ∧ (some 0 : Option ℕ) = some 0
      decide
  obtain ⟨p', hp', hpp⟩ := positive_top_points a a hm
  let p := Equiv.ofBijective p' hp'
  have hl : leftEnds₂ A [] = [0, 1] := by
    have hh (x : ℕ) : IsLeftEnd (pairing₂ A []) x ↔ x < 2 :=
      mem_leftEnds₂.symm.trans (positive_mem_leftEnds₂ a a hm x)
    unfold leftEnds₂
    simp only [show (pairing₂ A []).length = 4 from rfl, hh]
    decide
  have hq : ∀ x ∈ leftEnds₂ A [], OnStrand₂ A [] x (0, 1 - x) := by
    intro x hx
    rw [hl] at hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · change 1 < 2 ∧ 0 = 0
      decide
    · change 0 < 2 ∧ 2 = 2
      decide
  have hcount (x : ℕ) : strandCounts (a := A) (R := []) (fun _ => 1) x =
      if x ∈ [0, 1] then 1 else 0 := by
    unfold strandCounts
    simp only [hl, dite_eq_ite]
  have hd₀ : Decorates₂ A [] (fun x => (0, 1 - x))
      (strandCounts (a := A) (R := []) fun _ => 1) [.dt 0, .dt 1] := by
    constructor
    · rfl
    · simp only [hl, List.flatMap_cons, List.flatMap_nil, hcount]
      change List.Perm [(0, 0), (0, 1)] [(0, 1), (0, 0)]
      exact List.Perm.swap _ _ []
  have hd₁ : Decorates₂ A [] (fun x => (0, 1 - x))
      (strandCounts (a := A) (R := []) fun _ => 1) [.dt 1, .dt 0] := by
    constructor
    · rfl
    · simp only [hl, List.flatMap_cons, List.flatMap_nil, hcount]
      change List.Perm [(0, 1), (0, 0)] [(0, 1), (0, 0)]
      rfl
  intro ds hds
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hds
  rcases hds with rfl | rfl
  · simpa [a, word, Finset.sum_filter, Fin.sum_univ_two] using
      positive_point_decorated_degree_parity D sy μ a a hm hr (Equiv.refl _) he
        p hpp (fun x => (0, 1 - x)) hq (fun _ => 1) _ hd₀
  · simpa [a, word, Finset.sum_filter, Fin.sum_univ_two] using
      positive_point_decorated_degree_parity D sy μ a a hm hr (Equiv.refl _) he
        p hpp (fun x => (0, 1 - x)) hq (fun _ => 1) _ hd₁

-- Empty colours, and therefore no default colour, are permitted.
example {X : Type*} [AddCommGroup X] (D : Datum Empty X) (sy : Symmetrizer D) (μ : X) :
    ∃ (L : List (LayerData Empty)) (hL : SChain [] L []),
      L.map ofL = dLay [] [] ∧ Diagram.degree (gdeg D sy) (mkD D μ L hL) = 0 ∧
      xpar D μ (dLay [] []) = 0 := by
  let a : Fin 0 → Empty := Fin.elim0
  have hm : IsMatching₂ (List.ofFn fun r => (true, a r))
      (List.ofFn fun r => (true, a r)) [] := ⟨trivial, rfl⟩
  have hr : StrictReduced₂ (List.ofFn fun r => (true, a r)) [] :=
    ⟨⟨List.nodup_nil, by simp [tRun, tStart]⟩, List.nodup_nil⟩
  obtain ⟨p, hp, hpp⟩ := positive_top_points a a hm
  have hl : leftEnds₂ (List.ofFn fun r => (true, a r)) [] = [] := rfl
  have hq : ∀ x ∈ leftEnds₂ (List.ofFn fun r => (true, a r)) [],
      OnStrand₂ (List.ofFn fun r => (true, a r)) [] x (0, 0) := by
    rw [hl]
    simp
  have hd : Decorates₂ (List.ofFn fun r => (true, a r)) [] (fun _ => (0, 0))
      (strandCounts (a := List.ofFn fun r => (true, a r)) (R := []) fun _ => 0) [] := by
    simp only [Decorates₂, tmoves, dotPts, hl, List.flatMap_nil]
    exact ⟨trivial, List.Perm.refl []⟩
  simpa using positive_point_decorated_degree_parity D sy μ a a hm hr (Equiv.refl _)
    (fun r => Fin.elim0 r) (Equiv.ofBijective p hp) hpp (fun _ => (0, 0)) hq (fun _ => 0) [] hd

-- Repeated odd colours retain distinct strands: a crossing and one dot have even parity.
example {I X : Type*} [AddCommGroup X] (D : Datum I X) (sy : Symmetrizer D) (μ : X)
    (i : I) (hi : D.parity i = 1) :
    ∃ (L : List (LayerData I))
      (hL : SChain [(true, i), (true, i)] L [(true, i), (true, i)]),
      L.map ofL = dLay [(true, i), (true, i)] [.dt 0, .tm (.mv (.cross 0))] ∧
      Diagram.degree (gdeg D sy) (mkD D μ L hL) = 0 ∧
      xpar D μ (dLay [(true, i), (true, i)] [.dt 0, .tm (.mv (.cross 0))]) = 0 := by
  have h := crossing_dot_points D sy μ i i _ List.mem_cons_self
  have hz : (1 + 1 : ZMod 2) = 0 := by decide
  simpa [D.d_self, hi, hz, mul_neg, mul_comm] using h

/-- Two orthogonal roots: the first odd, the second even. -/
def twoColourDatum : Datum Bool (Bool → ℤ) where
  cd :=
    { root := fun j i => if i = j then 2 else 0
      coroot := fun i => LinearMap.proj i
      coroot_root_self := fun i => by simp }
  isGCM :=
    { diag := fun i => by simp [CartanDatum.cartanMatrix_apply]
      offDiag_nonpos := fun i j h => by simp [CartanDatum.cartanMatrix_apply, h]
      zero_comm := fun i j => by simp [CartanDatum.cartanMatrix_apply, eq_comm] }
  parity := fun i => if i then 0 else 1
  even_of_odd := by
    intro i j _
    change Even (if i = j then (2 : ℤ) else 0)
    split <;> simp

/-- Unequal dot degrees make confusing physical positions with strand ids detectable. -/
def twoColourSymmetrizer : Symmetrizer twoColourDatum where
  d := fun i => if i then 2 else 1
  pos := by intro i; cases i <;> decide
  symm := by intro i j; cases i <;> cases j <;> rfl

/-- Concrete different-colour crossing: below-left and above-right dots both have
integer degree two and odd parity, with every headline hypothesis discharged. -/
theorem two_colour_point_invariance :
    ∀ ds ∈ [[.dt 0, .tm (.mv (.cross 0))], [.tm (.mv (.cross 0)), .dt 1]],
    ∃ (L : List (LayerData Bool))
      (hL : SChain [(true, false), (true, true)] L [(true, true), (true, false)]),
      L.map ofL = dLay [(true, false), (true, true)] ds ∧
      Diagram.degree (gdeg twoColourDatum twoColourSymmetrizer)
        (mkD twoColourDatum 0 L hL) = 2 ∧
      xpar twoColourDatum 0 (dLay [(true, false), (true, true)] ds) = 1 := by
  simpa [twoColourDatum, twoColourSymmetrizer, Datum.d, Datum.h, Datum.α] using
    crossing_dot_points twoColourDatum twoColourSymmetrizer 0 false true

end OddMath.SKM.PositivePointGradingExamples
