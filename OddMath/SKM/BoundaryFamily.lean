import OddMath.SKM.BoundaryNormalization
import OddMath.SKM.MatchingStrandColour

/-! Strand-labelled boundary exchange for BE2 v2 Theorem 10.3 Claim 4.
Representatives are constructed by strict realization of the swapped pairing.
The finite strand map is the adjacent endpoint transposition, not a chosen
colour bijection. -/
noncomputable section
namespace OddMath.SKM
open StringDiagrams StringDiagrams.Chord
open scoped BigOperators
variable {I : Type*}

/-- Strict realization after swapping two adjacent bottom endpoints. -/
theorem exists_strictReduced_boundary_swap (a b : List (Letter I)) (x y : Letter I)
    {R : List (TMove (Letter I))} (hR : IsMatching₂ (a ++ x :: y :: b) [] R) :
    ∃ S, IsMatching₂ (a ++ y :: x :: b) [] S ∧
      StrictReduced₂ (a ++ y :: x :: b) S ∧
      Iso (pairing₂ (a ++ y :: x :: b) S)
        (swapAt (pairing₂ (a ++ x :: y :: b) R) b.length) := by
  obtain ⟨hv, hl, hs⟩ := hR.pairing_properties
  have hp : b.length + 1 < (pairing₂ (a ++ x :: y :: b) R).length := by
    have h := congrArg List.length hs
    simp only [List.length_map, List.length_append, length_dualW,
      List.length_cons, List.length_nil] at h
    omega
  apply exists_strictReduced_matching (hv.swapAt hp)
    (hl.swapAt_of_involutive flipL_involutive hp)
  rw [map_swapAt, hs]
  simp only [List.append_nil, dualW_append, dualW_cons, List.append_assoc,
    List.cons_append, List.nil_append]
  rw [← length_dualW b, swapAt_mid]

/-- Coverage and uniqueness construct the representative equivalence. -/
theorem boundary_swap_representatives_equiv (a b : List (Letter I)) (x y : Letter I)
    (M N : Set (List (TMove (Letter I))))
    (hM : ∀ R ∈ M, IsMatching₂ (a ++ x :: y :: b) [] R ∧ StrictReduced₂ (a ++ x :: y :: b) R)
    (hN : ∀ S ∈ N, IsMatching₂ (a ++ y :: x :: b) [] S ∧ StrictReduced₂ (a ++ y :: x :: b) S)
    (hMrep : ∀ R, IsMatching₂ (a ++ x :: y :: b) [] R → StrictReduced₂ (a ++ x :: y :: b) R →
      ∃ S ∈ M, Iso (pairing₂ (a ++ x :: y :: b) S) (pairing₂ (a ++ x :: y :: b) R))
    (hNrep : ∀ R, IsMatching₂ (a ++ y :: x :: b) [] R → StrictReduced₂ (a ++ y :: x :: b) R →
      ∃ S ∈ N, Iso (pairing₂ (a ++ y :: x :: b) S) (pairing₂ (a ++ y :: x :: b) R))
    (hMuniq : ∀ R ∈ M, ∀ S ∈ M,
      Iso (pairing₂ (a ++ x :: y :: b) R) (pairing₂ (a ++ x :: y :: b) S) → R = S)
    (hNuniq : ∀ R ∈ N, ∀ S ∈ N,
      Iso (pairing₂ (a ++ y :: x :: b) R) (pairing₂ (a ++ y :: x :: b) S) → R = S) :
    ∃ E : {R // R ∈ M} ≃ {S // S ∈ N}, ∀ R,
      Iso (pairing₂ (a ++ y :: x :: b) (E R).val)
        (swapAt (pairing₂ (a ++ x :: y :: b) R.val) b.length) := by
  classical
  have hex (R : {R // R ∈ M}) : ∃ S : {S // S ∈ N},
      Iso (pairing₂ (a ++ y :: x :: b) S.val)
        (swapAt (pairing₂ (a ++ x :: y :: b) R.val) b.length) := by
    obtain ⟨S, hS, hr, hi⟩ := exists_strictReduced_boundary_swap a b x y (hM R R.property).1
    obtain ⟨T, hT, hTS⟩ := hNrep S hS hr
    exact ⟨⟨T, hT⟩, hTS.trans hi⟩
  let f := fun R => (hex R).choose
  have hf (R : {R // R ∈ M}) : Iso (pairing₂ (a ++ y :: x :: b) (f R).val)
      (swapAt (pairing₂ (a ++ x :: y :: b) R.val) b.length) := (hex R).choose_spec
  have hinj : Function.Injective f := by
    intro R S h
    apply Subtype.ext
    apply hMuniq R R.property S S.property
    have hi := ((hf R).symm.trans (h ▸ hf S)).swapAt b.length
    simpa only [swapAt_swapAt] using hi
  have hsurj : Function.Surjective f := by
    intro S
    obtain ⟨R, hR, hr, hi⟩ := exists_strictReduced_boundary_swap a b y x (hN S S.property).1
    obtain ⟨T, hT, hTR⟩ := hMrep R hR hr
    refine ⟨⟨T, hT⟩, Subtype.ext ?_⟩
    apply hNuniq _ (f ⟨T, hT⟩).property S S.property
    have hh := (hf ⟨T, hT⟩).trans ((hTR.trans hi).swapAt b.length)
    simpa only [swapAt_swapAt] using hh
  exact ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, hf⟩

/-- Swapping endpoints of different strands preserves which endpoint is left. -/
theorem isLeftEnd_swapAt_of_not_same {s : List (ℕ × Letter I)} {p j : ℕ}
    (hp : p + 1 < s.length) (hn : ¬ Same s p (p + 1)) (hj : IsLeftEnd s j) :
    IsLeftEnd (swapAt s p) (tau p j) := by
  refine ⟨?_, ?_⟩
  · rw [length_swapAt]
    have := hj.1
    unfold tau
    split_ifs <;> omega
  · rintro ⟨k, hk, hs⟩
    rw [same_swapAt hp, tau_tau] at hs
    have hne : ¬ (tau p k = p ∧ j = p + 1) := by
      rintro ⟨he, rfl⟩
      rw [he] at hs
      exact hn hs.symm
    have hne' : ¬ (tau p k = p + 1 ∧ j = p) := by
      rintro ⟨he, rfl⟩
      rw [he] at hs
      exact hn hs
    have hlt := (tau_lt_iff p hne hne').mp (by simpa only [tau_tau] using hk)
    exact hj.2 ⟨tau p k, hlt, hs⟩

/-- The literal endpoint transposition on finite matching strands. -/
def matchingStrandEquivOfSwap {A B : List (Letter I)} {R S : List (TMove (Letter I))}
    {p : ℕ} (hp : p + 1 < (pairing₂ A R).length)
    (hn : ¬ Same (pairing₂ A R) p (p + 1))
    (hi : Iso (pairing₂ B S) (swapAt (pairing₂ A R) p)) :
    MatchingStrand A R ≃ MatchingStrand B S where
  toFun j := ⟨tau p j.val, mem_leftEnds₂.mpr ((isLeftEnd_iso hi).mpr
    (isLeftEnd_swapAt_of_not_same hp hn (mem_leftEnds₂.mp j.property)))⟩
  invFun j := ⟨tau p j.val, mem_leftEnds₂.mpr (by
    have hh := isLeftEnd_swapAt_of_not_same (by simpa only [length_swapAt] using hp)
      (s := swapAt (pairing₂ A R) p) (p := p)
      (by simpa only [same_swapAt hp, tau_left, tau_right] using fun h => hn h.symm)
      ((isLeftEnd_iso hi).mp (mem_leftEnds₂.mp j.property))
    simpa only [swapAt_swapAt] using hh)⟩
  left_inv j := Subtype.ext (tau_tau p j.val)
  right_inv j := Subtype.ext (tau_tau p j.val)

@[simp] theorem matchingStrandEquivOfSwap_val
    {A B : List (Letter I)} {R S : List (TMove (Letter I))}
    {p : ℕ} (hp : p + 1 < (pairing₂ A R).length)
    (hn : ¬ Same (pairing₂ A R) p (p + 1))
    (hi : Iso (pairing₂ B S) (swapAt (pairing₂ A R) p)) (j : MatchingStrand A R) :
    (matchingStrandEquivOfSwap hp hn hi j).val = tau p j.val := rfl

/-- Colour preservation follows from the transposed boundary letters. -/
theorem matchingStrandColour_swap {A B : List (Letter I)} {R S : List (TMove (Letter I))}
    {p : ℕ} (hp : p + 1 < (pairing₂ A R).length)
    (hn : ¬ Same (pairing₂ A R) p (p + 1))
    (hi : Iso (pairing₂ B S) (swapAt (pairing₂ A R) p)) (j : MatchingStrand A R) :
    matchingStrandColour B S (matchingStrandEquivOfSwap hp hn hi j) = matchingStrandColour A R j := by
  have he := congrArg (fun l : List (Letter I) => l[tau p j.val]?) hi.1
  rw [List.getElem?_map, List.getElem?_map, getElem?_swapAt _ hp, tau_tau] at he
  have hj := (mem_leftEnds₂.mp j.property).1
  have hk := (mem_leftEnds₂.mp (matchingStrandEquivOfSwap hp hn hi j).property).1
  simp only [matchingStrandEquivOfSwap_val] at hk
  simp only [List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hk,
    Option.map_some, Option.some.injEq] at he
  exact congrArg Prod.snd he

/-- Bounds and distinct-strand condition follow from the matching boundary. -/
theorem boundary_swap_strand_data (a b : List (Letter I)) (x y : Letter I)
    (hxy : x.2 ≠ y.2) {R : List (TMove (Letter I))}
    (hR : IsMatching₂ (a ++ x :: y :: b) [] R) :
    b.length + 1 < (pairing₂ (a ++ x :: y :: b) R).length ∧
      ¬ Same (pairing₂ (a ++ x :: y :: b) R) b.length (b.length + 1) := by
  obtain ⟨_, hl, hs⟩ := hR.pairing_properties
  have hs' : (pairing₂ (a ++ x :: y :: b) R).map Prod.snd =
      dualW b ++ flipL y :: flipL x :: dualW a := by
    simpa only [List.append_nil, dualW_append, dualW_cons, List.append_assoc,
      List.cons_append, List.nil_append] using hs
  constructor
  · have h := congrArg List.length hs'
    simp only [List.length_map, List.length_append, List.length_cons, length_dualW] at h
    omega
  · intro hn
    have he := hl b.length (b.length + 1) hn (by omega)
    have hx : ((pairing₂ (a ++ x :: y :: b) R)[b.length]?).map Prod.snd = some (flipL y) := by
      rw [← List.getElem?_map, hs', ← length_dualW b]
      simp
    have hy : ((pairing₂ (a ++ x :: y :: b) R)[b.length + 1]?).map Prod.snd = some (flipL x) := by
      rw [← List.getElem?_map, hs', ← length_dualW b]
      simp
    rw [hy, ← Option.map_map, hx] at he
    have e : flipL x = flipL (flipL y) := Option.some.inj he
    apply hxy
    simpa only [flipL] using congrArg Prod.snd e

/-- Reindex each finite strand sum by the constructed endpoint correspondence. -/
theorem matchingStrand_swap_sum {A B : List (Letter I)} {R S : List (TMove (Letter I))}
    {p : ℕ} (hp : p + 1 < (pairing₂ A R).length)
    (hn : ¬ Same (pairing₂ A R) p (p + 1))
    (hi : Iso (pairing₂ B S) (swapAt (pairing₂ A R) p))
    (c : MatchingStrand A R → ℕ) {K : Type*} [AddCommMonoid K] (f : ℕ → I → K) :
    (∑ j, f ((c ∘ (matchingStrandEquivOfSwap hp hn hi).symm) j) (matchingStrandColour B S j)) =
      ∑ j, f (c j) (matchingStrandColour A R j) := by
  classical
  rw [← (matchingStrandEquivOfSwap hp hn hi).sum_comp]
  simp only [Function.comp_apply, Equiv.symm_apply_apply, matchingStrandColour_swap]

/-- Lift the constructed endpoint maps to all natural strand counts by inverse precomposition. -/
def boundarySwapLabelledEquiv {a b : List (Letter I)} {x y : Letter I}
    {M N : Set (List (TMove (Letter I)))} (hxy : x.2 ≠ y.2)
    (hM : ∀ R ∈ M, IsMatching₂ (a ++ x :: y :: b) [] R)
    (E : {R // R ∈ M} ≃ {S // S ∈ N})
    (hE : ∀ R, Iso (pairing₂ (a ++ y :: x :: b) (E R).val)
      (swapAt (pairing₂ (a ++ x :: y :: b) R.val) b.length)) :
    (Σ R : {R // R ∈ M}, MatchingStrand (a ++ x :: y :: b) R.val → ℕ) ≃
      (Σ S : {S // S ∈ N}, MatchingStrand (a ++ y :: x :: b) S.val → ℕ) :=
  Equiv.sigmaCongr E (fun R => Equiv.arrowCongr
    (matchingStrandEquivOfSwap (boundary_swap_strand_data a b x y hxy (hM R R.property)).1
      (boundary_swap_strand_data a b x y hxy (hM R R.property)).2 (hE R)) (Equiv.refl ℕ))

end OddMath.SKM
