import OddMath.SKM.PositiveMatchingLayers
import OddMath.SKM.PositiveMatchingDots

/-!
# Enumeration of positive top-decorated matchings

The canonical distinguished-point choice of [BE2, arXiv:1701.04133v2, §8],
for positive boundaries in Theorem 10.3, proof of Claim 1. A crossing decoder
recovers the matching from the existing decorated-layer syntax; finite counts
then give an equivalence with the existing canonical `decoratedFamily₂`.
Representative coverage and uniqueness are explicit in the permutation enumeration.
No arbitrary-selector equality, arbitrary-point invariance, quotient-morphism
injectivity, grading comparison or series identity is claimed.
-/

namespace OddMath.SKM
open StringDiagrams.Chord
variable {I : Type*}

private def crossingMove (x : XLayer I) : Option (TMove (Letter I)) :=
  match x.2.1 with
  | .gen (.cross _ _) => some (.mv (.cross x.1.length))
  | _ => none

private theorem crossing_decode {k : ℕ} {u : List (Letter I)} (hu : u.length = k)
    (R : List (TMove (Letter I))) (T : TState (Letter I)) (l : List (Letter I))
    (hl : T.st.map Prod.snd = u ++ l) (hf : TFits flipL k T R)
    (hp : ∀ x ∈ l, x.1 = true) (hc : ∀ m ∈ R, ∃ p, m = TMove.mv (Move.cross p)) :
    (tLay l R).filterMap crossingMove = R := by
  induction R generalizing T l with
  | nil => rfl
  | cons m R ih =>
    obtain ⟨p, rfl⟩ := hc m List.mem_cons_self
    obtain ⟨hm, hf⟩ := hf
    have hlen : T.st.length = k + l.length := by
      have h := congrArg List.length hl
      simpa [hu] using h
    have hpos : p + 1 < l.length := by change k + p + 1 < T.st.length at hm; omega
    have hnext := letters_tRun hu [TMove.mv (Move.cross p)] T l hl ⟨hm, trivial⟩
    simp only [tRun, List.foldl_cons, List.foldl_nil] at hnext
    obtain ⟨v, x, y, w, rfl, rfl⟩ := exists_split_cross hpos
    have hx := hp x (by simp)
    have hy := hp y (by simp)
    obtain ⟨sx, i⟩ := x
    obtain ⟨sy, j⟩ := y
    dsimp only at hx hy
    subst sx sy
    have hstep : tLet (v ++ (true, i) :: (true, j) :: w) (.mv (.cross v.length)) =
        v ++ (true, j) :: (true, i) :: w := chStep_cross v w _ _
    rw [hstep] at hnext
    have hi := ih _ _ hnext hf
      (by simpa only [List.mem_append, List.mem_cons, or_left_comm, or_assoc] using hp)
      (fun m hm => hc m (List.mem_cons_of_mem _ hm))
    simp only [tLay, tmLay, moveLay_cross, hstep]
    simpa [show (true, i) = up i from rfl, show (true, j) = up j from rfl,
      xCrL_up_up, xwhL, crossingMove] using hi

private theorem topDotLayers_crossing_decode {a : List (Letter I)} {d : ℕ}
    (b : Fin d → I) {R : List (TMove (Letter I))}
    (p : MatchingStrand a R → Fin d) (c : MatchingStrand a R → ℕ) :
    ((topDotLayers b p c).map ofL).filterMap crossingMove = [] := by
  simp [topDotLayers, dotsL, List.filterMap_flatMap, ofL, crossingMove]

private theorem positive_topDotMoves_decode {n : ℕ} (a b : Fin n → I)
    {R : List (TMove (Letter I))}
    (hR : IsMatching₂ (List.ofFn fun r => (true, a r))
      (List.ofFn fun r => (true, b r)) R)
    (hred : StrictReduced₂ (List.ofFn fun r => (true, a r)) R)
    (p : MatchingStrand (List.ofFn fun r => (true, a r)) R → Fin n)
    (c : MatchingStrand (List.ofFn fun r => (true, a r)) R → ℕ) :
    (dLay (List.ofFn fun r => (true, a r))
      (topDotMoves (List.ofFn fun r => (true, a r)) R (fun j => (p j).val) c)).filterMap
        crossingMove = R := by
  rw [dLay_topDotMoves b hR p c, List.filterMap_append, topDotLayers_crossing_decode,
    List.append_nil]
  exact crossing_decode (length_dualW _) R _ _ (tStart_letters _) hR.1
    (by intro x hx; obtain ⟨r, rfl⟩ := List.mem_ofFn.mp hx; rfl)
    (hR.positive_crossing_moves a b hred)

/-- Joint syntactic injectivity for positive strictly reduced matchings with canonical
ordered top dots. This does not assert injectivity of evaluation in the SKM quotient. -/
theorem positive_topDotMoves_joint_injective {n : ℕ} (a b : Fin n → I)
    (M : Set (List (TMove (Letter I))))
    (hM : ∀ R ∈ M, IsMatching₂ (List.ofFn fun r => (true, a r))
      (List.ofFn fun r => (true, b r)) R ∧
      StrictReduced₂ (List.ofFn fun r => (true, a r)) R)
    (p : ∀ R : {R // R ∈ M}, MatchingStrand (List.ofFn fun r => (true, a r)) R.val ≃ Fin n) :
    Function.Injective (fun z : {R // R ∈ M} × (Fin n → ℕ) =>
      dLay (List.ofFn fun r => (true, a r))
        (topDotMoves (List.ofFn fun r => (true, a r)) z.1.val
          (fun j => (p z.1 j).val) (fun j => z.2 (p z.1 j)))) := by
  rintro ⟨R, c⟩ ⟨S, d⟩ he
  have hr := congrArg (List.filterMap crossingMove) he
  dsimp only at hr
  rw [positive_topDotMoves_decode a b (hM R R.property).1 (hM R R.property).2,
    positive_topDotMoves_decode a b (hM S S.property).1 (hM S S.property).2] at hr
  have hrs : R = S := Subtype.ext hr
  subst S
  have hc := dLay_topDotMoves_injective b (hM R R.property).1 (p R) (p R).injective he
  have hcd : c = d := by
    funext i
    obtain ⟨j, rfl⟩ := (p R).surjective i
    exact congrFun hc j
  subst d
  rfl

/-- Extend a family's finite top positions only as natural numbers. Outside the family
there need not be a top position, in particular for the empty boundary. -/
noncomputable def topPositionExtension {a : List (Letter I)} {n : ℕ}
    (M : Set (List (TMove (Letter I))))
    (p : ∀ R : {R // R ∈ M}, MatchingStrand a R.val ≃ Fin n)
    (R : List (TMove (Letter I))) : MatchingStrand a R → ℕ := by
  classical
  exact if h : R ∈ M then fun j => (p ⟨R, h⟩ j).val else fun _ => 0

@[simp] theorem topPositionExtension_mem {a : List (Letter I)} {n : ℕ}
    (M : Set (List (TMove (Letter I))))
    (p : ∀ R : {R // R ∈ M}, MatchingStrand a R.val ≃ Fin n)
    (R : {R // R ∈ M}) :
    topPositionExtension M p R.val = fun j => (p R j).val := by
  simp [topPositionExtension, R.property]

/-- The existing canonical decorated family is the range of matching/top-count pairs.
No equality with an arbitrary decoration selector is asserted. -/
theorem topDotMoves_family_range {a : List (Letter I)} {n : ℕ}
    (M : Set (List (TMove (Letter I))))
    (p : ∀ R : {R // R ∈ M}, MatchingStrand a R.val ≃ Fin n) :
    decoratedFamily₂ a M (fun R c => topDotMoves a R (topPositionExtension M p R)
      (fun j => c j)) = Set.range (fun z : {R // R ∈ M} × (Fin n → ℕ) =>
        dLay a (topDotMoves a z.1.val (fun j => (p z.1 j).val) (fun j => z.2 (p z.1 j)))) := by
  rw [topDotMoves_family]
  ext L
  constructor
  · rintro ⟨R, hR, c, rfl⟩
    refine ⟨(⟨R, hR⟩, fun i => c ((p ⟨R, hR⟩).symm i)), ?_⟩
    simp [topPositionExtension, hR]
  · rintro ⟨⟨R, c⟩, rfl⟩
    refine ⟨R.val, R.property, fun j => c (p R j), ?_⟩
    simp

/-- Canonical positive decorated layers are enumerated by a matching and a finite vector
of top dot counts. Both injectivity and surjectivity concern the existing syntactic set. -/
theorem positive_topDotMoves_family_equiv {n : ℕ} (a b : Fin n → I)
    (M : Set (List (TMove (Letter I))))
    (hM : ∀ R ∈ M, IsMatching₂ (List.ofFn fun r => (true, a r))
      (List.ofFn fun r => (true, b r)) R ∧
      StrictReduced₂ (List.ofFn fun r => (true, a r)) R)
    (p : ∀ R : {R // R ∈ M}, MatchingStrand (List.ofFn fun r => (true, a r)) R.val ≃ Fin n) :
    ∃ F : ({R // R ∈ M} × (Fin n → ℕ)) ≃
      {L // L ∈ decoratedFamily₂ (List.ofFn fun r => (true, a r)) M
        (fun R c => topDotMoves (List.ofFn fun r => (true, a r)) R
          (topPositionExtension M p R) (fun j => c j))},
      ∀ z, (F z).val = dLay (List.ofFn fun r => (true, a r))
        (topDotMoves (List.ofFn fun r => (true, a r)) z.1.val
          (fun j => (p z.1 j).val) (fun j => z.2 (p z.1 j))) := by
  classical
  let f := fun z : {R // R ∈ M} × (Fin n → ℕ) =>
    dLay (List.ofFn fun r => (true, a r))
      (topDotMoves (List.ofFn fun r => (true, a r)) z.1.val
        (fun j => (p z.1 j).val) (fun j => z.2 (p z.1 j)))
  have hfamily := topDotMoves_family_range M p
  let g := fun z => (⟨f z, hfamily.symm ▸ Set.mem_range_self z⟩ :
    {L // L ∈ decoratedFamily₂ (List.ofFn fun r => (true, a r)) M
      (fun R c => topDotMoves (List.ofFn fun r => (true, a r)) R
        (topPositionExtension M p R) (fun j => c j))})
  have hg : Function.Bijective g := by
    constructor
    · intro z w he
      exact positive_topDotMoves_joint_injective a b M hM p (congrArg Subtype.val he)
    · rintro ⟨L, hL⟩
      rw [hfamily] at hL
      obtain ⟨z, hz⟩ := hL
      exact ⟨z, Subtype.ext hz⟩
  exact ⟨Equiv.ofBijective g hg, fun _ => rfl⟩

/-- The canonical-top enumeration supporting [BE2, arXiv:1701.04133v2,
Theorem 10.3, proof of Claim 1]. The §8 representative coverage and uniqueness remain
explicit. Top positions are certified before counts are chosen. The permutations send
bottom positions to top positions, and the count vector is indexed at the top.
This is neither arbitrary-point invariance nor injectivity of quotient morphisms. -/
theorem positive_decorated_enumeration {n : ℕ} (a b : Fin n → I)
    (M : Set (List (TMove (Letter I))))
    (hM : ∀ R ∈ M, IsMatching₂ (List.ofFn fun r => (true, a r))
      (List.ofFn fun r => (true, b r)) R ∧
      StrictReduced₂ (List.ofFn fun r => (true, a r)) R)
    (hrep : ∀ R', IsMatching₂ (List.ofFn fun r => (true, a r))
      (List.ofFn fun r => (true, b r)) R' →
      StrictReduced₂ (List.ofFn fun r => (true, a r)) R' →
      ∃ R ∈ M, Iso (pairing₂ (List.ofFn fun r => (true, a r)) R)
        (pairing₂ (List.ofFn fun r => (true, a r)) R'))
    (huniq : ∀ R ∈ M, ∀ S ∈ M,
      Iso (pairing₂ (List.ofFn fun r => (true, a r)) R)
        (pairing₂ (List.ofFn fun r => (true, a r)) S) → R = S) :
    ∃ p : ∀ R : {R // R ∈ M}, MatchingStrand (List.ofFn fun r => (true, a r)) R.val ≃ Fin n,
      (∀ R (j : MatchingStrand (List.ofFn fun r => (true, a r)) R.val),
        OnStrand₂ (List.ofFn fun r => (true, a r)) R.val j.val (R.val.length, (p R j).val)) ∧
      ∃ E : {R // R ∈ M} ≃ {w : Equiv.Perm (Fin n) // ∀ r, a r = b (w r)},
        (∀ R r, Same (pairing₂ (List.ofFn fun r => (true, a r)) R.val)
          (n - 1 - r.val) (n + ((E R).val r).val)) ∧
        ∃ F : ({w : Equiv.Perm (Fin n) // ∀ r, a r = b (w r)} × (Fin n → ℕ)) ≃
          {L // L ∈ decoratedFamily₂ (List.ofFn fun r => (true, a r)) M
            (fun R c => topDotMoves (List.ofFn fun r => (true, a r)) R
              (topPositionExtension M p R) (fun j => c j))},
          ∀ R c, (F (E R, c)).val = dLay (List.ofFn fun r => (true, a r))
            (topDotMoves (List.ofFn fun r => (true, a r)) R.val
              (fun j => (p R j).val) (fun j => c (p R j))) := by
  classical
  have hpoint (R : {R // R ∈ M}) := positive_top_points a b (hM R R.property).1
  let p := fun R : {R // R ∈ M} => Equiv.ofBijective (hpoint R).choose
    (hpoint R).choose_spec.1
  obtain ⟨E, hE⟩ := positive_representatives_equiv a b M hM hrep huniq
  obtain ⟨G, hG⟩ := positive_topDotMoves_family_equiv a b M hM p
  refine ⟨p, fun R j => (hpoint R).choose_spec.2 j, E, hE,
    (Equiv.prodCongr E.symm (Equiv.refl _)).trans G, ?_⟩
  intro R c
  simpa using hG (R, c)

end OddMath.SKM
