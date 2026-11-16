/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.ShuffleBasis
import OddMath.QuiverHecke.InputParabolic

/-!
# Input-side prepend PBW basis

The scalar triangular step for the prepend corner decomposition needed by
Kang–Kashiwara–Oh, arXiv:1206.5933v2, Lemma 8.1; see
`docs/Nondegeneracy/PrependCoordinates.md`.

`PrependIdx.leadEquiv` splits input dots and input permutations, retaining
permutation indices even for repeated colours. `prependElt_eq_comp` identifies
the diagrams as a whiskered old normal form, new-strand dots, and inverse-shuffle
crossings. `prependElt_approx` proves their unit leading term against `basisNF`;
`prependBasis` applies `basisOfTriangular`. These statements concern scalar Hom
spaces, not an assumed right-old-algebra coordinate equivalence. Matrix assembly
and the balanced quotient remain separate obligations.
-/

noncomputable section
open CategoryTheory StringDiagrams Categorification.TypeA MonoidalCategory
namespace OddMath.QuiverHecke
universe u v w
variable {I : Type u}

/-- Input data for a prepend normal form with prescribed target. -/
abbrev PrependIdx (i : I) (s t : List I) :=
  {p : ℕ × List ℕ × Equiv.Perm (Fin s.length) × PrependShuffle s.length //
    p.2.1.Pairwise (· ≤ ·) ∧ (∀ a ∈ p.2.1, a < s.length) ∧
    tgt (i :: s) (cw (prependCrossingWord s.length p.2.2)) = t}

/-- Split a sorted input dot list into new-strand dots and shifted old dots. -/
theorem prependDots_exists {n : ℕ} (l : List ℕ) (hs : l.Pairwise (· ≤ ·))
    (hl : ∀ a ∈ l, a < n + 1) :
    ∃ (m : ℕ) (L : List ℕ), L.Pairwise (· ≤ ·) ∧ (∀ a ∈ L, a < n) ∧
      l = List.replicate m 0 ++ L.map (1 + ·) := by
  induction l with
  | nil => exact ⟨0, [], by simp, by simp, rfl⟩
  | cons a l ih =>
    rw [List.pairwise_cons] at hs
    by_cases ha : a = 0
    · subst a
      obtain ⟨m, L, hL, hlt, he⟩ := ih hs.2 (fun b hb => hl b (by simp [hb]))
      exact ⟨m + 1, L, hL, hlt, by simp [List.replicate_succ, he]⟩
    · have hp : ∀ b ∈ a :: l, 0 < b := by
        intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · omega
        · have := hs.1 b hb; omega
      refine ⟨0, (a :: l).map (· - 1), ?_, ?_, ?_⟩
      · rw [List.pairwise_map]
        exact (List.pairwise_cons.mpr hs).imp (by intro b c h; omega)
      · intro b hb
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
        have := hp c hc
        have := hl c hc
        omega
      · simp only [List.replicate_zero, List.nil_append, List.map_map]
        symm
        conv_rhs => rw [← List.map_id (a :: l)]
        apply List.map_congr_left
        intro b hb
        have := hp b hb
        change 1 + (b - 1) = b
        omega

/-- The new exponent and old input dot list are uniquely recovered. -/
theorem prependDots_injective {m m' : ℕ} {L L' : List ℕ}
    (he : List.replicate m 0 ++ L.map (1 + ·) =
      List.replicate m' 0 ++ L'.map (1 + ·)) : m = m' ∧ L = L' := by
  have hz := congrArg (List.filter (· == 0)) he
  have hp := congrArg (List.filter (· != 0)) he
  simp [List.filter_map, Function.comp_def, Nat.add_comm] at hz hp
  exact ⟨hz, ((List.map_injective_iff (f := fun a : ℕ => a + 1)).mpr
    (by intro a b h; exact Nat.add_right_cancel h)) hp⟩

namespace PrependIdx
variable {i : I} {s t : List I}
def dots (x : PrependIdx i s t) : List ℕ :=
  List.replicate x.1.1 0 ++ x.1.2.1.map (1 + ·)
def perm (x : PrependIdx i s t) := prependPermutation s.length x.1.2.2
def word (x : PrependIdx i s t) := prependCrossingWord s.length x.1.2.2

theorem dots_sorted (x : PrependIdx i s t) : x.dots.Pairwise (· ≤ ·) := by
  rw [dots, List.pairwise_append]
  refine ⟨by simp, ?_, ?_⟩
  · rw [List.pairwise_map]
    exact x.2.1.imp (by intro a b h; omega)
  · intro a ha b hb
    simp only [List.mem_replicate] at ha
    omega

theorem dots_lt (x : PrependIdx i s t) : ∀ a ∈ x.dots, a < (i :: s).length := by
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · simp only [List.mem_replicate] at ha
    simp [ha.2]
  · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    have := x.2.2.1 b hb
    simp only [List.length_cons]; omega

def lead (x : PrependIdx i s t) : NFIdx (i :: s) t :=
  ⟨(x.dots, x.perm), x.dots_sorted, x.dots_lt, by
    have he : tgt (i :: s) (x.dots.map PG.dot ++ cw (canWord _ x.perm)) = t := by
      rw [tgt_append, tgt_map_dot]
      exact (tgt_cw_eq (validWord_canWord _ _) (prependCrossingWord_spec _ _).1.1
        (by rw [wordProd_canWord, (prependCrossingWord_spec _ _).2]; rfl) rfl).trans x.2.2.2
    simpa only [List.length_cons, he] using sChain_pl (i :: s) (x.dots.map PG.dot ++ cw (canWord _ x.perm))⟩

theorem lead_injective : Function.Injective (lead (i := i) (s := s) (t := t)) := by
  intro x y h
  have hd := congrArg (fun z : NFIdx (i :: s) t => z.1.1) h
  have hw := congrArg (fun z : NFIdx (i :: s) t => z.1.2) h
  obtain ⟨hm, hL⟩ := prependDots_injective hd
  have hp := (prependPermutation_bijective s.length).1 hw
  exact Subtype.ext (Prod.ext hm (Prod.ext hL hp))

theorem lead_surjective : Function.Surjective (lead (i := i) (s := s) (t := t)) := by
  intro y
  obtain ⟨m, L, hs, hl, he⟩ := prependDots_exists y.1.1 y.2.1 y.2.2.1
  obtain ⟨p, hp⟩ := (prependPermutation_bijective s.length).2 y.1.2
  have ht : tgt (i :: s) (cw (prependCrossingWord s.length p)) = t := by
    apply Eq.trans _ y.tgt_cw
    exact tgt_cw_eq (prependCrossingWord_spec _ _).1.1 (validWord_canWord _ _)
      (by rw [(prependCrossingWord_spec _ _).2, wordProd_canWord, hp]) rfl
  exact ⟨⟨(m, L, p), hs, hl, ht⟩, Subtype.ext (Prod.ext he.symm hp)⟩

/-- The input-side leading indices enumerate the existing normal form indices once. -/
def leadEquiv : PrependIdx i s t ≃ NFIdx (i :: s) t :=
  Equiv.ofBijective lead ⟨lead_injective, lead_surjective⟩

@[simp] theorem leadEquiv_apply (x : PrependIdx i s t) : leadEquiv x = x.lead := rfl

/-- Chronological generators: old dots and crossings, new dots, moving crossings. -/
def gens (x : PrependIdx i s t) : List PG :=
  (x.1.2.1.map (1 + ·)).map PG.dot ++
    cw (shiftWord 1 (canWord s.length x.1.2.2.1)) ++
    (List.replicate x.1.1 0).map PG.dot ++
    cw (canWord (s.length + 1) x.1.2.2.2.1⁻¹)

theorem gens_target (x : PrependIdx i s t) : tgt (i :: s) x.gens = t := by
  simpa only [gens, prependCrossingWord, cw_append, tgt_append, tgt_map_dot]
    using x.2.2.2
/-- The intermediate old target, before the new strand moves. -/
def oldTarget (x : PrependIdx i s t) : List I :=
  tgt s (cw (canWord s.length x.1.2.2.1))

/-- The old coefficient is an index of the existing normal form basis. -/
def old (x : PrependIdx i s t) : NFIdx s x.oldTarget :=
  ⟨(x.1.2.1, x.1.2.2.1), x.2.1, x.2.2.1, by
    simpa only [oldTarget, tgt_append, tgt_map_dot] using
      sChain_pl s (x.1.2.1.map PG.dot ++ cw (canWord s.length x.1.2.2.1))⟩

theorem moving_target (x : PrependIdx i s t) :
    tgt (i :: x.oldTarget) (cw (canWord (s.length + 1) x.1.2.2.2.1⁻¹)) = t := by
  have he := tgt_shift [i] s (cw (canWord s.length x.1.2.2.1))
  simp only [List.length_singleton, cw_map_shift, List.singleton_append] at he
  simpa only [oldTarget, prependCrossingWord, cw_append, tgt_append, he] using x.2.2.2
end PrependIdx

variable {X : Type v} [AddCommGroup X] (D : SKM.Datum I X) {k : Type w} [CommRing k]
  (Sc : SKM.Scalars D k)
variable {i : I} {s t : List I}

/-- The positioned diagram of an input-side prepend term. -/
def prependElt (x : PrependIdx i s t) :
    (pres D Sc).obj (ob D (i :: s)) ⟶ (pres D Sc).obj (ob D t) :=
  cl D Sc _ _ x.gens (by simpa only [x.gens_target] using sChain_pl (i :: s) x.gens)

/-- The prepend diagram is the old basis morphism followed by new dots and moving crossings. -/
theorem prependElt_eq_comp (x : PrependIdx i s t) :
    prependElt D Sc x =
      ((pres D Sc).obj (ob D [i]) ◁ x.old.nf) ≫
      cl D Sc (i :: x.oldTarget) (i :: x.oldTarget) ((List.replicate x.1.1 0).map PG.dot)
        (by simpa only [tgt_map_dot] using
          sChain_pl (i :: x.oldTarget) ((List.replicate x.1.1 0).map PG.dot)) ≫
      cl D Sc (i :: x.oldTarget) t (cw (canWord (s.length + 1) x.1.2.2.2.1⁻¹))
        (by simpa only [x.moving_target] using
          sChain_pl (i :: x.oldTarget) (cw (canWord (s.length + 1) x.1.2.2.2.1⁻¹))) := by
  rw [whiskerLeft_nf]
  simp only [List.singleton_append]
  rw [cl_comp, cl_comp]
  unfold prependElt
  apply cl_eq_cl
  simp only [PrependIdx.gens, PrependIdx.old, List.map_append, List.length_singleton,
    dots_map_shift, cw_map_shift, List.append_assoc]

/-- Input-side triangularity for the chronological prepend diagram. -/
theorem prependElt_approx (x : PrependIdx i s t) :
    Approx D Sc (length (s.length + 1) x.perm) (prependElt D Sc x) x.lead.nf := by
  have hv : ValidWord (s.length + 1) (shiftWord 1 (canWord s.length x.1.2.2.1)) :=
    (validWord_canWord _ _).shiftWord (Nat.add_comm 1 s.length)
  have hZ : ∀ p ∈ List.replicate x.1.1 0, p < (s.length + 1) := by
    intro p hp
    simp only [List.mem_replicate] at hp
    omega
  have hfix : (List.replicate x.1.1 0).map
      (Realization.extN (s.length + 1)
        (wordProd (s.length + 1) (shiftWord 1 (canWord s.length x.1.2.2.1)))⁻¹) =
      List.replicate x.1.1 0 := by
    conv_rhs => rw [← List.map_id (List.replicate x.1.1 0)]
    apply List.map_congr_left
    intro p hp
    apply extN_wordProd_inv_of_lt hv (ℓ := 1)
    · intro a ha
      obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
      omega
    · simp only [List.mem_replicate] at hp
      omega
  unfold prependElt
  generalize_proofs h
  obtain ⟨h₁, hA⟩ := dots_down (D := D) (Sc := Sc) (t := i :: s) (n := s.length + 1)
    ((x.1.2.1.map (1 + ·)).map PG.dot) rfl _ hv
    (List.replicate x.1.1 0) hZ (cw (canWord (s.length + 1) x.1.2.2.2.1⁻¹)) h
  have e : (x.1.2.1.map (1 + ·)).map PG.dot ++
      ((List.replicate x.1.1 0).map (Realization.extN (s.length + 1)
        (wordProd (s.length + 1) (shiftWord 1 (canWord s.length x.1.2.2.1)))⁻¹)).map PG.dot ++
      cw (shiftWord 1 (canWord s.length x.1.2.2.1)) ++
      cw (canWord (s.length + 1) x.1.2.2.2.1⁻¹) =
      [] ++ (x.1.2.1.map (1 + ·) ++ List.replicate x.1.1 0).map PG.dot ++ cw x.word := by
    rw [hfix]
    simp only [PrependIdx.word, prependCrossingWord, cw_append, List.map_append,
      List.nil_append, List.append_assoc]
  have hL : ∀ a ∈ x.1.2.1.map (1 + ·) ++ List.replicate x.1.1 0,
      a < (i :: s).length := by
    intro a ha
    apply x.dots_lt
    exact List.mem_append.mpr ((List.mem_append.mp ha).elim Or.inr Or.inl)
  obtain ⟨c, hc, h₂, hB⟩ := dots_perm (D := D) (Sc := Sc) [] (cw x.word)
    (List.perm_append_comm : (x.1.2.1.map (1 + ·) ++ List.replicate x.1.1 0).Perm x.dots)
    hL (e ▸ h₁)
  have hb : BraidEquiv x.word (canWord (s.length + 1) x.perm) :=
    braidEquiv_of_isReduced (prependCrossingWord_spec _ _).1 (isReduced_canWord _ _)
      (by rw [PrependIdx.word, (prependCrossingWord_spec _ _).2, wordProd_canWord]; rfl)
  have hC := braid_move (D := D) (Sc := Sc) (x.dots.map PG.dot) rfl hb
    (prependCrossingWord_spec _ _).1.1 h₂ x.lead.2.2.2
  rw [cl_eq_cl e h₁ (e ▸ h₁), hB] at hA
  have hlen := (prependCrossingWord_spec s.length x.1.2.2).1.2
  rw [(prependCrossingWord_spec _ _).2] at hlen
  simp only [crossCount_dots, crossCount_cw, zero_add, length_shiftWord,
    PrependIdx.word, prependCrossingWord, List.length_append] at hA hC hlen
  have he : length (s.length + 1) x.perm =
      (canWord s.length x.1.2.2.1).length +
      (canWord (s.length + 1) x.1.2.2.2.1⁻¹).length := by
    change _ = length (s.length + 1) x.perm at hlen
    omega
  rw [he]
  exact hA.trans ((Approx.trans ⟨c, hc, by simp⟩ hC).mono (by omega))

theorem exists_unit_prependElt (y : NFIdx (i :: s) t) :
    ∃ c : k, IsUnit c ∧
      prependElt D Sc (PrependIdx.leadEquiv.symm y) - c • basisNF D Sc (i :: s) t y ∈
        Submodule.span k (basisNF D Sc (i :: s) t ''
          {z | length (s.length + 1) z.1.2 < length (s.length + 1) y.1.2}) := by
  let x : PrependIdx i s t := PrependIdx.leadEquiv.symm y
  have hx : x.lead = y := PrependIdx.leadEquiv.apply_symm_apply y
  obtain ⟨c, hc, hm⟩ := prependElt_approx D Sc x
  refine ⟨c, hc, ?_⟩
  have hspan := low_le_span_nf D Sc (i :: s) t _ hm
  have hp : x.perm = y.1.2 := congrArg (fun z : NFIdx (i :: s) t => z.1.2) hx
  rw [hp] at hspan
  simpa only [basisNF_apply, hx, List.length_cons] using hspan

/-- The input prepend diagrams form a scalar Hom basis. This is not yet a
right-old-algebra basis of the matrix corner. -/
def prependBasis : Module.Basis (PrependIdx i s t) k
    ((pres D Sc).obj (ob D (i :: s)) ⟶ (pres D Sc).obj (ob D t)) :=
  (basisOfTriangular (basisNF D Sc (i :: s) t) (fun y => length (s.length + 1) y.1.2)
    (b := fun y => prependElt D Sc (PrependIdx.leadEquiv.symm y))
    (fun y => (exists_unit_prependElt D Sc y).choose_spec.1)
    (fun y => (exists_unit_prependElt D Sc y).choose_spec.2)).reindex
      PrependIdx.leadEquiv.symm

@[simp] theorem prependBasis_apply (x : PrependIdx i s t) :
    prependBasis D Sc x = prependElt D Sc x := by
  simp only [prependBasis, Module.Basis.reindex_apply, Equiv.symm_symm,
    basisOfTriangular_apply, Equiv.symm_apply_apply]

end OddMath.QuiverHecke
