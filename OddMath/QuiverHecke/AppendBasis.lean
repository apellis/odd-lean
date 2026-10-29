/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.ShuffleBasis
import OddMath.QuiverHecke.AppendParabolic

/-!
# Input-side append PBW basis

The mirror of `OddMath.QuiverHecke.PrependBasis`: a scalar basis of
`Hom(s ++ [i], t)` whose elements are an old normal form on the first strands,
followed by dots on the appended strand and then by the crossings of an inverse
shuffle. This is the triangular input of the append corner decomposition of
Kang–Kashiwara–Oh, arXiv:1206.5933v2, Lemma 8.1 and Theorem 8.3; see
`docs/Nondegeneracy/AppendCoordinates.md`.

`AppendIdx.leadEquiv` splits input dots and input permutations;
`appendElt_eq_comp` identifies the diagrams as a right-whiskered old normal form,
new-strand dots, and inverse-shuffle crossings. `appendElt_approx` proves their
unit leading term against `basisNF`, and `appendBasis` applies
`basisOfTriangular`.
-/

noncomputable section
open CategoryTheory StringDiagrams Categorification.TypeA MonoidalCategory
namespace OddMath.QuiverHecke
universe u v w
variable {I : Type u}

/-- Crossings of a word on the first `ℓ` strands fix every position `p ≥ ℓ`. -/
theorem extN_wordProd_of_ge {n ℓ : ℕ} {σ : List ℕ} (hv : ValidWord n σ)
    (hσ : ∀ a ∈ σ, a + 1 < ℓ) {p : ℕ} (hp : ℓ ≤ p) :
    Realization.extN n (wordProd n σ) p = p := by
  induction σ with
  | nil => simp
  | cons a σ ih =>
    have ha : a + 1 < n := hv a (by simp)
    have := hσ a (by simp)
    rw [wordProd_cons, map_mul, Equiv.Perm.mul_apply,
      ih (fun x hx => hv x (by simp [hx])) (fun x hx => hσ x (by simp [hx])),
      Realization.extN_sadj ha]
    exact Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)

theorem extN_wordProd_inv_of_ge {n ℓ : ℕ} {σ : List ℕ} (hv : ValidWord n σ)
    (hσ : ∀ a ∈ σ, a + 1 < ℓ) {p : ℕ} (hp : ℓ ≤ p) :
    Realization.extN n (wordProd n σ)⁻¹ p = p := by
  rw [map_inv]
  conv_lhs => rw [← extN_wordProd_of_ge hv hσ hp]
  simp

theorem appendLen (s : List I) (i : I) : s.length + 1 = (s ++ [i]).length := by simp

/-- Input data for an append normal form with prescribed target. -/
abbrev AppendIdx (i : I) (s t : List I) :=
  {p : ℕ × List ℕ × Equiv.Perm (Fin s.length) × AppendShuffle (appendLen s i) //
    p.2.1.Pairwise (· ≤ ·) ∧ (∀ a ∈ p.2.1, a < s.length) ∧
    tgt (s ++ [i]) (cw (appendCrossingWord (appendLen s i) p.2.2)) = t}

/-- Split a sorted input dot list into old dots and new-strand dots. -/
theorem appendDots_exists {n : ℕ} (l : List ℕ) (hs : l.Pairwise (· ≤ ·))
    (hl : ∀ a ∈ l, a < n + 1) :
    ∃ (m : ℕ) (L : List ℕ), L.Pairwise (· ≤ ·) ∧ (∀ a ∈ L, a < n) ∧
      l = L ++ List.replicate m n := by
  induction l with
  | nil => exact ⟨0, [], by simp, by simp, rfl⟩
  | cons a l ih =>
    rw [List.pairwise_cons] at hs
    obtain ⟨m, L, hL, hlt, he⟩ := ih hs.2 (fun b hb => hl b (by simp [hb]))
    by_cases ha : a < n
    · refine ⟨m, a :: L, List.pairwise_cons.mpr ⟨fun b hb => hs.1 b (by simp [he, hb]), hL⟩,
        ?_, by simp [he]⟩
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact ha
      · exact hlt b hb
    · have han : a = n := by have := hl a (by simp); omega
      subst han
      have hall : ∀ b ∈ l, b = a := by
        intro b hb
        have := hs.1 b hb
        have := hl b (by simp [hb])
        omega
      refine ⟨l.length + 1, [], by simp, by simp, ?_⟩
      rw [List.nil_append, List.replicate_succ]
      exact congrArg _ (List.eq_replicate_iff.mpr ⟨rfl, hall⟩)

/-- The new exponent and old input dot list are uniquely recovered. -/
theorem appendDots_injective {n m m' : ℕ} {L L' : List ℕ} (hL : ∀ a ∈ L, a < n)
    (hL' : ∀ a ∈ L', a < n)
    (he : L ++ List.replicate m n = L' ++ List.replicate m' n) : m = m' ∧ L = L' := by
  have hz := congrArg (List.filter (fun a => decide (n ≤ a))) he
  have hp := congrArg (List.filter (fun a => decide (a < n))) he
  have f1 : ∀ K : List ℕ, (∀ a ∈ K, a < n) →
      K.filter (fun a => decide (n ≤ a)) = [] := by
    intro K hK
    exact List.filter_eq_nil_iff.mpr (fun a ha => by have := hK a ha; simp; omega)
  have f2 : ∀ K : List ℕ, (∀ a ∈ K, a < n) → K.filter (fun a => decide (a < n)) = K := by
    intro K hK
    exact List.filter_eq_self.mpr (fun a ha => by simpa using hK a ha)
  simp only [List.filter_append, f1 L hL, f1 L' hL', f2 L hL, f2 L' hL',
    List.filter_replicate] at hz hp
  simp at hz hp
  exact ⟨hz, hp⟩

namespace AppendIdx
variable {i : I} {s t : List I}
def dots (x : AppendIdx i s t) : List ℕ :=
  x.1.2.1 ++ List.replicate x.1.1 s.length
def perm (x : AppendIdx i s t) := appendPermutation (appendLen s i) x.1.2.2
def word (x : AppendIdx i s t) := appendCrossingWord (appendLen s i) x.1.2.2

theorem dots_sorted (x : AppendIdx i s t) : x.dots.Pairwise (· ≤ ·) := by
  rw [dots, List.pairwise_append]
  refine ⟨x.2.1, by simp, ?_⟩
  intro a ha b hb
  simp only [List.mem_replicate] at hb
  have := x.2.2.1 a ha
  omega

theorem dots_lt (x : AppendIdx i s t) : ∀ a ∈ x.dots, a < (s ++ [i]).length := by
  intro a ha
  rw [← appendLen]
  rcases List.mem_append.mp ha with ha | ha
  · have := x.2.2.1 a ha; omega
  · simp only [List.mem_replicate] at ha
    omega

def lead (x : AppendIdx i s t) : NFIdx (s ++ [i]) t :=
  ⟨(x.dots, x.perm), x.dots_sorted, x.dots_lt, by
    have he : tgt (s ++ [i]) (x.dots.map PG.dot ++ cw (canWord _ x.perm)) = t := by
      rw [tgt_append, tgt_map_dot]
      exact (tgt_cw_eq (validWord_canWord _ _) (appendCrossingWord_spec _ _).1.1
        (by rw [wordProd_canWord, (appendCrossingWord_spec _ _).2]; rfl) rfl).trans x.2.2.2
    simpa only [he] using sChain_pl (s ++ [i]) (x.dots.map PG.dot ++ cw (canWord _ x.perm))⟩

theorem lead_injective : Function.Injective (lead (i := i) (s := s) (t := t)) := by
  intro x y h
  have hd := congrArg (fun z : NFIdx (s ++ [i]) t => z.1.1) h
  have hw := congrArg (fun z : NFIdx (s ++ [i]) t => z.1.2) h
  obtain ⟨hm, hL⟩ := appendDots_injective x.2.2.1 y.2.2.1 hd
  have hp := (appendPermutation_bijective (appendLen s i)).1 hw
  exact Subtype.ext (Prod.ext hm (Prod.ext hL hp))

theorem lead_surjective : Function.Surjective (lead (i := i) (s := s) (t := t)) := by
  intro y
  obtain ⟨m, L, hs, hl, he⟩ := appendDots_exists (n := s.length) y.1.1 y.2.1
    (fun a ha => by rw [appendLen s i]; exact y.2.2.1 a ha)
  obtain ⟨p, hp⟩ := (appendPermutation_bijective (appendLen s i)).2 y.1.2
  have ht : tgt (s ++ [i]) (cw (appendCrossingWord (appendLen s i) p)) = t := by
    apply Eq.trans _ y.tgt_cw
    exact tgt_cw_eq (appendCrossingWord_spec _ _).1.1 (validWord_canWord _ _)
      (by rw [(appendCrossingWord_spec _ _).2, wordProd_canWord, hp]) rfl
  exact ⟨⟨(m, L, p), hs, hl, ht⟩, Subtype.ext (Prod.ext he.symm hp)⟩

/-- The input-side leading indices enumerate the existing normal form indices once. -/
def leadEquiv : AppendIdx i s t ≃ NFIdx (s ++ [i]) t :=
  Equiv.ofBijective lead ⟨lead_injective, lead_surjective⟩

@[simp] theorem leadEquiv_apply (x : AppendIdx i s t) : leadEquiv x = x.lead := rfl

/-- Chronological generators: old dots and crossings, new dots, moving crossings. -/
def gens (x : AppendIdx i s t) : List PG :=
  x.1.2.1.map PG.dot ++ cw (canWord s.length x.1.2.2.1) ++
    (List.replicate x.1.1 s.length).map PG.dot ++
    cw (canWord (s ++ [i]).length x.1.2.2.2.1⁻¹)

theorem gens_target (x : AppendIdx i s t) : tgt (s ++ [i]) x.gens = t := by
  simpa only [gens, appendCrossingWord, cw_append, tgt_append, tgt_map_dot]
    using x.2.2.2

/-- The intermediate old target, before the new strand moves. -/
def oldTarget (x : AppendIdx i s t) : List I :=
  tgt s (cw (canWord s.length x.1.2.2.1))

/-- The old coefficient is an index of the existing normal form basis. -/
def old (x : AppendIdx i s t) : NFIdx s x.oldTarget :=
  ⟨(x.1.2.1, x.1.2.2.1), x.2.1, x.2.2.1, by
    simpa only [oldTarget, tgt_append, tgt_map_dot] using
      sChain_pl s (x.1.2.1.map PG.dot ++ cw (canWord s.length x.1.2.2.1))⟩

theorem moving_target (x : AppendIdx i s t) :
    tgt (x.oldTarget ++ [i]) (cw (canWord (s ++ [i]).length x.1.2.2.2.1⁻¹)) = t := by
  have he := tgt_append_right [i] (t := s) (fits_cw (validWord_canWord s.length x.1.2.2.1))
  simpa only [oldTarget, appendCrossingWord, cw_append, tgt_append, he] using x.2.2.2
end AppendIdx

variable {X : Type v} [AddCommGroup X] (D : SKM.Datum I X) {k : Type w} [CommRing k]
  (Sc : SKM.Scalars D k)
variable {i : I} {s t : List I}

/-- The positioned diagram of an input-side append term. -/
def appendElt (x : AppendIdx i s t) :
    (pres D Sc).obj (ob D (s ++ [i])) ⟶ (pres D Sc).obj (ob D t) :=
  cl D Sc _ _ x.gens (by simpa only [x.gens_target] using sChain_pl (s ++ [i]) x.gens)

/-- The append diagram is the old basis morphism followed by new dots and moving crossings. -/
theorem appendElt_eq_comp (x : AppendIdx i s t) :
    appendElt D Sc x =
      (x.old.nf ▷ (pres D Sc).obj (ob D [i])) ≫
      cl D Sc (x.oldTarget ++ [i]) (x.oldTarget ++ [i])
        ((List.replicate x.1.1 s.length).map PG.dot)
        (by simpa only [tgt_map_dot] using
          sChain_pl (x.oldTarget ++ [i]) ((List.replicate x.1.1 s.length).map PG.dot)) ≫
      cl D Sc (x.oldTarget ++ [i]) t (cw (canWord (s ++ [i]).length x.1.2.2.2.1⁻¹))
        (by simpa only [x.moving_target] using
          sChain_pl (x.oldTarget ++ [i]) (cw (canWord (s ++ [i]).length x.1.2.2.2.1⁻¹))) := by
  rw [nf_whiskerRight]
  rw [cl_comp, cl_comp]
  unfold appendElt
  apply cl_eq_cl
  simp only [AppendIdx.gens, AppendIdx.old, List.append_assoc]

/-- Input-side triangularity for the chronological append diagram. -/
theorem appendElt_approx (x : AppendIdx i s t) :
    Approx D Sc (length (s ++ [i]).length x.perm) (appendElt D Sc x) x.lead.nf := by
  have hv : ValidWord (s ++ [i]).length (canWord s.length x.1.2.2.1) :=
    (validWord_canWord _ _).of_le (by rw [← appendLen]; omega)
  have hZ : ∀ p ∈ List.replicate x.1.1 s.length, p < (s ++ [i]).length := by
    intro p hp
    simp only [List.mem_replicate] at hp
    rw [← appendLen]
    omega
  have hfix : (List.replicate x.1.1 s.length).map
      (Realization.extN (s ++ [i]).length
        (wordProd (s ++ [i]).length (canWord s.length x.1.2.2.1))⁻¹) =
      List.replicate x.1.1 s.length := by
    conv_rhs => rw [← List.map_id (List.replicate x.1.1 s.length)]
    apply List.map_congr_left
    intro p hp
    simp only [List.mem_replicate] at hp
    apply extN_wordProd_inv_of_ge hv (ℓ := s.length)
    · intro a ha
      exact validWord_canWord s.length x.1.2.2.1 a ha
    · omega
  unfold appendElt
  generalize_proofs h
  obtain ⟨h₁, hA⟩ := dots_down (D := D) (Sc := Sc) (t := s ++ [i]) (n := (s ++ [i]).length)
    (x.1.2.1.map PG.dot) rfl _ hv
    (List.replicate x.1.1 s.length) hZ (cw (canWord (s ++ [i]).length x.1.2.2.2.1⁻¹)) h
  have e : x.1.2.1.map PG.dot ++
      ((List.replicate x.1.1 s.length).map (Realization.extN (s ++ [i]).length
        (wordProd (s ++ [i]).length (canWord s.length x.1.2.2.1))⁻¹)).map PG.dot ++
      cw (canWord s.length x.1.2.2.1) ++
      cw (canWord (s ++ [i]).length x.1.2.2.2.1⁻¹) =
      x.dots.map PG.dot ++ cw x.word := by
    rw [hfix]
    simp only [AppendIdx.dots, AppendIdx.word, appendCrossingWord, cw_append, List.map_append,
      List.append_assoc]
  have hb : BraidEquiv x.word (canWord (s ++ [i]).length x.perm) :=
    braidEquiv_of_isReduced (appendCrossingWord_spec _ _).1 (isReduced_canWord _ _)
      (by rw [AppendIdx.word, (appendCrossingWord_spec _ _).2, wordProd_canWord]; rfl)
  have hC := braid_move (D := D) (Sc := Sc) (x.dots.map PG.dot) rfl hb
    (appendCrossingWord_spec _ _).1.1 (e ▸ h₁) x.lead.2.2.2
  rw [cl_eq_cl e h₁ (e ▸ h₁)] at hA
  have hlen := (appendCrossingWord_spec (appendLen s i) x.1.2.2).1.2
  rw [(appendCrossingWord_spec _ _).2] at hlen
  simp only [crossCount_dots, crossCount_cw, zero_add,
    AppendIdx.word, appendCrossingWord, List.length_append] at hA hC hlen
  have he : length (s ++ [i]).length x.perm =
      (canWord s.length x.1.2.2.1).length +
      (canWord (s ++ [i]).length x.1.2.2.2.1⁻¹).length := by
    change _ = length (s ++ [i]).length x.perm at hlen
    omega
  rw [he]
  exact hA.trans (hC.mono (by omega))

theorem exists_unit_appendElt (y : NFIdx (s ++ [i]) t) :
    ∃ c : k, IsUnit c ∧
      appendElt D Sc (AppendIdx.leadEquiv.symm y) - c • basisNF D Sc (s ++ [i]) t y ∈
        Submodule.span k (basisNF D Sc (s ++ [i]) t ''
          {z | length (s ++ [i]).length z.1.2 < length (s ++ [i]).length y.1.2}) := by
  let x : AppendIdx i s t := AppendIdx.leadEquiv.symm y
  have hx : x.lead = y := AppendIdx.leadEquiv.apply_symm_apply y
  obtain ⟨c, hc, hm⟩ := appendElt_approx D Sc x
  refine ⟨c, hc, ?_⟩
  have hspan := low_le_span_nf D Sc (s ++ [i]) t _ hm
  have hp : x.perm = y.1.2 := congrArg (fun z : NFIdx (s ++ [i]) t => z.1.2) hx
  rw [hp] at hspan
  simpa only [basisNF_apply, hx] using hspan

/-- The input append diagrams form a scalar Hom basis. -/
def appendBasis : Module.Basis (AppendIdx i s t) k
    ((pres D Sc).obj (ob D (s ++ [i])) ⟶ (pres D Sc).obj (ob D t)) :=
  (basisOfTriangular (basisNF D Sc (s ++ [i]) t) (fun y => length (s ++ [i]).length y.1.2)
    (b := fun y => appendElt D Sc (AppendIdx.leadEquiv.symm y))
    (fun y => (exists_unit_appendElt D Sc y).choose_spec.1)
    (fun y => (exists_unit_appendElt D Sc y).choose_spec.2)).reindex
      AppendIdx.leadEquiv.symm

@[simp] theorem appendBasis_apply (x : AppendIdx i s t) :
    appendBasis D Sc x = appendElt D Sc x := by
  simp only [appendBasis, Module.Basis.reindex_apply, Equiv.symm_symm,
    basisOfTriangular_apply, Equiv.symm_apply_apply]

end OddMath.QuiverHecke
