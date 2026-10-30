/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVParabolicSpan
import OddMath.QuiverHecke.InputParabolic

/-!
# Short and long output shuffles

The output-shuffle identification for the ideal-sum calculation in
`DeformedIdealSum.md`. Short shuffles right-extend an old shuffle; the longest
shuffle is the prescribed last-to-first chain.
-/

noncomputable section
open CategoryTheory StringDiagrams MonoidalCategory Categorification.TypeA
namespace OddMath.QuiverHecke.OutputShuffle
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k)

theorem cl_heq {s t t' : List I} {L M : List PG}
    (hL : SChain s (pl s L) t) (hM : SChain s (pl s M) t') (e : L = M) :
    HEq (cl D Sc s t L hL) (cl D Sc s t' M hM) := by
  subst M
  have ht : t = t' := (tgt_eq hL).symm.trans (tgt_eq hM)
  subst t'
  rfl

theorem long_of_word (i : I) (v : List I)
    (d : Equiv.Perm (Fin (v ++ [i]).length))
    (hd : cw (canWord (v ++ [i]).length d) = crossingDescent v.length) :
    HEq (shPsi D Sc 1 d) (lastToFirstHom D Sc i v) := by
  obtain ⟨h, he⟩ := lastToFirstHom_eq_cl D Sc i v
  rw [he]
  exact cl_heq D Sc _ h hd

theorem short_of_word (i : I) (v : List I)
    (d : Equiv.Perm (Fin (v ++ [i]).length))
    (e : Equiv.Perm (Fin v.length))
    (hd : cw (canWord (v ++ [i]).length d) = cw (canWord v.length e)) :
    HEq (shPsi D Sc 1 d) ((shPsi D Sc 1 e) ▷ (pres D Sc).obj (ob D [i])) := by
  unfold shPsi
  rw [cl_whiskerRight D Sc _ _ [i] (fits_cw (validWord_canWord _ _))]
  exact cl_heq D Sc _ _ hd

def firstCode (r : ℕ) : ℕ → List ℕ
  | 0 => []
  | n + 1 => (if n < r then n else n + 1) :: firstCode r n

@[simp] theorem length_firstCode (r n : ℕ) : (firstCode r n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [firstCode, ih]

theorem isCode_firstCode (r n : ℕ) : IsCode (firstCode r n) := by
  induction n with
  | zero => trivial
  | succ n ih => exact ⟨by simp only [length_firstCode]; split <;> omega, ih⟩

theorem codeWord_firstCode (r n : ℕ) : codeWord (firstCode r n) = List.range (min r n) := by
  induction n with
  | zero => simp [firstCode]
  | succ n ih =>
    rw [firstCode, codeWord_cons, ih, length_firstCode]
    split
    · rename_i h
      rw [show n + 1 - n = 1 by omega, descRun_one,
        Nat.min_eq_right (by omega : n ≤ r), Nat.min_eq_right (by omega : n + 1 ≤ r),
        List.range_succ]
    · rename_i h
      rw [Nat.sub_self, descRun_zero, List.append_nil,
        Nat.min_eq_left (by omega : r ≤ n), Nat.min_eq_left (by omega : r ≤ n + 1)]

def firstPerm (n r : ℕ) : Equiv.Perm (Fin (n + 1)) := wordProd (n + 1) (List.range r)

theorem canWord_firstPerm (n r : ℕ) (hr : r ≤ n) :
    canWord (n + 1) (firstPerm n r) = List.range r := by
  have hc : codeWord (firstCode r n) = List.range r := by
    rw [codeWord_firstCode, Nat.min_eq_left hr]
  rw [firstPerm, ← hc, canWord_wordProd_codeWord (isCode_firstCode r n) (by simp)]

theorem firstPerm_val (n r : ℕ) (hr : r ≤ n) (x : Fin (n + 1)) :
    (firstPerm n r x : ℕ) = if x.val < r then x.val + 1 else if x.val = r then 0 else x.val := by
  induction r generalizing x with
  | zero =>
    simp only [firstPerm, List.range_zero, wordProd_nil, Equiv.Perm.one_apply]
    split_ifs <;> omega
  | succ r ih =>
    simp only [firstPerm, List.range_succ, wordProd_append, wordProd_singleton,
      Equiv.Perm.mul_apply]
    change (firstPerm n r (sadj (n + 1) r x) : ℕ) = _
    rw [ih (by omega), sadj_val]
    unfold swapNat
    have := x.isLt
    split_ifs <;> omega

theorem firstPerm_inv_val (n r : ℕ) (hr : r ≤ n) (x : Fin (n + 1)) :
    ((firstPerm n r)⁻¹ x : ℕ) =
      if x.val = 0 then r else if x.val ≤ r then x.val - 1 else x.val := by
  have hh := firstPerm_val n r hr ((firstPerm n r)⁻¹ x)
  rw [show (firstPerm n r) ((firstPerm n r)⁻¹ x) = x from
    (firstPerm n r).apply_symm_apply x] at hh
  split_ifs at hh ⊢ <;> omega

def firstRun (n : ℕ) (r : Fin (n + 1)) : PrependShuffle n :=
  ⟨firstPerm n r, by
    refine ⟨fun x y h => absurd h (by simp [Subsingleton.elim x y]), fun x y h => ?_⟩
    rw [Fin.lt_def, firstPerm_inv_val n r (by omega), firstPerm_inv_val n r (by omega)]
    simp only [blockEquiv_inr_val]
    have : (x : ℕ) < y := h
    split_ifs <;> omega⟩

theorem firstRun_injective (n : ℕ) : Function.Injective (firstRun n) := by
  intro r s h
  have hh := congrArg (fun d : PrependShuffle n => (d.1⁻¹ ⟨0, by omega⟩).val) h
  change ((firstPerm n r)⁻¹ ⟨0, by omega⟩).val =
    ((firstPerm n s)⁻¹ ⟨0, by omega⟩).val at hh
  rw [firstPerm_inv_val n r (by omega), firstPerm_inv_val n s (by omega)] at hh
  apply Fin.ext
  simpa using hh

open scoped Classical in
theorem card_firstShuffle (n : ℕ) : Fintype.card (PrependShuffle n) = n + 1 := by
  have h := Fintype.card_congr (Equiv.ofBijective _ (prependPermutation_bijective n))
  rw [Fintype.card_prod, Fintype.card_perm, Fintype.card_perm, Fintype.card_fin,
    Fintype.card_fin, Nat.factorial_succ, mul_comm] at h
  exact Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos n) h

open scoped Classical in
def firstRunEquiv (n : ℕ) : Fin (n + 1) ≃ PrependShuffle n :=
  Equiv.ofBijective (firstRun n) ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨firstRun_injective n, by rw [Fintype.card_fin, card_firstShuffle]⟩)

theorem canWord_firstShuffle (n : ℕ) (d : PrependShuffle n) :
    canWord (n + 1) d.1 = List.range (d.1.symm ⟨0, by omega⟩).val := by
  obtain ⟨r, hr⟩ := (firstRunEquiv n).surjective d
  subst d
  change canWord (n + 1) (firstPerm n r) =
    List.range (((firstPerm n r)⁻¹ ⟨0, by omega⟩).val)
  rw [canWord_firstPerm n r (by omega), firstPerm_inv_val n r (by omega)]
  rfl

theorem cw_range (r : ℕ) : cw (List.range r) = crossingDescent r := by
  induction r with
  | zero => rfl
  | succ r ih => simp [List.range_succ, cw, crossingDescent, ← ih]

theorem shuffle_word_cases {N n : ℕ} (hN : 1 + n = N) (d : Shuffle hN) :
    ∃ r ≤ n, cw (canWord N d.1) = crossingDescent r := by
  have hn : N = n + 1 := by omega
  revert d hN
  rw [hn]
  intro hN d
  refine ⟨(d.1.symm ⟨0, by omega⟩).val, by omega, ?_⟩
  rw [canWord_firstShuffle, cw_range]

theorem canWord_wordProd_range {N r : ℕ} (hr : r < N) :
    canWord N (wordProd N (List.range r)) = List.range r := by
  cases N with
  | zero => omega
  | succ n => exact canWord_firstPerm n r (by omega)

/-- Exhaustive short/long identification of the output shuffle. Short retains
an explicit old first-shuffle word; long is the prescribed last-to-first map. -/
theorem output_shuffle_cases (i : I) (v : List I)
    (d : Shuffle (show 1 + v.length = (v ++ [i]).length by simp; omega)) :
    (∃ (r : ℕ) (_hr : r < v.length),
      HEq (shPsi D Sc 1 d.1)
        ((shPsi D Sc 1 (wordProd v.length (List.range r))) ▷
          (pres D Sc).obj (ob D [i]))) ∨
      HEq (shPsi D Sc 1 d.1) (lastToFirstHom D Sc i v) := by
  obtain ⟨r, hr, he⟩ := shuffle_word_cases _ d
  by_cases hshort : r < v.length
  · left
    refine ⟨r, hshort, short_of_word D Sc i v d.1 _ ?_⟩
    rw [he, canWord_wordProd_range hshort, cw_range]
  · right
    have hl : r = v.length := by omega
    exact long_of_word D Sc i v d.1 (hl ▸ he)

theorem isShuffle_wordProd_range {N r : ℕ} (hr : r < N) :
    IsShuffle (show 1 + (N - 1) = N by omega) (wordProd N (List.range r)) := by
  cases N with
  | zero => omega
  | succ n => exact (firstRun n ⟨r, by omega⟩).property

theorem short_target_of_word (i : I) (v : List I)
    (d : Equiv.Perm (Fin (v ++ [i]).length)) (e : Equiv.Perm (Fin v.length))
    (hd : cw (canWord (v ++ [i]).length d) = cw (canWord v.length e)) :
    shL (v ++ [i]) 1 d ++ shR (v ++ [i]) 1 d =
      (shL v 1 e ++ shR v 1 e) ++ [i] := by
  rw [shL_append_shR, shL_append_shR, shTop, shTop, hd,
    tgt_append_right [i] (fits_cw (validWord_canWord _ _))]

include D Sc in
theorem long_target_of_word (i : I) (v : List I)
    (d : Equiv.Perm (Fin (v ++ [i]).length))
    (hd : cw (canWord (v ++ [i]).length d) = crossingDescent v.length) :
    shL (v ++ [i]) 1 d ++ shR (v ++ [i]) 1 d = i :: v := by
  obtain ⟨h, _⟩ := lastToFirstHom_eq_cl D Sc i v
  rw [shL_append_shR, shTop, hd]
  exact tgt_eq h

theorem hom_eq_of_heq {s t u : List I} (e : t = u)
    (f : (pres D Sc).obj (ob D s) ⟶ (pres D Sc).obj (ob D t))
    (g : (pres D Sc).obj (ob D s) ⟶ (pres D Sc).obj (ob D u)) (h : HEq f g) :
    f ≫ eqToHom (congrArg (fun w => (pres D Sc).obj (ob D w)) e) = g := by
  subst u
  simpa only [eqToHom_refl, Category.comp_id] using eq_of_heq h

theorem output_shuffle_cases_of_length (i : I) (v t : List I)
    (hN : 1 + t.length = (v ++ [i]).length) (d : Shuffle hN) :
    (∃ (r : ℕ) (_hr : r < v.length),
      HEq (shPsi D Sc 1 d.1)
        ((shPsi D Sc 1 (wordProd v.length (List.range r))) ▷
          (pres D Sc).obj (ob D [i]))) ∨
      HEq (shPsi D Sc 1 d.1) (lastToFirstHom D Sc i v) := by
  have ht : t.length = v.length := by
    have hh := hN
    simp only [List.length_append, List.length_singleton] at hh
    omega
  have hd : IsShuffle (show 1 + v.length = (v ++ [i]).length by simp; omega) d.1 := by
    simpa only [ht] using d.2
  exact output_shuffle_cases D Sc i v ⟨d.1, hd⟩

theorem short_eq_of_word (i : I) (v : List I)
    (d : Equiv.Perm (Fin (v ++ [i]).length)) (e : Equiv.Perm (Fin v.length))
    (hd : cw (canWord (v ++ [i]).length d) = cw (canWord v.length e)) :
    shPsi D Sc 1 d ≫ eqToHom (congrArg (fun w => (pres D Sc).obj (ob D w))
      (short_target_of_word i v d e hd)) =
        ((shPsi D Sc 1 e) ▷ (pres D Sc).obj (ob D [i])) :=
  hom_eq_of_heq D Sc (short_target_of_word i v d e hd) _ _ (short_of_word D Sc i v d e hd)

theorem long_eq_of_word (i : I) (v : List I)
    (d : Equiv.Perm (Fin (v ++ [i]).length))
    (hd : cw (canWord (v ++ [i]).length d) = crossingDescent v.length) :
    shPsi D Sc 1 d ≫ eqToHom (congrArg (fun w => (pres D Sc).obj (ob D w))
      (long_target_of_word D Sc i v d hd)) = lastToFirstHom D Sc i v :=
  hom_eq_of_heq D Sc (long_target_of_word D Sc i v d hd) _ _ (long_of_word D Sc i v d hd)

example (i : I)
    (d : Shuffle (show 1 + ([] : List I).length = ([] ++ [i]).length by simp)) :
    HEq (shPsi D Sc 1 d.1) (lastToFirstHom D Sc i []) := by
  rcases output_shuffle_cases D Sc i [] d with ⟨r, hr, _⟩ | h
  · simp at hr
  · exact h

end OddMath.QuiverHecke.OutputShuffle
