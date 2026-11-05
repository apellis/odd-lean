/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.IntertwinerNaturality
import OddMath.QuiverHecke.CyclotomicAction.ContentBlocks

/-!
# Moving-strand elements in the finite-support Hom algebra

The colour-corner assembly of KKO I, arXiv:1206.5933v2, (8.13).
`contentMove_balance` is the algebra balance used to descend the map Q of
Proposition 8.4. Rows are targets, so multiplication reverses diagrammatic
composition. This module does not assert the tensor descent or the QP formula.
-/

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams MonoidalCategory
open scoped Classical

variable {I X : Type*} [AddCommGroup X] (D : SKM.Datum I X)
  {k : Type*} [CommRing k] (Sc : SKM.Scalars D k)

/-- Insertion of the distinguished strand on the left. -/
def prependWord (i : I) {n : ℕ} (w : Word I n) : Word I (n + 1) :=
  ⟨i :: w.1, by simp [w.2]⟩

theorem prependWord_injective (i : I) (n : ℕ) :
    Function.Injective (prependWord i (n := n)) := by
  intro a b h
  apply Subtype.ext
  exact List.cons.inj (congrArg Subtype.val h) |>.2

/-- Left insertion on each entry of the existing Hom algebra. -/
def prependHom (i : I) {n : ℕ} (s t : Word I n) :
    (wordObj D Sc s ⟶ wordObj D Sc t) →ₗ[k]
      (wordObj D Sc (prependWord i s) ⟶ wordObj D Sc (prependWord i t)) where
  toFun f := (pres D Sc).obj (ob D [i]) ◁ f
  map_add' f g := MonoidalSupercategory.whiskerLeft_add (R := k) _ f g
  map_smul' c f := MonoidalSupercategory.whiskerLeft_smul (R := k) _ c f

/-- A single left-inserted entry, with its dependent Hom fibre explicit. -/
def prependEntry (i : I) {n : ℕ} (s t : Word I n) :
    (wordObj D Sc s ⟶ wordObj D Sc t) →ₗ[k] Hn D Sc (n + 1) where
  toFun f := FiniteHomMatrix.single (prependWord i t) (prependWord i s)
    (prependHom D Sc i s t f)
  map_add' := by intros; simp [FiniteHomMatrix.single, DFinsupp.single_add]
  map_smul' := by intros; simp [FiniteHomMatrix.single, DFinsupp.single_smul]

/-- The affine left insertion, extended by the matrix coordinate sum. -/
def prependLinear (i : I) (n : ℕ) : Hn D Sc n →ₗ[k] Hn D Sc (n + 1) :=
  DFinsupp.lsum k fun p => prependEntry D Sc i p.2 p.1

@[simp] theorem prependLinear_single (i : I) {n : ℕ} (s t : Word I n)
    (f : wordObj D Sc s ⟶ wordObj D Sc t) :
    prependLinear D Sc i n (FiniteHomMatrix.single t s f) =
      FiniteHomMatrix.single (prependWord i t) (prependWord i s)
        (prependHom D Sc i s t f) := by
  let : DecidableEq (Word I n) := Classical.decEq _
  let : DecidableEq (Word I (n + 1)) := Classical.decEq _
  exact DFinsupp.lsum_single (S := k)
    (fun p : Word I n × Word I n => prependEntry D Sc i p.2 p.1) (t, s) f

/-- Insert a parity-twisted Hom entry. -/
def homTwistEntry (p : ZMod 2) {n : ℕ} (s t : Word I n) :
    (wordObj D Sc s ⟶ wordObj D Sc t) →ₗ[k] Hn D Sc n where
  toFun f := FiniteHomMatrix.single t s (Supercategory.twist k p f)
  map_add' := by intros; simp [FiniteHomMatrix.single, DFinsupp.single_add]
  map_smul' := by intros; simp [FiniteHomMatrix.single, DFinsupp.single_smul]

/-- Parity involution on matrix entries; the exponent is uniform on a content block. -/
def homMatrixTwist (n : ℕ) (p : ZMod 2) : Hn D Sc n →ₗ[k] Hn D Sc n :=
  DFinsupp.lsum k fun q => homTwistEntry D Sc p q.2 q.1

@[simp] theorem homMatrixTwist_single (p : ZMod 2) {n : ℕ} (s t : Word I n)
    (f : wordObj D Sc s ⟶ wordObj D Sc t) :
    homMatrixTwist D Sc n p (FiniteHomMatrix.single t s f) =
      FiniteHomMatrix.single t s (Supercategory.twist k p f) := by
  let : DecidableEq (Word I n) := Classical.decEq _
  exact DFinsupp.lsum_single (S := k)
    (fun q : Word I n × Word I n => homTwistEntry D Sc p q.2 q.1) (t, s) f

theorem homMatrixTwist_twice (n : ℕ) (p : ZMod 2) (z : Hn D Sc n) :
    homMatrixTwist D Sc n p (homMatrixTwist D Sc n p z) = z := by
  induction z using FiniteHomMatrix.induction with
  | hz => simp
  | ha a b ha hb => simp [ha, hb]
  | hs s t f => simp [Supercategory.twist_twist]

/-- Left insertion respects multiplication, including off-diagonal zero products. -/
def prependAlgebra (i : I) (n : ℕ) : Hn D Sc n →ₙₐ[k] Hn D Sc (n + 1) where
  toFun := prependLinear D Sc i n
  map_zero' := map_zero _
  map_add' := map_add _
  map_smul' := map_smul _
  map_mul' a b := by
    induction a using FiniteHomMatrix.induction with
    | hz => simp
    | ha a b ha hb => simp [add_mul, ha, hb]
    | hs s t f =>
      induction b using FiniteHomMatrix.induction with
      | hz => simp
      | ha a b ha hb => simp [mul_add, ha, hb]
      | hs r q g =>
        by_cases h : t = r
        · subst r
          simp only [FiniteHomMatrix.single_mul_single, prependLinear_single]
          congr 1
          exact MonoidalSupercategory.whiskerLeft_comp (R := k) _ g f
        · have h' : prependWord i t ≠ prependWord i r := fun e => h (prependWord_injective i n e)
          simp [FiniteHomMatrix.single_mul_single_of_ne, h, h']

/-- Entrywise parity twisting is an algebra map. -/
def homMatrixTwistAlgebra (n : ℕ) (p : ZMod 2) : Hn D Sc n →ₙₐ[k] Hn D Sc n where
  toFun := homMatrixTwist D Sc n p
  map_zero' := map_zero _
  map_add' := map_add _
  map_smul' := map_smul _
  map_mul' a b := by
    induction a using FiniteHomMatrix.induction with
    | hz => simp
    | ha a b ha hb => simp [add_mul, ha, hb]
    | hs s t f =>
      induction b using FiniteHomMatrix.induction with
      | hz => simp
      | ha a b ha hb => simp [mul_add, ha, hb]
      | hs r q g =>
        by_cases h : t = r
        · subst r
          simp [Supercategory.twist_comp]
        · simp [FiniteHomMatrix.single_mul_single_of_ne, h]

/-- The parity of an unordered colour content. -/
def contentSumParity (β : Multiset I) : ZMod 2 := (β.map D.parity).sum

theorem wordSumParity_eq_content {n : ℕ} (s : Word I n) :
    wordSumParity D s.1 = contentSumParity D (wordContent s) := rfl

variable [Fintype I]

/-- The sum of `g_n ⋯ g_1 e(i,ν)` over the words of content `β`. -/
def contentMove (i : I) (n : ℕ) (β : Multiset I) : Hn D Sc (n + 1) :=
  ∑ w ∈ Finset.univ.filter (fun w : Word I n => wordContent w = β),
    FiniteHomMatrix.single (appendWord i w) (prependWord i w) (moveHom D Sc i [] w.1)

private theorem contentMove_mul_entry (i : I) {n : ℕ} (β : Multiset I) (s t : Word I n)
    (f : wordObj D Sc (prependWord i s) ⟶ wordObj D Sc (prependWord i t)) :
    contentMove D Sc i n β * FiniteHomMatrix.single (prependWord i t) (prependWord i s) f =
      if wordContent t = β then
        FiniteHomMatrix.single (appendWord i t) (prependWord i s) (f ≫ moveHom D Sc i [] t.1)
      else 0 := by
  rw [contentMove, Finset.sum_mul]
  by_cases ht : wordContent t = β
  · rw [ite_eq_left ht, Finset.sum_eq_single t]
    · simp
    · intro b _ hb
      exact FiniteHomMatrix.single_mul_single_of_ne _ _ _ _
        (fun h => hb (prependWord_injective i n h)) _ _
    · simp [ht]
  · rw [ite_eq_right ht]
    apply Finset.sum_eq_zero
    intro b hb
    apply FiniteHomMatrix.single_mul_single_of_ne
    intro h
    have he := prependWord_injective i n h
    subst b
    exact ht (Finset.mem_filter.mp hb).2

private theorem entry_mul_contentMove (i : I) {n : ℕ} (β : Multiset I) (s t : Word I n)
    (f : wordObj D Sc (appendWord i s) ⟶ wordObj D Sc (appendWord i t)) :
    FiniteHomMatrix.single (appendWord i t) (appendWord i s) f * contentMove D Sc i n β =
      if wordContent s = β then
        FiniteHomMatrix.single (appendWord i t) (prependWord i s) (moveHom D Sc i [] s.1 ≫ f)
      else 0 := by
  rw [contentMove, Finset.mul_sum]
  by_cases hs : wordContent s = β
  · rw [ite_eq_left hs, Finset.sum_eq_single s]
    · simp
    · intro b _ hb
      exact FiniteHomMatrix.single_mul_single_of_ne _ _ _ _
        (fun h => hb (appendWord_injective i n h.symm)) _ _
    · simp [hs]
  · rw [ite_eq_right hs]
    apply Finset.sum_eq_zero
    intro b hb
    apply FiniteHomMatrix.single_mul_single_of_ne
    intro h
    have he := appendWord_injective i n h.symm
    subst b
    exact hs (Finset.mem_filter.mp hb).2

/-- KKO (8.13) as an equality in `Hn`, for arbitrary inhomogeneous algebra elements.
The exponent `p(i)p(β)` is the twist required by the shifted coefficient factor in Q. -/
theorem contentMove_balance (i : I) (n : ℕ) (β : Multiset I) (z : Hn D Sc n) :
    appendLinear D Sc i n (homMatrixTwist D Sc n (D.parity i * contentSumParity D β) z) *
        contentMove D Sc i n β =
      contentMove D Sc i n β * prependLinear D Sc i n z := by
  induction z using FiniteHomMatrix.induction with
  | hz => simp
  | ha a b ha hb => simp only [map_add, add_mul, mul_add, ha, hb]
  | hs t s f =>
    rw [homMatrixTwist_single, appendLinear_single, prependLinear_single,
      entry_mul_contentMove, contentMove_mul_entry]
    by_cases h : wordContent s = wordContent t
    · rw [h]
      split_ifs with ht
      · congr 1
        have hp : wordSumParity D s.1 = contentSumParity D β := by
          rw [wordSumParity_eq_content, h, ht]
        simpa only [hp, appendHom, prependHom, LinearMap.coe_mk, AddHom.coe_mk,
          wordObj, prependWord, appendWord, List.nil_append, List.singleton_append] using
          (hom_comp_moveHom D Sc i f).symm
      · rfl
    · have hf := hom_eq_zero_of_content_ne D Sc h f
      subst f
      simp [appendHom, prependHom, MonoidalSupercategory.whiskerLeft_zero (R := k),
        MonoidalSupercategory.zero_whiskerRight (R := k)]

end OddMath.QuiverHecke
