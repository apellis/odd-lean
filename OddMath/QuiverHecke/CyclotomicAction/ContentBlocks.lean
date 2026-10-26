import OddMath.QuiverHecke.CyclotomicAction.Induction

/-!
# Content idempotents in cyclotomic quotients

The content decomposition underlying BE2 §11 is formed in the finite-support
Hom algebra and descends along its cyclotomic quotient map. Multiplication
is composition with the right factor first. Content is an unordered multiset
of colours; no weight is assigned using strand number alone.
-/

noncomputable section
open CategoryTheory StringDiagrams
open scoped Classical
namespace OddMath.QuiverHecke
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  {k : Type w} [CommRing k] (Sc : SKM.Scalars D k)

/-- The unordered colour content of a word. -/
def wordContent {n : ℕ} (s : Word I n) : Multiset I := s.1

private theorem content_act (g : PG) (t : List I) :
    (g.act t : Multiset I) = (t : Multiset I) := by
  cases g with
  | dot p => rfl
  | cross p =>
    simp only [PG.act]
    split
    · next x y r h =>
      have ht : t = t.take p ++ x :: y :: r := by
        rw [← h, List.take_append_drop]
      apply Quot.sound
      conv_rhs => rw [ht]
      exact (List.Perm.swap x y r).append_left (t.take p)
    · rfl

private theorem content_tgt (t : List I) (gs : List PG) :
    (tgt t gs : Multiset I) = (t : Multiset I) := by
  induction gs generalizing t with
  | nil => rfl
  | cons g gs ih => exact (ih (g.act t)).trans (content_act g t)

/-- Morphisms cannot change unordered colour content. -/
theorem hom_eq_zero_of_content_ne {s t : List I}
    (h : (s : Multiset I) ≠ (t : Multiset I))
    (f : (pres D Sc).obj (ob D s) ⟶ (pres D Sc).obj (ob D t)) : f = 0 := by
  induction f using (pres D Sc).hom_induction with
  | diag d =>
    obtain ⟨ls, hc, rfl⟩ := exists_mkD d
    have he := tgt_eq ((exists_pl hc).symm ▸ hc)
    exact (h ((content_tgt s (ls.map LayerData.pg)).symm.trans
      (congrArg (fun l : List I => (l : Multiset I)) he))).elim
  | zero => rfl
  | add f g hf hg => rw [hf, hg, add_zero]
  | smul c f hf => rw [hf, smul_zero]

variable [Fintype I]

/-- Sum of the word identities of a given content. -/
def contentIdempotent (n : ℕ) (β : Multiset I) : Hn D Sc n :=
  FiniteHomMatrix.localUnit (Finset.univ.filter (fun s => wordContent s = β))

@[simp] theorem contentIdempotent_sq (n : ℕ) (β : Multiset I) :
    contentIdempotent D Sc n β * contentIdempotent D Sc n β =
      contentIdempotent D Sc n β := FiniteHomMatrix.localUnit_sq _

private theorem content_mul_single {n : ℕ} (β : Multiset I) (s t : Word I n)
    (f : wordObj D Sc t ⟶ wordObj D Sc s) :
    contentIdempotent D Sc n β * FiniteHomMatrix.single s t f =
      if wordContent s = β then FiniteHomMatrix.single s t f else 0 := by
  split_ifs with h
  · exact FiniteHomMatrix.localUnit_mul_single _ _ _ _ (by simp [h])
  · unfold contentIdempotent FiniteHomMatrix.localUnit
    rw [Finset.sum_mul]
    apply Finset.sum_eq_zero
    intro b hb
    apply FiniteHomMatrix.single_mul_single_of_ne
    intro e
    subst b
    exact h (Finset.mem_filter.mp hb).2

private theorem single_mul_content {n : ℕ} (β : Multiset I) (s t : Word I n)
    (f : wordObj D Sc t ⟶ wordObj D Sc s) :
    FiniteHomMatrix.single s t f * contentIdempotent D Sc n β =
      if wordContent t = β then FiniteHomMatrix.single s t f else 0 := by
  split_ifs with h
  · exact FiniteHomMatrix.single_mul_localUnit _ _ _ _ (by simp [h])
  · unfold contentIdempotent FiniteHomMatrix.localUnit
    rw [Finset.mul_sum]
    apply Finset.sum_eq_zero
    intro b hb
    apply FiniteHomMatrix.single_mul_single_of_ne
    intro e
    subst b
    exact h (Finset.mem_filter.mp hb).2

/-- Content identities commute with every affine element, including odd ones. -/
theorem contentIdempotent_central (n : ℕ) (β : Multiset I) (z : Hn D Sc n) :
    contentIdempotent D Sc n β * z = z * contentIdempotent D Sc n β := by
  induction z using FiniteHomMatrix.induction with
  | hz => simp
  | ha a b ha hb => simp [mul_add, add_mul, ha, hb]
  | hs s t f =>
    rw [content_mul_single, single_mul_content]
    by_cases h : wordContent t = wordContent s
    · rw [h]
    · have hf := hom_eq_zero_of_content_ne D Sc h f
      simp [hf]

/-- Distinct contents are orthogonal. -/
theorem contentIdempotent_orthogonal (n : ℕ) {β γ : Multiset I} (h : β ≠ γ) :
    contentIdempotent D Sc n β * contentIdempotent D Sc n γ = 0 := by
  conv_lhs => rhs; unfold contentIdempotent FiniteHomMatrix.localUnit
  rw [Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro s hs
  change contentIdempotent D Sc n β * FiniteHomMatrix.single s s _ = 0
  rw [content_mul_single, ite_eq_right]
  exact fun e => h (e.symm.trans (Finset.mem_filter.mp hs).2)

/-- Content idempotent in the specified cyclotomic quotient. -/
def cyclotomicContentIdempotent (a : I → _root_.Polynomial k) (n : ℕ)
    (β : Multiset I) : CyclotomicAlgebra D Sc a n :=
  cyclotomicMk D Sc a n (contentIdempotent D Sc (n + 1) β)

@[simp] theorem cyclotomicContentIdempotent_sq (a : I → _root_.Polynomial k)
    (n : ℕ) (β : Multiset I) :
    cyclotomicContentIdempotent D Sc a n β * cyclotomicContentIdempotent D Sc a n β =
      cyclotomicContentIdempotent D Sc a n β := by
  simp [cyclotomicContentIdempotent, ← map_mul]

theorem cyclotomicContentIdempotent_central (a : I → _root_.Polynomial k)
    (n : ℕ) (β : Multiset I) (z : CyclotomicAlgebra D Sc a n) :
    cyclotomicContentIdempotent D Sc a n β * z =
      z * cyclotomicContentIdempotent D Sc a n β := by
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
  exact congrArg (cyclotomicMk D Sc a n) (contentIdempotent_central D Sc (n + 1) β z)

theorem cyclotomicContentIdempotent_orthogonal (a : I → _root_.Polynomial k)
    (n : ℕ) {β γ : Multiset I} (h : β ≠ γ) :
    cyclotomicContentIdempotent D Sc a n β * cyclotomicContentIdempotent D Sc a n γ = 0 := by
  rw [cyclotomicContentIdempotent, cyclotomicContentIdempotent, ← map_mul,
    contentIdempotent_orthogonal D Sc (n + 1) h, map_zero]

omit [Fintype I] in
/-- Rightmost strand insertion adds exactly its colour to content. -/
@[simp] theorem wordContent_append (i : I) {n : ℕ} (s : Word I n) :
    wordContent (appendWord i s) = {i} + wordContent s := by
  simp only [wordContent, appendWord, ← Multiset.coe_add, Multiset.coe_singleton,
    Multiset.add_comm]

/-- The affine inclusion shifts the content projector by the appended colour. -/
theorem contentIdempotent_appendAlgebra (i : I) (n : ℕ) (β : Multiset I)
    (z : Hn D Sc n) :
    contentIdempotent D Sc (n + 1) ({i} + β) * appendAlgebra D Sc i n z =
      appendAlgebra D Sc i n (contentIdempotent D Sc n β * z) := by
  induction z using FiniteHomMatrix.induction with
  | hz => simp
  | ha x y hx hy => simp only [map_add, mul_add, hx, hy]
  | hs s t f =>
    rw [content_mul_single]
    change contentIdempotent D Sc (n + 1) ({i} + β) *
      appendLinear D Sc i n (FiniteHomMatrix.single s t f) = _
    rw [appendLinear_single, content_mul_single, wordContent_append]
    simp only [add_right_inj]
    split_ifs
    · exact (appendLinear_single D Sc i t s f).symm
    · exact (map_zero (appendAlgebra D Sc i n)).symm

/-- The same projector identity holds on the cyclotomic quotient itself. -/
theorem cyclotomicContentIdempotent_append (i : I) (a : I → _root_.Polynomial k)
    (n : ℕ) (β : Multiset I) (z : CyclotomicAlgebra D Sc a n) :
    cyclotomicContentIdempotent D Sc a (n + 1) ({i} + β) *
        cyclotomicAppend D Sc i a n z =
      cyclotomicAppend D Sc i a n (cyclotomicContentIdempotent D Sc a n β * z) := by
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
  exact congrArg (cyclotomicMk D Sc a (n + 1))
    (contentIdempotent_appendAlgebra D Sc i (n + 1) β z)

end OddMath.QuiverHecke
