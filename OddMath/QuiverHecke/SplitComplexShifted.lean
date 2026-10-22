/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SplitComplexK0
import OddMath.SKM.IdempotentSummands

/-!
# Split complexes of shifted summands

The `K₀` step of Brundan–Ellis, arXiv:1701.04133v2, Proposition 11.2 and Lemma 11.6, for any
graded supercategory `A` (the quiver Hecke supercategory, or a hom category of `𝔘(𝔤)`).

`ShiftedData k A M` is a family of objects `W a` (`a ≤ M`) of `A` with homogeneous idempotents
`e a` (even, of degree `0`), maps `u a : W a → W (a + 1)` and `d a : W (a + 1) → W a` (`a < M`),
and shifts `sh a`,
`par a`, such that `u a` and `d a` are absorbed by the idempotents and have degree
`sh a - sh (a + 1)`, `sh (a + 1) - sh a` and parity `par a + par (a + 1)`. Then
`term a = Q^{sh a} Π^{par a} (W a, e a)` is a summand of the completed category
`Karoubi (Mat_ (Base k A))` and `u`, `d` lift to even degree-zero maps between the terms
(`liftU`, `liftD`). If moreover `M ≥ 1`, `u u = 0`, `d d = 0`, `e 0 = u 0 d 0`,
`e (a + 1) = u (a + 1) d (a + 1) + d a u a` for `a + 1 < M` and `e M = d (M - 1) u (M - 1)`
(`ShiftedData.Split`), the lifts form
a split complex (`Split.isSplitK`) and `∑_{a ≤ M} (-1)^a [term a] = 0`
(`Split.alternating_sum_eq_zero`).
-/

noncomputable section
open scoped BigOperators
namespace OddMath.QuiverHecke.SplitComplex
open CategoryTheory CategoryTheory.Idempotents StringDiagrams GradedSupercategory
open OddMath.SKM.Summands

variable {k : Type*} [CommRing k] {A : Type*} [Category A] [Preadditive A] [Linear k A]
  [Supercategory k A] [GradedSupercategory k A]

/-- A homogeneous morphism `g : f → f'` as an even degree-zero morphism between the shifts
`Q^m Π^p f → Q^n Π^{p'} f'`. -/
def hlift {f f' : A} {m n : ℤ} {p p' : ZMod 2} (g : f ⟶ f')
    (hd : g ∈ degree (R := k) f f' (m - n))
    (hp : g ∈ Supercategory.parity (R := k) f f' (p + p')) :
    shifted (k := k) f m p ⟶ shifted (k := k) f' n p' :=
  ⟨⟨g, by change g ∈ degree (R := k) _ _ (0 + (m - n)); simpa using hd⟩,
    by change g ∈ Supercategory.parity (R := k) _ _ (0 + (p + p')); simpa using hp⟩

theorem base_ext {f f' : A} {m n : ℤ} {p p' : ZMod 2}
    {x y : shifted (k := k) f m p ⟶ shifted (k := k) f' n p'} (h : x.1.1 = y.1.1) : x = y :=
  Subtype.ext (Subtype.ext h)

variable (k A) in
/-- A family of homogeneous idempotents `e a` on objects `W a` (`a ≤ M`) and maps between them
(`a < M`), with the shifts that make the maps even of degree zero. -/
structure ShiftedData (M : ℕ) where
  /-- The objects. -/
  W : (a : ℕ) → a ≤ M → A
  /-- The idempotents. -/
  e : ∀ a (h : a ≤ M), W a h ⟶ W a h
  /-- The maps up. -/
  u : ∀ a (h : a < M), W a h.le ⟶ W (a + 1) h
  /-- The maps down. -/
  d : ∀ a (h : a < M), W (a + 1) h ⟶ W a h.le
  /-- The degree shifts. -/
  sh : ℕ → ℤ
  /-- The parity shifts. -/
  par : ℕ → ZMod 2
  e_idem : ∀ a h, e a h ≫ e a h = e a h
  e_degree : ∀ a h, e a h ∈ degree (R := k) (W a h) (W a h) 0
  e_even : ∀ a h, e a h ∈ Supercategory.parity (R := k) (W a h) (W a h) 0
  u_degree : ∀ a (h : a < M), u a h ∈ degree (R := k) _ _ (sh a - sh (a + 1))
  u_parity : ∀ a (h : a < M), u a h ∈ Supercategory.parity (R := k) _ _ (par a + par (a + 1))
  d_degree : ∀ a (h : a < M), d a h ∈ degree (R := k) _ _ (sh (a + 1) - sh a)
  d_parity : ∀ a (h : a < M), d a h ∈ Supercategory.parity (R := k) _ _ (par (a + 1) + par a)
  e_u : ∀ a (h : a < M), e a h.le ≫ u a h ≫ e (a + 1) h = u a h
  e_d : ∀ a (h : a < M), e (a + 1) h ≫ d a h ≫ e a h.le = d a h

namespace ShiftedData

variable {M : ℕ} (S : ShiftedData k A M)

/-- The summand `Q^{sh a} Π^{par a} (W a, e a)`. -/
def term (a : ℕ) (h : a ≤ M) : Karoubi (Mat_ (Base k A)) :=
  raw (S.e_idem a h) (S.e_degree a h) (S.e_even a h) (S.sh a) (S.par a)

/-- `u a` as a map of summands. -/
def liftU (a : ℕ) (h : a < M) : S.term a h.le ⟶ S.term (a + 1) h :=
  ⟨(Mat_.embedding _).map (hlift (S.u a h) (S.u_degree a h) (S.u_parity a h)), by
    change (Mat_.embedding _).map _ ≫ (Mat_.embedding _).map _ ≫ (Mat_.embedding _).map _ = _
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    exact base_ext (S.e_u a h)⟩

/-- `d a` as a map of summands. -/
def liftD (a : ℕ) (h : a < M) : S.term (a + 1) h ⟶ S.term a h.le :=
  ⟨(Mat_.embedding _).map (hlift (S.d a h) (S.d_degree a h) (S.d_parity a h)), by
    change (Mat_.embedding _).map _ ≫ (Mat_.embedding _).map _ ≫ (Mat_.embedding _).map _ = _
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    exact base_ext (S.e_d a h)⟩

/-- The identities of a split complex, with the idempotents in place of the identities. -/
structure Split : Prop where
  pos : 0 < M
  uu : ∀ a (h : a + 1 < M), S.u a (Nat.lt_of_succ_lt h) ≫ S.u (a + 1) h = 0
  dd : ∀ a (h : a + 1 < M), S.d (a + 1) h ≫ S.d a (Nat.lt_of_succ_lt h) = 0
  split_zero : S.e 0 (Nat.zero_le M) = S.u 0 pos ≫ S.d 0 pos
  split_succ : ∀ a (h : a + 1 < M), S.e (a + 1) h.le =
    S.u (a + 1) h ≫ S.d (a + 1) h + S.d a (Nat.lt_of_succ_lt h) ≫ S.u a (Nat.lt_of_succ_lt h)
  split_top : ∀ a (h : a < M), a + 1 = M → S.e (a + 1) h = S.d a h ≫ S.u a h

variable {S}

theorem Split.isSplitK [Limits.HasBinaryBiproducts (Karoubi (Mat_ (Base k A)))] (h : S.Split) :
    IsSplitK M S.term S.liftU S.liftD where
  pos := h.pos
  ff a ha := by
    apply Karoubi.hom_ext
    change (Mat_.embedding _).map _ ≫ (Mat_.embedding _).map _ = 0
    rw [← Functor.map_comp, ← Functor.map_zero (Mat_.embedding _)]
    congr 1
    exact base_ext (h.uu a ha)
  gg a ha := by
    apply Karoubi.hom_ext
    change (Mat_.embedding _).map _ ≫ (Mat_.embedding _).map _ = 0
    rw [← Functor.map_comp, ← Functor.map_zero (Mat_.embedding _)]
    congr 1
    exact base_ext (h.dd a ha)
  split_zero := by
    apply Karoubi.hom_ext
    change (Mat_.embedding _).map _ = (Mat_.embedding _).map _ ≫ (Mat_.embedding _).map _
    rw [← Functor.map_comp]
    congr 1
    exact base_ext h.split_zero
  split_succ a ha := by
    apply Karoubi.hom_ext
    change (Mat_.embedding _).map _ = (Mat_.embedding _).map _ ≫ (Mat_.embedding _).map _ +
      (Mat_.embedding _).map _ ≫ (Mat_.embedding _).map _
    rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_add]
    congr 1
    exact base_ext (h.split_succ a ha)
  split_top a ha ht := by
    apply Karoubi.hom_ext
    change (Mat_.embedding _).map _ = (Mat_.embedding _).map _ ≫ (Mat_.embedding _).map _
    rw [← Functor.map_comp]
    congr 1
    exact base_ext (h.split_top a ha ht)

/-- **The alternating sum of the terms of a split complex vanishes**:
`∑_{a ≤ M} (-1)^a [term a] = 0`. -/
theorem Split.alternating_sum_eq_zero [Limits.HasBinaryBiproducts (Karoubi (Mat_ (Base k A)))]
    (h : S.Split) :
    ∑ a : Fin (M + 1), ((-1 : ℤ) ^ (a : ℕ)) • K₀.mk (S.term a (Nat.le_of_lt_succ a.2)) = 0 :=
  h.isSplitK.alternating_sum_eq_zero

end ShiftedData

end OddMath.QuiverHecke.SplitComplex
