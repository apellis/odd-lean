/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.AppendBalance
import OddMath.QuiverHecke.CyclotomicAction.IntertwinerCorners

/-!
# The append Mackey map `P` on induced modules

`docs/Nondegeneracy/AppendMackeySource.md` §4. Let `ψ = appendAlgebra i (n+1)` and
`φ_ε = prependAlgebra i (n+1) ∘ tw_ε` (the prepend inclusion after the entrywise parity twist).
The matrix

  `W = Σ_s single (i :: s) (s ++ [i]) W_s`,  `W_s = T_s ≫ f_i(x₁)`,

satisfies, entry by entry, `W ψ(a) - φ_ε(a) W = single (i :: s) (t ++ [i]) E(g)` for
`a = single s t g`, where `E` is the balance error of `AppendBalance.lean` when the parity
`q_t` of `W_t` is `ε`. Since `E(g)` lies in the killed part (`appendError_mem_appendKill`),
`P : z ⊗ b ↦ z W ⊗ b` descends from `Ind_(φ_ε) N` to `Ind_ψ N` for every left
`Hn (n+1)`-module `N` on which the cyclotomic ideal acts by zero and the diagonal idempotent of
every word `t` with `q_t ≠ ε` acts by zero (for instance a content corner of parity `ε`).

This is the source map of the append-side Mackey boundary (`DeformedMackeyBoundary.md` §1;
Kang–Kashiwara–Oh, arXiv:1206.5933v2, proof of Lemma 8.1, mirror form).

## Main results

* `InductionAlong.Ind.descend`: the map `z ⊗ n ↦ z x ⊗ n` from a balance hypothesis;
* `appendMoveMatrix_mul_append`, `prependTwist_mul_appendMoveMatrix`: the entries of `W ψ(a)`
  and `φ_ε(a) W`;
* `single_mem_cyclotomicIdeal`: the old cyclotomic ideal of morphisms lies in the cyclotomic
  ideal of the matrix algebra;
* `appendMackeyMap`: the descended map `P : Ind_(φ_ε) N → Ind_ψ N`.
-/

noncomputable section

namespace Categorification.InductionAlong.Ind

universe x y
variable {A H : Type x} [Ring A] [Ring H] {N : Type y} [AddCommGroup N] [Module A N]
  {φ ψ : A →ₙ+* H}

theorem mul_mem_of_mul_right {w : H} (hw : w * ψ 1 = w) (z : H) : z * w ∈ lIdeal (ψ 1) := by
  rw [mem_lIdeal, mul_assoc, hw]

/-- Right multiplication by `w` under a balance hypothesis: `z ⊗ n ↦ z w ⊗ n`. -/
def descend {w : H} (hw : w * ψ 1 = w)
    (hb : ∀ (z : Corner φ) (a : A) (m : N),
      (tmul ⟨z.1 * φ a * w, mul_mem_of_mul_right hw _⟩ m : Ind N ψ) =
        tmul ⟨z.1 * w, mul_mem_of_mul_right hw _⟩ (a • m)) :
    Ind N φ →ₗ[H] Ind N ψ :=
  lift (fun z m => tmul ⟨z.1 * w, mul_mem_of_mul_right hw _⟩ m)
    (fun z z' m => by rw [← add_tmul]; congr 1; exact Subtype.ext (add_mul _ _ _))
    (fun z m m' => tmul_add _ m m')
    (fun z a m => hb z a m)
    (fun b z m => by rw [smul_tmul]; congr 1; exact Subtype.ext (mul_assoc b z.1 w))

@[simp] theorem descend_tmul {w : H} (hw : w * ψ 1 = w) (hb) (z : Corner φ) (m : N) :
    descend hw hb (tmul z m) = tmul ⟨z.1 * w, mul_mem_of_mul_right hw _⟩ m := rfl

/-- A tensor whose corner factor ends in `ψ(c)`, with `c` acting by zero, vanishes. -/
theorem tmul_mul_eq_zero {X : H} (hX : X * ψ 1 = X) {c : A} (hc : ∀ m : N, c • m = 0)
    (z : H) (hm : z * (X * ψ c) ∈ lIdeal (ψ 1)) (m : N) :
    (tmul ⟨z * (X * ψ c), hm⟩ m : Ind N ψ) = 0 := by
  have e : (⟨z * (X * ψ c), hm⟩ : InductionAlong.Corner ψ) =
      MulOpposite.op c • ⟨z * X, mul_mem_of_mul_right hX z⟩ :=
    Subtype.ext (by rw [op_smul_val, mul_assoc])
  rw [e, op_smul_tmul, hc, tmul_zero]

end Categorification.InductionAlong.Ind


namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams MonoidalCategory Categorification Categorification.InductionAlong
open scoped Classical

universe u v w
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]

section Matrix
variable (a : I → _root_.Polynomial k) (i : I) (n : ℕ)

local notation "ψ" =>
  (appendAlgebra D Sc i (n + 1) : Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1))

/-- `φ_ε = prependAlgebra ∘ tw_ε`: the prepend inclusion after the entrywise parity twist. -/
def prependTwist (ε : ZMod 2) : Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1) :=
  (((prependAlgebra D Sc i (n + 1)).comp (homMatrixTwistAlgebra D Sc (n + 1) ε) :
    Hn D Sc (n + 1) →ₙₐ[k] Hn D Sc (n + 1 + 1)) : Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1))

theorem prependTwist_single (ε : ZMod 2) (s t : Word I (n + 1))
    (g : wordObj D Sc t ⟶ wordObj D Sc s) :
    prependTwist D Sc i n ε (FiniteHomMatrix.single s t g) =
      FiniteHomMatrix.single (prependWord i s) (prependWord i t)
        (prependHom D Sc i t s (Supercategory.twist k ε g)) := by
  change prependLinear D Sc i (n + 1)
    (homMatrixTwist D Sc (n + 1) ε (FiniteHomMatrix.single s t g)) = _
  rw [homMatrixTwist_single, prependLinear_single]

theorem appendAlgebra_single (s t : Word I (n + 1)) (g : wordObj D Sc t ⟶ wordObj D Sc s) :
    ψ (FiniteHomMatrix.single s t g) =
      FiniteHomMatrix.single (appendWord i s) (appendWord i t) (appendHom D Sc i t s g) := by
  exact appendLinear_single D Sc i t s g

/-- The matrix `W = Σ_s single (i :: s) (s ++ [i]) W_s`. -/
def appendMoveMatrix : Hn D Sc (n + 1 + 1) :=
  ∑ s : Word I (n + 1), FiniteHomMatrix.single (prependWord i s) (appendWord i s)
    (appendW D Sc a i s.1 : wordObj D Sc (appendWord i s) ⟶ wordObj D Sc (prependWord i s))

omit [Fintype I] in
theorem appendHom_id (t : Word I (n + 1)) :
    appendHom D Sc i t t (𝟙 (wordObj D Sc t)) = 𝟙 _ :=
  MonoidalSupercategory.id_whiskerRight (R := k) (wordObj D Sc t) ((pres D Sc).obj (ob D [i]))

theorem single_mul_appendOne {r : Word I (n + 1 + 1)} (c : Word I (n + 1))
    (f : wordObj D Sc (appendWord i c) ⟶ wordObj D Sc r) :
    FiniteHomMatrix.single r (appendWord i c) f * ψ 1 =
      FiniteHomMatrix.single r (appendWord i c) f := by
  have h1 : (1 : Hn D Sc (n + 1)) =
      ∑ t : Word I (n + 1), FiniteHomMatrix.single t t (𝟙 (wordObj D Sc t)) := rfl
  rw [h1, map_sum, Finset.mul_sum, Finset.sum_eq_single c]
  · rw [appendAlgebra_single, FiniteHomMatrix.single_mul_single, appendHom_id, Category.id_comp]
  · intro t _ ht
    rw [appendAlgebra_single, FiniteHomMatrix.single_mul_single_of_ne]
    exact fun e => ht (appendWord_injective i _ e).symm
  · intro h; exact (h (Finset.mem_univ _)).elim

theorem appendMoveMatrix_mul_appendOne :
    appendMoveMatrix D Sc a i n * ψ 1 = appendMoveMatrix D Sc a i n := by
  rw [appendMoveMatrix, Finset.sum_mul]
  exact Finset.sum_congr rfl fun s _ => single_mul_appendOne D Sc i n s _

/-- The entries of `W ψ(a)`. -/
theorem appendMoveMatrix_mul_append (s t : Word I (n + 1))
    (g : wordObj D Sc t ⟶ wordObj D Sc s) :
    appendMoveMatrix D Sc a i n * ψ (FiniteHomMatrix.single s t g) =
      FiniteHomMatrix.single (prependWord i s) (appendWord i t)
        (appendHom D Sc i t s g ≫ appendW D Sc a i s.1) := by
  rw [appendMoveMatrix, appendAlgebra_single, Finset.sum_mul, Finset.sum_eq_single s]
  · rw [FiniteHomMatrix.single_mul_single]
  · intro u _ hu
    rw [FiniteHomMatrix.single_mul_single_of_ne]
    exact fun e => hu (appendWord_injective i _ e)
  · intro h; exact (h (Finset.mem_univ _)).elim

/-- The entries of `φ_ε(a) W`. -/
theorem prependTwist_mul_appendMoveMatrix (ε : ZMod 2) (s t : Word I (n + 1))
    (g : wordObj D Sc t ⟶ wordObj D Sc s) :
    prependTwist D Sc i n ε (FiniteHomMatrix.single s t g) * appendMoveMatrix D Sc a i n =
      FiniteHomMatrix.single (prependWord i s) (appendWord i t)
        (appendW D Sc a i t.1 ≫ prependHom D Sc i t s (Supercategory.twist k ε g)) := by
  rw [appendMoveMatrix, prependTwist_single, Finset.mul_sum, Finset.sum_eq_single t]
  · rw [FiniteHomMatrix.single_mul_single]
  · intro u _ hu
    rw [FiniteHomMatrix.single_mul_single_of_ne]
    exact fun e => hu (prependWord_injective i _ e).symm
  · intro h; exact (h (Finset.mem_univ _)).elim

omit [Fintype I] in
theorem matrix_single_sub {r c : Word I (n + 1 + 1)} (f g : wordObj D Sc c ⟶ wordObj D Sc r) :
    (FiniteHomMatrix.single r c (f - g) : Hn D Sc (n + 1 + 1)) =
      FiniteHomMatrix.single r c f - FiniteHomMatrix.single r c g :=
  by convert DFinsupp.single_sub (β := fun p : Word I (n + 1 + 1) × Word I (n + 1 + 1) =>
    (wordObj D Sc p.2 ⟶ wordObj D Sc p.1)) (r, c) f g

omit [Fintype I] in
theorem length_eq_of_hom_ne_zero {s : Word I (n + 1)} {w : List I}
    {p : wordObj D Sc s ⟶ (pres D Sc).obj (ob D w)} (hp : p ≠ 0) : w.length = n + 1 := by
  by_contra hl
  refine hp (hom_eq_zero_of_content_ne D Sc (fun h => hl ?_) p)
  have := congrArg Multiset.card h
  simpa [s.2] using this.symm

/-- The old cyclotomic ideal of morphisms lies in the cyclotomic ideal of `Hn (n+1)`. -/
theorem single_mem_cyclotomicIdeal (u t : Word I (n + 1))
    {y : wordObj D Sc t ⟶ wordObj D Sc u} (hy : y ∈ cycHom D Sc a t.1 u.1) :
    FiniteHomMatrix.single u t y ∈ cyclotomicIdeal D Sc a n := by
  induction hy using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨j, w, p, q, rfl⟩ := hf
    by_cases hp : p = 0
    · rw [hp, Limits.zero_comp, FiniteHomMatrix.single_zero]
      exact Submodule.zero_mem _
    let w' : Word I (n + 1) := ⟨j :: w, length_eq_of_hom_ne_zero D Sc n hp⟩
    have e : FiniteHomMatrix.single u t (p ≫ firstDotPoly D Sc a j w ≫ q) =
        FiniteHomMatrix.single u w' (q : wordObj D Sc w' ⟶ wordObj D Sc u) *
          (cyclotomicGenerator D Sc a w' *
            FiniteHomMatrix.single w' t (p : wordObj D Sc t ⟶ wordObj D Sc w')) := by
      rw [cyclotomicGenerator, FiniteHomMatrix.single_mul_single,
        FiniteHomMatrix.single_mul_single, Category.assoc]
      rfl
    rw [e]
    exact Ideal.mul_mem_left _ _ (Submodule.subset_span ⟨w', _, rfl⟩)
  | zero => rw [FiniteHomMatrix.single_zero]; exact Submodule.zero_mem _
  | add f g _ _ hf hg => rw [FiniteHomMatrix.single_add]; exact Submodule.add_mem _ hf hg
  | smul c f _ hf =>
    rw [FiniteHomMatrix.single_smul, Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ hf

end Matrix

section Descent
variable (a : I → _root_.Polynomial k) (i : I) (n : ℕ) (ε : ZMod 2)
  (N : Type w) [AddCommGroup N] [Module (Hn D Sc (n + 1)) N]

local notation "ψ" =>
  (appendAlgebra D Sc i (n + 1) : Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1))

/-- The elements `y` with `y ψ(1) = y` such that `z y ⊗ m = 0` in `Ind_ψ N` for all `z`, `m`. -/
def appendVanishing : Submodule k (Hn D Sc (n + 1 + 1)) where
  carrier := {y | ∃ hy : y * ψ 1 = y, ∀ (z : Hn D Sc (n + 1 + 1)) (m : N),
    (Ind.tmul ⟨z * y, Ind.mul_mem_of_mul_right hy z⟩ m : Ind N ψ) = 0}
  add_mem' := by
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    refine ⟨by rw [add_mul, hx, hy], fun z m => ?_⟩
    have e : (⟨z * (x + y), Ind.mul_mem_of_mul_right (by rw [add_mul, hx, hy]) z⟩ :
        InductionAlong.Corner ψ) = ⟨z * x, Ind.mul_mem_of_mul_right hx z⟩ +
          ⟨z * y, Ind.mul_mem_of_mul_right hy z⟩ := Subtype.ext (mul_add _ _ _)
    rw [e, Ind.add_tmul, hx', hy', add_zero]
  zero_mem' := ⟨zero_mul _, fun z m => by
    have e : (⟨z * 0, Ind.mul_mem_of_mul_right (zero_mul _) z⟩ : InductionAlong.Corner ψ) = 0 :=
      Subtype.ext (mul_zero _)
    rw [e, Ind.zero_tmul]⟩
  smul_mem' := by
    rintro c x ⟨hx, hx'⟩
    refine ⟨by rw [smul_mul_assoc, hx], fun z m => ?_⟩
    have e : (⟨z * (c • x), Ind.mul_mem_of_mul_right (by rw [smul_mul_assoc, hx]) z⟩ :
        InductionAlong.Corner ψ) = ⟨(c • z) * x, Ind.mul_mem_of_mul_right hx _⟩ :=
      Subtype.ext ((mul_smul_comm c z x).trans (smul_mul_assoc c z x).symm)
    rw [e, hx']

variable {a i n ε N}

theorem mul_append_mem_appendVanishing {r : Word I (n + 1 + 1)} (c' : Word I (n + 1))
    (f : wordObj D Sc (appendWord i c') ⟶ wordObj D Sc r) {c : Hn D Sc (n + 1)}
    (hc : ∀ m : N, c • m = 0) :
    FiniteHomMatrix.single r (appendWord i c') f * ψ c ∈ appendVanishing D Sc i n N := by
  have hX := single_mul_appendOne D Sc i n c' f
  refine ⟨by rw [mul_assoc, ← map_mul, mul_one], fun z m => ?_⟩
  exact Ind.tmul_mul_eq_zero hX hc z _ m

/-- The killed part maps into the vanishing elements. -/
theorem single_appendKill_mem (hcyc : ∀ r ∈ cyclotomicIdeal D Sc a n, ∀ m : N, r • m = 0)
    (s t : Word I (n + 1))
    {h : wordObj D Sc (appendWord i t) ⟶ wordObj D Sc (prependWord i s)}
    (hh : h ∈ appendKill D Sc a i t.1 s.1) :
    FiniteHomMatrix.single (prependWord i s) (appendWord i t) h ∈
      appendVanishing D Sc i n N := by
  induction hh using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨u, y, h', hy, rfl⟩ := hf
    by_cases hy0 : y = 0
    · rw [hy0, MonoidalSupercategory.zero_whiskerRight (R := k), Limits.zero_comp,
        FiniteHomMatrix.single_zero]
      exact Submodule.zero_mem _
    let u' : Word I (n + 1) := ⟨u, length_eq_of_hom_ne_zero D Sc n hy0⟩
    have e : FiniteHomMatrix.single (prependWord i s) (appendWord i t)
          ((y ▷ (pres D Sc).obj (ob D [i])) ≫ h') =
        FiniteHomMatrix.single (prependWord i s) (appendWord i u')
            (h' : wordObj D Sc (appendWord i u') ⟶ wordObj D Sc (prependWord i s)) *
          ψ (FiniteHomMatrix.single u' t (y : wordObj D Sc t ⟶ wordObj D Sc u')) := by
      rw [appendAlgebra_single, FiniteHomMatrix.single_mul_single]
      rfl
    rw [e]
    exact mul_append_mem_appendVanishing D Sc u' _
      (hcyc _ (single_mem_cyclotomicIdeal D Sc a n u' t hy))
  | zero => rw [FiniteHomMatrix.single_zero]; exact Submodule.zero_mem _
  | add f g _ _ hf hg => rw [FiniteHomMatrix.single_add]; exact Submodule.add_mem _ hf hg
  | smul c f _ hf => rw [FiniteHomMatrix.single_smul]; exact Submodule.smul_mem _ c hf

/-- **Matrix form (2)** of `AppendMackeySource.md` §4: `W ψ(c) - φ_ε(c) W` vanishes in
`Ind_ψ N`, for `N` killed by the cyclotomic ideal and by the idempotents of the words `t` with
`q_t ≠ ε`. -/
theorem appendMove_balance_mem (ha : CyclotomicPolynomialParity D a)
    (hcyc : ∀ r ∈ cyclotomicIdeal D Sc a n, ∀ m : N, r • m = 0)
    (hpar : ∀ t : Word I (n + 1), appendQ D a i t.1 ≠ ε →
      ∀ m : N, FiniteHomMatrix.single t t (𝟙 (wordObj D Sc t)) • m = 0)
    (c : Hn D Sc (n + 1)) :
    appendMoveMatrix D Sc a i n * ψ c - prependTwist D Sc i n ε c * appendMoveMatrix D Sc a i n ∈
      appendVanishing D Sc i n N := by
  induction c using FiniteHomMatrix.induction with
  | hz => rw [map_zero, map_zero, mul_zero, zero_mul, sub_zero]; exact Submodule.zero_mem _
  | ha c c' hc hc' =>
    rw [map_add, map_add, mul_add, add_mul, add_sub_add_comm]
    exact Submodule.add_mem _ hc hc'
  | hs s t g =>
    rw [appendMoveMatrix_mul_append, prependTwist_mul_appendMoveMatrix,
      ← matrix_single_sub]
    by_cases hq : appendQ D a i t.1 = ε
    · subst hq
      exact single_appendKill_mem D Sc hcyc s t (appendError_mem_appendKill D Sc ha g)
    · have e : ∀ f : wordObj D Sc (appendWord i t) ⟶ wordObj D Sc (prependWord i s),
          FiniteHomMatrix.single (prependWord i s) (appendWord i t) f =
            FiniteHomMatrix.single (prependWord i s) (appendWord i t) f *
              ψ (FiniteHomMatrix.single t t (𝟙 (wordObj D Sc t))) := fun f => by
        rw [appendAlgebra_single, FiniteHomMatrix.single_mul_single, appendHom_id,
          Category.id_comp]
      rw [e]
      exact mul_append_mem_appendVanishing D Sc t _ (hpar t hq)

/-- **The append Mackey map** `P : Ind_(φ_ε) N → Ind_ψ N`, `z ⊗ m ↦ z W ⊗ m`
(`AppendMackeySource.md` §4). -/
def appendMackeyMap (ha : CyclotomicPolynomialParity D a)
    (hcyc : ∀ r ∈ cyclotomicIdeal D Sc a n, ∀ m : N, r • m = 0)
    (hpar : ∀ t : Word I (n + 1), appendQ D a i t.1 ≠ ε →
      ∀ m : N, FiniteHomMatrix.single t t (𝟙 (wordObj D Sc t)) • m = 0) :
    Ind N (prependTwist D Sc i n ε) →ₗ[Hn D Sc (n + 1 + 1)] Ind N ψ :=
  Ind.descend (appendMoveMatrix_mul_appendOne D Sc a i n) fun z c m => by
    obtain ⟨_, hv⟩ := appendMove_balance_mem D Sc (N := N) ha hcyc hpar c
    have h0 := hv z.1 m
    rw [← Ind.op_smul_tmul]
    have e : (⟨z.1 * (appendMoveMatrix D Sc a i n * ψ c -
          prependTwist D Sc i n ε c * appendMoveMatrix D Sc a i n),
          Ind.mul_mem_of_mul_right ‹_› _⟩ : InductionAlong.Corner ψ) =
        MulOpposite.op c • ⟨z.1 * appendMoveMatrix D Sc a i n,
          Ind.mul_mem_of_mul_right (appendMoveMatrix_mul_appendOne D Sc a i n) _⟩ -
        ⟨z.1 * prependTwist D Sc i n ε c * appendMoveMatrix D Sc a i n,
          Ind.mul_mem_of_mul_right (appendMoveMatrix_mul_appendOne D Sc a i n) _⟩ :=
      Subtype.ext (by
        rw [Submodule.coe_sub, InductionAlong.op_smul_val]
        noncomm_ring)
    rw [e, sub_eq_add_neg, Ind.add_tmul, Ind.neg_tmul, add_neg_eq_zero] at h0
    exact h0.symm

@[simp] theorem appendMackeyMap_tmul (ha : CyclotomicPolynomialParity D a)
    (hcyc : ∀ r ∈ cyclotomicIdeal D Sc a n, ∀ m : N, r • m = 0)
    (hpar : ∀ t : Word I (n + 1), appendQ D a i t.1 ≠ ε →
      ∀ m : N, FiniteHomMatrix.single t t (𝟙 (wordObj D Sc t)) • m = 0)
    (z : InductionAlong.Corner (prependTwist D Sc i n ε)) (m : N) :
    appendMackeyMap D Sc ha hcyc hpar (Ind.tmul z m) =
      Ind.tmul ⟨z.1 * appendMoveMatrix D Sc a i n,
        Ind.mul_mem_of_mul_right (appendMoveMatrix_mul_appendOne D Sc a i n) _⟩ m := rfl

end Descent

end OddMath.QuiverHecke
