/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.AppendMackeyMap
import OddMath.QuiverHecke.CyclotomicAction.AppendTensorRightDot
import OddMath.QuiverHecke.CyclotomicAction.IntertwinerTargetDot
import OddMath.QuiverHecke.CyclotomicAction.PrependMatrix

/-!
# The source right dot of the append Mackey boundary

For the append Mackey map `P : z ⊗ m ↦ z W ⊗ m` (`AppendMackeyMap.lean`), the source right dot
is `ρ(z ⊗ m) = z X₁ ⊗ θ m`, where `X₁` is the diagonal first dot of the prepend corner and
`θ` is the parity-twisted right action of the target. This file proves the first obligation of
the source side of `MackeyCosets` (`DeformedMackeyBoundary.md` §1; Kang–Kashiwara–Oh,
arXiv:1206.5933v2, proof of Lemma 8.1, mirror form):

  `P (ρ t) = c • R_t (P t)`,   `c = (-1)^(ε + N p(i))`,

with `R_t = appendTensorRightDot θ` (`z ⊗ y ↦ z x_last ⊗ θ y`).

The local input is the last-dot slide through `W_ν = T_ν ≫ f_i(x₁)`:

  `x_last ≫ W_ν - (-1)^(p(i) p(ν)) W_ν ≫ x₁ ∈ Kill(ν, ν)`,

proved by peeling the last letter of `ν` (`W_(ν++[x]) = σ ≫ (W_ν ▷ x)`). The dot slide (1.8)
through `σ` gives the sign `(-1)^(p(x) p(i))` and, for `x = i`, the term `W_ν ▷ i`, which is in
the killed part. On the words acting nontrivially (`q_t = ε`, i.e. `p(i) p(t) = ε + N p(i)`)
the sign is the constant `c`.

## Main results

* `lastDot_comp_appendW_mem`: the last-dot slide through `W_ν` modulo `Kill`;
* `affineFirstDot_mul_appendMoveMatrix_sub_mem`: `c X₁ W - W X_last` vanishes in `Ind_ψ N`;
* `appendSourceDot`: the source right dot `ρ` on `Ind_(φ_ε) N`;
* `appendMackeyMap_appendSourceDot`: `P ∘ ρ = c • R_t ∘ P`.
-/

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams MonoidalCategory Categorification Categorification.InductionAlong
open SKM (zsign)
open scoped Classical
universe u v w
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k)

set_option quotPrecheck false in
local notation "O[" l "]" => (pres D Sc).obj (ob D l)

section Slide
variable {a : I → _root_.Polynomial k} {i : I}

/-- The dot on the last strand slides down through the last crossing (distinct colours). -/
theorem lastDotE_comp_crossLast_ne (ν : List I) {x : I} (hx : x ≠ i) :
    dotE D Sc (ν ++ [x] ++ [i]) (ν.length + 1) ≫ crossLast D Sc ν x i =
      zsign k (D.parity x * D.parity i) •
        (crossLast D Sc ν x i ≫ dotE D Sc (ν ++ [i] ++ [x]) ν.length) := by
  rw [dotE_eq, dotE_eq, crossLast, cl_comp, cl_comp]
  refine eq_zsign_smul_symm ?_
  exact (IntertwinerMeet.slide_right_ne_gen D Sc ν [] x i hx rfl (by simp) (by simp) _ _)

/-- The dot slide (1.8), right form, for equal colours on any word `l ++ [j, j] ++ r`. -/
theorem slide_right_eq_gen {t : List I} (l r : List I) (j : I) {p : ℕ} (hp : l.length = p)
    (ht : t = l ++ [j, j] ++ r) (h₁ : SChain t (pl t [.cross p, .dot p]) t)
    (h₂ : SChain t (pl t [.dot (p + 1), .cross p]) t) :
    cl D Sc t t [.cross p, .dot p] h₁ =
      zsign k (D.parity j * D.parity j) • cl D Sc t t [.dot (p + 1), .cross p] h₂ +
        cl D Sc t t [] rfl := by
  subst hp ht
  exact slide_right_eq D Sc l r j h₁ h₂

theorem crossLast_comp_dotE_self (ν : List I) :
    crossLast D Sc ν i i ≫ dotE D Sc (ν ++ [i] ++ [i]) ν.length =
      zsign k (D.parity i * D.parity i) •
        (dotE D Sc (ν ++ [i] ++ [i]) (ν.length + 1) ≫ crossLast D Sc ν i i) + 𝟙 _ := by
  rw [dotE_eq, dotE_eq, crossLast, cl_comp, cl_comp, ← cl_nil D Sc (ν ++ [i] ++ [i]) rfl]
  exact slide_right_eq_gen D Sc ν [] i rfl (by simp) _ _

theorem zsign_smul_zsign_smul {M : Type*} [AddCommGroup M] [Module k M] (q : ZMod 2) (m : M) :
    zsign k q • zsign k q • m = m := by
  rw [smul_smul, ← zsign_add_eq, CharTwo.add_self_eq_zero]
  simp [zsign]

/-- The dot on the last strand slides down through the last crossing (equal colours). -/
theorem lastDotE_comp_crossLast_self (ν : List I) :
    dotE D Sc (ν ++ [i] ++ [i]) (ν.length + 1) ≫ crossLast D Sc ν i i =
      zsign k (D.parity i * D.parity i) •
        (crossLast D Sc ν i i ≫ dotE D Sc (ν ++ [i] ++ [i]) ν.length) -
      zsign k (D.parity i * D.parity i) • 𝟙 _ := by
  rw [crossLast_comp_dotE_self, smul_add, zsign_smul_zsign_smul, add_sub_cancel_right]

end Slide

section LastDot
variable {a : I → _root_.Polynomial k} {i : I}

theorem zsign_lastDot_append (ν : List I) (x : I) :
    zsign k (D.parity i * wordSumParity D (ν ++ [x])) =
      zsign k (D.parity x * D.parity i) * zsign k (D.parity i * wordSumParity D ν) := by
  rw [← zsign_add_eq]
  congr 1
  simp only [wordSumParity, List.map_append, List.map_cons, List.map_nil, List.sum_append,
    List.sum_cons, List.sum_nil]
  ring

end LastDot

/-! ## Matrix form -/

section Matrix
variable [Fintype I] (a : I → _root_.Polynomial k) (i : I) (n : ℕ)

local notation "ψ" =>
  (appendAlgebra D Sc i (n + 1) : Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1))

omit [Fintype I] in
theorem homMatrixTwist_comm (p q : ZMod 2) (z : Hn D Sc n) :
    homMatrixTwist D Sc n p (homMatrixTwist D Sc n q z) =
      homMatrixTwist D Sc n q (homMatrixTwist D Sc n p z) := by
  induction z using FiniteHomMatrix.induction with
  | hz => simp
  | ha a b ha hb => simp [ha, hb]
  | hs s t f => simp [← Supercategory.twist_add, add_comm]

theorem prependTwist_apply (ε : ZMod 2) (r : Hn D Sc (n + 1)) :
    prependTwist D Sc i n ε r = prependAlgebra D Sc i (n + 1) (homMatrixTwist D Sc (n + 1) ε r) :=
  rfl

theorem prependTwist_one (ε : ZMod 2) :
    prependTwist D Sc i n ε 1 = prependAlgebra D Sc i (n + 1) 1 := by
  rw [prependTwist_apply, homMatrixTwist_one]

theorem affineFirstDot_mul_prependTwist_one (ε : ZMod 2) :
    affineFirstDot D Sc i (n + 1) * prependTwist D Sc i n ε 1 = affineFirstDot D Sc i (n + 1) := by
  rw [prependTwist_one, affineFirstDot_mul_prepend_one]

/-- The first dot intertwines `φ_ε` with its parity twist. -/
theorem prependTwist_mul_affineFirstDot (ε : ZMod 2) (r : Hn D Sc (n + 1)) :
    prependTwist D Sc i n ε r * affineFirstDot D Sc i (n + 1) =
      affineFirstDot D Sc i (n + 1) *
        prependTwist D Sc i n ε (homMatrixTwist D Sc (n + 1) (D.parity i) r) := by
  rw [prependTwist_apply, prependTwist_apply, affineFirstDot_twist_comm, homMatrixTwist_comm]

/-- The constant sign `(-1)^(ε + N p(i))` of the last-dot slide on words with `q_t = ε`. -/
def appendSourceSign (ε : ZMod 2) : ZMod 2 := ε - (a i).natDegree • D.parity i

end Matrix

section Vanishing
variable [Fintype I] {a : I → _root_.Polynomial k} {i : I} {n : ℕ} {ε : ZMod 2}
  {N : Type w} [AddCommGroup N] [Module (Hn D Sc (n + 1)) N]

local notation "ψ" =>
  (appendAlgebra D Sc i (n + 1) : Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1))

end Vanishing

/-! ## The source right dot on the induced module -/

section Source
variable [Fintype I] (i : I) (n : ℕ) (ε : ZMod 2)

/-- Right multiplication by the first dot on the corner of `φ_ε`. -/
def sourceDotCorner :
    InductionAlong.Corner (prependTwist D Sc i n ε) →ₗ[Hn D Sc (n + 1 + 1)] InductionAlong.Corner (prependTwist D Sc i n ε) where
  toFun z := ⟨z.1 * affineFirstDot D Sc i (n + 1), by
    change (z.1 * affineFirstDot D Sc i (n + 1)) * prependTwist D Sc i n ε 1 = _
    rw [mul_assoc, affineFirstDot_mul_prependTwist_one]⟩
  map_add' z z' := Subtype.ext (add_mul _ _ _)
  map_smul' r z := Subtype.ext (mul_assoc _ _ _)

@[simp] theorem sourceDotCorner_val (z : InductionAlong.Corner (prependTwist D Sc i n ε)) :
    (sourceDotCorner D Sc i n ε z).1 = z.1 * affineFirstDot D Sc i (n + 1) := rfl

theorem sourceDotCorner_op_smul (z : InductionAlong.Corner (prependTwist D Sc i n ε)) (r : Hn D Sc (n + 1)) :
    sourceDotCorner D Sc i n ε (MulOpposite.op r • z) =
      MulOpposite.op (homMatrixTwist D Sc (n + 1) (D.parity i) r) •
        sourceDotCorner D Sc i n ε z := by
  apply Subtype.ext
  change (z.1 * prependTwist D Sc i n ε r) * affineFirstDot D Sc i (n + 1) = _
  rw [mul_assoc, prependTwist_mul_affineFirstDot, ← mul_assoc]
  rfl

variable {N : Type w} [AddCommGroup N] [Module (Hn D Sc (n + 1)) N] (θ : N →+ N)
  (hθ : ∀ (r : Hn D Sc (n + 1)) (y : N),
    θ (r • y) = homMatrixTwist D Sc (n + 1) (D.parity i) r • θ y)

/-- **The source right dot** `ρ : z ⊗ y ↦ z X₁ ⊗ θ y` on `Ind_(φ_ε) N`. -/
def appendSourceDot : Module.End (Hn D Sc (n + 1 + 1)) (Ind N (prependTwist D Sc i n ε)) :=
  Ind.lift (fun z y => Ind.tmul (sourceDotCorner D Sc i n ε z) (θ y))
    (by intros; rw [map_add, Ind.add_tmul])
    (by intros; rw [map_add, Ind.tmul_add])
    (by intros; rw [sourceDotCorner_op_smul, Ind.op_smul_tmul, hθ])
    (by intros; rw [map_smul, Ind.smul_tmul])

@[simp] theorem appendSourceDot_tmul (z : InductionAlong.Corner (prependTwist D Sc i n ε)) (y : N) :
    appendSourceDot D Sc i n ε θ hθ (Ind.tmul z y) =
      Ind.tmul (sourceDotCorner D Sc i n ε z) (θ y) := rfl

end Source

end OddMath.QuiverHecke
