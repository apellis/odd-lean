import OddMath.QuiverHecke.CyclotomicAction.AppendBalance.AppendMackeyMap
import OddMath.QuiverHecke.CyclotomicAction.AppendMackey.AppendLeftCrossing
import OddMath.QuiverHecke.CyclotomicAction.IntertwinerRight.IntertwinerRightCoefficient
import OddMath.QuiverHecke.CyclotomicAction.PrependCoordinates
import OddMath.QuiverHecke.CyclotomicAction.BoundaryDivision
import OddMath.QuiverHecke.CyclotomicAction.SuperQuotient

/-!
# Append mackey

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-!
# The twisted right dot on append-induced modules

The new dot `x_(n+2)` only supercommutes with the append map: `ψ(r) x = x ψ(tw r)`
(`affineLastDot_twist_comm`). Right multiplication by it therefore descends to the induced
module `Ind M = Hn (n+2) ψ(1) ⊗_(Hn (n+1)) M` only after twisting the coefficients. We encode
the twist by an additive map `θ : M → M` with

`θ (r • y) = tw(r) • θ y`,

where `tw` is the parity twist `homMatrixTwist (n+1) (D.parity i)`. For the regular
supermodule of the cyclotomic quotient this is the parity involution `rightDotCoefficient`
(`rightDotCoefficient_smul`).

Main results: the twisted right dot `appendTensorRightDot θ` (`z ⊗ y ↦ z x ⊗ θ y`), its action
on the two summands of `appendTensorCornerEquiv`,

* `R_t(Σ z^m ⊗ g_m) = Σ z^(m+1) ⊗ θ g_m`,
* `R_t(Σ ψ(c'_j x^m) τ ⊗ f_(j,m)) = s Σ ψ(c'_j x^(m+1)) τ ⊗ θ f_(j,m) - s (1 ⊗ Σ c'_j x^m ψ'(1) θ f_(j,m))`,

with `s = koszulSign (D.parity i) (D.parity i)`, and the stability of the `ψ(1)`-fixed part and
of the left-crossing coordinates. These are the module forms of `appendPolySum_mul_lastDot`
and `appendLeftSum_mul_lastDot` (the identities `R_t j = j t` and `R_t F = F X + j E` of
`DeformedMackeyBoundary.md`, append side; Kang–Kashiwara–Oh, arXiv:1206.5933v2, proof of
Lemma 8.1, mirror form).
-/

noncomputable section
open StringDiagrams Categorification MulOpposite
namespace OddMath.QuiverHecke
universe u v w
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
variable (i : I) (n : ℕ) (M : Type w) [AddCommGroup M] [Module (Hn D Sc (n + 1)) M]
local notation "ψ" =>
  (appendAlgebra D Sc i (n + 1) : Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1))
local notation "C" => InductionAlong.Corner ψ
local notation "T" => InductionAlong.Ind M ψ

/-- Elementary tensors as an additive map in the corner variable. -/
def appendTensorCornerHom (y : M) : C →+ T :=
  AddMonoidHom.mk' (fun z => InductionAlong.Ind.tmul z y)
    (fun z z' => InductionAlong.Ind.add_tmul z z' y)

variable (θ : M →+ M)
  (hθ : ∀ (r : Hn D Sc (n + 1)) (y : M),
    θ (r • y) = homMatrixTwist D Sc (n + 1) (D.parity i) r • θ y)

/-- The twisted right dot `z ⊗ y ↦ z x_(n+2) ⊗ θ y` on the induced module. -/
def appendTensorRightDot : Module.End (Hn D Sc (n + 1 + 1)) T :=
  InductionAlong.Ind.lift
    (fun z y => InductionAlong.Ind.tmul (rightDotCorner D Sc i (n + 1) z) (θ y))
    (by intros; rw [map_add, InductionAlong.Ind.add_tmul])
    (by intros; rw [map_add, InductionAlong.Ind.tmul_add])
    (by intros; rw [rightDotCorner_op_smul, InductionAlong.Ind.op_smul_tmul, hθ])
    (by intros; rw [map_smul, InductionAlong.Ind.smul_tmul])

@[simp] theorem appendTensorRightDot_tmul (z : C) (y : M) :
    appendTensorRightDot D Sc i n M θ hθ (InductionAlong.Ind.tmul z y) =
      InductionAlong.Ind.tmul (rightDotCorner D Sc i (n + 1) z) (θ y) := rfl

/-- The twisted right dot preserves the `ψ(1)`-fixed part. -/
theorem appendTensorRightDot_mem_fixed (t : T) (ht : t ∈ appendTensorFixed D Sc i n M) :
    appendTensorRightDot D Sc i n M θ hθ t ∈ appendTensorFixed D Sc i n M := by
  change (appendAlgebra D Sc i (n + 1) 1 : Hn D Sc (n + 1 + 1)) • _ = _
  rw [← LinearMap.map_smul]
  exact congrArg _ ht

/-! ## Coordinate maps -/

/-! ## The slides -/

end OddMath.QuiverHecke
end

end

section

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
end

end

section

/-!
# The target side of the append-side Mackey boundary

`MackeyCosets` (`BoundaryCosets.lean`) bundles claims about the target `L₀` (its decomposition
`L₀ = F(L₀') ⊕ j(V₀)`, the dot slides and the right `B`-action) with claims about the source
`L₁` and the map `P`. `MackeyTarget` records the target-side fields alone, and
`MackeyCosets.ofTarget` assembles a `MackeyCosets` from them and the source-side data.

For a ring `B` that is a left `Hn (n+1)`-module with `(r • y) b = r • (y b)`, and a ring
endomorphism `σ` of `B` with `σ (r • y) = tw(r) • σ y` (`tw` the parity twist of the appended
colour), `appendMackeyTarget` instantiates every target-side field on

* `L₀ = ψ(1) (Hn (n+2) ψ(1) ⊗_(Hn (n+1)) B)` (`appendTensorFixed`),
* `L₀' = ⊕_(j ≤ n, m) ψ'(1) B` (`appendTensorLeftCoordinates`),

with `F`, `j` the two summands of `appendTensorCornerEquiv` (so `direct` and `span` are that
equivalence), `R_t` the `σ`-twisted right dot `appendTensorRightDot`, and the right `B`-action
`z ⊗ y ↦ z ⊗ y b`. This is the target of `DeformedMackeyBoundary.md` (append side,
`AppendCoordinates.md` §4; Kang–Kashiwara–Oh, arXiv:1206.5933v2, proof of Lemma 8.1, mirror
form).
-/

noncomputable section
open Finsupp Categorification StringDiagrams

namespace OddMath.QuiverHecke.CyclotomicAction.BoundaryPolynomial

variable {B : Type*} [Ring B] (σ : B →+* B)

/-- The target-side fields of `MackeyCosets`. -/
structure MackeyTarget (L₀ L₀' : Type*) [AddCommGroup L₀] [AddCommGroup L₀'] where
  /-- The target right-dot action `R_t`. -/
  Rt : L₀ →+ L₀
  /-- The crossing summand `F : L₀' → L₀`. -/
  F : L₀' →+ L₀
  /-- The polynomial summand. -/
  j : (ℕ →₀ B) →+ L₀
  /-- The crossing-contraction operator `X` on `L₀'`. -/
  X : L₀' →+ L₀'
  /-- The degree-zero operator `E : L₀' → B`. -/
  E : L₀' →+ B
  /-- The right `B`-action on the target. -/
  r₀ : B → L₀ →+ L₀
  Rt_F : ∀ u, Rt (F u) = F (X u) + j (single 0 (E u))
  Rt_j : ∀ f, Rt (j f) = j (tShift σ f)
  direct : ∀ u f, F u + j f = 0 → u = 0 ∧ f = 0
  span : ∀ y, ∃ u f, y = F u + j f
  F_r : ∀ (b : B) u, ∃ u', r₀ b (F u) = F u'
  j_r : ∀ (b : B) f, r₀ b (j f) = j (rsmul b f)

end OddMath.QuiverHecke.CyclotomicAction.BoundaryPolynomial

namespace OddMath.QuiverHecke
open CyclotomicAction.BoundaryPolynomial
universe u v w
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
variable (i : I) (n : ℕ) (B : Type w) [Ring B] [Module (Hn D Sc (n + 1)) B]
local notation "ψ" =>
  (appendAlgebra D Sc i (n + 1) : Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1))
local notation "T" => InductionAlong.Ind B ψ

/-! ## The two summands -/

/-- The crossing summand `F u = Σ ψ(c'_j x^m) τ ⊗ u_(j,m)`. -/
def appendTargetF : appendTensorLeftCoordinates D Sc i n B →+ appendTensorFixed D Sc i n B :=
  (appendTensorCornerEquiv D Sc i n B).toAddMonoidHom.comp (AddMonoidHom.inl _ _)

/-- The polynomial summand `j g = Σ z^m ⊗ g_m`. -/
def appendTargetJ : (ℕ →₀ B) →+ appendTensorFixed D Sc i n B :=
  (appendTensorCornerEquiv D Sc i n B).toAddMonoidHom.comp (AddMonoidHom.inr _ _)

@[simp] theorem appendTargetF_coe (u : appendTensorLeftCoordinates D Sc i n B) :
    (appendTargetF D Sc i n B u : T) = appendLeftTensor D Sc i n B u.1 := by
  simp [appendTargetF, appendTensorCornerEquiv_apply]

@[simp] theorem appendTargetJ_coe (f : ℕ →₀ B) :
    (appendTargetJ D Sc i n B f : T) = appendPolyTensor D Sc i n B f := by
  simp [appendTargetJ, appendTensorCornerEquiv_apply]

/-! ## The twisted right dot -/

variable (σ : B →+* B)
  (hσ : ∀ (r : Hn D Sc (n + 1)) (y : B),
    σ (r • y) = homMatrixTwist D Sc (n + 1) (D.parity i) r • σ y)

/-- The `σ`-twisted right dot on the `ψ(1)`-fixed part. -/
def appendTargetRt : appendTensorFixed D Sc i n B →+ appendTensorFixed D Sc i n B :=
  AddMonoidHom.codRestrict
    ((appendTensorRightDot D Sc i n B σ.toAddMonoidHom hσ).toAddMonoidHom.comp
      (appendTensorFixed D Sc i n B).subtype)
    _ fun t => appendTensorRightDot_mem_fixed D Sc i n B _ hσ t.1 t.2

@[simp] theorem appendTargetRt_coe (t : appendTensorFixed D Sc i n B) :
    (appendTargetRt D Sc i n B σ hσ t : T) =
      appendTensorRightDot D Sc i n B σ.toAddMonoidHom hσ t.1 := rfl

/-! ## Right multiplication on the coefficients -/

variable [IsScalarTower (Hn D Sc (n + 1)) B B]

end OddMath.QuiverHecke
end

end

section

/-!
# The append Mackey target on the content corner of the cyclotomic quotient

Let `A = Hn (n+1) / I^Λ` be the cyclotomic quotient (`CyclotomicAlgebra`) and
`e = e(β)` the content idempotent of a multiset `β` (`cyclotomicContentIdempotent`), which is
central and even. The coefficient ring of the append-side Mackey boundary
(`DeformedMackeyBoundary.md`, append side; Kang–Kashiwara–Oh, arXiv:1206.5933v2, proof of
Lemma 8.1) is the corner `B_β = e A e` (`CyclotomicContentCorner`), a ring with unit `e`:

* `B_β` is a left `Hn (n+1)`-module through `A`, with `(r • y) b = r • (y b)`;
* the parity involution `φ_i = coefficientParityHom (D.parity i)` fixes `e` and restricts to a
  ring endomorphism `σ_β` of `B_β` (`contentCornerParity`) with
  `σ_β (r • y) = tw(r) • σ_β y` (`contentCornerParity_smul`), where `tw` is the parity twist of
  the appended colour; the identity `φ_i = rightDotCoefficient i`
  (`coefficientParityHom_parity_eq_rightDotCoefficient`) brings in `rightDotCoefficient_smul`.

`appendContentMackeyTarget` is then `appendMackeyTarget` at `B_β`, `σ_β`: the target side of
`MackeyCosets` on `L₀ = ψ(1) (Hn (n+2) ψ(1) ⊗_(Hn (n+1)) B_β)`, with `direct` and `span` the
decomposition `L₀ = F(L₀') ⊕ j(V₀)` of `appendTensorCornerEquiv`.
-/

noncomputable section
open StringDiagrams Categorification Supercategory

namespace OddMath.QuiverHecke

universe u v

variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
  (a : I → _root_.Polynomial k) (n : ℕ) (β : Multiset I)

theorem cyclotomicContentIdempotent_isIdempotentElem :
    IsIdempotentElem (cyclotomicContentIdempotent D Sc a n β) :=
  cyclotomicContentIdempotent_sq D Sc a n β

/-- The content-`β` corner `e(β) A e(β)` of the cyclotomic quotient `A`, a ring with unit
`e(β)`. -/
abbrev CyclotomicContentCorner :=
  (cyclotomicContentIdempotent_isIdempotentElem D Sc a n β).Corner

theorem cyclotomicContentCorner_mem_iff (x : CyclotomicAlgebra D Sc a n) :
    x ∈ Subsemigroup.corner (cyclotomicContentIdempotent D Sc a n β) ↔
      cyclotomicContentIdempotent D Sc a n β * x = x :=
  (Subsemigroup.mem_corner_iff (cyclotomicContentIdempotent_isIdempotentElem D Sc a n β)).trans
    ⟨fun h => h.1, fun h => ⟨h, by rw [← cyclotomicContentIdempotent_central, h]⟩⟩

/-- The underlying element of the quotient. -/
def contentCornerVal (x : CyclotomicContentCorner D Sc a n β) : CyclotomicAlgebra D Sc a n :=
  (show Subsemigroup.corner (cyclotomicContentIdempotent D Sc a n β) from x).1

theorem contentCornerVal_mem (x : CyclotomicContentCorner D Sc a n β) :
    contentCornerVal D Sc a n β x ∈ Subsemigroup.corner (cyclotomicContentIdempotent D Sc a n β) :=
  (show Subsemigroup.corner (cyclotomicContentIdempotent D Sc a n β) from x).2

/-- The corner element of an element of the corner subsemigroup. -/
def contentCornerMk (y : CyclotomicAlgebra D Sc a n)
    (hy : y ∈ Subsemigroup.corner (cyclotomicContentIdempotent D Sc a n β)) :
    CyclotomicContentCorner D Sc a n β :=
  show Subsemigroup.corner (cyclotomicContentIdempotent D Sc a n β) from ⟨y, hy⟩

@[simp] theorem contentCornerVal_mk (y : CyclotomicAlgebra D Sc a n)
    (hy : y ∈ Subsemigroup.corner (cyclotomicContentIdempotent D Sc a n β)) :
    contentCornerVal D Sc a n β (contentCornerMk D Sc a n β y hy) = y := rfl

theorem contentCornerVal_injective : Function.Injective (contentCornerVal D Sc a n β) :=
  fun x y h => (Subtype.ext h :
    (show Subsemigroup.corner (cyclotomicContentIdempotent D Sc a n β) from x) =
      show Subsemigroup.corner (cyclotomicContentIdempotent D Sc a n β) from y)

theorem contentCornerVal_e_mul (x : CyclotomicContentCorner D Sc a n β) :
    cyclotomicContentIdempotent D Sc a n β * contentCornerVal D Sc a n β x =
      contentCornerVal D Sc a n β x :=
  (cyclotomicContentCorner_mem_iff D Sc a n β _).mp (contentCornerVal_mem D Sc a n β x)

theorem cyclotomicContentCorner_mul_mem (z : CyclotomicAlgebra D Sc a n)
    (x : CyclotomicContentCorner D Sc a n β) :
    z * contentCornerVal D Sc a n β x ∈
      Subsemigroup.corner (cyclotomicContentIdempotent D Sc a n β) := by
  rw [cyclotomicContentCorner_mem_iff, ← mul_assoc, cyclotomicContentIdempotent_central,
    mul_assoc, contentCornerVal_e_mul]

/-- The inclusion of the corner as an additive map. -/
def contentCornerValHom :
    CyclotomicContentCorner D Sc a n β →+ CyclotomicAlgebra D Sc a n where
  toFun := contentCornerVal D Sc a n β
  map_zero' := rfl
  map_add' _ _ := rfl

instance : SMul (Hn D Sc (n + 1)) (CyclotomicContentCorner D Sc a n β) :=
  ⟨fun r x => contentCornerMk D Sc a n β (r • contentCornerVal D Sc a n β x) (by
    exact cyclotomicContentCorner_mul_mem D Sc a n β (cyclotomicMk D Sc a n r) x)⟩

instance : Module (Hn D Sc (n + 1)) (CyclotomicContentCorner D Sc a n β) :=
  Function.Injective.module _ (contentCornerValHom D Sc a n β)
    (contentCornerVal_injective D Sc a n β) fun _ _ => rfl

instance : IsScalarTower (Hn D Sc (n + 1)) (CyclotomicContentCorner D Sc a n β)
    (CyclotomicContentCorner D Sc a n β) :=
  ⟨fun r x y => contentCornerVal_injective D Sc a n β
    (smul_mul_assoc r (contentCornerVal D Sc a n β x) (contentCornerVal D Sc a n β y))⟩

variable (i : I) (ha : CyclotomicPolynomialParity D a)

/-- The parity involution fixes the (even) content idempotent. -/
theorem coefficientParityHom_contentIdempotent (p : ZMod 2) :
    coefficientParityHom D Sc a ha n p (cyclotomicContentIdempotent D Sc a n β) =
      cyclotomicContentIdempotent D Sc a n β := by
  change (cyclotomicSuperspace D Sc a ha n).sgn p _ = _
  rw [SVec.sgn_apply_of_mem p (cyclotomicContentIdempotent_parity D Sc a ha n β)]
  simp

/-- The parity involution of the appended colour, restricted to the content corner. -/
def contentCornerParity :
    CyclotomicContentCorner D Sc a n β →+* CyclotomicContentCorner D Sc a n β where
  toFun x := contentCornerMk D Sc a n β
    (coefficientParityHom D Sc a ha n (D.parity i) (contentCornerVal D Sc a n β x)) (by
      rw [cyclotomicContentCorner_mem_iff, ← coefficientParityHom_contentIdempotent D Sc a n β ha
          (D.parity i), ← map_mul, contentCornerVal_e_mul])
  map_zero' := contentCornerVal_injective D Sc a n β (map_zero _)
  map_add' x y := contentCornerVal_injective D Sc a n β (map_add _ _ _)
  map_one' := contentCornerVal_injective D Sc a n β
    (coefficientParityHom_contentIdempotent D Sc a n β ha (D.parity i))
  map_mul' x y := contentCornerVal_injective D Sc a n β (map_mul _ _ _)

end OddMath.QuiverHecke
end

end

section

/-!
# Coordinates of the twisted prepend induction

The source module of the append-side Mackey boundary is `Ind_(φ_ε) N` with
`φ_ε = prependAlgebra i (n+1) ∘ tw_ε` (`prependTwist`); the parity shift `Π^ε` of
`docs/Nondegeneracy/DeformedMackeyBoundary.md` §1 is the twist `tw_ε`. Since
`tw_ε` is an involution fixing `1`, inducing along `φ_ε` is the same as inducing
along `prependAlgebra i (n+1)` from the twisted module `N^ε` (`TwistModule`), on
which `r` acts as `tw_ε(r)`.

## Main results

* `TwistModule`: `N` with the action precomposed by the parity twist.
* `prependTwistEquiv`: `Ind_(φ_ε) N ≃+ Ind_(prependAlgebra) N^ε`, `z ⊗ m ↦ z ⊗ m`.
* `prependTwistCoordinates`: the affine prepend PBW coordinates of `Ind_(φ_ε) N`,
  `((PrependShuffle (n+1) × ℕ) →₀ N) ≃+ Ind_(φ_ε) N`, sending `single (u, l) m` to
  `prependPBWCorner u l 1 ⊗ m`.
-/

noncomputable section
open CategoryTheory Categorification Categorification.InductionAlong MulOpposite
namespace OddMath.QuiverHecke
universe u v w
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]

section Twist
variable (n : ℕ) (p : ZMod 2)

/-- The parity twist as a unital ring endomorphism. -/
def homMatrixTwistRingHom : Hn D Sc n →+* Hn D Sc n :=
  { (homMatrixTwistAlgebra D Sc n p : Hn D Sc n →ₙ+* Hn D Sc n) with
    map_one' := homMatrixTwist_one D Sc n p }

@[simp] theorem homMatrixTwistRingHom_apply (r : Hn D Sc n) :
    homMatrixTwistRingHom D Sc n p r = homMatrixTwist D Sc n p r := rfl

variable (N : Type w) [AddCommGroup N] [Module (Hn D Sc n) N]

/-- `N` with the action precomposed by the parity twist `tw_p`. -/
@[nolint unusedArguments]
def TwistModule (_ : SKM.Scalars D k) (_ : ℕ) (_ : ZMod 2) (N : Type w) : Type w := N

instance : AddCommGroup (TwistModule D Sc n p N) := inferInstanceAs (AddCommGroup N)

instance : Module (Hn D Sc n) (TwistModule D Sc n p N) :=
  Module.compHom N (homMatrixTwistRingHom D Sc n p)

/-- The identity of the underlying group. -/
def toTwistModule : N ≃+ TwistModule D Sc n p N := AddEquiv.refl N

theorem smul_toTwistModule (r : Hn D Sc n) (m : N) :
    r • toTwistModule D Sc n p N m = toTwistModule D Sc n p N (homMatrixTwist D Sc n p r • m) :=
  rfl

theorem toTwistModule_smul (r : Hn D Sc n) (m : N) :
    toTwistModule D Sc n p N (r • m) = homMatrixTwist D Sc n p r • toTwistModule D Sc n p N m := by
  rw [smul_toTwistModule, homMatrixTwist_twice]

end Twist

variable (i : I) (n : ℕ) (ε : ZMod 2) (N : Type w) [AddCommGroup N]
  [Module (Hn D Sc (n + 1)) N]

local notation "φ" => (prependAlgebra D Sc i (n + 1) : Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1))

/-- The two corners agree: `φ_ε(1) = φ(1)`. -/
def prependTwistCorner : InductionAlong.Corner (prependTwist D Sc i n ε) ≃+ InductionAlong.Corner φ where
  toFun z := ⟨z.1, by
    change z.1 * prependAlgebra D Sc i (n + 1) 1 = z.1
    have h : z.1 * prependTwist D Sc i n ε 1 = z.1 := z.2
    exact (congrArg (z.1 * ·) (prependTwist_one D Sc i n ε)).symm.trans h⟩
  invFun z := ⟨z.1, by
    change z.1 * prependTwist D Sc i n ε 1 = z.1
    have h : z.1 * prependAlgebra D Sc i (n + 1) 1 = z.1 := z.2
    exact (congrArg (z.1 * ·) (prependTwist_one D Sc i n ε)).trans h⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

@[simp] theorem prependTwistCorner_val (z : InductionAlong.Corner (prependTwist D Sc i n ε)) :
    (prependTwistCorner D Sc i n ε z).1 = z.1 := rfl

@[simp] theorem prependTwistCorner_symm_val (z : InductionAlong.Corner φ) :
    ((prependTwistCorner D Sc i n ε).symm z).1 = z.1 := rfl

theorem prependTwistCorner_op_smul (a : Hn D Sc (n + 1))
    (z : InductionAlong.Corner (prependTwist D Sc i n ε)) :
    prependTwistCorner D Sc i n ε (op a • z) =
      op (homMatrixTwist D Sc (n + 1) ε a) • prependTwistCorner D Sc i n ε z := rfl

/-- The forward map `z ⊗ m ↦ z ⊗ m` from `Ind_(φ_ε) N` to `Ind_φ N^ε`. -/
def prependTwistForward : Ind N (prependTwist D Sc i n ε) →+ Ind (TwistModule D Sc (n + 1) ε N) φ :=
  Ind.liftAdd
    (fun z m => Ind.tmul (prependTwistCorner D Sc i n ε z) (toTwistModule D Sc (n + 1) ε N m))
    (fun _ _ _ => by rw [map_add, Ind.add_tmul])
    (fun _ _ _ => by rw [map_add, Ind.tmul_add])
    (fun z a m => by
      rw [prependTwistCorner_op_smul, Ind.op_smul_tmul, toTwistModule_smul])

theorem prependTwistForward_tmul (z : InductionAlong.Corner (prependTwist D Sc i n ε)) (m : N) :
    prependTwistForward D Sc i n ε N (Ind.tmul z m) =
      Ind.tmul (prependTwistCorner D Sc i n ε z) (toTwistModule D Sc (n + 1) ε N m) := rfl

/-- The backward map `z ⊗ m ↦ z ⊗ m` from `Ind_φ N^ε` to `Ind_(φ_ε) N`. -/
def prependTwistBackward : Ind (TwistModule D Sc (n + 1) ε N) φ →+ Ind N (prependTwist D Sc i n ε) :=
  Ind.liftAdd
    (fun z m => Ind.tmul ((prependTwistCorner D Sc i n ε).symm z)
      ((toTwistModule D Sc (n + 1) ε N).symm m))
    (fun _ _ _ => by rw [map_add, Ind.add_tmul])
    (fun _ _ _ => by rw [map_add, Ind.tmul_add])
    (fun z a m => by
      have h : (prependTwistCorner D Sc i n ε).symm (op a • z) =
          op (homMatrixTwist D Sc (n + 1) ε a) • (prependTwistCorner D Sc i n ε).symm z :=
        Subtype.ext (by
          change z.1 * prependAlgebra D Sc i (n + 1) a =
            z.1 * prependAlgebra D Sc i (n + 1)
              (homMatrixTwist D Sc (n + 1) ε (homMatrixTwist D Sc (n + 1) ε a))
          rw [homMatrixTwist_twice])
      rw [h, Ind.op_smul_tmul]
      rfl)

theorem prependTwistBackward_tmul (z : InductionAlong.Corner φ)
    (m : TwistModule D Sc (n + 1) ε N) :
    prependTwistBackward D Sc i n ε N (Ind.tmul z m) =
      Ind.tmul ((prependTwistCorner D Sc i n ε).symm z) ((toTwistModule D Sc (n + 1) ε N).symm m) :=
  rfl

/-- `Ind_(φ_ε) N ≃+ Ind_φ N^ε`, `z ⊗ m ↦ z ⊗ m`. -/
def prependTwistEquiv :
    Ind N (prependTwist D Sc i n ε) ≃+ Ind (TwistModule D Sc (n + 1) ε N) φ where
  toFun := prependTwistForward D Sc i n ε N
  invFun := prependTwistBackward D Sc i n ε N
  left_inv t := by
    induction t using Ind.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul z m =>
      rw [prependTwistForward_tmul, prependTwistBackward_tmul, AddEquiv.symm_apply_apply,
        AddEquiv.symm_apply_apply]
    | add s t hs ht => rw [map_add, map_add, hs, ht]
  right_inv t := by
    induction t using Ind.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul z m =>
      rw [prependTwistBackward_tmul, prependTwistForward_tmul, AddEquiv.apply_symm_apply,
        AddEquiv.apply_symm_apply]
    | add s t hs ht => rw [map_add, map_add, hs, ht]
  map_add' := map_add _

@[simp] theorem prependTwistEquiv_tmul (z : InductionAlong.Corner (prependTwist D Sc i n ε))
    (m : N) :
    prependTwistEquiv D Sc i n ε N (Ind.tmul z m) =
      Ind.tmul (prependTwistCorner D Sc i n ε z) (toTwistModule D Sc (n + 1) ε N m) := rfl

@[simp] theorem prependTwistEquiv_symm_tmul (z : InductionAlong.Corner φ)
    (m : TwistModule D Sc (n + 1) ε N) :
    (prependTwistEquiv D Sc i n ε N).symm (Ind.tmul z m) =
      Ind.tmul ((prependTwistCorner D Sc i n ε).symm z) ((toTwistModule D Sc (n + 1) ε N).symm m) :=
  rfl

/-- The affine prepend PBW coordinates of the twisted induction. -/
def prependTwistCoordinates :
    ((PrependShuffle (n + 1) × ℕ) →₀ N) ≃+ Ind N (prependTwist D Sc i n ε) :=
  ((Finsupp.mapRange.addEquiv (toTwistModule D Sc (n + 1) ε N)).trans
    (prependTensorEquiv D Sc i (n + 1) (TwistModule D Sc (n + 1) ε N))).trans
    (prependTwistEquiv D Sc i n ε N).symm

@[simp] theorem prependTwistCoordinates_single (q : PrependShuffle (n + 1) × ℕ) (m : N) :
    prependTwistCoordinates D Sc i n ε N (Finsupp.single q m) =
      Ind.tmul ((prependTwistCorner D Sc i n ε).symm (prependPBWCorner D Sc i q.1 q.2 1)) m := by
  simp [prependTwistCoordinates, prependTensorEquiv]

end OddMath.QuiverHecke
end

end
