import OddMath.Frontier.ThickMatrixUnits
import OddMath.Frontier.CyclotomicMatrix

/-! # Categorification: the decompositions (6.1)–(6.2)

EKL arXiv:1111.1320v1, §6, (6.1)–(6.2), pp. 46–47.  `ONH_a = NilHeckeAction.Presented n`,
`a = n+2`; a product `x * y` is `x` drawn on top of `y`.  A left `ONH_a`-module map between
projective modules `ONH_a·P → ONH_a·e` is right multiplication by an element of `P·ONH_a·e`.

* `Splitting P e I`: elements `σ_i ∈ P R e`, `λ_i ∈ e R P` with `∑ σ_i λ_i = P` and
  `λ_i σ_j = δ_ij e`.  It gives the left module isomorphism `R·P ≃ ⊕_{i ∈ I} R·e`,
  `x ↦ (x σ_i)_i`, `(y_i) ↦ ∑ y_i λ_i` (`Splitting.equiv`), and the Murray–von Neumann
  equivalence `diag(P) ~ diag(e, …, e)` by the row `u = (σ_i)_i` and the column `v = (λ_i)_i`:
  `u v = P`, `v u = diag(e)` (`Splitting.row_mul_col`, `Splitting.col_mul_row`).  Here
  `R·e = {x | x e = x}` (`leftIdeal`), equal to `Submodule.span R {e}` for `e² = e`.
* (6.1) `eq_6_1`: `ONH_a ≅ ⊕_{ℓ ∈ Sq(a)} ONH_a e_a`, `x ↦ (x σ_ℓ)_ℓ`, inverse `∑ y_ℓ λ_ℓ`, from
  Lemma 4.13 and Theorem 4.15 (`ThickMatrixUnits`).  In this convention the forward map is right
  multiplication by `σ_ℓ` (the paper labels the arrow by `λ_ℓ`).
* (6.2) `eq_6_2`: `ONH_{a+b}(e_a ⊗ e_b) ≅ ⊕_{α ∈ P(a,b)} ONH_{a+b} e_{a+b}`, `x ↦ (x σ_α)_α`,
  from (4.54) and Theorem 4.16, with `e_a ⊗ e_b = blockE n 0 a * blockE n a b`.
* Gradings (`ProjectorRank.Vd`, a dot of degree `1`; `Vd N d = polynomialPiece N (2d)`, the
  paper's degree is twice ours): the `ℓ`-component of (6.1) raises degree by
  `deg σ_ℓ = |ℓ| - C(a,2)`, the `α`-component of (6.2) by `deg σ_α = |α| - ab`.  With the
  normalizations `E^{(a)} = ONH_a e_a {-C(a,2)}` and `E^{(a)}E^{(b)} = ONH_{a+b}(e_a ⊗ e_b)
  {-C(a,2)-C(b,2)}`, `C(a+b,2) = C(a,2) + C(b,2) + ab`, the paper exponents are
  `2 deg σ_ℓ + C(a,2) = 2|ℓ| - C(a,2)` and `2 deg σ_α + ab = 2|α| - ab`, up to the global sign
  of the shift convention (both multisets are symmetric under `ℓ ↦ ℓ̂`, `α ↦ α̂`).  The second is
  the printed exponent of (6.2); the printed exponent `a-1-2|ℓ|` of (6.1) agrees with the first
  only for `a ≤ 2`: `∑_{ℓ ∈ Sq(a)} q^{C(a,2)-2|ℓ|} = [a]!`, while for `a = 3` the printed
  exponents `2, 0, 0, -2, -2, -4` are not symmetric.
* p. 47: `ONH_a^N = 0` for `a > N` (`cyclotomic_vanish`, from Proposition 5.2). -/

namespace OddMath.Frontier.Categorification
open NilHeckeAction ZeroHecke GradedTrace ProjectorRank

noncomputable section

/-! ## Split idempotents -/

section General
variable {R : Type*} [Ring R]

/-- The left ideal `R·e = {x | x e = x}`. -/
def leftIdeal (e : R) : Submodule R R where
  carrier := {x | x * e = x}
  add_mem' {x y} hx hy := by
    change (x + y) * e = x + y
    rw [add_mul, hx, hy]
  zero_mem' := zero_mul e
  smul_mem' r x hx := by
    change r * x * e = r * x
    rw [mul_assoc, hx]

theorem mem_leftIdeal {e x : R} : x ∈ leftIdeal e ↔ x * e = x := Iff.rfl

theorem leftIdeal_one : leftIdeal (1 : R) = ⊤ :=
  eq_top_iff.mpr fun x _ => mul_one x

/-- For an idempotent `e`, `leftIdeal e = R·e`. -/
theorem leftIdeal_eq_span {e : R} (he : e * e = e) : leftIdeal e = Submodule.span R {e} := by
  ext x
  rw [Submodule.mem_span_singleton, mem_leftIdeal]
  constructor
  · intro hx
    exact ⟨x, hx⟩
  · rintro ⟨r, rfl⟩
    rw [smul_eq_mul, mul_assoc, he]

section Orth
variable {P e : R} {I : Type*} [Fintype I] [DecidableEq I] {σ lam : I → R}
  (hsum : ∑ i, σ i * lam i = P) (horth : ∀ i j, lam i * σ j = if i = j then e else 0)
include hsum horth

theorem mul_sigma_eq (j : I) : P * σ j = σ j * e := by
  rw [← hsum, Finset.sum_mul]
  simp_rw [mul_assoc, horth, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem lam_mul_eq (i : I) : lam i * P = e * lam i := by
  rw [← hsum, Finset.mul_sum]
  simp_rw [← mul_assoc, horth, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

end Orth

/-- `P = ∑_i σ_i λ_i` with `λ_i σ_j = δ_ij e`, `σ_i ∈ P R`, `λ_i ∈ R P`. -/
structure Splitting (P e : R) (I : Type*) [Fintype I] [DecidableEq I] where
  σ : I → R
  lam : I → R
  sum_eq : ∑ i, σ i * lam i = P
  orth : ∀ i j, lam i * σ j = if i = j then e else 0
  mul_sigma : ∀ i, P * σ i = σ i
  lam_mul : ∀ i, lam i * P = lam i

namespace Splitting
variable {P e : R} {I : Type*} [Fintype I] [DecidableEq I] (S : Splitting P e I)

theorem sigma_mul (j : I) : S.σ j * e = S.σ j :=
  (mul_sigma_eq S.sum_eq S.orth j).symm.trans (S.mul_sigma j)

theorem mul_lam (i : I) : e * S.lam i = S.lam i :=
  (lam_mul_eq S.sum_eq S.orth i).symm.trans (S.lam_mul i)

/-- `R·P ≃ ⊕_{i ∈ I} R·e` as left `R`-modules: `x ↦ (x σ_i)_i`, `(y_i) ↦ ∑ y_i λ_i`. -/
def equiv : leftIdeal P ≃ₗ[R] (I → leftIdeal e) where
  toFun x i := ⟨x.1 * S.σ i, by rw [mem_leftIdeal, mul_assoc, S.sigma_mul]⟩
  map_add' x y := funext fun i => Subtype.ext (add_mul _ _ _)
  map_smul' r x := funext fun i => Subtype.ext (mul_assoc _ _ _)
  invFun y := ⟨∑ i, (y i).1 * S.lam i, by
    rw [mem_leftIdeal, Finset.sum_mul]
    simp_rw [mul_assoc, S.lam_mul]⟩
  left_inv x := Subtype.ext <| by
    change ∑ i, x.1 * S.σ i * S.lam i = x.1
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum, S.sum_eq, x.2]
  right_inv y := funext fun j => Subtype.ext <| by
    change (∑ i, (y i).1 * S.lam i) * S.σ j = (y j).1
    rw [Finset.sum_mul]
    simp_rw [mul_assoc, S.orth, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact (y j).2

theorem equiv_apply (x : leftIdeal P) (i : I) : (S.equiv x i : R) = x.1 * S.σ i := rfl

theorem equiv_symm_apply (y : I → leftIdeal e) :
    (S.equiv.symm y : R) = ∑ i, (y i : R) * S.lam i := rfl

/-- The row `u = (σ_i)_i`. -/
def row : Matrix (Fin 1) I R := Matrix.of fun _ i => S.σ i

/-- The column `v = (λ_i)_i`. -/
def col : Matrix I (Fin 1) R := Matrix.of fun i _ => S.lam i

/-- `u v = P`. -/
theorem row_mul_col : S.row * S.col = Matrix.diagonal fun _ => P := by
  ext r c
  rw [Subsingleton.elim r c, Matrix.mul_apply, Matrix.diagonal_apply_eq]
  exact S.sum_eq

/-- `v u = diag(e, …, e)`. -/
theorem col_mul_row : S.col * S.row = Matrix.diagonal fun _ => e := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_one, Matrix.diagonal_apply]
  exact S.orth i j

/-- `u ∈ P·Mat·diag(e)`. -/
theorem diag_mul_row : (Matrix.diagonal fun _ => P) * S.row = S.row := by
  ext r i
  rw [Matrix.diagonal_mul]
  exact S.mul_sigma i

theorem row_mul_diag : S.row * (Matrix.diagonal fun _ => e) = S.row := by
  ext r i
  rw [Matrix.mul_diagonal]
  exact S.sigma_mul i

/-- `v ∈ diag(e)·Mat·P`. -/
theorem diag_mul_col : (Matrix.diagonal fun _ => e) * S.col = S.col := by
  ext i r
  rw [Matrix.diagonal_mul]
  exact S.mul_lam i

theorem col_mul_diag : S.col * (Matrix.diagonal fun _ => P) = S.col := by
  ext i r
  rw [Matrix.mul_diagonal]
  exact S.lam_mul i

end Splitting

end General

variable {n : ℕ}

theorem hasDegree_sum {ι : Type*} (s : Finset ι) {k : ℤ} (f : ι → Presented n)
    (h : ∀ i ∈ s, HasDegree (Vd (n+2)) k (action n (f i))) :
    HasDegree (Vd (n+2)) k (action n (∑ i ∈ s, f i)) := fun d v hv => by
  rw [map_sum, LinearMap.coeFn_sum, Finset.sum_apply]
  exact Submodule.sum_mem _ fun i hi => h i hi d v hv

/-! ## (6.1) -/

section Eq61
open ThickMatrixUnits BoxPartitionCount

theorem mem_Sq' (ℓ : Sq (n+2)) : ∀ ν : Fin (n+1), ℓ.1 ν ≤ ν.val + 1 := mem_Sq.mp ℓ.2

theorem sum_eq_61 : ∑ ℓ : Sq (n+2), sigma ℓ.1 * lam ℓ.1 = (1 : Presented n) := by
  rw [Finset.sum_coe_sort (Sq (n+2)) fun ℓ => sigma (n := n) ℓ * lam ℓ]
  exact thm_4_15_sum

theorem orth_61 (ℓ' ℓ : Sq (n+2)) :
    lam ℓ'.1 * sigma ℓ.1 = if ℓ' = ℓ then projector n else 0 := by
  rw [lemma_4_13 (mem_Sq' ℓ) (mem_Sq' ℓ')]
  exact if_congr Subtype.ext_iff.symm rfl rfl

/-- `σ_ℓ e_a = σ_ℓ`. -/
theorem sigma_mul_projector_61 (ℓ : Sq (n+2)) : sigma ℓ.1 * projector n = sigma ℓ.1 :=
  (mul_sigma_eq sum_eq_61 orth_61 ℓ).symm.trans (one_mul _)

/-- `e_a λ_ℓ = λ_ℓ`. -/
theorem projector_mul_lam_61 (ℓ : Sq (n+2)) : projector n * lam ℓ.1 = lam ℓ.1 :=
  projector_mul_lam ℓ.1

/-- The splitting `1 = ∑_{ℓ ∈ Sq(a)} σ_ℓ λ_ℓ`, `λ_{ℓ'} σ_ℓ = δ_{ℓℓ'} e_a` (Lemma 4.13, Thm 4.15). -/
def split61 (n : ℕ) : Splitting (1 : Presented n) (projector n) (Sq (n+2)) where
  σ ℓ := sigma ℓ.1
  lam ℓ := lam ℓ.1
  sum_eq := sum_eq_61
  orth := orth_61
  mul_sigma _ := one_mul _
  lam_mul _ := mul_one _

/-- **EKL (6.1)**: `ONH_a ≅ ⊕_{ℓ ∈ Sq(a)} ONH_a e_a` as left `ONH_a`-modules,
`x ↦ (x σ_ℓ)_ℓ`, inverse `(y_ℓ)_ℓ ↦ ∑_ℓ y_ℓ λ_ℓ`. -/
def eq_6_1 (n : ℕ) : Presented n ≃ₗ[Presented n] (Sq (n+2) → leftIdeal (projector n)) :=
  (Submodule.topEquiv.symm.trans (LinearEquiv.ofEq _ _ leftIdeal_one.symm)).trans
    (split61 n).equiv

theorem eq_6_1_apply (x : Presented n) (ℓ : Sq (n+2)) :
    (eq_6_1 n x ℓ : Presented n) = x * sigma ℓ.1 := rfl

theorem eq_6_1_symm_apply (y : Sq (n+2) → leftIdeal (projector n)) :
    (eq_6_1 n).symm y = ∑ ℓ, (y ℓ : Presented n) * lam ℓ.1 := rfl

/-- The degree `|ℓ| - C(a,2)` of `σ_ℓ` (a dot has degree `1`). -/
def deg61 (ℓ : Fin (n+1) → ℕ) : ℤ := ((∑ ν, ℓ ν : ℕ) : ℤ) - (((n+2).choose 2 : ℕ) : ℤ)

/-- The `ℓ`-component of (6.1) raises degree by `|ℓ| - C(a,2)`. -/
theorem eq_6_1_hasDegree {x : Presented n} {d : ℤ} (hx : HasDegree (Vd (n+2)) d (action n x))
    (ℓ : Sq (n+2)) : HasDegree (Vd (n+2)) (d + deg61 ℓ.1) (action n (eq_6_1 n x ℓ)) := by
  rw [eq_6_1_apply, deg61, ← sigmaDeg_extend]
  exact hasDegree_action_mul hx (hasDegree_sigma (mem_Sq' ℓ))

/-- The inverse of (6.1) is homogeneous: components of degree `d + |ℓ| - C(a,2)` go to degree
`d`. -/
theorem eq_6_1_symm_hasDegree {y : Sq (n+2) → leftIdeal (projector n)} {d : ℤ}
    (hy : ∀ ℓ, HasDegree (Vd (n+2)) (d + deg61 ℓ.1) (action n (y ℓ))) :
    HasDegree (Vd (n+2)) d (action n ((eq_6_1 n).symm y)) := by
  rw [eq_6_1_symm_apply]
  refine hasDegree_sum _ _ fun ℓ _ => ?_
  have h := hasDegree_action_mul (hy ℓ) (hasDegree_lam (mem_Sq' ℓ))
  rwa [sigmaDeg_extend, ← deg61, add_neg_cancel_right] at h

/-- Paper normalization of (6.1): the `ℓ`-summand `E^{(a)}` carries the shift
`2 deg σ_ℓ + C(a,2) = 2|ℓ| - C(a,2)`. -/
theorem shift_6_1 (ℓ : Fin (n+1) → ℕ) :
    2 * deg61 ℓ + (n+2).choose 2 = 2 * (∑ ν, ℓ ν : ℕ) - (n+2).choose 2 := by
  rw [deg61]; ring

/-- (6.1) as a Murray–von Neumann equivalence `1 ~ diag(e_a)_{ℓ ∈ Sq(a)}`: `u v = 1`. -/
theorem eq_6_1_row_mul_col : (split61 n).row * (split61 n).col = 1 :=
  (split61 n).row_mul_col.trans Matrix.diagonal_one

/-- `v u = diag(e_a)`. -/
theorem eq_6_1_col_mul_row :
    (split61 n).col * (split61 n).row = Matrix.diagonal fun _ => projector n :=
  (split61 n).col_mul_row

end Eq61

/-! ## (6.2) -/

section Eq62
open ThickBubble BoxPartitionCount
variable {a b : ℕ}

theorem mem_box' (α : box a b) : Antitone α.1 ∧ ∀ k, α.1 k ≤ b := mem_box.mp α.2

theorem sum_eq_62 (hab : a + b = n+2) :
    ∑ α : box a b, sigma n a b hab α.1 * lam n a b hab α.1 = blockE n 0 a * blockE n a b := by
  rw [Finset.sum_coe_sort (box a b) fun α => sigma n a b hab α * lam n a b hab α,
    ThickDecomposition.thm_4_16 hab]
  rfl

theorem orth_62 (hab : a + b = n+2) (β α : box a b) :
    lam n a b hab β.1 * sigma n a b hab α.1 = if β = α then projector n else 0 := by
  rw [eq_4_54 hab (mem_box' α).1 (mem_box' α).2 (mem_box' β).1 (mem_box' β).2]
  exact if_congr Subtype.ext_iff.symm rfl rfl

/-- `σ_α e_{a+b} = σ_α`. -/
theorem sigma_mul_projector_62 (hab : a + b = n+2) (α : box a b) :
    sigma n a b hab α.1 * projector n = sigma n a b hab α.1 :=
  (mul_sigma_eq (sum_eq_62 hab) (orth_62 hab) α).symm.trans (blockE_mul_sigma hab α.1)

/-- `e_{a+b} λ_α = λ_α`. -/
theorem projector_mul_lam_62 (hab : a + b = n+2) (α : box a b) :
    projector n * lam n a b hab α.1 = lam n a b hab α.1 :=
  projector_mul_lam hab α.1

/-- The splitting `e_a ⊗ e_b = ∑_{α ∈ P(a,b)} σ_α λ_α`, `λ_β σ_α = δ_{αβ} e_{a+b}`
((4.54), Theorem 4.16). -/
def split62 (hab : a + b = n+2) :
    Splitting (blockE n 0 a * blockE n a b) (projector n) (box a b) where
  σ α := sigma n a b hab α.1
  lam α := lam n a b hab α.1
  sum_eq := sum_eq_62 hab
  orth := orth_62 hab
  mul_sigma α := blockE_mul_sigma hab α.1
  lam_mul α := lam_mul_blockE hab α.1

/-- **EKL (6.2)**: `ONH_{a+b}(e_a ⊗ e_b) ≅ ⊕_{α ∈ P(a,b)} ONH_{a+b} e_{a+b}` as left
`ONH_{a+b}`-modules, `x ↦ (x σ_α)_α`, inverse `(y_α)_α ↦ ∑_α y_α λ_α`. -/
def eq_6_2 (hab : a + b = n+2) :
    leftIdeal (blockE n 0 a * blockE n a b) ≃ₗ[Presented n] (box a b → leftIdeal (projector n)) :=
  (split62 hab).equiv

theorem eq_6_2_apply (hab : a + b = n+2) (x : leftIdeal (blockE n 0 a * blockE n a b))
    (α : box a b) : (eq_6_2 hab x α : Presented n) = x.1 * sigma n a b hab α.1 := rfl

theorem eq_6_2_symm_apply (hab : a + b = n+2) (y : box a b → leftIdeal (projector n)) :
    ((eq_6_2 hab).symm y : Presented n) = ∑ α, (y α : Presented n) * lam n a b hab α.1 := rfl

/-- The `α`-component of (6.2) raises degree by `|α| - ab` (`ThickDecomposition.shift`). -/
theorem eq_6_2_hasDegree (hab : a + b = n+2) {x : leftIdeal (blockE n 0 a * blockE n a b)}
    {d : ℤ} (hx : HasDegree (Vd (n+2)) d (action n x)) (α : box a b) :
    HasDegree (Vd (n+2)) (d + ThickDecomposition.shift a b α.1) (action n (eq_6_2 hab x α)) := by
  rw [eq_6_2_apply]
  exact hasDegree_action_mul hx (ThickDecomposition.hasDegree_sigma hab α.1)

/-- The inverse of (6.2) is homogeneous: components of degree `d + |α| - ab` go to degree `d`. -/
theorem eq_6_2_symm_hasDegree (hab : a + b = n+2) {y : box a b → leftIdeal (projector n)}
    {d : ℤ} (hy : ∀ α, HasDegree (Vd (n+2)) (d + ThickDecomposition.shift a b α.1)
      (action n (y α))) :
    HasDegree (Vd (n+2)) d (action n ((eq_6_2 hab).symm y)) := by
  rw [eq_6_2_symm_apply]
  refine hasDegree_sum _ _ fun α _ => ?_
  have h := hasDegree_action_mul (hy α) (ThickDecomposition.hasDegree_lam hab (mem_box' α).2)
  rwa [add_neg_cancel_right] at h

/-- Paper normalization of (6.2): the `α`-summand carries the shift
`2 deg σ_α + ab = 2|α| - ab`. -/
theorem shift_6_2 (α : Fin a → ℕ) :
    2 * ThickDecomposition.shift a b α + (a * b : ℕ) = 2 * (∑ i, α i : ℕ) - (a * b : ℕ) := by
  rw [ThickDecomposition.shift]; ring

/-- (6.2) as a Murray–von Neumann equivalence `e_a ⊗ e_b ~ diag(e_{a+b})_{α ∈ P(a,b)}`:
`u v = e_a ⊗ e_b`. -/
theorem eq_6_2_row_mul_col (hab : a + b = n+2) :
    (split62 hab).row * (split62 hab).col =
      Matrix.diagonal fun _ => blockE n 0 a * blockE n a b :=
  (split62 hab).row_mul_col

/-- `v u = diag(e_{a+b})`. -/
theorem eq_6_2_col_mul_row (hab : a + b = n+2) :
    (split62 hab).col * (split62 hab).row = Matrix.diagonal fun _ => projector n :=
  (split62 hab).col_mul_row

end Eq62

/-! ## Cyclotomic quotients -/

/-- EKL p. 47: the cyclotomic quotient `ONH_a^N` is zero unless `a ≤ N` (Proposition 5.2 and
`OH_{a,N} = 0` for `a > N`). -/
theorem cyclotomic_vanish {N : ℕ} (h : N < n+2) (x : Cyclotomic.ONH n N) : x = 0 :=
  haveI := Cyclotomic.ONH_subsingleton h
  Subsingleton.elim x 0

end

end OddMath.Frontier.Categorification
