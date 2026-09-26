import OddMath.Frontier.OddBialgebraRes

/-!
# Graded Morita invariance for a full corner

EKL arXiv:1111.1320v1, §6, pp. 46–47. Let `R` be a `ℤ`-graded ring, `e ∈ R_0` an idempotent and
`1 = ∑ᵢ σᵢ λᵢ` with `λᵢ σⱼ = δᵢⱼ e`, `σᵢ` of degree `dᵢ`, `λᵢ` of degree `-dᵢ`
(`Categorification.Splitting 1 e I`), so that `R ≅ ⊕ᵢ Re{-dᵢ}` and `e` is full. The corner ring
`eRe` (`IsIdempotentElem.Corner`, unit `e`) is graded by `cornerGrading`.

* `fromCorner`: a graded idempotent `(n, s, F)` over `eRe` gives `(n, s, F)` over `R`, the graded
  projective `R^n{s} F = (Re)^n{s} F`.
* `toCorner`: `(n, s, E) ↦ (n · |I|, s_k - dᵢ, (λᵢ E_{kl} σⱼ))`, the idempotent over `eRe` of
  `Hom_R(Re, R^n{s} E)`.
* The two are mutually inverse up to Murray–von Neumann equivalence, so
  `K₀(eRe) ≃ K₀(R)` (`K0.cornerEquiv`); if `eRe` is connected, `K₀(R) ≃ ℤ[q,q⁻¹]` with
  `[Re{k}] ↦ q^k` (`K0.cornerClassify`).
-/

noncomputable section
open Matrix

namespace OddMath.Frontier.OddBialgebra
open GradedK0 OddCategorification

variable {R : Type*} [Ring R] {A : ℤ → AddSubgroup R} {e : R} (he : IsIdempotentElem e)

/-- The underlying element of the corner, as an additive map. -/
def cval : he.Corner →+ R where
  toFun := Subtype.val
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem cval_apply (x : he.Corner) : cval he x = x.1 := rfl

theorem cval_mul (x y : he.Corner) : (x * y).1 = x.1 * y.1 := rfl

theorem cval_one : (1 : he.Corner).1 = e := rfl

@[simp] theorem cval_zero : (0 : he.Corner).1 = 0 := rfl

include he in
theorem mem_corner {x : R} (h1 : e * x = x) (h2 : x * e = x) : x ∈ Subsemigroup.corner e :=
  (Subsemigroup.mem_corner_iff he).2 ⟨h1, h2⟩

theorem corner_left (x : he.Corner) : e * x.1 = x.1 :=
  ((Subsemigroup.mem_corner_iff he).1 x.2).1

theorem corner_right (x : he.Corner) : x.1 * e = x.1 :=
  ((Subsemigroup.mem_corner_iff he).1 x.2).2

/-- The grading of the corner ring `eRe`, restricted from `R`. -/
def cornerGrading (A : ℤ → AddSubgroup R) {e : R} (he : IsIdempotentElem e) (d : ℤ) :
    AddSubgroup he.Corner :=
  (A d).comap (cval he)

theorem mem_cornerGrading {d : ℤ} {x : he.Corner} : x ∈ cornerGrading A he d ↔ x.1 ∈ A d :=
  Iff.rfl

instance cornerGrading.gradedMonoid [SetLike.GradedMonoid A] [Fact (e ∈ A 0)] :
    SetLike.GradedMonoid (cornerGrading A he) where
  one_mem := (Fact.out : e ∈ A 0)
  mul_mem _ _ x y hx hy := show x.1 * y.1 ∈ A _ from SetLike.GradedMul.mul_mem (A := A) hx hy

theorem map_cval_mul {ι κ μ : Type*} [Fintype κ] (X : Matrix ι κ he.Corner)
    (Y : Matrix κ μ he.Corner) : (X * Y).map (cval he) = X.map (cval he) * Y.map (cval he) := by
  ext i j
  simp only [map_apply, mul_apply, map_sum]
  rfl

/-! ### A Murray–von Neumann equivalence from a one-sided inverse -/

section Conj

variable {S : Type*} [Ring S] {B : ℤ → AddSubgroup S} [SetLike.GradedMonoid B]

/-- If `r c = 1` then `E ~ c E r`. -/
theorem mvn_conj {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] {s : ι → ℤ} {t : κ → ℤ}
    {r : Matrix ι κ S} {c : Matrix κ ι S} {E : Matrix ι ι S} (hr : IsHom B s t r)
    (hc : IsHom B t s c) (hrc : r * c = 1) (hE : IsHom B s s E) (hEE : E * E = E) :
    MvN B s E t (c * E * r) := by
  have k1 : ∀ X : Matrix ι ι S, r * (c * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hrc, Matrix.one_mul]
  have k1' : ∀ X : Matrix ι κ S, r * (c * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hrc, Matrix.one_mul]
  have k2 : ∀ X : Matrix ι κ S, E * (E * X) = E * X := fun X => by
    rw [← Matrix.mul_assoc, hEE]
  refine ⟨E * r, c * E, hE.mul hr, hc.mul hE, ?_, ?_, ?_, ?_⟩
  · simp only [Matrix.mul_assoc, k1, hEE]
  · simp only [Matrix.mul_assoc, k2]
  · simp only [Matrix.mul_assoc, k1', k2]
  · simp only [Matrix.mul_assoc, k1, k2, hEE]

end Conj

/-! ### Corner and ambient idempotents -/

section Morita

variable [SetLike.GradedMonoid A] [Fact (e ∈ A 0)] {I : Type*} [Fintype I] [DecidableEq I]
  (S : Categorification.Splitting (1 : R) e I) (dσ : I → ℤ)

/-- A graded idempotent over `eRe` as one over `R`. -/
def fromCorner (Q : GIdem (cornerGrading A he)) : GIdem A where
  n := Q.n
  s := Q.s
  e := Q.e.map (cval he)
  hom i j := Q.hom i j
  idem := by rw [← map_cval_mul, Q.idem]

omit [SetLike.GradedMonoid A] [Fact (e ∈ A 0)] in
theorem mvn_map_cval {ι κ : Type*} [Fintype ι] [Fintype κ] {s : ι → ℤ}
    {F : Matrix ι ι he.Corner} {t : κ → ℤ} {F' : Matrix κ κ he.Corner}
    (h : MvN (cornerGrading A he) s F t F') : MvN A s (F.map (cval he)) t (F'.map (cval he)) := by
  obtain ⟨u, v, hu, hv, h1, h2, h3, h4⟩ := h
  exact ⟨u.map (cval he), v.map (cval he), fun i j => hu i j, fun i j => hv i j,
    by rw [← map_cval_mul, h1], by rw [← map_cval_mul, h2],
    by rw [← map_cval_mul, ← map_cval_mul, h3], by rw [← map_cval_mul, ← map_cval_mul, h4]⟩

theorem fromCorner_congr {Q Q' : GIdem (cornerGrading A he)} (h : Q ≈ Q') :
    fromCorner he Q ≈ fromCorner he Q' :=
  mvn_map_cval he h

omit [Fact (e ∈ A 0)] in
theorem fromCorner_sum (Q Q' : GIdem (cornerGrading A he)) :
    fromCorner he (Q.sum Q') ≈ (fromCorner he Q).sum (fromCorner he Q') := by
  refine MvN.of_equiv (Equiv.refl _) (fromCorner he (Q.sum Q')).hom
    (fromCorner he (Q.sum Q')).idem (fun i => rfl) (fun i j => ?_)
  show fromBlocks (Q.e.map (cval he)) 0 0 (Q'.e.map (cval he)) (finSumFinEquiv.symm i)
      (finSumFinEquiv.symm j) =
    cval he (fromBlocks Q.e 0 0 Q'.e (finSumFinEquiv.symm i) (finSumFinEquiv.symm j))
  generalize finSumFinEquiv.symm i = x
  generalize finSumFinEquiv.symm j = y
  cases x <;> cases y <;> simp

/-- `X ↦ (λᵢ X_{kl} σⱼ)`, with values in the corner. -/
def cj {κ μ : Type*} (X : Matrix κ μ R) : Matrix (κ × I) (μ × I) he.Corner :=
  fun x y => ⟨S.lam x.2 * X x.1 y.1 * S.σ y.2, mem_corner he
    (by rw [← mul_assoc, ← mul_assoc, S.mul_lam]) (by rw [mul_assoc, S.sigma_mul])⟩

omit [SetLike.GradedMonoid A] [Fact (e ∈ A 0)] in
theorem cj_val {κ μ : Type*} (X : Matrix κ μ R) (x : κ × I) (y : μ × I) :
    (cj he S X x y).1 = S.lam x.2 * X x.1 y.1 * S.σ y.2 := rfl

omit [SetLike.GradedMonoid A] [Fact (e ∈ A 0)] in
theorem cj_mul {κ μ ν : Type*} [Fintype μ] (X : Matrix κ μ R) (Y : Matrix μ ν R) :
    cj he S X * cj he S Y = cj he S (X * Y) := by
  ext ⟨k, i⟩ ⟨m, p⟩
  apply Subtype.ext
  rw [cj_val, mul_apply, ← cval_apply, map_sum, Fintype.sum_prod_type, mul_apply,
    Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [cval_apply, cval_mul, cj_val]
  calc ∑ j, S.lam i * X k l * S.σ j * (S.lam j * Y l m * S.σ p)
      = S.lam i * X k l * (∑ j, S.σ j * S.lam j) * Y l m * S.σ p := by
        rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
        simp only [mul_assoc]
    _ = _ := by rw [S.sum_eq, mul_one]; simp only [mul_assoc]

variable {dσ} in
omit [Fact (e ∈ A 0)] in
theorem isHom_cj (hσ : ∀ i, S.σ i ∈ A (dσ i)) (hlam : ∀ i, S.lam i ∈ A (-dσ i))
    {κ μ : Type*} {s : κ → ℤ} {t : μ → ℤ} {X : Matrix κ μ R} (hX : IsHom A s t X) :
    IsHom (cornerGrading A he) (fun x : κ × I => s x.1 - dσ x.2)
      (fun y : μ × I => t y.1 - dσ y.2) (cj he S X) := fun x y =>
  mem_of_deg_eq (SetLike.GradedMul.mul_mem (SetLike.GradedMul.mul_mem (hlam x.2) (hX x.1 y.1))
    (hσ y.2)) (by ring)

end Morita

section Morita2

variable [SetLike.GradedMonoid A] [Fact (e ∈ A 0)] {I : Type*} [Fintype I] [DecidableEq I]
  (S : Categorification.Splitting (1 : R) e I) {dσ : I → ℤ}
  (hσ : ∀ i, S.σ i ∈ A (dσ i)) (hlam : ∀ i, S.lam i ∈ A (-dσ i))
include hσ hlam

/-- `(n, s, E) ↦ (n · |I|, s_k - dᵢ, (λᵢ E_{kl} σⱼ))`, a graded idempotent over `eRe`. -/
def toCorner (P : GIdem A) : GIdem (cornerGrading A he) :=
  GIdem.ofEquiv (fun x : Fin P.n × I => P.s x.1 - dσ x.2) (cj he S P.e)
    (isHom_cj he S hσ hlam P.hom) (by rw [cj_mul, P.idem]) (Fintype.equivFin _)

omit [Fact (e ∈ A 0)] in
theorem mvn_cj {κ μ : Type*} [Fintype κ] [Fintype μ] {s : κ → ℤ} {E : Matrix κ κ R}
    {t : μ → ℤ} {F : Matrix μ μ R} (h : MvN A s E t F) :
    MvN (cornerGrading A he) (fun x : κ × I => s x.1 - dσ x.2) (cj he S E)
      (fun y : μ × I => t y.1 - dσ y.2) (cj he S F) := by
  obtain ⟨u, v, hu, hv, h1, h2, h3, h4⟩ := h
  exact ⟨cj he S u, cj he S v, isHom_cj he S hσ hlam hu, isHom_cj he S hσ hlam hv,
    by rw [cj_mul, h1], by rw [cj_mul, h2], by rw [cj_mul, cj_mul, h3],
    by rw [cj_mul, cj_mul, h4]⟩

theorem toCorner_congr {P P' : GIdem A} (h : P ≈ P') :
    toCorner he S hσ hlam P ≈ toCorner he S hσ hlam P' :=
  MvN.trans (toCorner he S hσ hlam P).idem (by rw [cj_mul, P.idem])
    (toCorner he S hσ hlam P').idem (GIdem.mvn_ofEquiv _ _ _ _ _).symm
    (MvN.trans (by rw [cj_mul, P.idem]) (by rw [cj_mul, P'.idem]) (toCorner he S hσ hlam P').idem
      (mvn_cj he S hσ hlam h) (GIdem.mvn_ofEquiv _ _ _ _ _))

omit hσ hlam in
/-- The row `(δ_{kl} σⱼ)`. -/
def rowS (n : ℕ) : Matrix (Fin n) (Fin n × I) R := fun k y => if k = y.1 then S.σ y.2 else 0

omit hσ hlam in
/-- The column `(δ_{kl} λᵢ)`. -/
def colS (n : ℕ) : Matrix (Fin n × I) (Fin n) R := fun x l => if x.1 = l then S.lam x.2 else 0

omit [SetLike.GradedMonoid A] [Fact (e ∈ A 0)] hσ hlam in
theorem rowS_mul_colS (n : ℕ) : rowS S n * colS S n = 1 := by
  ext k l
  rw [mul_apply, Fintype.sum_prod_type, one_apply]
  simp only [rowS, colS, ite_mul, zero_mul, mul_ite, mul_zero]
  rw [Finset.sum_eq_single k (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
  by_cases h : k = l
  · subst h; simp [S.sum_eq]
  · simp [h]

omit [SetLike.GradedMonoid A] [Fact (e ∈ A 0)] hσ hlam in
theorem colS_mul_mul_rowS {n : ℕ} (E : Matrix (Fin n) (Fin n) R) :
    colS S n * E * rowS S n = (cj he S E).map (cval he) := by
  ext ⟨k, i⟩ ⟨l, j⟩
  simp only [mul_apply, colS, rowS, map_apply, cval_apply, cj_val, ite_mul, zero_mul, mul_ite,
    mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_ite_eq']

omit [SetLike.GradedMonoid A] [Fact (e ∈ A 0)] hlam in
theorem isHom_rowS {n : ℕ} (s : Fin n → ℤ) :
    IsHom A s (fun y : Fin n × I => s y.1 - dσ y.2) (rowS S n) := fun k y => by
  simp only [rowS]
  split_ifs with h
  · subst h; exact mem_of_deg_eq (hσ y.2) (by ring)
  · exact zero_mem _

omit [SetLike.GradedMonoid A] [Fact (e ∈ A 0)] hσ in
theorem isHom_colS {n : ℕ} (s : Fin n → ℤ) :
    IsHom A (fun y : Fin n × I => s y.1 - dσ y.2) s (colS S n) := fun x l => by
  simp only [colS]
  split_ifs with h
  · subst h; exact mem_of_deg_eq (hlam x.2) (by ring)
  · exact zero_mem _

/-- `R^n{s} E ≅ (Re)^{n·|I|} (λ E σ)`: every graded projective comes from the corner. -/
theorem fromCorner_toCorner (P : GIdem A) :
    fromCorner he (toCorner he S hσ hlam P) ≈ P := by
  have h1 : MvN A P.s P.e (fun x : Fin P.n × I => P.s x.1 - dσ x.2)
      ((cj he S P.e).map (cval he)) := by
    rw [← colS_mul_mul_rowS]
    exact mvn_conj (isHom_rowS S hσ P.s) (isHom_colS S hlam P.s) (rowS_mul_colS S _)
      P.hom P.idem
  have hidem : (cj he S P.e).map (cval he) * (cj he S P.e).map (cval he) =
      (cj he S P.e).map (cval he) := by rw [← map_cval_mul, cj_mul, P.idem]
  have h2 := mvn_map_cval he (GIdem.mvn_ofEquiv (fun x : Fin P.n × I => P.s x.1 - dσ x.2)
    (cj he S P.e) (isHom_cj he S hσ hlam P.hom) (by rw [cj_mul, P.idem])
    (Fintype.equivFin (Fin P.n × I)))
  exact (MvN.trans P.idem hidem (fromCorner he _).idem h1 h2).symm

omit hσ hlam in
/-- The row `(δ_{kl} e σⱼ)` over the corner. -/
def rowC (n : ℕ) : Matrix (Fin n) (Fin n × I) he.Corner := fun k y =>
  if k = y.1 then ⟨e * S.σ y.2, mem_corner he (by rw [← mul_assoc, he.eq])
    (by rw [mul_assoc, S.sigma_mul])⟩ else 0

omit hσ hlam in
/-- The column `(δ_{kl} λᵢ e)` over the corner. -/
def colC (n : ℕ) : Matrix (Fin n × I) (Fin n) he.Corner := fun x l =>
  if x.1 = l then ⟨S.lam x.2 * e, mem_corner he (by rw [← mul_assoc, S.mul_lam])
    (by rw [mul_assoc, he.eq])⟩ else 0

omit [SetLike.GradedMonoid A] [Fact (e ∈ A 0)] hσ hlam in
theorem rowC_mul_colC (n : ℕ) : rowC he S n * colC he S n = 1 := by
  ext k l
  apply Subtype.ext
  rw [mul_apply, ← cval_apply, map_sum, Fintype.sum_prod_type, one_apply]
  simp only [rowC, colC, ite_mul, zero_mul, mul_ite, mul_zero]
  rw [Finset.sum_eq_single k (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
  by_cases h : k = l
  · subst h
    simp only [if_true, cval_apply, cval_mul, cval_one]
    rw [show ∑ j, e * S.σ j * (S.lam j * e) = e * (∑ j, S.σ j * S.lam j) * e by
      rw [Finset.mul_sum, Finset.sum_mul]; simp only [mul_assoc], S.sum_eq, mul_one, he.eq]
  · simp [h]

omit [SetLike.GradedMonoid A] [Fact (e ∈ A 0)] hσ hlam in
theorem colC_mul_mul_rowC {n : ℕ} (F : Matrix (Fin n) (Fin n) he.Corner) :
    colC he S n * F * rowC he S n = cj he S (F.map (cval he)) := by
  ext ⟨k, i⟩ ⟨l, j⟩
  apply Subtype.ext
  simp only [mul_apply, colC, rowC, ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, Finset.sum_ite_eq', cj_val, map_apply, cval_apply, cval_mul]
  simp only [mul_assoc]
  rw [← mul_assoc e (F k l).1, corner_left, ← mul_assoc (F k l).1 e, corner_right]

omit hlam in
theorem isHom_rowC {n : ℕ} (s : Fin n → ℤ) :
    IsHom (cornerGrading A he) s (fun y : Fin n × I => s y.1 - dσ y.2) (rowC he S n) :=
  fun k y => by
    simp only [rowC]
    split_ifs with h
    · subst h
      exact mem_of_deg_eq (SetLike.GradedMul.mul_mem (Fact.out : e ∈ A 0) (hσ y.2)) (by ring)
    · exact zero_mem _

omit hσ in
theorem isHom_colC {n : ℕ} (s : Fin n → ℤ) :
    IsHom (cornerGrading A he) (fun y : Fin n × I => s y.1 - dσ y.2) s (colC he S n) :=
  fun x l => by
    simp only [colC]
    split_ifs with h
    · subst h
      exact mem_of_deg_eq (SetLike.GradedMul.mul_mem (hlam x.2) (Fact.out : e ∈ A 0)) (by ring)
    · exact zero_mem _

/-- Over the corner, `toCorner ∘ fromCorner` is the identity up to equivalence. -/
theorem toCorner_fromCorner (Q : GIdem (cornerGrading A he)) :
    toCorner he S hσ hlam (fromCorner he Q) ≈ Q := by
  have h1 : MvN (cornerGrading A he) Q.s Q.e (fun x : Fin Q.n × I => Q.s x.1 - dσ x.2)
      (cj he S (Q.e.map (cval he))) := by
    rw [← colC_mul_mul_rowC]
    exact mvn_conj (isHom_rowC he S hσ Q.s) (isHom_colC he S hlam Q.s) (rowC_mul_colC he S _)
      Q.hom Q.idem
  have hidem : cj he S (Q.e.map (cval he)) * cj he S (Q.e.map (cval he)) =
      cj he S (Q.e.map (cval he)) := by rw [cj_mul, ← map_cval_mul, Q.idem]
  exact (MvN.trans Q.idem hidem (toCorner he S hσ hlam _).idem h1
    (GIdem.mvn_ofEquiv _ _ _ _ _)).symm

end Morita2

section Morita3

variable [SetLike.GradedMonoid A] [Fact (e ∈ A 0)] {I : Type*} [Fintype I] [DecidableEq I]

/-! ### `K₀(eRe) ≃ K₀(R)` -/

omit [Fact (e ∈ A 0)] in
theorem fromCorner_zero : fromCorner he (GIdem.zero : GIdem (cornerGrading A he)) ≈ GIdem.zero :=
  MvN.of_equiv (Equiv.refl _) (fromCorner he GIdem.zero).hom (fromCorner he GIdem.zero).idem
    (fun i => i.elim0) (fun i => i.elim0)

variable (A) in
/-- `fromCorner` on isomorphism classes. -/
def cornerProj : GProj (cornerGrading A he) →+ GProj A where
  toFun := Quotient.map (fromCorner he) fun _ _ h => fromCorner_congr he h
  map_zero' := GProj.mk_eq_mk.2 (fromCorner_zero he)
  map_add' := by
    refine GProj.ind fun P => GProj.ind fun Q => ?_
    exact GProj.mk_eq_mk.2 (fromCorner_sum he P Q)

theorem cornerProj_mk (Q : GIdem (cornerGrading A he)) :
    cornerProj A he (GProj.mk Q) = GProj.mk (fromCorner he Q) := rfl

variable {he} in
theorem cornerProj_bijective (S : Categorification.Splitting (1 : R) e I) {dσ : I → ℤ}
    (hσ : ∀ i, S.σ i ∈ A (dσ i)) (hlam : ∀ i, S.lam i ∈ A (-dσ i)) :
    Function.Bijective (cornerProj A he) := by
  refine ⟨fun x y h => ?_, fun y => ?_⟩
  · induction x using GProj.ind with
    | h Q =>
      induction y using GProj.ind with
      | h Q' =>
        have h' : fromCorner he Q ≈ fromCorner he Q' := GProj.mk_eq_mk.1 h
        refine GProj.mk_eq_mk.2 ?_
        exact Setoid.trans (Setoid.symm (toCorner_fromCorner he S hσ hlam Q))
          (Setoid.trans (toCorner_congr he S hσ hlam h') (toCorner_fromCorner he S hσ hlam Q'))
  · induction y using GProj.ind with
    | h P =>
      exact ⟨GProj.mk (toCorner he S hσ hlam P),
        GProj.mk_eq_mk.2 (fromCorner_toCorner he S hσ hlam P)⟩

variable {he} in
/-- **Graded Morita invariance for a full corner**: `K₀(eRe) ≃ K₀(R)`, `[Q] ↦ [R^n{s} Q]`. -/
def K0.cornerEquiv (S : Categorification.Splitting (1 : R) e I) {dσ : I → ℤ}
    (hσ : ∀ i, S.σ i ∈ A (dσ i)) (hlam : ∀ i, S.lam i ∈ A (-dσ i)) :
    K0 (cornerGrading A he) ≃ₗ[LaurentPolynomial ℤ] K0 A :=
  let E : K0 (cornerGrading A he) ≃+ K0 A :=
    GrothendieckGroup.mapEquiv (AddEquiv.ofBijective _ (cornerProj_bijective S hσ hlam))
  E.toLinearEquiv (K0.map_smul_of_shift E.toAddMonoidHom fun k x => by
    rw [K0.T_smul]
    have : E.toAddMonoidHom.comp (K0.shift k) = (K0.shift k).comp E.toAddMonoidHom :=
      K0.hom_ext fun P => by
        simp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, E]
        rw [K0.shift_of]
        erw [GrothendieckGroup.mapEquiv_of, GrothendieckGroup.mapEquiv_of]
        exact K0.shift_of k (fromCorner he P) |>.symm
    exact DFunLike.congr_fun this x)

variable {he} in
theorem K0.cornerEquiv_of (S : Categorification.Splitting (1 : R) e I) {dσ : I → ℤ}
    (hσ : ∀ i, S.σ i ∈ A (dσ i)) (hlam : ∀ i, S.lam i ∈ A (-dσ i))
    (Q : GIdem (cornerGrading A he)) :
    K0.cornerEquiv S hσ hlam (K0.of Q) = K0.of (fromCorner he Q) :=
  GrothendieckGroup.mapEquiv_of _ _

theorem fromCorner_single (hee : e * e = e) (he0 : e ∈ A 0) (k : ℤ) :
    fromCorner he (GIdem.single k : GIdem (cornerGrading A he)) ≈ gelem he0 hee k :=
  MvN.of_equiv (Equiv.refl _) (fromCorner he (GIdem.single k)).hom
    (fromCorner he (GIdem.single k)).idem (fun _ => rfl) (fun i j => by
      simp only [fromCorner, GIdem.single, GIdem.free, gelem, gdiag, map_apply, one_apply,
        diagonal_apply, Equiv.refl_apply]
      split_ifs <;> rfl)

variable {he} in
/-- If the corner `eRe` is connected, `K₀(R) ≃ ℤ[q,q⁻¹]` with `[Re{k}] ↦ q^k`. -/
def K0.cornerClassify (S : Categorification.Splitting (1 : R) e I) {dσ : I → ℤ}
    (hσ : ∀ i, S.σ i ∈ A (dσ i)) (hlam : ∀ i, S.lam i ∈ A (-dσ i))
    (hC : Connected (cornerGrading A he)) : K0 A ≃ₗ[LaurentPolynomial ℤ] LaurentPolynomial ℤ :=
  (K0.cornerEquiv S hσ hlam).symm.trans (K0.classify hC)

variable {he} in
theorem K0.cornerClassify_gelem (S : Categorification.Splitting (1 : R) e I) {dσ : I → ℤ}
    (hσ : ∀ i, S.σ i ∈ A (dσ i)) (hlam : ∀ i, S.lam i ∈ A (-dσ i))
    (hC : Connected (cornerGrading A he)) (hee : e * e = e) (he0 : e ∈ A 0) (k : ℤ) :
    K0.cornerClassify S hσ hlam hC (K0.of (gelem he0 hee k)) = LaurentPolynomial.T k := by
  rw [K0.cornerClassify, LinearEquiv.trans_apply, ← K0.of_eq (fromCorner_single he hee he0 k),
    ← K0.cornerEquiv_of S hσ hlam, LinearEquiv.symm_apply_apply, K0.classify_single]

end Morita3

end OddMath.Frontier.OddBialgebra
