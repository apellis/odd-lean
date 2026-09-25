import OddMath.Frontier.GradedK0
import OddMath.Frontier.Categorification

/-!
# Graded `K₀`: graded ring isomorphisms and split idempotents

Auxiliary results on `GradedK0` used for EKL arXiv:1111.1320v1, §6, (6.1)–(6.3).

* `k0Equiv`: a ring isomorphism `φ : R ≃+* S` with `x ∈ A d ↔ φ x ∈ B d` induces
  `K0 A ≃ₗ[ℤ[T;T⁻¹]] K0 B`, `[(n, s, e)] ↦ [(n, s, φ(e))]`.
* `gdiag e t`: the graded idempotent `diag(e, …, e)` on `R^m{t}` for a degree-zero
  idempotent `e ∈ R`; `gelem e k = R{k} · e`, the graded projective `Re{k}`.
  `[diag e t] = ∑ᵢ [Re{t i}]` (`of_diag`) and `T a • [Re{k}] = [Re{k + a}]`.
* `of_elem_splitting`: for a splitting `P = ∑ᵢ σᵢ λᵢ`, `λᵢ σⱼ = δᵢⱼ e`
  (`Categorification.Splitting`) with `σᵢ` of degree `dᵢ` and `λᵢ` of degree `-dᵢ`,
  `[RP{k}] = ∑ᵢ T (k - dᵢ) • [Re]`: the row `(σᵢ)` and column `(λᵢ)` are a degree-zero
  Murray–von Neumann equivalence `RP{k} ≅ ⊕ᵢ Re{k - dᵢ}`.
-/

noncomputable section
open Matrix LaurentPolynomial

namespace OddMath.Frontier.OddCategorification
open GradedK0

/-! ### Transport along graded ring isomorphisms -/

section Transport

variable {R S : Type*} [Ring R] [Ring S] {A : ℤ → AddSubgroup R} {B : ℤ → AddSubgroup S}
  (φ : R ≃+* S)

theorem map_mul_map {ι κ μ : Type*} [Fintype κ] (u : Matrix ι κ R) (v : Matrix κ μ R) :
    u.map φ * v.map φ = (u * v).map φ :=
  (Matrix.map_mul (f := (φ : R →+* S))).symm

theorem map_symm_map {ι κ : Type*} (u : Matrix ι κ R) : (u.map φ).map φ.symm = u := by
  ext i j
  simp

variable (hφ : ∀ d x, x ∈ A d ↔ φ x ∈ B d)
include hφ

theorem isHom_map {ι κ : Type*} {s : ι → ℤ} {t : κ → ℤ} {u : Matrix ι κ R}
    (hu : IsHom A s t u) : IsHom B s t (u.map φ) :=
  fun i j => (hφ _ _).1 (hu i j)

theorem mvn_map {ι κ : Type*} [Fintype ι] [Fintype κ] {s : ι → ℤ} {e : Matrix ι ι R}
    {t : κ → ℤ} {f : Matrix κ κ R} (h : MvN A s e t f) :
    MvN B s (e.map φ) t (f.map φ) := by
  obtain ⟨u, v, hu, hv, h1, h2, h3, h4⟩ := h
  exact ⟨u.map φ, v.map φ, isHom_map φ hφ hu, isHom_map φ hφ hv,
    by rw [map_mul_map, h1], by rw [map_mul_map, h2],
    by rw [map_mul_map, map_mul_map, h3], by rw [map_mul_map, map_mul_map, h4]⟩

theorem mem_symm_iff : ∀ d y, y ∈ B d ↔ φ.symm y ∈ A d := fun d y => by
  rw [hφ, RingEquiv.apply_symm_apply]

variable [SetLike.GradedMonoid A] [SetLike.GradedMonoid B]

/-- The image `(n, s, φ(e))` of a graded idempotent. -/
def gmap (P : GIdem A) : GIdem B where
  n := P.n
  s := P.s
  e := P.e.map φ
  hom := isHom_map φ hφ P.hom
  idem := by rw [map_mul_map, P.idem]

theorem gmap_equiv_iff {P Q : GIdem A} : gmap φ hφ P ≈ gmap φ hφ Q ↔ P ≈ Q := by
  refine ⟨fun h => ?_, fun h => mvn_map φ hφ h⟩
  have h' := mvn_map φ.symm (mem_symm_iff φ hφ) h
  simp only [gmap, map_symm_map] at h'
  exact h'

omit [SetLike.GradedMonoid A] in
theorem gmap_zero : gmap φ hφ (GIdem.zero : GIdem A) ≈ GIdem.zero :=
  MvN.of_equiv (Equiv.refl _) (gmap φ hφ GIdem.zero).hom (gmap φ hφ GIdem.zero).idem
    (fun i => i.elim0) (fun i => i.elim0)

omit [SetLike.GradedMonoid A] in
theorem gmap_sum (P Q : GIdem A) :
    gmap φ hφ (P.sum Q) ≈ (gmap φ hφ P).sum (gmap φ hφ Q) := by
  refine MvN.of_equiv (Equiv.refl _) (gmap φ hφ (P.sum Q)).hom (gmap φ hφ (P.sum Q)).idem
    (fun i => ?_) (fun i j => ?_)
  · show Sum.elim P.s Q.s (finSumFinEquiv.symm i) = Sum.elim P.s Q.s (finSumFinEquiv.symm i)
    rfl
  · show fromBlocks (P.e.map φ) 0 0 (Q.e.map φ) (finSumFinEquiv.symm i) (finSumFinEquiv.symm j) =
      φ (fromBlocks P.e 0 0 Q.e (finSumFinEquiv.symm i) (finSumFinEquiv.symm j))
    generalize finSumFinEquiv.symm i = x
    generalize finSumFinEquiv.symm j = y
    cases x <;> cases y <;> simp

omit [SetLike.GradedMonoid A] [SetLike.GradedMonoid B] in
theorem gmap_shift (k : ℤ) (P : GIdem A) : gmap φ hφ (P.shift k) = (gmap φ hφ P).shift k :=
  rfl

omit [SetLike.GradedMonoid B] in
theorem gmap_symm_map (P : GIdem A) :
    gmap φ.symm (mem_symm_iff φ hφ) (gmap φ hφ P) ≈ P :=
  MvN.of_equiv (Equiv.refl _) (gmap φ.symm (mem_symm_iff φ hφ) (gmap φ hφ P)).hom
    (gmap φ.symm (mem_symm_iff φ hφ) (gmap φ hφ P)).idem (fun _ => rfl)
    (fun i j => by simp [gmap])

/-- Transport of isomorphism classes along a graded ring isomorphism. -/
def gprojMap : GProj A →+ GProj B where
  toFun := Quotient.map (gmap φ hφ) fun _ _ h => (gmap_equiv_iff φ hφ).2 h
  map_zero' := GProj.mk_eq_mk.2 (gmap_zero φ hφ)
  map_add' := by
    refine GProj.ind fun P => GProj.ind fun Q => ?_
    exact GProj.mk_eq_mk.2 (gmap_sum φ hφ P Q)

theorem gprojMap_bijective : Function.Bijective (gprojMap φ hφ) := by
  refine ⟨fun x y => ?_, fun y => ?_⟩
  · induction x using GProj.ind with
    | h P =>
      induction y using GProj.ind with
      | h Q =>
        intro h
        exact GProj.mk_eq_mk.2 ((gmap_equiv_iff φ hφ).1 (GProj.mk_eq_mk.1 h))
  · induction y using GProj.ind with
    | h Q =>
      refine ⟨GProj.mk (gmap φ.symm (mem_symm_iff φ hφ) Q), GProj.mk_eq_mk.2 ?_⟩
      show gmap φ hφ (gmap φ.symm (mem_symm_iff φ hφ) Q) ≈ Q
      exact MvN.of_equiv (Equiv.refl _) (gmap φ hφ (gmap φ.symm (mem_symm_iff φ hφ) Q)).hom
        (gmap φ hφ (gmap φ.symm (mem_symm_iff φ hφ) Q)).idem (fun _ => rfl)
        (fun i j => by simp [gmap])

/-- Transport of isomorphism classes along a graded ring isomorphism, as an equivalence. -/
def gprojEquiv : GProj A ≃+ GProj B :=
  AddEquiv.ofBijective (gprojMap φ hφ) (gprojMap_bijective φ hφ)

/-- A graded ring isomorphism induces an isomorphism of graded `K₀`, as an additive map. -/
def k0EquivAdd : K0 A ≃+ K0 B :=
  GrothendieckGroup.mapEquiv (gprojEquiv φ hφ)

theorem k0EquivAdd_of (P : GIdem A) :
    k0EquivAdd φ hφ (K0.of P) = K0.of (gmap φ hφ P) :=
  GrothendieckGroup.mapEquiv_of _ _

theorem k0EquivAdd_shift (k : ℤ) (x : K0 A) :
    k0EquivAdd φ hφ (K0.shift k x) = K0.shift k (k0EquivAdd φ hφ x) := by
  have : (k0EquivAdd φ hφ).toAddMonoidHom.comp (K0.shift k) =
      (K0.shift k).comp (k0EquivAdd φ hφ).toAddMonoidHom :=
    K0.hom_ext fun P => by
      show k0EquivAdd φ hφ (K0.shift k (K0.of P)) =
        K0.shift k (k0EquivAdd φ hφ (K0.of P))
      rw [K0.shift_of, k0EquivAdd_of, k0EquivAdd_of, K0.shift_of, gmap_shift]
  exact DFunLike.congr_fun this x

/-- A graded ring isomorphism induces `K0 A ≃ₗ[ℤ[T;T⁻¹]] K0 B`. -/
def k0Equiv : K0 A ≃ₗ[LaurentPolynomial ℤ] K0 B :=
  (k0EquivAdd φ hφ).toLinearEquiv
    (K0.map_smul_of_shift (k0EquivAdd φ hφ).toAddMonoidHom fun k x => by
      rw [K0.T_smul]
      exact k0EquivAdd_shift φ hφ k x)

theorem k0Equiv_of (P : GIdem A) : k0Equiv φ hφ (K0.of P) = K0.of (gmap φ hφ P) :=
  k0EquivAdd_of φ hφ P

end Transport

/-! ### Diagonal graded idempotents -/

section Diag

variable {R : Type*} [Ring R] {A : ℤ → AddSubgroup R} [SetLike.GradedMonoid A] {e : R}

omit [SetLike.GradedMonoid A] in
theorem isHom_diagonal (he : e ∈ A 0) {ι : Type*} [DecidableEq ι] (t : ι → ℤ) :
    IsHom A t t (diagonal fun _ => e) := fun i j => by
  rw [diagonal_apply]
  split_ifs with h
  · subst h
    exact mem_of_deg_eq he (sub_self _).symm
  · exact zero_mem _

omit [SetLike.GradedMonoid A] in
theorem diagonal_idem (hee : e * e = e) {ι : Type*} [Fintype ι] [DecidableEq ι] :
    (diagonal fun _ : ι => e) * diagonal (fun _ => e) = diagonal fun _ => e := by
  rw [diagonal_mul_diagonal, hee]

/-- `diag(e, …, e)` on `R^m{t}`. -/
def gdiag (he : e ∈ A 0) (hee : e * e = e) {m : ℕ} (t : Fin m → ℤ) : GIdem A where
  n := m
  s := t
  e := diagonal fun _ => e
  hom := isHom_diagonal he t
  idem := diagonal_idem hee

/-- The graded projective module `Re{k}`. -/
def gelem (he : e ∈ A 0) (hee : e * e = e) (k : ℤ) : GIdem A := gdiag he hee fun _ : Fin 1 => k

theorem of_diag (he : e ∈ A 0) (hee : e * e = e) : ∀ {m : ℕ} (t : Fin m → ℤ),
    K0.of (gdiag he hee t) = ∑ a, K0.of (gelem he hee (t a))
  | 0, t => by
    rw [Finset.univ_eq_empty, Finset.sum_empty, ← K0.of_zero]
    exact K0.of_eq (MvN.of_equiv (Equiv.refl _) (gdiag he hee t).hom
      (gdiag he hee t).idem (fun i => i.elim0) (fun i => i.elim0))
  | m + 1, t => by
    have h : MvN A (Sum.elim (fun i => t (Fin.castSucc i)) fun _ : Fin 1 => t (Fin.last m))
        (fromBlocks (diagonal fun _ => e) 0 0 (diagonal fun _ => e)) t
        (diagonal fun _ => e) := by
      refine MvN.of_equiv finSumFinEquiv
        ((isHom_diagonal he _).fromBlocks IsHom.zero IsHom.zero (isHom_diagonal he _))
        (fromBlocks_idem (diagonal_idem hee) (diagonal_idem hee)) ?_ ?_
      · rintro (i | i)
        · rfl
        · obtain rfl : i = 0 := Subsingleton.elim _ _
          rfl
      · rintro (i | i) (j | j) <;>
          simp [diagonal_apply, Fin.ext_iff, Fin.castAdd, Fin.natAdd] <;> omega
    have h' : gdiag he hee t ≈ (gdiag he hee fun i => t (Fin.castSucc i)).sum
        (gelem he hee (t (Fin.last m))) :=
      MvN.trans (diagonal_idem hee) (fromBlocks_idem (diagonal_idem hee) (diagonal_idem hee))
        (GIdem.sum _ _).idem h.symm
        (GIdem.mvn_sum (gdiag he hee fun i => t (Fin.castSucc i))
          (gelem he hee (t (Fin.last m))))
    rw [K0.of_eq h', K0.of_sum, of_diag he hee, Fin.sum_univ_castSucc]

theorem T_smul_elem (he : e ∈ A 0) (hee : e * e = e) (a k : ℤ) :
    (T a : LaurentPolynomial ℤ) • K0.of (gelem he hee k) = K0.of (gelem he hee (k + a)) := by
  rw [K0.T_smul_of]
  exact K0.of_eq (MvN.of_equiv (Equiv.refl _) ((gelem he hee k).shift a).hom
    (gelem he hee k).idem (fun _ => rfl) (fun _ _ => rfl))

theorem of_elem (he : e ∈ A 0) (hee : e * e = e) (k : ℤ) :
    K0.of (gelem he hee k) = (T k : LaurentPolynomial ℤ) • K0.of (gelem he hee 0) := by
  rw [T_smul_elem, zero_add]

end Diag

/-! ### Split idempotents -/

section Splitting

variable {R : Type*} [Ring R] {A : ℤ → AddSubgroup R} [SetLike.GradedMonoid A]
  {P e : R} {I : Type*} [Fintype I] [DecidableEq I]

omit [SetLike.GradedMonoid A] in
/-- The row `(σᵢ)` and the column `(λᵢ)` realise `RP{k} ≅ ⊕ᵢ Re{k - dᵢ}`. -/
theorem mvn_splitting (S : Categorification.Splitting P e I) (dσ : I → ℤ)
    (hσ : ∀ i, S.σ i ∈ A (dσ i)) (hlam : ∀ i, S.lam i ∈ A (-dσ i)) (k : ℤ) :
    MvN A (fun _ : Fin 1 => k) (diagonal fun _ => P) (fun i => k - dσ i)
      (diagonal fun _ => e) :=
  ⟨S.row, S.col, fun _ i => mem_of_deg_eq (hσ i) (by ring),
    fun i _ => mem_of_deg_eq (hlam i) (by ring), S.row_mul_col, S.col_mul_row,
    by rw [S.diag_mul_row, S.row_mul_diag], by rw [S.diag_mul_col, S.col_mul_diag]⟩

/-- `[RP{k}] = ∑ᵢ T (k - dᵢ) • [Re]` in `K₀`. -/
theorem of_elem_splitting (hP : P ∈ A 0) (hPP : P * P = P) (he : e ∈ A 0) (hee : e * e = e)
    (S : Categorification.Splitting P e I) (dσ : I → ℤ)
    (hσ : ∀ i, S.σ i ∈ A (dσ i)) (hlam : ∀ i, S.lam i ∈ A (-dσ i)) (k : ℤ) :
    K0.of (gelem hP hPP k) =
      ∑ i, (T (k - dσ i) : LaurentPolynomial ℤ) • K0.of (gelem he hee 0) := by
  let σ := Fintype.equivFin I
  let Q : GIdem A := GIdem.ofEquiv (fun i => k - dσ i) (diagonal fun _ => e)
    (isHom_diagonal he _) (diagonal_idem hee) σ
  have hQ : Q = gdiag he hee fun j => k - dσ (σ.symm j) := by
    simp only [Q, GIdem.ofEquiv, gdiag, submatrix_diagonal_equiv]
    rfl
  have h : gelem hP hPP k ≈ Q :=
    MvN.trans (diagonal_idem hPP) (diagonal_idem hee) Q.idem (mvn_splitting S dσ hσ hlam k)
      (GIdem.mvn_ofEquiv _ _ _ _ σ)
  rw [K0.of_eq h, hQ, of_diag]
  simp_rw [of_elem he hee (k - _)]
  exact Equiv.sum_comp σ.symm (fun i => (T (k - dσ i) : LaurentPolynomial ℤ) •
    K0.of (gelem he hee 0))

end Splitting

end OddMath.Frontier.OddCategorification
