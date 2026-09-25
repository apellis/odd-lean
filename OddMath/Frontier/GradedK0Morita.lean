import OddMath.Frontier.GradedK0Basic
import Mathlib.Data.Matrix.Composition

/-!
# Graded Morita invariance of `K₀` for matrix rings

For shifts `d : κ → ℤ` the ring `Matrix κ κ R` is graded by `matGrading A d`:
`M` has degree `k` when `M a b ∈ A (k - d a + d b)`, i.e. `deg (E_ab r) = deg r + d a - d b`.
This is the graded endomorphism ring of `⊕ₐ R{-d a}` in the conventions of `GradedK0Basic`.

Flattening a block matrix (`Matrix.comp`) turns a graded idempotent `(n, s, E)` over
`Matrix κ κ R` into the graded idempotent on `Fin n × κ` with shifts `(i, a) ↦ s i - d a`
(`GIdem.flatten`). Flattening preserves and reflects Murray–von Neumann equivalence, is
additive and shift-equivariant, and is essentially surjective when `κ` is nonempty
(`GIdem.flatten_embed`). Hence `K0 (matGrading A d) ≃ K0 A` as `ℤ[T;T⁻¹]`-modules
(`K0.morita`), and the corner idempotent `E_aa` goes to `[R{-d a}]` (`K0.morita_corner`).
-/

noncomputable section
open Matrix

namespace OddMath.Frontier.GradedK0

variable {R : Type*} [Ring R] {κ : Type*}

variable (A : ℤ → AddSubgroup R) in
/-- The grading of `Matrix κ κ R` with `deg (E_ab r) = deg r + d a - d b`. -/
def matGrading (d : κ → ℤ) (k : ℤ) : AddSubgroup (Matrix κ κ R) where
  carrier := {M | ∀ a b, M a b ∈ A (k - d a + d b)}
  add_mem' hM hN a b := add_mem (hM a b) (hN a b)
  zero_mem' _ _ := zero_mem _
  neg_mem' hM a b := neg_mem (hM a b)

variable {A : ℤ → AddSubgroup R}

theorem mem_matGrading {d : κ → ℤ} {k : ℤ} {M : Matrix κ κ R} :
    M ∈ matGrading A d k ↔ ∀ a b, M a b ∈ A (k - d a + d b) := Iff.rfl

instance matGrading.gradedMonoid [SetLike.GradedMonoid A] [Fintype κ] [DecidableEq κ]
    (d : κ → ℤ) : SetLike.GradedMonoid (matGrading A d) where
  one_mem a b := by
    rw [one_apply]
    split_ifs with h
    · subst h
      exact mem_of_deg_eq SetLike.GradedOne.one_mem (by ring)
    · exact zero_mem _
  mul_mem _ _ _ _ hM hN a c := by
    rw [mul_apply]
    exact sum_mem fun b _ => mem_of_deg_eq (SetLike.GradedMul.mul_mem (hM a b) (hN b c)) (by ring)

/-! ### Flattening -/

section Flat

variable {ι ι' ι'' : Type*}

/-- Flattening a matrix of `κ × κ` blocks. -/
abbrev flat : Matrix ι ι' (Matrix κ κ R) ≃ Matrix (ι × κ) (ι' × κ) R :=
  Matrix.comp ι ι' κ κ R

theorem flat_mul [Fintype κ] [Fintype ι'] (U : Matrix ι ι' (Matrix κ κ R))
    (V : Matrix ι' ι'' (Matrix κ κ R)) : flat (U * V) = flat U * flat V := by
  ext ⟨i, a⟩ ⟨k, c⟩
  simp only [flat, comp_apply, mul_apply, Matrix.sum_apply, Fintype.sum_prod_type]

theorem isHom_flat_iff [Fintype κ] [DecidableEq κ] {d : κ → ℤ} {s : ι → ℤ}
    {t : ι' → ℤ} {U : Matrix ι ι' (Matrix κ κ R)} :
    IsHom (matGrading A d) s t U ↔
      IsHom A (fun x : ι × κ => s x.1 - d x.2) (fun y : ι' × κ => t y.1 - d y.2) (flat U) :=
  ⟨fun h x y => mem_of_deg_eq (h x.1 y.1 x.2 y.2) (by ring),
    fun h i j a b => mem_of_deg_eq (h (i, a) (j, b)) (by ring)⟩

theorem mvn_flat_iff [Fintype κ] [DecidableEq κ] [Fintype ι] [Fintype ι'] {d : κ → ℤ}
    {s : ι → ℤ} {t : ι' → ℤ} {E : Matrix ι ι (Matrix κ κ R)}
    {F : Matrix ι' ι' (Matrix κ κ R)} :
    MvN (matGrading A d) s E t F ↔
      MvN A (fun x : ι × κ => s x.1 - d x.2) (flat E) (fun y : ι' × κ => t y.1 - d y.2)
        (flat F) := by
  constructor
  · rintro ⟨u, v, hu, hv, h1, h2, h3, h4⟩
    exact ⟨flat u, flat v, isHom_flat_iff.1 hu, isHom_flat_iff.1 hv,
      by rw [← flat_mul, h1], by rw [← flat_mul, h2], by rw [← flat_mul, ← flat_mul, h3],
      by rw [← flat_mul, ← flat_mul, h4]⟩
  · rintro ⟨u, v, hu, hv, h1, h2, h3, h4⟩
    refine ⟨flat.symm u, flat.symm v, isHom_flat_iff.2 (by rwa [Equiv.apply_symm_apply]),
      isHom_flat_iff.2 (by rwa [Equiv.apply_symm_apply]), ?_, ?_, ?_, ?_⟩ <;>
    refine flat.injective ?_ <;>
    simp only [flat_mul, Equiv.apply_symm_apply, h1, h2, h3, h4]

end Flat

/-! ### Flattening graded idempotents -/

variable [Fintype κ] [DecidableEq κ] [SetLike.GradedMonoid A] {d : κ → ℤ}

namespace GIdem

/-- The graded idempotent over `R` underlying a graded idempotent over `Matrix κ κ R`. -/
def flatten (P : GIdem (matGrading A d)) : GIdem A :=
  ofEquiv (fun x : Fin P.n × κ => P.s x.1 - d x.2) (flat P.e) (isHom_flat_iff.1 P.hom)
    (by rw [← flat_mul, P.idem]) (Fintype.equivFin _)

omit [SetLike.GradedMonoid A] in
theorem flat_idem (P : GIdem (matGrading A d)) : flat P.e * flat P.e = flat P.e := by
  rw [← flat_mul, P.idem]

theorem mvn_flatten (P : GIdem (matGrading A d)) :
    MvN A (fun x : Fin P.n × κ => P.s x.1 - d x.2) (flat P.e) P.flatten.s P.flatten.e :=
  mvn_ofEquiv _ _ _ _ _

theorem flatten_equiv_iff {P Q : GIdem (matGrading A d)} : P.flatten ≈ Q.flatten ↔ P ≈ Q := by
  rw [equiv_def, equiv_def, mvn_flat_iff]
  constructor
  · intro h
    exact MvN.trans (flat_idem P) P.flatten.idem (flat_idem Q) (mvn_flatten P)
      (MvN.trans P.flatten.idem Q.flatten.idem (flat_idem Q) h (mvn_flatten Q).symm)
  · intro h
    exact MvN.trans P.flatten.idem (flat_idem P) Q.flatten.idem (mvn_flatten P).symm
      (MvN.trans (flat_idem P) (flat_idem Q) Q.flatten.idem h (mvn_flatten Q))

theorem flatten_zero : (zero : GIdem (matGrading A d)).flatten ≈ zero := by
  refine MvN.trans zero.flatten.idem (flat_idem zero) zero.idem (mvn_flatten zero).symm ?_
  let σ : Fin (zero : GIdem (matGrading A d)).n × κ ≃ Fin (zero : GIdem A).n :=
    ⟨fun x => x.1.elim0, fun x => x.elim0, fun x => x.1.elim0, fun x => x.elim0⟩
  exact MvN.of_equiv σ (isHom_flat_iff.1 zero.hom) (flat_idem zero)
    (fun x => x.1.elim0) (fun x => x.1.elim0)

theorem flatten_sum (P Q : GIdem (matGrading A d)) :
    (P.sum Q).flatten ≈ P.flatten.sum Q.flatten := by
  have i1 := flat_idem (P.sum Q)
  have i2 := fromBlocks_idem (flat_idem P) (flat_idem Q)
  have i3 := fromBlocks_idem P.flatten.idem Q.flatten.idem
  let σ : Fin (P.n + Q.n) × κ ≃ (Fin P.n × κ) ⊕ (Fin Q.n × κ) :=
    (Equiv.prodCongr finSumFinEquiv.symm (Equiv.refl κ)).trans (Equiv.sumProdDistrib _ _ _)
  have h : MvN A (fun x : Fin (P.n + Q.n) × κ => (P.sum Q).s x.1 - d x.2) (flat (P.sum Q).e)
      (Sum.elim (fun x : Fin P.n × κ => P.s x.1 - d x.2) fun x : Fin Q.n × κ => Q.s x.1 - d x.2)
      (fromBlocks (flat P.e) 0 0 (flat Q.e)) := by
    refine MvN.of_equiv σ (isHom_flat_iff.1 (P.sum Q).hom) i1 ?_ ?_
    · rintro ⟨i, a⟩
      show Sum.elim _ _ (Equiv.sumProdDistrib _ _ _ (finSumFinEquiv.symm i, a)) =
        Sum.elim P.s Q.s (finSumFinEquiv.symm i) - d a
      generalize finSumFinEquiv.symm i = y
      cases y <;> rfl
    · rintro ⟨i, a⟩ ⟨j, b⟩
      show fromBlocks (flat P.e) 0 0 (flat Q.e)
          (Equiv.sumProdDistrib _ _ _ (finSumFinEquiv.symm i, a))
          (Equiv.sumProdDistrib _ _ _ (finSumFinEquiv.symm j, b)) =
        fromBlocks P.e 0 0 Q.e (finSumFinEquiv.symm i) (finSumFinEquiv.symm j) a b
      generalize finSumFinEquiv.symm i = y
      generalize finSumFinEquiv.symm j = y'
      cases y <;> cases y' <;> rfl
  exact MvN.trans (P.sum Q).flatten.idem i1 (P.flatten.sum Q.flatten).idem
    (mvn_flatten (P.sum Q)).symm <|
    MvN.trans i1 i2 (P.flatten.sum Q.flatten).idem h <|
    MvN.trans i2 i3 (P.flatten.sum Q.flatten).idem (MvN.sum (mvn_flatten P) (mvn_flatten Q))
      (mvn_sum _ _)

theorem flatten_shift (k : ℤ) (P : GIdem (matGrading A d)) :
    (P.shift k).flatten ≈ P.flatten.shift k :=
  MvN.of_equiv (Equiv.refl _) (P.shift k).flatten.hom (P.shift k).flatten.idem
    (fun i => by simp only [flatten, ofEquiv, shift, Function.comp_apply, Equiv.refl_apply]; ring)
    (fun _ _ => rfl)

/-! ### Essential surjectivity -/

/-- The inclusion `R^n → R^n ⊗ R^κ` onto the `a₀` column. -/
def incl (n : ℕ) (a₀ : κ) : Matrix (Fin n) (Fin n × κ) R :=
  Matrix.of fun i x => if x = (i, a₀) then 1 else 0

/-- The projection `R^n ⊗ R^κ → R^n` from the `a₀` column. -/
def proj (n : ℕ) (a₀ : κ) : Matrix (Fin n × κ) (Fin n) R :=
  Matrix.of fun x i => if x = (i, a₀) then 1 else 0

omit [SetLike.GradedMonoid A] in
theorem incl_mul_proj (n : ℕ) (a₀ : κ) :
    incl n a₀ * proj n a₀ = (1 : Matrix (Fin n) (Fin n) R) := by
  ext i j
  simp only [incl, proj, mul_apply, of_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, one_apply, Prod.mk.injEq, and_true]

omit [Fintype κ] in
theorem isHom_incl {n : ℕ} (s : Fin n → ℤ) (a₀ : κ) :
    IsHom A s (fun x : Fin n × κ => s x.1 + d a₀ - d x.2) (incl n a₀) := by
  intro i x
  simp only [incl, of_apply]
  split_ifs with h
  · subst h
    exact mem_of_deg_eq SetLike.GradedOne.one_mem (by ring)
  · exact zero_mem _

omit [Fintype κ] in
theorem isHom_proj {n : ℕ} (s : Fin n → ℤ) (a₀ : κ) :
    IsHom A (fun x : Fin n × κ => s x.1 + d a₀ - d x.2) s (proj n a₀) := by
  intro x i
  simp only [proj, of_apply]
  split_ifs with h
  · subst h
    exact mem_of_deg_eq SetLike.GradedOne.one_mem (by ring)
  · exact zero_mem _

variable (d) in
/-- A graded idempotent over `R`, placed in the `a₀` corner of `Matrix κ κ R`. -/
def embed (a₀ : κ) (Q : GIdem A) : GIdem (matGrading A d) where
  n := Q.n
  s i := Q.s i + d a₀
  e := flat.symm (proj Q.n a₀ * Q.e * incl Q.n a₀)
  hom := isHom_flat_iff.2 (by
    rw [Equiv.apply_symm_apply]
    exact ((isHom_proj Q.s a₀).mul Q.hom).mul (isHom_incl Q.s a₀))
  idem := flat.injective (by
    rw [flat_mul, Equiv.apply_symm_apply, Matrix.mul_assoc (proj Q.n a₀ * Q.e),
      ← Matrix.mul_assoc (incl Q.n a₀) (proj Q.n a₀ * Q.e),
      ← Matrix.mul_assoc (incl Q.n a₀) (proj Q.n a₀), incl_mul_proj, Matrix.one_mul,
      ← Matrix.mul_assoc (proj Q.n a₀ * Q.e) Q.e, Matrix.mul_assoc (proj Q.n a₀) Q.e Q.e,
      Q.idem])

theorem flatten_embed (a₀ : κ) (Q : GIdem A) : (embed d a₀ Q).flatten ≈ Q := by
  have hJ := incl_mul_proj (R := R) Q.n a₀
  have h : MvN A (fun x : Fin Q.n × κ => Q.s x.1 + d a₀ - d x.2)
      (proj Q.n a₀ * Q.e * incl Q.n a₀) Q.s Q.e := by
    refine ⟨proj Q.n a₀ * Q.e, Q.e * incl Q.n a₀, (isHom_proj Q.s a₀).mul Q.hom,
      Q.hom.mul (isHom_incl Q.s a₀), ?_, ?_, ?_, ?_⟩
    · rw [Matrix.mul_assoc, ← Matrix.mul_assoc Q.e, Q.idem, ← Matrix.mul_assoc]
    · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (incl Q.n a₀), hJ, Matrix.one_mul, Q.idem]
    · simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (incl Q.n a₀), hJ, Matrix.one_mul, Q.idem, Q.idem]
    · simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (incl Q.n a₀), hJ, Matrix.one_mul, ← Matrix.mul_assoc Q.e Q.e,
        Q.idem, ← Matrix.mul_assoc Q.e Q.e, Q.idem]
  exact MvN.trans (embed d a₀ Q).flatten.idem (flat_idem _) Q.idem (mvn_flatten _).symm h

variable (d) in
/-- The corner idempotent `E_aa` of `Matrix κ κ R`, as a graded idempotent of rank one. -/
def corner (a : κ) : GIdem (matGrading A d) where
  n := 1
  s _ := 0
  e := Matrix.of fun _ _ => stdBasisMatrix a a 1
  hom _ _ b c := by
    simp only [of_apply, stdBasisMatrix]
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h
      exact mem_of_deg_eq SetLike.GradedOne.one_mem (by ring)
    · exact zero_mem _
  idem := by
    ext i j : 2
    simp [mul_apply]

theorem corner_equiv_embed (a : κ) : corner d a ≈ embed d a (single (A := A) (-d a)) := by
  refine MvN.of_equiv (Equiv.refl _) (corner d a).hom (corner d a).idem
    (fun _ => neg_add_cancel _) (fun i j => ?_)
  obtain ⟨i, hi⟩ := i
  obtain ⟨j, hj⟩ := j
  obtain rfl : i = 0 := Nat.lt_one_iff.1 hi
  obtain rfl : j = 0 := Nat.lt_one_iff.1 hj
  ext b c
  show (proj 1 a * (1 : Matrix (Fin 1) (Fin 1) R) * incl 1 a :
      Matrix (Fin 1 × κ) (Fin 1 × κ) R) (0, b) (0, c) = stdBasisMatrix a a (1 : R) b c
  rw [Matrix.mul_one, mul_apply, Fin.sum_univ_one]
  simp only [proj, incl, of_apply, stdBasisMatrix, Prod.mk.injEq, true_and]
  rcases eq_or_ne b a with rfl | hb <;> rcases eq_or_ne c b with rfl | hc <;>
    simp_all [Ne.symm]

end GIdem

/-! ### `K₀` -/

namespace GProj

/-- Flattening on isomorphism classes. -/
def flatten : GProj (matGrading A d) →+ GProj A where
  toFun := Quotient.map GIdem.flatten fun _ _ h => GIdem.flatten_equiv_iff.2 h
  map_zero' := mk_eq_mk.2 GIdem.flatten_zero
  map_add' := by
    refine ind fun P => ind fun Q => ?_
    exact mk_eq_mk.2 (GIdem.flatten_sum P Q)

theorem flatten_mk (P : GIdem (matGrading A d)) : flatten (mk P) = mk P.flatten := rfl

theorem flatten_bijective [Nonempty κ] : Function.Bijective (flatten (A := A) (d := d)) := by
  refine ⟨fun x y => ?_, fun y => ?_⟩
  · induction x using ind with
    | h P =>
      induction y using ind with
      | h Q =>
        intro h
        exact mk_eq_mk.2 (GIdem.flatten_equiv_iff.1 (mk_eq_mk.1 h))
  · induction y using ind with
    | h Q =>
      exact ⟨mk (GIdem.embed d (Classical.arbitrary κ) Q),
        mk_eq_mk.2 (GIdem.flatten_embed _ Q)⟩

/-- Graded Morita equivalence on isomorphism classes. -/
def moritaEquiv [Nonempty κ] : GProj (matGrading A d) ≃+ GProj A :=
  AddEquiv.ofBijective flatten flatten_bijective

end GProj

namespace K0

/-- Graded Morita equivalence on `K₀`, as an additive isomorphism. -/
def moritaAdd [Nonempty κ] : K0 (matGrading A d) ≃+ K0 A :=
  GrothendieckGroup.mapEquiv GProj.moritaEquiv

theorem moritaAdd_of [Nonempty κ] (P : GIdem (matGrading A d)) :
    moritaAdd (of P) = of P.flatten :=
  GrothendieckGroup.mapEquiv_of _ _

theorem moritaAdd_shift [Nonempty κ] (k : ℤ) (x : K0 (matGrading A d)) :
    moritaAdd (shift k x) = shift k (moritaAdd x) := by
  have : (moritaAdd (A := A) (d := d)).toAddMonoidHom.comp (shift k) =
      (shift k).comp moritaAdd.toAddMonoidHom :=
    hom_ext fun P => by
      show moritaAdd (shift k (of P)) = shift k (moritaAdd (of P))
      rw [shift_of, moritaAdd_of, moritaAdd_of, shift_of]
      exact of_eq (GIdem.flatten_shift k P)
  exact DFunLike.congr_fun this x

/-- Graded Morita invariance: `K₀ (Mat_κ(R){d}) ≃ K₀ R` as `ℤ[T;T⁻¹]`-modules. -/
def morita [Nonempty κ] : K0 (matGrading A d) ≃ₗ[LaurentPolynomial ℤ] K0 A :=
  moritaAdd.toLinearEquiv
    (map_smul_of_shift moritaAdd.toAddMonoidHom fun k x => by
      rw [T_smul]
      exact moritaAdd_shift k x)

theorem morita_of [Nonempty κ] (P : GIdem (matGrading A d)) :
    morita (of P) = of P.flatten := moritaAdd_of P

/-- The corner idempotent `E_aa` corresponds to `R{-d a}`. -/
theorem morita_corner [Nonempty κ] (a : κ) :
    morita (of (GIdem.corner d a : GIdem (matGrading A d))) = of (GIdem.single (-d a)) := by
  rw [of_eq (GIdem.corner_equiv_embed a), morita_of]
  exact of_eq (GIdem.flatten_embed a _)

end K0

end OddMath.Frontier.GradedK0
