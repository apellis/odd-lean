import OddMath.Frontier.GradedK0
import Mathlib.Algebra.Ring.NegOnePow

/-!
# Induction of graded idempotents along a super pair

EKL arXiv:1111.1320v1, §6, pp. 46–47: the inclusions `ONH_a ⊗ ONH_b ⊂ ONH_{a+b}` give rise to
induction functors on graded projectives. This file treats the general situation: graded rings
`R₁`, `R₂`, `S` (gradings `A₁`, `A₂`, `B`) with graded ring maps `ι₁ : R₁ → S`, `ι₂ : R₂ → S`
whose images supercommute (`SuperPair`): all degrees are even, and for `x ∈ A₁ (2i)`,
`y ∈ A₂ (2j)`, `ι₂ y · ι₁ x = (-1)^{ij} ι₁ x · ι₂ y` (the super-degree of an element of degree
`2i` is `i mod 2`, as for dots of degree `2` and crossings of degree `-2`).

* `SuperPair.kron`: the super-Kronecker product of matrices,
  `(u ⊠ v)_{(i,k),(j,l)} = (-1)^{(⌊s'_k/2⌋ + ⌊t'_l/2⌋)⌊t_j/2⌋} ι₁(u_{ij}) ι₂(v_{kl})` for
  `u : (ι, s) → (κ, t)` and `v : (ι', s') → (κ', t')`; the Koszul sign makes it multiplicative
  (`kron_mul`), so it carries graded idempotents to graded idempotents.
* `SuperPair.ind : GIdem A₁ → GIdem A₂ → GIdem B`, the induction `P ⊠ Q ↦ S ⊗_{R₁ ⊗ R₂} (P ⊠ Q)`
  on the level of idempotents: `(n, s, e) ⊠ (m, t, f) = (nm, s + t, e ⊠ f)`. It respects
  Murray–von Neumann equivalence (`ind_congr`), block sums in each variable (`ind_sum_left`,
  `ind_sum_right`) and shifts (`ind_shift_left`, `ind_shift_right`; for the left variable the
  two idempotents differ by a diagonal sign conjugation).
* `SuperPair.indK0 : K₀(A₁) →ₗ K₀(A₂) →ₗ K₀(B)`, `ℤ[q,q⁻¹]`-bilinear, `[P] ⊗ [Q] ↦ [ind P Q]`.
-/

noncomputable section
open Matrix

namespace OddMath.Frontier.OddBialgebra
open GradedK0

/-- The parity index `⌊s/2⌋` of a shift `s`. -/
abbrev par (s : ℤ) : ℤ := s / 2

variable {R₁ R₂ S : Type*} [Ring R₁] [Ring R₂] [Ring S]

/-- Graded ring maps `ι₁ : R₁ → S`, `ι₂ : R₂ → S` with supercommuting images; all degrees even. -/
structure SuperPair (A₁ : ℤ → AddSubgroup R₁) (A₂ : ℤ → AddSubgroup R₂)
    (B : ℤ → AddSubgroup S) where
  /-- The left factor. -/
  ι₁ : R₁ →+* S
  /-- The right factor. -/
  ι₂ : R₂ →+* S
  map₁ : ∀ {d : ℤ} {x : R₁}, x ∈ A₁ d → ι₁ x ∈ B d
  map₂ : ∀ {d : ℤ} {y : R₂}, y ∈ A₂ d → ι₂ y ∈ B d
  even₁ : ∀ {d : ℤ} {x : R₁}, x ∈ A₁ d → x ≠ 0 → Even d
  even₂ : ∀ {d : ℤ} {y : R₂}, y ∈ A₂ d → y ≠ 0 → Even d
  comm : ∀ {i j : ℤ} {x : R₁} {y : R₂}, x ∈ A₁ (2 * i) → y ∈ A₂ (2 * j) →
    ι₂ y * ι₁ x = (i * j).negOnePow • (ι₁ x * ι₂ y)

variable {A₁ : ℤ → AddSubgroup R₁} {A₂ : ℤ → AddSubgroup R₂} {B : ℤ → AddSubgroup S}

theorem intCast_mem [SetLike.GradedMonoid B] (z : ℤ) : (z : S) ∈ B 0 := by
  rw [← zsmul_one]
  exact zsmul_mem SetLike.GradedOne.one_mem z

theorem units_smul_mem {d : ℤ} (u : ℤˣ) {z : S} (hz : z ∈ B d) : u • z ∈ B d := by
  rw [Units.smul_def]
  exact zsmul_mem hz _

namespace SuperPair

variable (P : SuperPair A₁ A₂ B)

theorem comm' {a b c e : ℤ} {x : R₁} {y : R₂} (hx : x ∈ A₁ (a - b)) (hy : y ∈ A₂ (c - e)) :
    P.ι₂ y * P.ι₁ x = ((par c - par e) * (par a - par b)).negOnePow • (P.ι₁ x * P.ι₂ y) := by
  by_cases hx0 : x = 0
  · simp [hx0]
  by_cases hy0 : y = 0
  · simp [hy0]
  obtain ⟨m, hm⟩ := P.even₁ hx hx0
  obtain ⟨m', hm'⟩ := P.even₂ hy hy0
  have h1 : a - b = 2 * (par a - par b) := by simp only [par]; omega
  have h2 : c - e = 2 * (par c - par e) := by simp only [par]; omega
  rw [h1] at hx
  rw [h2] at hy
  rw [P.comm hx hy, mul_comm (par c - par e)]

/-! ### The super-Kronecker product -/

section Kron

variable {ι κ μ ι' κ' μ' : Type*}

/-- The super-Kronecker product of `u : (ι, s) → (κ, t)` over `R₁` and
`v : (ι', s') → (κ', t')` over `R₂`. -/
def kron (t : κ → ℤ) (s' : ι' → ℤ) (t' : κ' → ℤ) (u : Matrix ι κ R₁) (v : Matrix ι' κ' R₂) :
    Matrix (ι × ι') (κ × κ') S :=
  fun x y => ((par (s' x.2) + par (t' y.2)) * par (t y.1)).negOnePow •
    (P.ι₁ (u x.1 y.1) * P.ι₂ (v x.2 y.2))

theorem kron_apply (t : κ → ℤ) (s' : ι' → ℤ) (t' : κ' → ℤ) (u : Matrix ι κ R₁)
    (v : Matrix ι' κ' R₂) (i : ι) (k : ι') (j : κ) (l : κ') :
    P.kron t s' t' u v (i, k) (j, l) = ((par (s' k) + par (t' l)) * par (t j)).negOnePow •
      (P.ι₁ (u i j) * P.ι₂ (v k l)) := rfl

theorem kron_hom [SetLike.GradedMonoid B] {s : ι → ℤ} {t : κ → ℤ} {s' : ι' → ℤ} {t' : κ' → ℤ}
    {u : Matrix ι κ R₁} {v : Matrix ι' κ' R₂} (hu : IsHom A₁ s t u) (hv : IsHom A₂ s' t' v) :
    IsHom B (fun x => s x.1 + s' x.2) (fun y => t y.1 + t' y.2) (P.kron t s' t' u v) := by
  rintro ⟨i, k⟩ ⟨j, l⟩
  refine units_smul_mem _ (mem_of_deg_eq (SetLike.GradedMul.mul_mem (P.map₁ (hu i j))
    (P.map₂ (hv k l))) ?_)
  simp only
  ring

theorem kron_mul [Fintype κ] [Fintype κ'] {t : κ → ℤ} {r : μ → ℤ} {s' : ι' → ℤ}
    {t' : κ' → ℤ} {r' : μ' → ℤ} {u : Matrix ι κ R₁} {u' : Matrix κ μ R₁}
    {v : Matrix ι' κ' R₂} {v' : Matrix κ' μ' R₂} (hu' : IsHom A₁ t r u')
    (hv : IsHom A₂ s' t' v) :
    P.kron t s' t' u v * P.kron r t' r' u' v' = P.kron r s' r' (u * u') (v * v') := by
  ext ⟨i, k⟩ ⟨j, l⟩
  rw [Matrix.mul_apply, Fintype.sum_prod_type, kron_apply, Matrix.mul_apply, Matrix.mul_apply,
    map_sum, map_sum, Finset.sum_mul_sum]
  simp only [Finset.smul_sum]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  rw [kron_apply, kron_apply, smul_mul_smul_comm, map_mul, map_mul]
  have hc := P.comm' (hu' p j) (hv k q)
  have e1 : P.ι₁ (u i p) * P.ι₂ (v k q) * (P.ι₁ (u' p j) * P.ι₂ (v' q l)) =
      P.ι₁ (u i p) * (P.ι₂ (v k q) * P.ι₁ (u' p j)) * P.ι₂ (v' q l) := by
    simp only [mul_assoc]
  rw [e1, hc, mul_smul_comm, smul_mul_assoc, smul_smul]
  have e2 : P.ι₁ (u i p) * (P.ι₁ (u' p j) * P.ι₂ (v k q)) * P.ι₂ (v' q l) =
      P.ι₁ (u i p) * P.ι₁ (u' p j) * (P.ι₂ (v k q) * P.ι₂ (v' q l)) := by
    simp only [mul_assoc]
  rw [e2]
  congr 1
  rw [← Int.negOnePow_add, ← Int.negOnePow_add, Int.negOnePow_eq_iff]
  exact ⟨par (s' k) * par (t p) + par (t' q) * par (r j) - par (s' k) * par (r j), by ring⟩

theorem kron_zero_left (t : κ → ℤ) (s' : ι' → ℤ) (t' : κ' → ℤ) (v : Matrix ι' κ' R₂) :
    P.kron t s' t' (0 : Matrix ι κ R₁) v = 0 := by
  ext x y
  simp [kron]

theorem kron_zero_right (t : κ → ℤ) (s' : ι' → ℤ) (t' : κ' → ℤ) (u : Matrix ι κ R₁) :
    P.kron t s' t' u (0 : Matrix ι' κ' R₂) = 0 := by
  ext x y
  simp [kron]

end Kron

/-! ### Murray–von Neumann equivalence -/

section MvN

variable {ι κ ι' κ' : Type*} [Fintype ι] [Fintype κ] [Fintype ι'] [Fintype κ']

theorem kron_idem {s : ι → ℤ} {s' : ι' → ℤ} {e : Matrix ι ι R₁} {f : Matrix ι' ι' R₂}
    (he : IsHom A₁ s s e) (hf : IsHom A₂ s' s' f) (hee : e * e = e) (hff : f * f = f) :
    P.kron s s' s' e f * P.kron s s' s' e f = P.kron s s' s' e f := by
  rw [P.kron_mul he hf, hee, hff]

theorem mvn_kron [SetLike.GradedMonoid A₁] [SetLike.GradedMonoid A₂] [SetLike.GradedMonoid B]
    {s : ι → ℤ} {e : Matrix ι ι R₁} {s₂ : κ → ℤ} {e₂ : Matrix κ κ R₁}
    {t : ι' → ℤ} {f : Matrix ι' ι' R₂} {t₂ : κ' → ℤ} {f₂ : Matrix κ' κ' R₂}
    (h : MvN A₁ s e s₂ e₂) (h' : MvN A₂ t f t₂ f₂) :
    MvN B (fun x => s x.1 + t x.2) (P.kron s t t e f) (fun x => s₂ x.1 + t₂ x.2)
      (P.kron s₂ t₂ t₂ e₂ f₂) := by
  obtain ⟨u, v, hu, hv, h1, h2, h3, h4⟩ := h
  obtain ⟨u', v', hu', hv', h1', h2', h3', h4'⟩ := h'
  refine ⟨P.kron s₂ t t₂ u u', P.kron s t₂ t v v', P.kron_hom hu hu', P.kron_hom hv hv', ?_, ?_,
    ?_, ?_⟩
  · rw [P.kron_mul hv hu', h1, h1']
  · rw [P.kron_mul hu hv', h2, h2']
  · have hf : IsHom A₂ t t f := h1' ▸ hu'.mul hv'
    have he₂ : IsHom A₁ s₂ s₂ e₂ := h2 ▸ hv.mul hu
    rw [P.kron_mul hu hf, P.kron_mul he₂ (hf.mul hu'), h3, h3']
  · have he : IsHom A₁ s s e := h1 ▸ hu.mul hv
    have hf₂ : IsHom A₂ t₂ t₂ f₂ := h2' ▸ hv'.mul hu'
    rw [P.kron_mul hv hf₂, P.kron_mul he (hf₂.mul hv'), h4, h4']

/-- Conjugation by a diagonal sign matrix is a Murray–von Neumann equivalence. -/
theorem mvn_signConj [SetLike.GradedMonoid B] [DecidableEq ι] {s : ι → ℤ}
    {e e' : Matrix ι ι S} (D : ι → ℤ) (he : IsHom B s s e) (hee : e * e = e)
    (h : ∀ i j, e' i j = (D i + D j).negOnePow • e i j) : MvN B s e s e' := by
  let d : Matrix ι ι S := diagonal fun i => (((D i).negOnePow : ℤ) : S)
  have hd : d * d = 1 := by
    rw [diagonal_mul_diagonal, ← Matrix.diagonal_one]
    refine congrArg diagonal (funext fun i => ?_)
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  have he' : e' = d * e * d := by
    ext i j
    have := (Int.cast_commute (((D j).negOnePow : ℤ)) (e i j)).eq
    rw [h, mul_diagonal, diagonal_mul, Int.negOnePow_add, Units.smul_def, zsmul_eq_mul]
    push_cast
    rw [mul_assoc, this, ← mul_assoc]
  have hdh : IsHom B s s d := by
    intro i j
    simp only [d, diagonal_apply]
    split_ifs with hij
    · subst hij
      rw [sub_self]
      exact intCast_mem _
    · exact zero_mem _
  have k1 : ∀ X : Matrix ι ι S, d * (d * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hd, Matrix.one_mul]
  have k2 : ∀ X : Matrix ι ι S, e * (e * X) = e * X := fun X => by rw [← Matrix.mul_assoc, hee]
  refine ⟨e * d, d * e, he.mul hdh, hdh.mul he, ?_, ?_, ?_, ?_⟩
  · simp only [Matrix.mul_assoc, k1, hee]
  · simp only [he', Matrix.mul_assoc, k2]
  · simp only [he', Matrix.mul_assoc, k1, k2]
  · simp only [he', Matrix.mul_assoc, k1, k2, hee]

end MvN

theorem kron_shift_right {ι κ ι' κ' : Type*} {s' : ι' → ℤ} {t' : κ' → ℤ} (t : κ → ℤ)
    (u : Matrix ι κ R₁) {v : Matrix ι' κ' R₂} (hv : IsHom A₂ s' t' v) (b : ℤ) :
    P.kron t (fun k => s' k + b) (fun l => t' l + b) u v = P.kron t s' t' u v := by
  ext ⟨i, k⟩ ⟨j, l⟩
  rw [kron_apply, kron_apply]
  by_cases hz : v k l = 0
  · simp [hz]
  have hev := P.even₂ (hv k l) hz
  have hδ : par (s' k + b) - par (s' k) = par (t' l + b) - par (t' l) := by
    obtain ⟨m, hm⟩ := hev
    simp only [par]
    omega
  congr 1
  rw [Int.negOnePow_eq_iff]
  exact ⟨(par (s' k + b) - par (s' k)) * par (t j), by linear_combination (-par (t j)) * hδ⟩

/-! ### Induction of graded idempotents -/

section Ind

variable [SetLike.GradedMonoid A₁] [SetLike.GradedMonoid A₂] [SetLike.GradedMonoid B]

/-- Induction on graded idempotents: `(n, s, e) ⊠ (m, t, f) = (nm, s + t, e ⊠ f)`, the graded
projective `S ⊗_{R₁ ⊗ R₂} (R₁^n{s} e ⊠ R₂^m{t} f)`. -/
def ind (X : GIdem A₁) (Y : GIdem A₂) : GIdem B :=
  GIdem.ofEquiv (fun x => X.s x.1 + Y.s x.2) (P.kron X.s Y.s Y.s X.e Y.e) (P.kron_hom X.hom Y.hom)
    (P.kron_idem X.hom Y.hom X.idem Y.idem) finProdFinEquiv

omit [SetLike.GradedMonoid A₁] [SetLike.GradedMonoid A₂] in
theorem mvn_ind (X : GIdem A₁) (Y : GIdem A₂) :
    MvN B (fun x => X.s x.1 + Y.s x.2) (P.kron X.s Y.s Y.s X.e Y.e) (P.ind X Y).s (P.ind X Y).e :=
  GIdem.mvn_ofEquiv _ _ _ _ _

omit [SetLike.GradedMonoid A₁] [SetLike.GradedMonoid A₂] in
theorem mvn_ind' (X : GIdem A₁) (Y : GIdem A₂) (s : Fin X.n × Fin Y.n → ℤ)
    (hs : ∀ x, s x = X.s x.1 + Y.s x.2) :
    MvN B s (P.kron X.s Y.s Y.s X.e Y.e) (P.ind X Y).s (P.ind X Y).e := by
  obtain rfl : s = fun x => X.s x.1 + Y.s x.2 := funext hs
  exact P.mvn_ind X Y

theorem ind_congr {X X' : GIdem A₁} {Y Y' : GIdem A₂} (h : X ≈ X') (h' : Y ≈ Y') :
    P.ind X Y ≈ P.ind X' Y' :=
  MvN.trans (P.ind X Y).idem (P.kron_idem X.hom Y.hom X.idem Y.idem) (P.ind X' Y').idem
    (P.mvn_ind X Y).symm (MvN.trans (P.kron_idem X.hom Y.hom X.idem Y.idem)
      (P.kron_idem X'.hom Y'.hom X'.idem Y'.idem) (P.ind X' Y').idem (P.mvn_kron h h')
      (P.mvn_ind X' Y'))

/-- Induction is additive in the first variable. -/
theorem ind_sum_left (X X' : GIdem A₁) (Y : GIdem A₂) :
    P.ind (X.sum X') Y ≈ (P.ind X Y).sum (P.ind X' Y) := by
  have hb := X.hom.fromBlocks IsHom.zero IsHom.zero X'.hom
  have ib := fromBlocks_idem X.idem X'.idem
  have i1 := P.kron_idem (X.sum X').hom Y.hom (X.sum X').idem Y.idem
  have i2 := P.kron_idem hb Y.hom ib Y.idem
  have i3 := fromBlocks_idem (P.kron_idem X.hom Y.hom X.idem Y.idem)
    (P.kron_idem X'.hom Y.hom X'.idem Y.idem)
  have i4 := fromBlocks_idem (P.ind X Y).idem (P.ind X' Y).idem
  have h2 := P.mvn_kron (GIdem.mvn_sum X X').symm (MvN.refl Y.hom Y.idem)
  have h3 : MvN B (fun x => Sum.elim X.s X'.s x.1 + Y.s x.2)
      (P.kron (Sum.elim X.s X'.s) Y.s Y.s (fromBlocks X.e 0 0 X'.e) Y.e)
      (Sum.elim (fun x => X.s x.1 + Y.s x.2) (fun x => X'.s x.1 + Y.s x.2))
      (fromBlocks (P.kron X.s Y.s Y.s X.e Y.e) 0 0 (P.kron X'.s Y.s Y.s X'.e Y.e)) := by
    refine MvN.of_equiv (Equiv.sumProdDistrib _ _ _) (P.kron_hom hb Y.hom) i2 ?_ ?_
    · rintro ⟨i | i, k⟩ <;> rfl
    · rintro ⟨i | i, k⟩ ⟨j | j, l⟩ <;> simp [kron_apply]
  exact MvN.trans (P.ind _ Y).idem i1 (GIdem.sum _ _).idem (P.mvn_ind _ Y).symm <|
    MvN.trans i1 i2 (GIdem.sum _ _).idem h2 <| MvN.trans i2 i3 (GIdem.sum _ _).idem h3 <|
    MvN.trans i3 i4 (GIdem.sum _ _).idem (MvN.sum (P.mvn_ind X Y) (P.mvn_ind X' Y))
      (GIdem.mvn_sum _ _)

/-- Induction is additive in the second variable. -/
theorem ind_sum_right (X : GIdem A₁) (Y Y' : GIdem A₂) :
    P.ind X (Y.sum Y') ≈ (P.ind X Y).sum (P.ind X Y') := by
  have hb := Y.hom.fromBlocks IsHom.zero IsHom.zero Y'.hom
  have ib := fromBlocks_idem Y.idem Y'.idem
  have i1 := P.kron_idem X.hom (Y.sum Y').hom X.idem (Y.sum Y').idem
  have i2 := P.kron_idem X.hom hb X.idem ib
  have i3 := fromBlocks_idem (P.kron_idem X.hom Y.hom X.idem Y.idem)
    (P.kron_idem X.hom Y'.hom X.idem Y'.idem)
  have i4 := fromBlocks_idem (P.ind X Y).idem (P.ind X Y').idem
  have h2 := P.mvn_kron (MvN.refl X.hom X.idem) (GIdem.mvn_sum Y Y').symm
  have h3 : MvN B (fun x => X.s x.1 + Sum.elim Y.s Y'.s x.2)
      (P.kron X.s (Sum.elim Y.s Y'.s) (Sum.elim Y.s Y'.s) X.e (fromBlocks Y.e 0 0 Y'.e))
      (Sum.elim (fun x => X.s x.1 + Y.s x.2) (fun x => X.s x.1 + Y'.s x.2))
      (fromBlocks (P.kron X.s Y.s Y.s X.e Y.e) 0 0 (P.kron X.s Y'.s Y'.s X.e Y'.e)) := by
    refine MvN.of_equiv (Equiv.prodSumDistrib _ _ _) (P.kron_hom X.hom hb) i2 ?_ ?_
    · rintro ⟨i, k | k⟩ <;> rfl
    · rintro ⟨i, k | k⟩ ⟨j, l | l⟩ <;> simp [kron_apply]
  exact MvN.trans (P.ind X _).idem i1 (GIdem.sum _ _).idem (P.mvn_ind X _).symm <|
    MvN.trans i1 i2 (GIdem.sum _ _).idem h2 <| MvN.trans i2 i3 (GIdem.sum _ _).idem h3 <|
    MvN.trans i3 i4 (GIdem.sum _ _).idem (MvN.sum (P.mvn_ind X Y) (P.mvn_ind X Y'))
      (GIdem.mvn_sum _ _)

omit [SetLike.GradedMonoid A₁] [SetLike.GradedMonoid A₂] in
/-- Induction commutes with the shift of the second variable. -/
theorem ind_shift_right (k : ℤ) (X : GIdem A₁) (Y : GIdem A₂) :
    P.ind X (Y.shift k) ≈ (P.ind X Y).shift k := by
  refine MvN.of_equiv (Equiv.refl _) (P.ind X (Y.shift k)).hom (P.ind X (Y.shift k)).idem
    (fun i => ?_) (fun i j => ?_)
  · simp only [ind, GIdem.ofEquiv, GIdem.shift, Function.comp_apply, Equiv.refl_apply]
    ring
  · simp only [ind, GIdem.ofEquiv, GIdem.shift, Equiv.refl_apply, submatrix_apply]
    rw [P.kron_shift_right X.s X.e Y.hom k]

omit [SetLike.GradedMonoid A₁] [SetLike.GradedMonoid A₂] in
/-- Induction commutes with the shift of the first variable, up to a diagonal sign
conjugation. -/
theorem ind_shift_left (k : ℤ) (X : GIdem A₁) (Y : GIdem A₂) :
    P.ind (X.shift k) Y ≈ (P.ind X Y).shift k := by
  let sA : Fin X.n × Fin Y.n → ℤ := fun x => X.s x.1 + Y.s x.2 + k
  have i0 := P.kron_idem X.hom Y.hom X.idem Y.idem
  have i1 := P.kron_idem (X.shift k).hom Y.hom X.idem Y.idem
  have h1 : MvN B sA (P.kron (X.shift k).s Y.s Y.s X.e Y.e) (P.ind (X.shift k) Y).s
      (P.ind (X.shift k) Y).e :=
    P.mvn_ind' (X.shift k) Y sA fun x => by simp only [sA, GIdem.shift]; ring
  have h2 : MvN B sA (P.kron X.s Y.s Y.s X.e Y.e) sA (P.kron (X.shift k).s Y.s Y.s X.e Y.e) := by
    refine mvn_signConj (fun x => (par (X.s x.1 + k) - par (X.s x.1)) * par (Y.s x.2))
      ((P.kron_hom X.hom Y.hom).shift k) i0 ?_
    rintro ⟨i, a⟩ ⟨j, b⟩
    rw [kron_apply, kron_apply, smul_smul, ← Int.negOnePow_add]
    by_cases hz : X.e i j = 0
    · simp [hz]
    have hc : par (X.s i + k) - par (X.s i) = par (X.s j + k) - par (X.s j) := by
      obtain ⟨m, hm⟩ := P.even₁ (X.hom i j) hz
      simp only [par]
      omega
    congr 2
    simp only [GIdem.shift]
    linear_combination (-par (Y.s a)) * hc
  exact MvN.trans (P.ind _ Y).idem i1 (GIdem.shift k _).idem h1.symm <|
    MvN.trans i1 i0 (GIdem.shift k _).idem h2.symm ((P.mvn_ind X Y).shift k)

end Ind

/-! ### Induction on `K₀` -/

section K0

variable [SetLike.GradedMonoid A₁] [SetLike.GradedMonoid A₂] [SetLike.GradedMonoid B]

/-- `[P] ↦ [ind P Q]` on isomorphism classes, for fixed `Q`. -/
def indProj (Y : GIdem A₂) : GProj A₁ →+ K0 B :=
  AddMonoidHom.mk' (Quotient.lift (fun X => K0.of (P.ind X Y)) fun _ _ h =>
      K0.of_eq (P.ind_congr h (MvN.refl Y.hom Y.idem))) fun a b => by
    induction a using GProj.ind with
    | h X =>
      induction b using GProj.ind with
      | h X' =>
        show K0.of (P.ind (X.sum X') Y) = K0.of (P.ind X Y) + K0.of (P.ind X' Y)
        rw [K0.of_eq (P.ind_sum_left X X' Y), K0.of_sum]

/-- `x ↦ x ⊠ [Q]` on `K₀`. -/
def indLeft (Y : GIdem A₂) : K0 A₁ →+ K0 B := GrothendieckGroup.lift (P.indProj Y)

theorem indLeft_of (X : GIdem A₁) (Y : GIdem A₂) : P.indLeft Y (K0.of X) = K0.of (P.ind X Y) :=
  GrothendieckGroup.lift_of _ _

/-- `[Q] ↦ (x ↦ x ⊠ [Q])` on isomorphism classes. -/
def indProj₂ : GProj A₂ →+ (K0 A₁ →+ K0 B) :=
  AddMonoidHom.mk' (Quotient.lift (fun Y => P.indLeft Y) fun _ _ h => K0.hom_ext fun X => by
      rw [indLeft_of, indLeft_of]
      exact K0.of_eq (P.ind_congr (MvN.refl X.hom X.idem) h)) fun a b => by
    induction a using GProj.ind with
    | h Y =>
      induction b using GProj.ind with
      | h Y' =>
        show P.indLeft (Y.sum Y') = P.indLeft Y + P.indLeft Y'
        refine K0.hom_ext fun X => ?_
        rw [AddMonoidHom.add_apply, indLeft_of, indLeft_of, indLeft_of,
          K0.of_eq (P.ind_sum_right X Y Y'), K0.of_sum]

/-- Induction `K₀(A₁) × K₀(A₂) → K₀(B)`, as a biadditive map. -/
def indZ : K0 A₁ →+ K0 A₂ →+ K0 B := (GrothendieckGroup.lift P.indProj₂).flip

theorem indZ_of_of (X : GIdem A₁) (Y : GIdem A₂) :
    P.indZ (K0.of X) (K0.of Y) = K0.of (P.ind X Y) := by
  show GrothendieckGroup.lift P.indProj₂ (GrothendieckGroup.of (GProj.mk Y)) (K0.of X) = _
  rw [GrothendieckGroup.lift_of]
  exact P.indLeft_of X Y

theorem indZ_shift_left (k : ℤ) (x : K0 A₁) (y : K0 A₂) :
    P.indZ (K0.shift k x) y = K0.shift k (P.indZ x y) := by
  have hX : ∀ X : GIdem A₁,
      P.indZ (K0.shift k (K0.of X)) = (K0.shift k).comp (P.indZ (K0.of X)) :=
    fun X => K0.hom_ext fun Y => by
      rw [AddMonoidHom.comp_apply, K0.shift_of, P.indZ_of_of, P.indZ_of_of, K0.shift_of]
      exact K0.of_eq (P.ind_shift_left k X Y)
  have h : (P.indZ.flip y).comp (K0.shift k) = (K0.shift k).comp (P.indZ.flip y) :=
    K0.hom_ext fun X => by
      simp only [AddMonoidHom.comp_apply, AddMonoidHom.flip_apply]
      rw [hX, AddMonoidHom.comp_apply]
  exact DFunLike.congr_fun h x

theorem indZ_shift_right (k : ℤ) (x : K0 A₁) (y : K0 A₂) :
    P.indZ x (K0.shift k y) = K0.shift k (P.indZ x y) := by
  have hY : ∀ Y : GIdem A₂,
      P.indZ.flip (K0.shift k (K0.of Y)) = (K0.shift k).comp (P.indZ.flip (K0.of Y)) :=
    fun Y => K0.hom_ext fun X => by
      rw [AddMonoidHom.comp_apply, AddMonoidHom.flip_apply, AddMonoidHom.flip_apply, K0.shift_of,
        P.indZ_of_of, P.indZ_of_of, K0.shift_of]
      exact K0.of_eq (P.ind_shift_right k X Y)
  have h : (P.indZ x).comp (K0.shift k) = (K0.shift k).comp (P.indZ x) :=
    K0.hom_ext fun Y => by
      have := DFunLike.congr_fun (hY Y) x
      simp only [AddMonoidHom.comp_apply, AddMonoidHom.flip_apply] at this ⊢
      exact this
  exact DFunLike.congr_fun h y

/-- Induction on `K₀`, `ℤ[q,q⁻¹]`-bilinear: `[P] ⊗ [Q] ↦ [ind P Q]`. -/
def indK0 : K0 A₁ →ₗ[LaurentPolynomial ℤ] K0 A₂ →ₗ[LaurentPolynomial ℤ] K0 B :=
  LinearMap.mk₂' _ _ (fun x y => P.indZ x y)
    (fun x x' y => by simp only [map_add, AddMonoidHom.add_apply])
    (fun c x y => K0.map_smul_of_shift (P.indZ.flip y) (fun k x => by
      simp only [AddMonoidHom.flip_apply]
      rw [P.indZ_shift_left, K0.T_smul]) c x)
    (fun x y y' => map_add _ _ _)
    (fun c x y => K0.map_smul_of_shift (P.indZ x) (fun k y => by
      rw [P.indZ_shift_right, K0.T_smul]) c y)

theorem indK0_apply (x : K0 A₁) (y : K0 A₂) : P.indK0 x y = P.indZ x y := rfl

theorem indK0_of_of (X : GIdem A₁) (Y : GIdem A₂) :
    P.indK0 (K0.of X) (K0.of Y) = K0.of (P.ind X Y) :=
  P.indZ_of_of X Y

end K0

end SuperPair

end OddMath.Frontier.OddBialgebra
