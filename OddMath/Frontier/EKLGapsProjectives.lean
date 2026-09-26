import OddMath.Frontier.OnhStructure
import OddMath.Frontier.OddCategorificationRank

/-! # EKL: primitive idempotents and indecomposable graded projectives of `ONH_a`

EKL = Ellis–Khovanov–Lauda, *The odd nilHecke algebra and its diagrammatics*,
arXiv:1111.1320v1. `ONH_a = NilHeckeAction.Presented n`, `a = n+2`.

* §1.2, p. 2 (Theorems 4.15 and 4.16): the summands `e_ℓ = σ_ℓ λ_ℓ` of `1 ∈ ONH_a` and
  `e_α = σ_α λ_α` of `e_a ⊗ e_b ∈ ONH_{a+b}` are primitive idempotents and the left ideals they
  generate are indecomposable (`thm_4_15_primitive`, `thm_4_15_indecomposable`,
  `thm_4_16_primitive`, `thm_4_16_indecomposable`). From `λσ = e_a` and the primitivity of `e_a`
  (`OnhStructure.projector_primitive`) via `IsPrimitiveIdem.transfer`.
* §6, p. 47, "the unique indecomposable projective module of `ONH_a`": in the graded idempotent
  model of `GradedK0`, every finitely generated graded projective `ONH_a`-module is a direct sum
  `⊕ᵢ ONH_a e_a {tᵢ}` (`onh_gproj_classify`), it is indecomposable iff it is `≅ ONH_a e_a {k}` for
  some `k` (`indecomposable_iff`), and `k` is unique (`projE_equiv_iff`). On underlying modules:
  `ONH_a^m e ≅ (ONH_a e_a)^{m'}` (`onh_module_classify`), and `≅ ONH_a e_a` when the graded
  projective is indecomposable (`indecomposable_module`). The proof transports
  along the graded Morita equivalence `ONH_a ≅ Mat(OΛ_a)` to the connected ring `OΛ_a`, where
  every graded projective is graded free (`GradedK0.GIdem.exists_free`).
-/

namespace OddMath.Frontier.EKLGaps
open Categorification GradedK0 OddCategorification Matrix LaurentPolynomial
noncomputable section

/-! ### Primitive idempotents -/

section Primitive
variable {R : Type*} [Ring R]

/-- `e` is a primitive idempotent: `e² = e ≠ 0`, and the only idempotents of `eRe` are `0`, `e`. -/
def IsPrimitiveIdem (e : R) : Prop :=
  e * e = e ∧ e ≠ 0 ∧ ∀ y : R, e * y * e * (e * y * e) = e * y * e → e * y * e = 0 ∨ e * y * e = e

/-- If `λσ = e` with `e` primitive and `eλ = λ`, then `σλ` is primitive. -/
theorem IsPrimitiveIdem.transfer {e σ lam : R} (he : IsPrimitiveIdem e) (hls : lam * σ = e)
    (hel : e * lam = lam) : IsPrimitiveIdem (σ * lam) := by
  obtain ⟨hee, hne, hprim⟩ := he
  have hff : σ * lam * (σ * lam) = σ * lam := by
    rw [mul_assoc, ← mul_assoc lam, hls, hel]
  refine ⟨hff, ?_, ?_⟩
  · intro h0
    apply hne
    rw [← hee, ← hls, mul_assoc, ← mul_assoc σ, h0, zero_mul, mul_zero]
  · intro y hz
    set f := σ * lam
    set z := f * y * f
    have hzf : z * f = z := by simp only [z, mul_assoc, hff]
    have hfz : f * z = z := by simp only [z, ← mul_assoc, hff]
    -- `λ z σ = e (λ y σ) e`
    have hlz : lam * z * σ = e * (lam * y * σ) * e := by
      simp only [z, f, ← hls, mul_assoc]
    have hidem : e * (lam * y * σ) * e * (e * (lam * y * σ) * e) = e * (lam * y * σ) * e := by
      rw [← hlz]
      calc lam * z * σ * (lam * z * σ) = lam * (z * f) * z * σ := by
            simp only [f, mul_assoc]
        _ = lam * z * σ := by rw [hzf, mul_assoc lam z z, hz]
    have hback : z = σ * (lam * z * σ) * lam := by
      calc z = f * z * f := by rw [hfz, hzf]
        _ = _ := by simp only [f, mul_assoc]
    rcases hprim _ hidem with h0 | h1
    · left; rw [hback, hlz, h0, mul_zero, zero_mul]
    · right; rw [hback, hlz, h1, mul_assoc, hel]

/-- The left ideal `R e` of a primitive idempotent is indecomposable: in any decomposition
`R e = N₁ ⊕ N₂` into left submodules one summand vanishes. -/
theorem IsPrimitiveIdem.leftIdeal_indecomposable {e : R} (he : IsPrimitiveIdem e)
    (N₁ N₂ : Submodule R R) (hsup : N₁ ⊔ N₂ = leftIdeal e) (hinf : N₁ ⊓ N₂ = ⊥) :
    N₁ = ⊥ ∨ N₂ = ⊥ := by
  obtain ⟨hee, -, hprim⟩ := he
  set P := e
  have hP : P ∈ N₁ ⊔ N₂ := by rw [hsup]; exact hee
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hP
  have hu' : u * P = u := (hsup ▸ Submodule.mem_sup_left hu : u ∈ leftIdeal P)
  have hv' : v * P = v := (hsup ▸ Submodule.mem_sup_right hv : v ∈ leftIdeal P)
  have huv0 : u * v = 0 := by
    have : u * v ∈ N₁ ⊓ N₂ := by
      refine ⟨?_, N₂.smul_mem u hv⟩
      have e : u * v = u - u * u := by
        rw [eq_sub_iff_add_eq, ← mul_add, add_comm, huv, hu']
      rw [e]
      exact N₁.sub_mem hu (N₁.smul_mem u hu)
    rwa [hinf, Submodule.mem_bot] at this
  have hvu0 : v * u = 0 := by
    have : v * u ∈ N₁ ⊓ N₂ := by
      refine ⟨N₁.smul_mem v hu, ?_⟩
      have e : v * u = v - v * v := by
        rw [eq_sub_iff_add_eq, ← mul_add, huv, hv']
      rw [e]
      exact N₂.sub_mem hv (N₂.smul_mem v hv)
    rwa [hinf, Submodule.mem_bot] at this
  have huu : u * u = u := by
    have := congrArg (u * ·) huv
    simp only [mul_add, huv0, add_zero, hu'] at this
    exact this
  have hvv : v * v = v := by
    have := congrArg (v * ·) huv
    simp only [mul_add, hvu0, zero_add, hv'] at this
    exact this
  have htu : P * u * P = P * u := by rw [mul_assoc, hu']
  have hidem : P * u * P * (P * u * P) = P * u * P := by
    rw [htu, mul_assoc, ← mul_assoc u P u, hu', huu]
  have le_of (N : Submodule R R) (hN : P ∈ N) : leftIdeal P ≤ N := fun x hx => by
    rw [← (hx : x * P = x)]; exact N.smul_mem x hN
  rcases hprim u hidem with h0 | h1
  · left
    rw [htu] at h0
    have hu0 : u = 0 :=
      calc u = u * u := huu.symm
        _ = u * P * u := by rw [hu']
        _ = 0 := by rw [mul_assoc, h0, mul_zero]
    have hPv : P ∈ N₂ := by rw [← huv, hu0, zero_add]; exact hv
    rw [eq_bot_iff, ← hinf]
    exact le_inf le_rfl ((hsup ▸ le_sup_left : N₁ ≤ leftIdeal P).trans (le_of N₂ hPv))
  · right
    rw [htu] at h1
    have hPv : P * v = 0 := by
      have := congrArg (P * ·) huv
      simp only [mul_add, h1, hee, P] at this
      exact left_eq_add.mp this.symm
    have hv0 : v = 0 :=
      calc v = v * v := hvv.symm
        _ = v * P * v := by rw [hv']
        _ = 0 := by rw [mul_assoc, hPv, mul_zero]
    have hPu : P ∈ N₁ := by rw [← huv, hv0, add_zero]; exact hu
    rw [eq_bot_iff, ← hinf]
    exact le_inf ((hsup ▸ le_sup_right : N₂ ≤ leftIdeal P).trans (le_of N₁ hPu)) le_rfl

/-- In a splitting `P = Σ σ_i λ_i`, `λ_i σ_j = δ_{ij} e`, with `e` primitive, every summand
`σ_i λ_i` is a primitive idempotent. -/
theorem splitting_primitive {P e : R} {I : Type*} [Fintype I] [DecidableEq I]
    (S : Splitting P e I) (he : IsPrimitiveIdem e) (i : I) : IsPrimitiveIdem (S.σ i * S.lam i) :=
  he.transfer (by rw [S.orth, if_pos rfl]) (S.mul_lam i)

end Primitive

/-! ### Theorems 4.15 and 4.16: the summands are primitive -/

section Onh
open ZeroHecke
variable {n : ℕ}

theorem projector_isPrimitive (n : ℕ) : IsPrimitiveIdem (projector n) :=
  ⟨projector_mul_projector, OnhStructure.projector_ne_zero n,
    fun y h => OnhStructure.projector_primitive y h⟩

/-- **EKL §1.2 / Theorem 4.15**: each idempotent `e_ℓ = σ_ℓ λ_ℓ`, `ℓ ∈ Sq(a)`, of the
decomposition `1 = Σ_ℓ e_ℓ` of `ONH_a` is primitive, and `ONH_a e_ℓ` is indecomposable. -/
theorem thm_4_15_primitive (ℓ : BoxPartitionCount.Sq (n+2)) :
    IsPrimitiveIdem (ThickMatrixUnits.idem (n := n) ℓ.1) :=
  splitting_primitive (split61 n) (projector_isPrimitive n) ℓ

theorem thm_4_15_indecomposable (ℓ : BoxPartitionCount.Sq (n+2))
    (N₁ N₂ : Submodule (NilHeckeAction.Presented n) (NilHeckeAction.Presented n))
    (hsup : N₁ ⊔ N₂ = leftIdeal (ThickMatrixUnits.idem (n := n) ℓ.1)) (hinf : N₁ ⊓ N₂ = ⊥) :
    N₁ = ⊥ ∨ N₂ = ⊥ :=
  (thm_4_15_primitive ℓ).leftIdeal_indecomposable N₁ N₂ hsup hinf

/-- **EKL §1.2 / Theorem 4.16**: each idempotent `e_α = σ_α λ_α`, `α ∈ P(a,b)`, of the
decomposition `e_a ⊗ e_b = Σ_α e_α` in `ONH_{a+b}` is primitive, and `ONH_{a+b} e_α` is
indecomposable. -/
theorem thm_4_16_primitive {a b : ℕ} (hab : a + b = n+2) (α : BoxPartitionCount.box a b) :
    IsPrimitiveIdem (ThickBubble.idem n a b hab α.1) :=
  splitting_primitive (split62 hab) (projector_isPrimitive n) α

theorem thm_4_16_indecomposable {a b : ℕ} (hab : a + b = n+2) (α : BoxPartitionCount.box a b)
    (N₁ N₂ : Submodule (NilHeckeAction.Presented n) (NilHeckeAction.Presented n))
    (hsup : N₁ ⊔ N₂ = leftIdeal (ThickBubble.idem n a b hab α.1)) (hinf : N₁ ⊓ N₂ = ⊥) :
    N₁ = ⊥ ∨ N₂ = ⊥ :=
  (thm_4_16_primitive hab α).leftIdeal_indecomposable N₁ N₂ hsup hinf

end Onh

section Diag
variable {R : Type*} [Ring R] {A : ℤ → AddSubgroup R} [SetLike.GradedMonoid A] {e : R}

theorem gdiag_zero_equiv (he : e ∈ A 0) (hee : e * e = e) (t : Fin 0 → ℤ) :
    gdiag he hee t ≈ GIdem.zero :=
  MvN.of_equiv (Equiv.refl _) (gdiag he hee t).hom (gdiag he hee t).idem
    (fun i => i.elim0) (fun i => i.elim0)

theorem gdiag_succ_equiv (he : e ∈ A 0) (hee : e * e = e) {m : ℕ} (t : Fin (m+1) → ℤ) :
    gdiag he hee t ≈ (gdiag he hee fun i => t (Fin.castSucc i)).sum
      (gelem he hee (t (Fin.last m))) := by
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
  exact MvN.trans (diagonal_idem hee) (fromBlocks_idem (diagonal_idem hee) (diagonal_idem hee))
    (GIdem.sum _ _).idem h.symm
    (GIdem.mvn_sum (gdiag he hee fun i => t (Fin.castSucc i)) (gelem he hee (t (Fin.last m))))

theorem mk_gdiag (he : e ∈ A 0) (hee : e * e = e) : ∀ {m : ℕ} (t : Fin m → ℤ),
    GProj.mk (gdiag he hee t) = ∑ a, GProj.mk (gelem he hee (t a))
  | 0, t => by
    rw [Finset.univ_eq_empty, Finset.sum_empty, GProj.zero_def, GProj.mk_eq_mk]
    exact gdiag_zero_equiv he hee t
  | m + 1, t => by
    rw [GProj.mk_eq_mk.2 (gdiag_succ_equiv he hee t), ← GProj.mk_add, mk_gdiag,
      Fin.sum_univ_castSucc]

theorem mk_gelem (he : e ∈ A 0) (hee : e * e = e) (k : ℤ) :
    GProj.mk (gelem he hee k) = GProj.shift k (GProj.mk (gelem he hee 0)) := by
  rw [GProj.shift_mk, GProj.mk_eq_mk]
  exact MvN.of_equiv (Equiv.refl _) (gelem he hee k).hom (gelem he hee k).idem
    (fun _ => by simp [GIdem.shift, gelem, gdiag]) (fun _ _ => rfl)

omit [SetLike.GradedMonoid A] in
theorem free_zero_equiv [SetLike.GradedMonoid A] (t : Fin 0 → ℤ) :
    (GIdem.free t : GIdem A) ≈ GIdem.zero :=
  MvN.of_equiv (Equiv.refl _) IsHom.one (mul_one 1) (fun i => i.elim0) (fun i => i.elim0)

theorem mk_free : ∀ {m : ℕ} (t : Fin m → ℤ),
    GProj.mk (GIdem.free t : GIdem A) = ∑ a, GProj.mk (GIdem.single (t a) : GIdem A)
  | 0, t => by
    rw [Finset.univ_eq_empty, Finset.sum_empty, GProj.zero_def, GProj.mk_eq_mk]
    exact free_zero_equiv t
  | m + 1, t => by
    have h : MvN A (Sum.elim (fun i => t (Fin.castSucc i)) fun _ : Fin 1 => t (Fin.last m))
        (fromBlocks 1 0 0 1) t 1 := by
      refine MvN.of_equiv finSumFinEquiv (IsHom.one.fromBlocks IsHom.zero IsHom.zero IsHom.one)
        (fromBlocks_idem (mul_one 1) (mul_one 1)) ?_ ?_
      · rintro (i | i)
        · rfl
        · obtain rfl : i = 0 := Subsingleton.elim _ _
          rfl
      · intro x y
        simp only [fromBlocks_one, one_apply, EmbeddingLike.apply_eq_iff_eq]
    have h' : GIdem.free t ≈ (GIdem.free fun i => t (Fin.castSucc i)).sum
        (GIdem.single (A := A) (t (Fin.last m))) :=
      MvN.trans (mul_one 1) (fromBlocks_idem (mul_one 1) (mul_one 1)) (GIdem.sum _ _).idem h.symm
        (GIdem.mvn_sum (GIdem.free fun i => t (Fin.castSucc i)) (GIdem.single (t (Fin.last m))))
    rw [GProj.mk_eq_mk.2 h', ← GProj.mk_add, mk_free, Fin.sum_univ_castSucc]

omit [SetLike.GradedMonoid A] in
theorem mk_single_shift [SetLike.GradedMonoid A] (c k : ℤ) :
    GProj.mk (GIdem.single k : GIdem A) = GProj.shift (k - c) (GProj.mk (GIdem.single c)) := by
  rw [GProj.shift_mk, GProj.mk_eq_mk]
  exact MvN.of_equiv (Equiv.refl _) (GIdem.single k).hom (GIdem.single (A := A) k).idem
    (fun _ => by simp [GIdem.shift, GIdem.single, GIdem.free]) (fun _ _ => rfl)

end Diag

section Onh
open ZeroHecke
variable {n : ℕ}

/-- The rank `q ↦ 1` of a graded projective `ONH_a`-module, counted in copies of `ONH_a e_a`. -/
def onhRank (P : GIdem (onhGrading n)) : ℤ := augment (onhK0Equiv n (K0.of P))

theorem onhRank_congr {P Q : GIdem (onhGrading n)} (h : P ≈ Q) : onhRank P = onhRank Q := by
  rw [onhRank, onhRank, K0.of_eq h]

theorem onhRank_sum (P Q : GIdem (onhGrading n)) :
    onhRank (P.sum Q) = onhRank P + onhRank Q := by
  rw [onhRank, onhRank, onhRank, K0.of_sum, map_add, map_add]

theorem onhRank_zero : onhRank (GIdem.zero : GIdem (onhGrading n)) = 0 := by
  rw [onhRank, K0.of_zero, map_zero, map_zero]

theorem onhK0Equiv_projE' (k : ℤ) :
    onhK0Equiv n (K0.of (projE n k)) = T k * T (-(2 * (((n+2).choose 2 : ℕ) : ℤ))) := by
  rw [projE, of_elem, map_smul, ← projE, onhK0Equiv_projE, smul_eq_mul]

theorem gelem_eq_projE (k : ℤ) :
    gelem (projector_mem n) projector_mul_projector k = projE n k := rfl

theorem onhRank_gdiag {m : ℕ} (t : Fin m → ℤ) :
    onhRank (gdiag (projector_mem n) projector_mul_projector t) = m := by
  rw [onhRank, of_diag, map_sum, map_sum]
  simp only [gelem_eq_projE, onhK0Equiv_projE', map_mul, augment_T, mul_one, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem onhRank_projE (k : ℤ) : onhRank (projE n k) = 1 := onhRank_gdiag _

/-- Graded Morita transport `ONH_a → OΛ_a` on isomorphism classes of graded projectives. -/
def onhToKer (n : ℕ) : GProj (onhGrading n) →+ GProj (kerGrading n) :=
  GProj.flatten.comp (gprojMap (onhIso n) (mem_onhGrading_iff n))

theorem onhToKer_mk (P : GIdem (onhGrading n)) :
    onhToKer n (GProj.mk P) = GProj.mk (gmap (onhIso n) (mem_onhGrading_iff n) P).flatten := rfl

theorem onhToKer_injective (n : ℕ) : Function.Injective (onhToKer n) :=
  GProj.flatten_bijective.1.comp (gprojMap_bijective _ _).1

theorem onhToKer_shift (k : ℤ) (x : GProj (onhGrading n)) :
    onhToKer n (GProj.shift k x) = GProj.shift k (onhToKer n x) := by
  induction x using GProj.ind with
  | h P =>
    rw [GProj.shift_mk, onhToKer_mk, onhToKer_mk, GProj.shift_mk, gmap_shift, GProj.mk_eq_mk]
    exact GIdem.flatten_shift k _

theorem onhToKer_projE :
    onhToKer n (GProj.mk (projE n 0)) =
      GProj.mk (GIdem.single (-(2 * (((n+2).choose 2 : ℕ) : ℤ)))) := by
  set c : ℤ := -(2 * (((n+2).choose 2 : ℕ) : ℤ))
  set X := (gmap (onhIso n) (mem_onhGrading_iff n) (projE n 0)).flatten
  obtain ⟨m, t, hX⟩ := GIdem.exists_free (kerConnected n) X
  have hg : ∑ a, T (t a) = (T c : LaurentPolynomial ℤ) := by
    have h := onhK0Equiv_projE (n := n)
    simp only [onhK0Equiv, LinearEquiv.trans_apply, k0Equiv_of, K0.morita_of,
      K0.classify_of] at h
    rw [gdimAux_eq_of_mvn (kerConnected n) hX] at h
    change gdimAux t 1 = _ at h
    rw [gdimAux_one (kerConnected n)] at h
    exact h
  have hm : m = 1 := by
    have := congrArg augment hg
    simp only [map_sum, augment_T, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one] at this
    exact_mod_cast this
  subst hm
  have ht : t 0 = c := by
    rw [Fin.sum_univ_one] at hg
    have := congrArg (fun p : LaurentPolynomial ℤ => p (t 0)) hg
    simp only [LaurentPolynomial.T_apply, if_true] at this
    split_ifs at this with hc
    · exact hc.symm
    · exact absurd this one_ne_zero
  rw [onhToKer_mk, GProj.mk_eq_mk]
  refine Setoid.trans hX ?_
  have : t = fun _ => c := funext fun a => by rw [Subsingleton.elim a 0, ht]
  rw [this]
  exact Setoid.refl _

/-- **Graded projective `ONH_a`-modules** (EKL §6): every graded idempotent matrix over `ONH_a`
is Murray–von Neumann equivalent to `diag(e_a, …, e_a)` on `ONH_a^m{t}`: every finitely generated
graded projective `ONH_a`-module is a direct sum of shifts `ONH_a e_a {t_i}`. -/
theorem onh_gproj_classify (P : GIdem (onhGrading n)) :
    ∃ (m : ℕ) (t : Fin m → ℤ), P ≈ gdiag (projector_mem n) projector_mul_projector t := by
  set c : ℤ := -(2 * (((n+2).choose 2 : ℕ) : ℤ))
  obtain ⟨m, t, hP⟩ := GIdem.exists_free (kerConnected n)
    (gmap (onhIso n) (mem_onhGrading_iff n) P).flatten
  refine ⟨m, fun a => t a - c, GProj.mk_eq_mk.1 (onhToKer_injective n ?_)⟩
  rw [onhToKer_mk, GProj.mk_eq_mk.2 hP, mk_free, mk_gdiag, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [mk_gelem, onhToKer_shift, ← projE, onhToKer_projE, ← mk_single_shift]

/-- A graded projective is indecomposable: nonzero, and in every decomposition `P ≅ Q ⊕ R` one
summand vanishes. -/
def IsIndecomposable {R : Type*} [Ring R] {A : ℤ → AddSubgroup R} [SetLike.GradedMonoid A]
    (P : GIdem A) : Prop :=
  ¬ P ≈ GIdem.zero ∧ ∀ Q S : GIdem A, P ≈ Q.sum S → Q ≈ GIdem.zero ∨ S ≈ GIdem.zero

theorem gdiag_equiv_zero_iff {m : ℕ} (t : Fin m → ℤ) :
    gdiag (projector_mem n) projector_mul_projector t ≈ GIdem.zero ↔ m = 0 := by
  constructor
  · intro h
    have := onhRank_congr h
    rw [onhRank_gdiag, onhRank_zero] at this
    exact_mod_cast this
  · rintro rfl
    exact gdiag_zero_equiv _ _ t

/-- **EKL §6, p. 46: the unique indecomposable graded projective**. A graded projective
`ONH_a`-module is indecomposable iff it is isomorphic to `ONH_a e_a {k}` for some `k`, and `k` is
unique. -/
theorem indecomposable_iff (P : GIdem (onhGrading n)) :
    IsIndecomposable P ↔ ∃ k : ℤ, P ≈ projE n k := by
  constructor
  · rintro ⟨hnz, hind⟩
    obtain ⟨m, t, hP⟩ := onh_gproj_classify P
    cases m with
    | zero => exact absurd (Setoid.trans hP (gdiag_zero_equiv _ _ t)) hnz
    | succ m =>
      have hs := Setoid.trans hP (gdiag_succ_equiv _ _ t)
      rcases hind _ _ hs with h | h
      · refine ⟨t (Fin.last m), Setoid.trans hs ?_⟩
        exact Setoid.trans (GIdem.sum_congr h (Setoid.refl _)) (GIdem.zero_sum _)
      · exfalso
        have := onhRank_congr h
        rw [onhRank_zero, show gelem (projector_mem n) projector_mul_projector (t (Fin.last m)) =
          projE n (t (Fin.last m)) from rfl, onhRank_projE] at this
        exact one_ne_zero this
  · rintro ⟨k, hk⟩
    refine ⟨fun h => ?_, fun Q S h => ?_⟩
    · have := onhRank_congr (Setoid.trans (Setoid.symm hk) h)
      rw [onhRank_projE, onhRank_zero] at this
      exact one_ne_zero this
    · obtain ⟨mQ, tQ, hQ⟩ := onh_gproj_classify Q
      obtain ⟨mS, tS, hS⟩ := onh_gproj_classify S
      have hr := onhRank_congr (Setoid.trans (Setoid.symm hk) h)
      rw [onhRank_projE, onhRank_sum, onhRank_congr hQ, onhRank_congr hS, onhRank_gdiag,
        onhRank_gdiag] at hr
      have : mQ = 0 ∨ mS = 0 := by omega
      rcases this with h0 | h0
      · exact Or.inl (Setoid.trans hQ ((gdiag_equiv_zero_iff tQ).2 h0))
      · exact Or.inr (Setoid.trans hS ((gdiag_equiv_zero_iff tS).2 h0))

theorem projE_equiv_iff (k k' : ℤ) : projE n k ≈ projE n k' ↔ k = k' := by
  constructor
  · intro h
    have h1 := congrArg (onhK0Equiv n) (K0.of_eq h)
    rw [onhK0Equiv_projE', onhK0Equiv_projE', ← T_add, ← T_add] at h1
    have := congrArg (fun p : LaurentPolynomial ℤ => p (k + -(2 * (((n+2).choose 2 : ℕ) : ℤ)))) h1
    simp only [LaurentPolynomial.T_apply, if_true] at this
    split_ifs at this with hc
    · omega
    · exact absurd this one_ne_zero
  · rintro rfl; exact Setoid.refl _

theorem projE_indecomposable (k : ℤ) : IsIndecomposable (projE n k) :=
  (indecomposable_iff _).2 ⟨k, Setoid.refl _⟩

end Onh

section RowModule
variable {R : Type*} [Ring R] {ι : Type*} [Fintype ι]

/-- The left `R`-module `R^ι e = {x ∈ R^ι : x e = x}` of row vectors, for an idempotent matrix `e`. -/
def rowModule (e : Matrix ι ι R) : Submodule R (ι → R) where
  carrier := {x | vecMul x e = x}
  add_mem' {x y} hx hy := by
    change vecMul (x + y) e = x + y
    rw [add_vecMul, hx, hy]
  zero_mem' := zero_vecMul e
  smul_mem' r x hx := by
    change vecMul (r • x) e = r • x
    rw [vecMul_smul, hx]

theorem mem_rowModule {e : Matrix ι ι R} {x : ι → R} : x ∈ rowModule e ↔ vecMul x e = x := Iff.rfl

variable {κ : Type*} [Fintype κ]

/-- Right multiplication by `u` as a map `R^ι e → R^κ f`, when `e u f = u`. -/
def rowMap {e : Matrix ι ι R} {f : Matrix κ κ R} (u : Matrix ι κ R) (hf : f * f = f)
    (hu : e * u * f = u) : rowModule e →ₗ[R] rowModule f where
  toFun x := ⟨vecMul x.1 u, by
    have huf : u * f = u := by
      calc u * f = e * u * f * f := by rw [hu]
        _ = u := by rw [Matrix.mul_assoc, hf, hu]
    rw [mem_rowModule, vecMul_vecMul, huf]⟩
  map_add' x y := Subtype.ext (add_vecMul _ _ _)
  map_smul' r x := Subtype.ext (vecMul_smul _ _ _)

/-- A Murray–von Neumann equivalence of idempotent matrices gives an isomorphism of the left
modules `R^ι e ≅ R^κ f`. -/
def rowEquiv {e : Matrix ι ι R} {f : Matrix κ κ R} (he : e * e = e) (hf : f * f = f)
    (u : Matrix ι κ R) (v : Matrix κ ι R) (h1 : u * v = e) (h2 : v * u = f)
    (h3 : e * u * f = u) (h4 : f * v * e = v) : rowModule e ≃ₗ[R] rowModule f :=
  { rowMap u hf h3 with
    invFun := rowMap v he h4
    left_inv := fun x => Subtype.ext (by
      change vecMul (vecMul x.1 u) v = x.1
      rw [vecMul_vecMul, h1]; exact x.2)
    right_inv := fun y => Subtype.ext (by
      change vecMul (vecMul y.1 v) u = y.1
      rw [vecMul_vecMul, h2]; exact y.2) }

/-- `R^m · diag(e, …, e) ≅ (R e)^m`. -/
def rowDiagEquiv (e : R) (m : ℕ) :
    rowModule (diagonal fun _ : Fin m => e) ≃ₗ[R] (Fin m → leftIdeal e) where
  toFun x i := ⟨x.1 i, by
    have := congrFun x.2 i
    rwa [vecMul_diagonal] at this⟩
  map_add' x y := rfl
  map_smul' r x := rfl
  invFun y := ⟨fun i => (y i).1, by
    rw [mem_rowModule]
    funext i
    rw [vecMul_diagonal]
    exact (y i).2⟩
  left_inv x := rfl
  right_inv y := rfl

end RowModule

section Onh
open ZeroHecke
variable {n : ℕ}

/-- **Module form of the classification**: the left `ONH_a`-module `ONH_a^m · e` of a graded
idempotent matrix `e` is isomorphic to a direct sum of copies of `ONH_a e_a`. -/
theorem onh_module_classify (P : GIdem (onhGrading n)) :
    ∃ m : ℕ, Nonempty (rowModule P.e ≃ₗ[NilHeckeAction.Presented n]
      (Fin m → leftIdeal (projector n))) := by
  obtain ⟨m, t, hP⟩ := onh_gproj_classify P
  obtain ⟨u, v, -, -, h1, h2, h3, h4⟩ := hP
  exact ⟨m, ⟨(rowEquiv P.idem (diagonal_idem projector_mul_projector) u v h1 h2 h3 h4).trans
    (rowDiagEquiv (projector n) m)⟩⟩

/-- **EKL §6, p. 47, module form**: the module `ONH_a^m · e` of an indecomposable graded
projective is isomorphic to `ONH_a e_a` (and, as a graded projective, to `ONH_a e_a {k}` for a
unique `k`: `indecomposable_iff`, `projE_equiv_iff`). -/
theorem indecomposable_module (P : GIdem (onhGrading n)) (hP : IsIndecomposable P) :
    Nonempty (rowModule P.e ≃ₗ[NilHeckeAction.Presented n] leftIdeal (projector n)) := by
  obtain ⟨k, hk⟩ := (indecomposable_iff P).1 hP
  obtain ⟨u, v, -, -, h1, h2, h3, h4⟩ := hk
  exact ⟨(rowEquiv P.idem (diagonal_idem projector_mul_projector) u v h1 h2 h3 h4).trans
    ((rowDiagEquiv (projector n) 1).trans (LinearEquiv.funUnique (Fin 1) _ _))⟩

end Onh

end
end OddMath.Frontier.EKLGaps
