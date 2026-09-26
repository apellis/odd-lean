import OddMath.Frontier.OddCyclotomicActionPoly
import OddMath.Frontier.SmallRankCyclotomic

/-!
# `ONH_{a+1}^N` over `ONH_a^N`

EKL arXiv:1111.1320v1, §6, last paragraph (p. 47). Along the inclusion
`ONH_a^N → ONH_{a+1}^N`, `x ↦ x ⊗ 1` (`OddBialgebra.incCyc`, `OddBialgebra.incCyc1`), the ring
`ONH_{a+1}^N` is, as a left `ONH_a^N`-module, the graded projective module
`⊕_{w ∈ S_{a+1}} ⊕_{0 ≤ k < N-a} ONH_a^N E {2k - 2ℓ(w)}`, where `E` (`Ecyc`) is the degree-zero
idempotent of `ONH_a^N` corresponding under Proposition 5.2 to the matrix unit at `(1, 1)`, so
that `ONH_a^N E` is the first column, `≅ ⊕_{v ∈ S_a} OH_{a,N}` (`AEequiv`). For `a ≤ 1`, `E = 1`:
then `ONH_{a+1}^N` is graded free over `ONH_a^N` of rank `(a+1)(N-a)`. The generators `β_{w,k}`
(`betaVec`) send the Schubert polynomial `𝔰_w` to `x_{a+1}^k` and the other Schubert polynomials
to `0`; `β_{w,k}` has degree `2k - 2ℓ(w)` (`betaVec_mem`).

The proof is the odd analogue of the cohomology of the two-step flag variety `Fl(a, a+1; N)` being
free over that of `Gr(a, N)` with basis `1, x, …, x^{N-a-1}`: the polynomial representation
`OPol_{a+1}/(OPol_{a+1}·J)` is spanned over `ONH_a^N` by the `x_{a+1}^k`, `k < N - a`
(`span_place`), and the ranks agree, `(N - a)·a!·C(N, a) = (a+1)!·C(N, a+1)`.

* `relBasisOfTheta`: a relative basis of `ONH_m^N` from a relative basis of the polynomial
  representation.
* `relBasisG n N`, `relBasis1 N`, `relBasis0 N`: the cases `a = n+2`, `a = 1`, `a = 0`.
-/

noncomputable section
open LaurentPolynomial Matrix

namespace OddMath.Frontier.OddCyclotomicAction
open GradedK0 OddCategorification Cyclotomic OddBialgebra
open OddMath.SkewPolynomial (SkewPolynomial generator monomial)
open NilHeckeAction NilCoxeterWords NilHeckeEndomorphism OddSchubertAction

attribute [-instance] Finsupp.instMul Finsupp.instMulZeroClass Finsupp.instSemigroupWithZero
  Finsupp.instNonUnitalNonAssocSemiring Finsupp.instNonUnitalSemiring
  Finsupp.instNonUnitalCommSemiring Finsupp.instNonUnitalNonAssocRing Finsupp.instNonUnitalRing
  Finsupp.instNonUnitalCommRing

local notation "L" => LaurentPolynomial ℤ

/-! ### Relative bases from the polynomial representation -/

section Generic

variable {m N : ℕ} {A' : Type*} [Ring A'] (ψ : A' →+* ONH m N) (b : ℕ)

/-- `Θ(α) = ∑_k ψ(α_k) · [x_a^k]` in `OPol_a/(OPol_a·J)`. -/
def theta : (Fin b → A') →+ VMod m N where
  toFun α := ∑ k, actV m N (ψ (α k)) (Submodule.Quotient.mk (xl m ^ (k : ℕ)))
  map_zero' := by simp
  map_add' α α' := by
    simp only [Pi.add_apply, map_add, LinearMap.add_apply, Finset.sum_add_distrib]

theorem theta_apply (α : Fin b → A') :
    theta ψ b α = ∑ k, actV m N (ψ (α k)) (Submodule.Quotient.mk (xl m ^ (k : ℕ))) := rfl

/-- `β_{w,k}`: `𝔰_w ↦ x_a^k`, `𝔰_{w'} ↦ 0` for `w' ≠ w`. -/
def betaVec (N : ℕ) (w : Perm m) (k : ℕ) : ONH m N :=
  toONH m N (ofCols fun w' => if w' = w then xl m ^ k else 0)

theorem actV_betaVec (w w' : Perm m) (k : ℕ) :
    actV m N (betaVec N w k) (Submodule.Quotient.mk (schubert w')) =
      if w' = w then Submodule.Quotient.mk (xl m ^ k) else 0 := by
  rw [betaVec, actV_toONH, action_ofCols]
  split_ifs <;> simp

theorem xl_pow_mem (k : ℕ) :
    xl m ^ k ∈ NilHeckeGradedEnd.polynomialPiece (m+2) (2 * (k : ℤ)) := by
  induction k with
  | zero => simpa using NilHeckeGradedEnd.one_mem (m+2)
  | succ k ih =>
    rw [pow_succ]
    have h := NilHeckeGradedEnd.polynomial_mul ih (NilHeckeGradedEnd.generator_mem (Fin.last (m+1)))
    convert h using 2

theorem betaVec_mem (w : Perm m) (k : ℕ) :
    betaVec N w k ∈ onhCycGrading m N (2 * (k : ℤ) - 2 * (length w : ℤ)) := by
  refine toONH_mem (n := m) (N := N) (ofCols_mem fun w' => ?_)
  split_ifs with h
  · subst h
    convert xl_pow_mem (m := m) k using 2
    ring
  · exact zero_mem _

variable {ψ b}

/-- A relative basis of `ONH_m^N` over `A'` from a relative basis `x_a^k` of the polynomial
representation: `β_{w,k}`, `w ∈ S_a`, `k < b`. -/
def relBasisOfTheta (E : A') (hE : E * E = E)
    (hEx : ∀ k : ℕ, actV m N (ψ E) (Submodule.Quotient.mk (xl m ^ k)) =
      Submodule.Quotient.mk (xl m ^ k))
    (hθ : ∀ v : VMod m N, ∃! α : Fin b → A', (∀ k, α k * E = α k) ∧ theta ψ b α = v) :
    RelBasis ψ E (Perm m × Fin b) where
  vec p := betaVec N p.1 p.2
  idem := hE
  E_vec p := eq_of_act fun w' => by
    rw [map_mul, Module.End.mul_apply, actV_betaVec]
    split_ifs
    · exact hEx _
    · exact map_zero _
  existsUnique y := by
    classical
    choose α hα hαu using fun w => hθ (actV m N y (Submodule.Quotient.mk (schubert w)))
    have hval : ∀ (c : Perm m × Fin b → A') (w' : Perm m),
        actV m N (∑ p, ψ (c p) * betaVec N p.1 p.2) (Submodule.Quotient.mk (schubert w')) =
          theta ψ b fun k => c (w', k) := by
      intro c w'
      rw [map_sum, LinearMap.coeFn_sum, Finset.sum_apply, Fintype.sum_prod_type,
        Finset.sum_eq_single w' (fun w _ hw => Finset.sum_eq_zero fun k _ => by
          rw [map_mul, Module.End.mul_apply, actV_betaVec, if_neg (Ne.symm hw), map_zero])
          (fun h => absurd (Finset.mem_univ _) h), theta_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul, Module.End.mul_apply, actV_betaVec, if_pos rfl]
    refine ⟨fun p => α p.1 p.2, ⟨fun p => (hα p.1).1 p.2, eq_of_act fun w' => ?_⟩, ?_⟩
    · rw [hval]
      exact (hα w').2
    · rintro c ⟨hcE, hc⟩
      funext p
      have := hαu p.1 (fun k => c (p.1, k)) ⟨fun k => hcE _, by rw [← hval, hc]⟩
      exact congrFun this p.2

/-- Uniqueness of relative coordinates from the bijectivity of `Θ` on `RE`-valued vectors. -/
theorem existsUnique_theta_of_bijective (E : A') (S : Submodule ℤ A')
    (hS : ∀ x, x ∈ S ↔ x * E = x)
    (hbij : Function.Bijective fun α : Fin b → S => theta ψ b fun k => (α k : A'))
    (v : VMod m N) : ∃! α : Fin b → A', (∀ k, α k * E = α k) ∧ theta ψ b α = v := by
  obtain ⟨α, hα⟩ := hbij.2 v
  replace hα : theta ψ b (fun k => (α k : A')) = v := hα
  refine ⟨fun k => α k, ⟨fun k => (hS _).1 (α k).2, hα⟩, ?_⟩
  rintro α' ⟨hα'E, hα'⟩
  have := hbij.1 (a₁ := fun k => ⟨α' k, (hS _).2 (hα'E k)⟩) (a₂ := α) (by
    simp only
    rw [hα', hα])
  funext k
  exact congrArg Subtype.val (congrFun this k)

end Generic

/-- `Θ` restricted to vectors with entries in a submodule, as a `ℤ`-linear map. -/
def thetaS {m N : ℕ} {A' : Type*} [Ring A'] (ψ : A' →+* ONH m N) (b : ℕ) (S : Submodule ℤ A') :
    (Fin b → S) →ₗ[ℤ] VMod m N where
  toFun α := theta ψ b fun k => (α k : A')
  map_add' α α' := by
    rw [← map_add]
    rfl
  map_smul' c α := by
    rw [RingHom.id_apply, ← map_zsmul]
    rfl

/-! ### `a = n+2`: `ONH_{n+3}^N` over `ONH_{n+2}^N` -/

section General

variable (n N : ℕ)

/-- The degree-zero idempotent `E ∈ ONH_a^N` (`a = n+2`), the matrix unit at `(1, 1)` of
Proposition 5.2: `𝔰_w ↦ δ_{w,1} 𝔰_1`. -/
def Ecyc : ONH n N := toONH n N (Etil n)

theorem Ecyc_mul_self : Ecyc n N * Ecyc n N = Ecyc n N := by
  rw [Ecyc, ← map_mul, Etil_mul_self]

theorem Ecyc_mem : Ecyc n N ∈ onhCycGrading n N 0 := toONH_mem (Etil_mem n)

theorem prop_5_2_Ecyc (v w : Perm n) :
    prop_5_2 n N (Ecyc n N) v w = if v = 1 ∧ w = 1 then 1 else 0 := by
  rw [Ecyc, prop_5_2_apply, cor214_apply, action_Etil_schubert]
  by_cases hw : w = 1
  · rw [if_pos hw, coordinates_schubert]
    by_cases hv : v = 1
    · rw [hv, Pi.single_eq_same, map_one, map_one, if_pos ⟨rfl, hw⟩]
    · rw [Pi.single_eq_of_ne hv, map_zero, map_zero, if_neg (fun h => hv h.1)]
  · rw [if_neg hw, map_zero, Pi.zero_apply, map_zero, map_zero, if_neg (fun h => hw h.2)]

theorem prop_5_2_mul_Ecyc (α : ONH n N) (v w : Perm n) :
    prop_5_2 n N (α * Ecyc n N) v w = if w = 1 then prop_5_2 n N α v 1 else 0 := by
  rw [map_mul, Matrix.mul_apply]
  simp_rw [prop_5_2_Ecyc]
  by_cases hw : w = 1
  · rw [if_pos hw, Finset.sum_eq_single 1 (fun u _ hu => by rw [if_neg (fun h => hu h.1),
      mul_zero]) (fun h => absurd (Finset.mem_univ _) h), if_pos ⟨rfl, hw⟩, mul_one]
  · rw [if_neg hw]
    exact Finset.sum_eq_zero fun u _ => by rw [if_neg (fun h => hw h.2), mul_zero]

/-- `ONH_a^N E`, the elements `α` with `α E = α`. -/
def AEsub : Submodule ℤ (ONH n N) where
  carrier := {α | α * Ecyc n N = α}
  add_mem' {α β} hα hβ := by
    simp only [Set.mem_setOf_eq] at *
    rw [add_mul, hα, hβ]
  zero_mem' := zero_mul _
  smul_mem' c α hα := by
    simp only [Set.mem_setOf_eq] at *
    rw [smul_mul_assoc, hα]

theorem mem_AEsub {α : ONH n N} : α ∈ AEsub n N ↔ α * Ecyc n N = α := Iff.rfl

/-- `ONH_a^N E ≅ ⊕_{v ∈ S_a} OH_{a,N}`, the first column under Proposition 5.2. -/
def AEequiv : AEsub n N ≃ₗ[ℤ] (Perm n → OH n N) where
  toFun α v := prop_5_2 n N α v 1
  invFun c := ⟨(prop_5_2 n N).symm (Matrix.of fun v w => if w = 1 then c v else 0), by
    rw [mem_AEsub]
    apply (prop_5_2 n N).injective
    ext v w
    rw [prop_5_2_mul_Ecyc, RingEquiv.apply_symm_apply]
    by_cases h : w = 1 <;> simp [h]⟩
  left_inv α := by
    apply Subtype.ext
    apply (prop_5_2 n N).injective
    ext v w
    have h := prop_5_2_mul_Ecyc n N α v w
    rw [(mem_AEsub n N).1 α.2] at h
    rw [RingEquiv.apply_symm_apply, Matrix.of_apply, h]
  right_inv c := by
    funext v
    simp
  map_add' α β := by
    funext v
    simp [Matrix.add_apply]
  map_smul' c α := by
    funext v
    show prop_5_2 n N (c • (α : ONH n N)) v 1 = c • prop_5_2 n N α v 1
    rw [map_zsmul]
    rfl

theorem AE_free_finite {n N : ℕ} (h : n+2 ≤ N) :
    Module.Free ℤ (AEsub n N) ∧ Module.Finite ℤ (AEsub n N) ∧
      Module.finrank ℤ (AEsub n N) = (n+2).factorial * N.choose (n+2) := by
  obtain ⟨h1, h2, h3⟩ := OH_free_finite h
  refine ⟨Module.Free.of_equiv (AEequiv n N).symm, Module.Finite.equiv (AEequiv n N).symm, ?_⟩
  rw [(AEequiv n N).finrank_eq, Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ,
    card_perm, h3, smul_eq_mul]

theorem actV_incCyc_Ecyc (k : ℕ) :
    actV (n+1) N (incCyc n N (Ecyc n N)) (Submodule.Quotient.mk (xl (n+1) ^ k)) =
      Submodule.Quotient.mk (xl (n+1) ^ k) := by
  rw [Ecyc, incCyc_toONH, actV_toONH]
  congr 1
  have h := action_window_place n (Etil n) 1 k
  rw [map_one, one_mul, action_Etil_one, map_one, one_mul] at h
  exact h

/-- **The relative basis of `ONH_{a+1}^N` over `ONH_a^N` spans** (`a = n+2`): the two-step flag
relation `span_place`. -/
theorem thetaS_surjective_G :
    Function.Surjective (thetaS (incCyc n N) (N - (n+2)) (AEsub n N)) := by
  intro v
  obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  obtain ⟨p, hp⟩ := span_place (m := n+1) N g
  refine ⟨fun k => ⟨toONH n N (OnhPolynomial.polyElem n (p k)) * Ecyc n N, by
    rw [mem_AEsub, mul_assoc, Ecyc_mul_self]⟩, ?_⟩
  show theta (incCyc n N) (N - (n+2)) (fun k =>
    toONH n N (OnhPolynomial.polyElem n (p k)) * Ecyc n N) = _
  rw [theta_apply]
  have hk : ∀ k : Fin (N - (n+2)), actV (n+1) N (incCyc n N (toONH n N
      (OnhPolynomial.polyElem n (p k)) * Ecyc n N)) (Submodule.Quotient.mk (xl (n+1) ^ (k : ℕ))) =
      Submodule.Quotient.mk (pl (n+1) (p k) * xl (n+1) ^ (k : ℕ)) := by
    intro k
    rw [Ecyc, ← map_mul, incCyc_toONH, actV_toONH]
    congr 1
    have h := action_window_place n (OnhPolynomial.polyElem n (p k) * Etil n) 1 k
    rw [map_one, one_mul, action_mul_apply, action_Etil_one, OnhPolynomial.action_polyElem,
      mul_one] at h
    exact h
  simp_rw [hk, ← Submodule.mkQ_apply, ← map_sum, Submodule.mkQ_apply]
  rw [eq_comm, Submodule.Quotient.eq]
  exact hp

theorem finrank_eq_G :
    (N - (n+2)) * ((n+2).factorial * N.choose (n+2)) = (n+3).factorial * N.choose (n+3) := by
  have hc := Nat.choose_succ_right_eq N (n+2)
  rw [Nat.factorial_succ]
  calc (N - (n+2)) * ((n+2).factorial * N.choose (n+2))
      = (n+2).factorial * (N.choose (n+2) * (N - (n+2))) := by ring
    _ = (n+2).factorial * (N.choose (n+2+1) * (n+2+1)) := by rw [hc]
    _ = (n+2+1) * (n+2).factorial * N.choose (n+3) := by ring

theorem thetaS_bijective_G (h : n+3 ≤ N) :
    Function.Bijective (thetaS (incCyc n N) (N - (n+2)) (AEsub n N)) := by
  obtain ⟨h1, h2, h3⟩ := AE_free_finite (n := n) (N := N) (by omega)
  obtain ⟨h4, h5, h6⟩ := vmod_free_finite (m := n+1) (N := N) h
  refine bijective_of_surjective_of_finrank_eq _ (thetaS_surjective_G n N) ?_
  rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, h3, h6,
    smul_eq_mul]
  exact finrank_eq_G n N

/-- **`ONH_{a+1}^N = ⊕_{w ∈ S_{a+1}, k < N-a} ONH_a^N E β_{w,k}`** as a left `ONH_a^N`-module,
`a = n+2 < N`. -/
def relBasisG (h : n+3 ≤ N) : RelBasis (incCyc n N) (Ecyc n N) (Perm (n+1) × Fin (N - (n+2))) :=
  relBasisOfTheta (Ecyc n N) (Ecyc_mul_self n N) (actV_incCyc_Ecyc n N)
    (existsUnique_theta_of_bijective (Ecyc n N) (AEsub n N) (fun _ => Iff.rfl)
      (thetaS_bijective_G n N h))

theorem relBasisG_vec (h : n+3 ≤ N) (p : Perm (n+1) × Fin (N - (n+2))) :
    (relBasisG n N h).vec p = betaVec N p.1 p.2 := rfl

end General

/-! ### `ONH_1^N = ℤ[x]/(x^N)` -/

/-- `ONH_1^N = ℤ[x]/(x^N)` is free on `1, x, …, x^{N-1}`. -/
def onh1Basis (N : ℕ) : Basis (Fin N) ℤ (ONH1 N) :=
  let pb := AdjoinRoot.powerBasis' (Polynomial.monic_X_pow (R := ℤ) N)
  (pb.basis.map (SmallRank.ONH1Equiv N).symm.toAddEquiv.toIntLinearEquiv).reindex
    (finCongr (by simp [pb, AdjoinRoot.powerBasis']))

theorem onh1Basis_apply (N : ℕ) (i : Fin N) :
    onh1Basis N i = toONH1 N (generator 0 ^ (i : ℕ)) := by
  simp only [onh1Basis, Basis.reindex_apply, Basis.map_apply, PowerBasis.coe_basis,
    AdjoinRoot.powerBasis'_gen]
  change (SmallRank.ONH1Equiv N).symm _ = _
  apply (SmallRank.ONH1Equiv N).injective
  rw [RingEquiv.apply_symm_apply, finCongr_symm_apply, Fin.coe_cast]
  change _ = AdjoinRoot.mk _ (SmallRank.rankOneEquiv (generator 0 ^ (i : ℕ)))
  rw [map_pow, SmallRank.rankOneEquiv_generator, map_pow, AdjoinRoot.mk_X]

theorem onh1_free_finite (N : ℕ) :
    Module.Free ℤ (ONH1 N) ∧ Module.Finite ℤ (ONH1 N) ∧ Module.finrank ℤ (ONH1 N) = N :=
  ⟨Module.Free.of_basis (onh1Basis N), Module.Finite.of_basis (onh1Basis N),
    by rw [Module.finrank_eq_card_basis (onh1Basis N), Fintype.card_fin]⟩

/-! ### `a = 1`: `ONH_2^N` over `ONH_1^N` -/

section One

variable (N : ℕ)

theorem actV_incCyc1_toONH1 (f : SkewPolynomial 1) (k : ℕ) :
    actV 0 N (incCyc1 N (toONH1 N f)) (Submodule.Quotient.mk (xl 0 ^ k)) =
      Submodule.Quotient.mk (pl 0 f * xl 0 ^ k) := by
  rw [incCyc1_toONH1, actV_toONH, action_dotHom_place]

theorem thetaS_surjective_1 :
    Function.Surjective (thetaS (incCyc1 N) (N - 1) (⊤ : Submodule ℤ (ONH1 N))) := by
  intro v
  obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  obtain ⟨p, hp⟩ := span_place (m := 0) N g
  refine ⟨fun k => ⟨toONH1 N (p k), Submodule.mem_top⟩, ?_⟩
  show theta (incCyc1 N) (N - 1) (fun k => toONH1 N (p k)) = _
  rw [theta_apply]
  simp_rw [actV_incCyc1_toONH1, ← Submodule.mkQ_apply, ← map_sum, Submodule.mkQ_apply]
  rw [eq_comm, Submodule.Quotient.eq]
  exact hp

theorem thetaS_bijective_1 (h : 2 ≤ N) :
    Function.Bijective (thetaS (incCyc1 N) (N - 1) (⊤ : Submodule ℤ (ONH1 N))) := by
  obtain ⟨h1, h2, h3⟩ := onh1_free_finite N
  obtain ⟨h4, h5, h6⟩ := vmod_free_finite (m := 0) (N := N) h
  haveI : Module.Free ℤ (⊤ : Submodule ℤ (ONH1 N)) := Module.Free.of_equiv Submodule.topEquiv.symm
  haveI : Module.Finite ℤ (⊤ : Submodule ℤ (ONH1 N)) := Module.Finite.equiv Submodule.topEquiv.symm
  refine bijective_of_surjective_of_finrank_eq _ (thetaS_surjective_1 N) ?_
  rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, finrank_top,
    h3, h6, smul_eq_mul]
  have hc := Nat.choose_succ_right_eq N 1
  rw [Nat.choose_one_right] at hc
  simp only [zero_add, Nat.factorial_two]
  rw [mul_comm 2, hc, mul_comm]

/-- **`ONH_2^N` is graded free over `ONH_1^N`** with basis `β_{w,k}`, `w ∈ S_2`, `k < N-1`. -/
def relBasis1 (h : 2 ≤ N) : RelBasis (incCyc1 N) (1 : ONH1 N) (Perm 0 × Fin (N - 1)) :=
  relBasisOfTheta 1 (mul_one 1) (fun k => by rw [map_one, map_one, Module.End.one_apply])
    (existsUnique_theta_of_bijective 1 ⊤ (fun x => by simp) (thetaS_bijective_1 N h))

theorem relBasis1_vec (h : 2 ≤ N) (p : Perm 0 × Fin (N - 1)) :
    (relBasis1 N h).vec p = betaVec N p.1 p.2 := rfl

end One

/-! ### `a = 0`: `ONH_1^N` over `ℤ` -/

section Zero

variable (N : ℕ)

/-- **`ONH_1^N` is graded free over `ONH_0^N = ℤ`** with basis `x^k`, `k < N`. -/
def relBasis0 : RelBasis (Int.castRingHom (ONH1 N)) (1 : ℤ) (Fin N) where
  vec k := toONH1 N (generator 0 ^ (k : ℕ))
  idem := mul_one 1
  E_vec k := by rw [map_one, one_mul]
  existsUnique y := by
    refine ⟨(onh1Basis N).equivFun y, ⟨fun k => mul_one _, ?_⟩, ?_⟩
    · simp_rw [_root_.eq_intCast, ← zsmul_eq_mul, ← onh1Basis_apply]
      exact (onh1Basis N).sum_equivFun y
    · rintro c ⟨-, hc⟩
      simp_rw [_root_.eq_intCast, ← zsmul_eq_mul, ← onh1Basis_apply] at hc
      rw [← hc, ← Basis.equivFun_symm_apply, LinearEquiv.apply_symm_apply]

theorem relBasis0_vec (k : Fin N) : (relBasis0 N).vec k = toONH1 N (generator 0 ^ (k : ℕ)) := rfl

end Zero

/-- The grading of `ONH_0 = ℤ` is a direct sum decomposition. -/
theorem intDecomposition : UniqueDecomposition intGrading := by
  intro x
  refine ⟨Finsupp.single 0 x, ⟨fun d => ?_, Finsupp.sum_single_index rfl⟩, ?_⟩
  · by_cases hd : d = 0
    · subst hd
      exact Or.inr rfl
    · rw [Finsupp.single_eq_of_ne (Ne.symm hd)]
      exact Or.inl rfl
  · rintro f ⟨hf, hfx⟩
    have hf0 : f = Finsupp.single 0 (f 0) := by
      ext d
      by_cases hd : d = 0
      · subst hd
        rw [Finsupp.single_eq_same]
      · rw [Finsupp.single_eq_of_ne (Ne.symm hd)]
        exact (hf d).resolve_right hd
    rw [hf0, Finsupp.sum_single_index rfl] at hfx
    rw [hf0, hfx]

end OddMath.Frontier.OddCyclotomicAction
