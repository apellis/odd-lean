import OddMath.Frontier.OddCyclotomicActionBasis

/-!
# Restriction on `K₀(ONH^N)`

EKL arXiv:1111.1320v1, §6, last paragraph (p. 47): restriction along `ONH_a^N → ONH_{a+1}^N`
(the tensor product with the bimodule `ONH_{a+1}^N`, the odd analogue of the cohomology of the
two-step flag variety `Fl(a, a+1; N)` after the Morita equivalence of Proposition 5.2)
descends to `K₀`.

* `cycRes N a h : K₀(ONH_{a+1}^N) → K₀(ONH_a^N)`, `a < N`: restriction, well defined on `K₀`
  because `ONH_{a+1}^N` is a finitely generated graded projective left `ONH_a^N`-module
  (`relBasisG`, `relBasis1`, `relBasis0`).
* `cycRes_vCyc`: `Res [E^{(a+1)}] = q^{N-2a-1} [N-a] [E^{(a)}]`.
* `cycF N a h = q^{2a+1-N} Res`, i.e. restriction followed by the grading shift `{λ - 1}`, where
  `λ = 2(a+1) - N` is the weight of `[E^{(a+1)}]`; `cycF_vCyc`: `F [E^{(a+1)}] = [N-a] [E^{(a)}]`.

Conventions as in `OddBialgebraAction`: `q = T 1` acts on `K₀` by the shift `{1}`, dots have
degree `2`, `[E^{(a)}] = [ONH_a^N e_a {C(a,2)}]`.
-/

noncomputable section
open LaurentPolynomial Matrix

namespace OddMath.Frontier.OddCyclotomicAction
open GradedK0 OddCategorification Cyclotomic OddBialgebra QuantumSl2Plus
open OddMath.SkewPolynomial (SkewPolynomial generator monomial)
open NilHeckeAction NilCoxeterWords

local notation "L" => LaurentPolynomial ℤ

/-! ### Sums of monomials -/

/-- `∑_{k < b} q^{2k} = q^{b-1} [b]`. -/
theorem sum_T_two_mul (b : ℕ) :
    ∑ k : Fin b, (T (2 * (k : ℤ)) : L) = T ((b : ℤ) - 1) * qInt b := by
  rw [qInt, Finset.mul_sum, Fin.sum_univ_eq_sum_range (fun k => (T (2 * (k : ℤ)) : L)),
    ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun i hi => ?_
  have := Finset.mem_range.1 hi
  rw [← T_add]
  congr 1
  have e : ((b - 1 - i : ℕ) : ℤ) = (b : ℤ) - 1 - i := by omega
  rw [e]
  ring

/-- `∑_{w ∈ S_a} q^{-2ℓ(w)} = q^{-C(a,2)} [a]!`. -/
theorem sum_T_neg_length (n : ℕ) :
    ∑ w : Perm n, (T (-(2 * (length w : ℤ))) : L) =
      T (-(((n+2).choose 2 : ℕ) : ℤ)) * qFact (n+2) :=
  (onhCycK0Equiv_one n (n+2) le_rfl).symm.trans (onhCycK0Equiv_one_qFact n (n+2) le_rfl)

/-- `K₀(ONH_a^N)` is torsion free over `ℤ[q,q⁻¹]`, `a ≤ N`. -/
theorem smul_cancel {M : Type*} [AddCommGroup M] [Module L M] (e : M ≃ₗ[L] L) {c : L}
    (hc : c ≠ 0) {x y : M} (h : c • x = c • y) : x = y := by
  apply e.injective
  have := congrArg e h
  rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul] at this
  exact mul_left_cancel₀ hc this

/-! ### The three restrictions -/

/-- The degrees `2k - 2ℓ(w)` of `β_{w,k}`. -/
def sβ {m b : ℕ} (p : Perm m × Fin b) : ℤ := 2 * (p.2 : ℤ) - 2 * (length p.1 : ℤ)

theorem sum_T_sβ (m b : ℕ) (k : ℤ) :
    ∑ p : Perm m × Fin b, (T (k + sβ p) : L) =
      T k * (T (-(((m+2).choose 2 : ℕ) : ℤ)) * qFact (m+2)) * (T ((b : ℤ) - 1) * qInt b) := by
  rw [← sum_T_neg_length, ← sum_T_two_mul, mul_assoc, Finset.sum_mul_sum, Fintype.sum_prod_type]
  simp_rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← T_add, ← T_add, sβ]
  congr 1
  ring

section General

variable (n N : ℕ)

theorem nonempty_G (h : n+3 ≤ N) : Nonempty (Perm (n+1) × Fin (N - (n+2))) :=
  ⟨(1, ⟨0, by omega⟩)⟩

/-- **Restriction** `K₀(ONH_{a+1}^N) → K₀(ONH_a^N)`, `a = n+2 < N`. -/
def resG (h : n+3 ≤ N) : K0 (onhCycGrading (n+1) N) →ₗ[L] K0 (onhCycGrading n N) :=
  haveI := nonempty_G n N h
  (relBasisG n N h).res (onhCycDecomposition n N) (onhCycDecomposition (n+1) N) incCyc_mem
    (Ecyc_mem n N) sβ (fun p => betaVec_mem p.1 p.2)

theorem prop_5_2_Ecyc_eq : prop_5_2 n N (Ecyc n N) = stdBasisMatrix 1 1 1 := by
  ext v w
  rw [prop_5_2_Ecyc, stdBasisMatrix, Matrix.of_apply]
  simp only [eq_comm]

/-- `[ONH_a^N E] = q^{C(a,2)} [E^{(a)}]`. -/
theorem of_gelem_Ecyc (h : n+2 ≤ N) :
    K0.of (gelem (Ecyc_mem n N) (Ecyc_mul_self n N) 0) =
      (T (((n+2).choose 2 : ℕ) : ℤ) : L) • vCyc N (n+2) := by
  apply (onhCycK0Equiv n N h).injective
  rw [map_smul, show onhCycK0Equiv n N h (vCyc N (n+2)) = _ from cycRankEquiv_vCyc N (n+2) h,
    smul_eq_mul, ← T_add, add_neg_cancel]
  simp only [onhCycK0Equiv, LinearEquiv.trans_apply, k0Equiv_of]
  have hc : gmap (prop_5_2 n N) (prop_5_2_mem_matGrading n N)
      (gelem (Ecyc_mem n N) (Ecyc_mul_self n N) 0) ≈ GIdem.corner (lenShift n) 1 := by
    refine MvN.of_equiv (Equiv.refl _) (gmap _ _ _).hom (gmap _ _ _).idem (fun _ => rfl)
      (fun i j => ?_)
    obtain ⟨i, hi⟩ := i
    obtain ⟨j, hj⟩ := j
    change i < 1 at hi
    change j < 1 at hj
    obtain rfl : i = 0 := by omega
    obtain rfl : j = 0 := by omega
    show stdBasisMatrix (1 : Perm n) 1 (1 : OH n N) =
      ((diagonal fun _ : Fin 1 => Ecyc n N).map (prop_5_2 n N)) 0 0
    rw [Matrix.map_apply, diagonal_apply_eq, prop_5_2_Ecyc_eq]
  rw [K0.of_eq hc, K0.morita_corner, K0.classify_single]
  simp [lenShift]

theorem resG_vCyc (h : n+3 ≤ N) :
    resG n N h (vCyc N (n+3)) =
      (T ((N : ℤ) - 2 * ((n+2 : ℕ) : ℤ) - 1) * qInt (N - (n+2))) • vCyc N (n+2) := by
  haveI := nonempty_G n N h
  have hB := cyc_single_eq N (n+1)
  have hres := (relBasisG n N h).res_single (onhCycDecomposition n N)
    (onhCycDecomposition (n+1) N) incCyc_mem (Ecyc_mem n N) sβ (fun p => betaVec_mem p.1 p.2) 0
  rw [hB, map_smul] at hres
  change qFact (n+3) • resG n N h (vCyc N (n+3)) = _ at hres
  rw [of_gelem_Ecyc n N (by omega), ← Finset.sum_smul] at hres
  simp_rw [smul_smul] at hres
  rw [sum_T_sβ] at hres
  refine smul_cancel (onhCycK0Equiv n N (by omega)) (qFact_ne_zero (n+3)) ?_
  rw [hres, smul_smul]
  congr 1
  have h1 : ((n+3).choose 2 : ℤ) = ((n+2).choose 2 : ℤ) + (n+2) := by
    rw [Nat.choose_succ_succ', Nat.choose_one_right]
    push_cast
    ring
  rw [show (n+1+2) = n+3 from rfl]
  simp only [T_zero, one_mul]
  have e1 : ((N - (n+2) : ℕ) : ℤ) = (N : ℤ) - (n+2) := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [e1]
  calc T (-(((n+3).choose 2 : ℕ) : ℤ)) * qFact (n+3) *
        (T ((N : ℤ) - (n+2) - 1) * qInt (N - (n+2))) *
        T (((n+2).choose 2 : ℕ) : ℤ)
      = qFact (n+3) * ((T (-(((n+3).choose 2 : ℕ) : ℤ)) * T ((N : ℤ) - (n+2) - 1) *
          T (((n+2).choose 2 : ℕ) : ℤ)) * qInt (N - (n+2))) := by ring
    _ = qFact (n+3) * (T ((N : ℤ) - 2 * ((n+2 : ℕ) : ℤ) - 1) * qInt (N - (n+2))) := by
        rw [← T_add, ← T_add]
        congr 3
        push_cast at h1 ⊢
        linarith

end General

section One

variable (N : ℕ)

theorem nonempty_1 (h : 2 ≤ N) : Nonempty (Perm 0 × Fin (N - 1)) := ⟨(1, ⟨0, by omega⟩)⟩

theorem one_mem_onh1 : (1 : ONH1 N) ∈ onh1Grading N 0 := SetLike.GradedOne.one_mem

/-- **Restriction** `K₀(ONH_2^N) → K₀(ONH_1^N)`, `1 < N`. -/
def res1 (h : 2 ≤ N) : K0 (onhCycGrading 0 N) →ₗ[L] K0 (onh1Grading N) :=
  haveI := nonempty_1 N h
  (relBasis1 N h).res (onh1Decomposition N) (onhCycDecomposition 0 N) incCyc1_mem
    (one_mem_onh1 N) sβ (fun p => betaVec_mem p.1 p.2)

theorem of_gelem_one_onh1 :
    K0.of (gelem (one_mem_onh1 N) (mul_one (1 : ONH1 N)) 0) = vCyc N 1 := by
  rw [show vCyc N 1 = toKCyc N 1 (K0.of (GIdem.single 0)) from rfl, toKCyc_single_one]
  exact K0.of_eq (MvN.of_equiv (Equiv.refl _) (gelem _ _ 0).hom (gelem _ _ 0).idem
    (fun _ => rfl) (fun i j => by simp [gelem, gdiag, GIdem.single, GIdem.free, diagonal_one]))

theorem res1_vCyc (h : 2 ≤ N) :
    res1 N h (vCyc N 2) = (T ((N : ℤ) - 2 * ((1 : ℕ) : ℤ) - 1) * qInt (N - 1)) • vCyc N 1 := by
  haveI := nonempty_1 N h
  have hB := cyc_single_eq N 0
  have hres := (relBasis1 N h).res_single (onh1Decomposition N) (onhCycDecomposition 0 N)
    incCyc1_mem (one_mem_onh1 N) sβ (fun p => betaVec_mem p.1 p.2) 0
  rw [hB, map_smul] at hres
  change qFact 2 • res1 N h (vCyc N 2) = _ at hres
  rw [of_gelem_one_onh1, ← Finset.sum_smul, sum_T_sβ] at hres
  refine smul_cancel (cycRankEquiv N 1 (by omega)) (qFact_ne_zero 2) ?_
  rw [hres, smul_smul]
  congr 1
  have e1 : ((N - 1 : ℕ) : ℤ) = (N : ℤ) - 1 := by rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [e1, T_zero, one_mul]
  calc T (-((Nat.choose (0+2) 2 : ℕ) : ℤ)) * qFact (0+2) * (T ((N : ℤ) - 1 - 1) * qInt (N - 1))
      = qFact 2 * (T (-((Nat.choose 2 2 : ℕ) : ℤ)) * T ((N : ℤ) - 1 - 1) * qInt (N - 1)) := by
        ring
    _ = qFact 2 * (T ((N : ℤ) - 2 * ((1 : ℕ) : ℤ) - 1) * qInt (N - 1)) := by
        rw [← T_add]
        congr 3
        simp only [Nat.choose_self, Nat.cast_one]
        ring

end One

section Zero

variable (N : ℕ)

theorem nonempty_0 (h : 1 ≤ N) : Nonempty (Fin N) := ⟨⟨0, h⟩⟩

theorem one_mem_int : (1 : ℤ) ∈ intGrading 0 := Or.inr rfl

theorem toONH1_pow_mem (k : ℕ) :
    toONH1 N (generator 0 ^ k) ∈ onh1Grading N (2 * (k : ℤ)) :=
  toONH1_mem (generator_pow_mem k)

/-- **Restriction** `K₀(ONH_1^N) → K₀(ONH_0^N) = K₀(ℤ)`, `0 < N`. -/
def res0 (h : 1 ≤ N) : K0 (onh1Grading N) →ₗ[L] K0 intGrading :=
  haveI := nonempty_0 N h
  (relBasis0 N).res intDecomposition (onh1Decomposition N) intCast_onh1_mem one_mem_int
    (fun k : Fin N => 2 * (k : ℤ)) (fun k => toONH1_pow_mem N k)

theorem of_gelem_one_int :
    K0.of (gelem one_mem_int (mul_one (1 : ℤ)) 0) = vCyc N 0 :=
  K0.of_eq (MvN.of_equiv (Equiv.refl _) (gelem _ _ 0).hom (gelem _ _ 0).idem
    (fun _ => rfl) (fun i j => by simp [gelem, gdiag, GIdem.single, GIdem.free, diagonal_one]))

theorem res0_vCyc (h : 1 ≤ N) :
    res0 N h (vCyc N 1) = (T ((N : ℤ) - 2 * ((0 : ℕ) : ℤ) - 1) * qInt (N - 0)) • vCyc N 0 := by
  haveI := nonempty_0 N h
  have hres := (relBasis0 N).res_single intDecomposition (onh1Decomposition N) intCast_onh1_mem
    one_mem_int (fun k : Fin N => 2 * (k : ℤ)) (fun k => toONH1_pow_mem N k) 0
  rw [← toKCyc_single_one] at hres
  change res0 N h (vCyc N 1) = _ at hres
  rw [hres, of_gelem_one_int, ← Finset.sum_smul]
  congr 1
  simp only [zero_add, Nat.cast_zero, mul_zero, sub_zero, Nat.sub_zero]
  exact sum_T_two_mul N

end Zero

/-! ### Restriction and `F` on `K₀(ONH^N)` -/

/-- **Restriction** `K₀(ONH_{a+1}^N) → K₀(ONH_a^N)` along `x ↦ x ⊗ 1`, for `a < N`. -/
def cycRes (N : ℕ) : (a : ℕ) → a < N → (KCyc N (a+1) →ₗ[L] KCyc N a)
  | 0, h => res0 N h
  | 1, h => res1 N h
  | n+2, h => resG n N h

/-- **Restriction on the basis**: `Res [E^{(a+1)}] = q^{N-2a-1} [N-a] [E^{(a)}]`. -/
theorem cycRes_vCyc (N : ℕ) : ∀ (a : ℕ) (h : a < N),
    cycRes N a h (vCyc N (a+1)) = (T ((N : ℤ) - 2 * (a : ℤ) - 1) * qInt (N - a)) • vCyc N a
  | 0, h => res0_vCyc N h
  | 1, h => res1_vCyc N h
  | n+2, h => resG_vCyc n N h

/-- `F = Res{λ - 1}`, `λ = 2(a+1) - N` the weight of `[E^{(a+1)}]`. -/
def cycF (N a : ℕ) (h : a < N) : KCyc N (a+1) →ₗ[L] KCyc N a :=
  (T (2 * (a : ℤ) + 1 - N) : L) • cycRes N a h

/-- **`F` on the basis**: `F [E^{(a+1)}] = [N-a] [E^{(a)}]`. -/
theorem cycF_vCyc (N a : ℕ) (h : a < N) :
    cycF N a h (vCyc N (a+1)) = qInt (N - a) • vCyc N a := by
  rw [cycF, LinearMap.smul_apply, cycRes_vCyc, smul_smul, ← mul_assoc, ← T_add,
    show 2 * (a : ℤ) + 1 - N + (N - 2 * a - 1) = 0 by ring, T_zero, one_mul]

end OddMath.Frontier.OddCyclotomicAction
