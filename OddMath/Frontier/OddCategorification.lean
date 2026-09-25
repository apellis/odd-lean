import OddMath.Frontier.OddCategorificationInduction

/-!
# Odd categorification of `U_q^+(sl_2)`

EKL arXiv:1111.1320v1, §6, pp. 46–47, (6.1)–(6.3): `U_q^+(sl_2)_A ≅ K₀(ONH)`,
`ϑ^{(a)} ↦ [E^{(a)}]`, `A = ℤ[q,q⁻¹]`.

Conventions. Gradings are in the paper normalization (a dot of degree `2`, a crossing of
degree `-2`); `K₀` is the graded Grothendieck group of graded projectives, modelled by graded
idempotent matrices (`GradedK0`), a `ℤ[q,q⁻¹]`-module with `q = T 1` acting by the shift `{1}`
(`R{k}` has its generator in degree `k`). For `a ≥ 2` (`a = n+2`), `ONH_a =
NilHeckeAction.Presented n`, `e_a = ZeroHecke.projector n`, and
`E^{(a)} = ONH_a e_a {C(a,2)}` (`divE`); `ONH_0 = ℤ`, `ONH_1 = OPol_1 = SkewPolynomial 1`
and `E^{(0)} = ONH_0`, `E^{(1)} = ONH_1`. (The paper writes the shift of `E^{(a)}` as
`{-a(a-1)/2}`; the sign is the global sign of the shift convention.)

What is formalized.
* `K₀(ONH_a) ≃ ℤ[q,q⁻¹]` for every `a` (`rankEquiv`): for `a ≥ 2` through the graded ring
  isomorphism `ONH_a ≅ Mat_{S_a}(OΛ_a)` (Corollary 2.14), graded Morita invariance and the
  classification of graded projectives over the connected ring `OΛ_a`; `[E^{(a)}] ↦ q^{-C(a,2)}`,
  so `[E^{(a)}]` is a `ℤ[q,q⁻¹]`-basis of `K₀(ONH_a)` (`basisE`). This uses (6.1) as the
  Murray–von Neumann equivalence `ONH_a ≅ ⊕_{ℓ ∈ Sq(a)} E^{(a)}{C(a,2) - 2|ℓ|}`
  (`eq_6_1_K0`, `eq_6_1_qFact`: `[ONH_a] = [a]! [E^{(a)}]`) and the Mahonian identity
  `∑_{w ∈ S_a} q^{2ℓ(w)} = ∑_{ℓ ∈ Sq(a)} q^{2|ℓ|}`. The printed exponents `a - 1 - 2|ℓ|` of
  (6.1) are wrong for `a = 3` (`eq_6_1_printed_false`).
* Induction on indecomposables (`indClass`): `E^{(a)} ⊠ E^{(b)}` is induced to `ONH_{a+b}` as
  `ONH_{a+b}(e_a ⊗ e_b){C(a,2) + C(b,2)}` with the idempotent `e_a ⊗ e_b = blockE 0 a · blockE a b`
  (for `a + b ≤ 1` this is `ONH_{a+b}`), and (6.2) gives `[E^{(a)}E^{(b)}] = [a+b, a] [E^{(a+b)}]`
  (`indClass_eq`, from `eq_6_2_K0`).
* `K₀(ONH) = ⊕_a K₀(ONH_a)` (`K0ONH`, a `DFinsupp`), free on the `[E^{(a)}]` (`basisK0`), with the
  `ℤ[q,q⁻¹]`-bilinear product determined on this basis by `[E^{(a)}] · [E^{(b)}] := [E^{(a)}E^{(b)}]`
  (`mulK0`). The product on classes of arbitrary graded projectives (the induction functor on
  all of `K₀(ONH_a) ⊗ K₀(ONH_b)`) is not constructed.
* **(6.3)** (`eq_6_3`, `eq_6_3_UA`): `DivPowAlg ≃ₐ[ℤ[q,q⁻¹]] K₀(ONH)` and
  `U_q^+(sl_2)_A ≃ₐ K₀(ONH)`, `ϑ^{(a)} = E^{(a)} ↦ [E^{(a)}]`.
-/

noncomputable section
open LaurentPolynomial

namespace OddMath.Frontier.OddCategorification
open GradedK0 QuantumSl2Plus

local notation "L" => LaurentPolynomial ℤ

/-! ### `K₀(ONH_a)` for all `a` -/

/-- `K₀(ONH_a)`: `ONH_0 = ℤ`, `ONH_1 = OPol_1`, `ONH_{n+2} = NilHeckeAction.Presented n`. -/
def KONH : ℕ → Type
  | 0 => K0 intGrading
  | 1 => K0 opolGrading
  | n+2 => K0 (onhGrading n)

instance KONH.addCommGroup : ∀ a, AddCommGroup (KONH a)
  | 0 => inferInstanceAs (AddCommGroup (K0 intGrading))
  | 1 => inferInstanceAs (AddCommGroup (K0 opolGrading))
  | n+2 => inferInstanceAs (AddCommGroup (K0 (onhGrading n)))

instance KONH.module : ∀ a, Module L (KONH a)
  | 0 => inferInstanceAs (Module L (K0 intGrading))
  | 1 => inferInstanceAs (Module L (K0 opolGrading))
  | n+2 => inferInstanceAs (Module L (K0 (onhGrading n)))

/-- The class `[E^{(a)}] ∈ K₀(ONH_a)`. -/
def Eclass : (a : ℕ) → KONH a
  | 0 => (K0.of (GIdem.single 0) : K0 intGrading)
  | 1 => (K0.of (GIdem.single 0) : K0 opolGrading)
  | n+2 => (K0.of (divE n) : K0 (onhGrading n))

/-- `K₀(ONH_a) ≃ ℤ[q,q⁻¹]`. -/
def rankEquiv : (a : ℕ) → KONH a ≃ₗ[L] L
  | 0 => K0.classify intConnected
  | 1 => K0.classify opolConnected
  | n+2 => onhK0Equiv n

theorem rankEquiv_Eclass : ∀ a, rankEquiv a (Eclass a) = T (-((a.choose 2 : ℕ) : ℤ))
  | 0 => K0.classify_single intConnected 0
  | 1 => K0.classify_single opolConnected 0
  | n+2 => onhK0Equiv_divE n

/-- `[E^{(a)}]` is a `ℤ[q,q⁻¹]`-basis of `K₀(ONH_a)`. -/
def basisE (a : ℕ) : Basis (Fin 1) L (KONH a) :=
  ((Basis.singleton (Fin 1) L).map (rankEquiv a).symm).unitsSMul
    fun _ => (isUnit_T (-((a.choose 2 : ℕ) : ℤ))).unit

theorem basisE_apply (a : ℕ) (i : Fin 1) : basisE a i = Eclass a := by
  rw [basisE, Basis.unitsSMul_apply, Basis.map_apply, Basis.singleton_apply, Units.smul_def,
    IsUnit.unit_spec, ← map_smul, smul_eq_mul, mul_one, LinearEquiv.symm_apply_eq,
    rankEquiv_Eclass]

/-! ### Induction on the indecomposables -/

/-- `[E^{(a)}E^{(b)}] ∈ K₀(ONH_m)`, `a + b = m`: the class of `ONH_m(e_a ⊗ e_b){C(a,2)+C(b,2)}`
for `m ≥ 2`, and of `ONH_m` for `m ≤ 1`. -/
def indAux : (m a b : ℕ) → a + b = m → KONH m
  | 0, _, _, _ => (K0.of (GIdem.single 0) : K0 intGrading)
  | 1, _, _, _ => (K0.of (GIdem.single 0) : K0 opolGrading)
  | _+2, _, _, hab => (K0.of (indE hab) : K0 (onhGrading _))

/-- The induced class `[E^{(a)}E^{(b)}] ∈ K₀(ONH_{a+b})` of `E^{(a)} ⊠ E^{(b)}`. -/
def indClass (a b : ℕ) : KONH (a + b) := indAux (a + b) a b rfl

theorem indAux_eq : ∀ m a b (hab : a + b = m), indAux m a b hab = qBinom a b • Eclass m
  | 0, a, b, hab => by
    obtain ⟨rfl, rfl⟩ : a = 0 ∧ b = 0 := by omega
    rw [qBinom_zero_left, one_smul]
    rfl
  | 1, a, b, hab => by
    rcases (by omega : a = 0 ∧ b = 1 ∨ a = 1 ∧ b = 0) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [qBinom_zero_left, one_smul]
      rfl
    · rw [qBinom_zero_right, one_smul]
      rfl
  | _+2, _, _, hab => eq_6_2_K0 hab

/-- **(6.2)**: `[E^{(a)}E^{(b)}] = [a+b, a] [E^{(a+b)}]`. -/
theorem indClass_eq (a b : ℕ) : indClass a b = qBinom a b • Eclass (a + b) :=
  indAux_eq (a + b) a b rfl

/-! ### `K₀(ONH) = ⊕_a K₀(ONH_a)` -/

/-- `K₀(ONH) = ⊕_{a ≥ 0} K₀(ONH_a)`. -/
abbrev K0ONH : Type := Π₀ a, KONH a

/-- The basis `{[E^{(a)}]}` of `K₀(ONH)`. -/
def basisK0 : Basis ℕ L K0ONH :=
  (DFinsupp.basis basisE).reindex (Equiv.sigmaUnique ℕ fun _ => Fin 1)

theorem basisK0_apply (a : ℕ) : basisK0 a = DFinsupp.single a (Eclass a) := by
  rw [basisK0, Basis.reindex_apply]
  simp [DFinsupp.basis, sigmaFinsuppLequivDFinsupp, basisE_apply]

/-- The `ℤ[q,q⁻¹]`-bilinear product of `K₀(ONH)`, determined on the basis by
`[E^{(a)}] · [E^{(b)}] = [E^{(a)}E^{(b)}]`. -/
def mulK0 : K0ONH →ₗ[L] K0ONH →ₗ[L] K0ONH :=
  basisK0.constr L fun a => basisK0.constr L fun b => DFinsupp.single (a + b) (indClass a b)

theorem mulK0_basis (a b : ℕ) :
    mulK0 (basisK0 a) (basisK0 b) = DFinsupp.single (a + b) (indClass a b) := by
  rw [mulK0, Basis.constr_basis, Basis.constr_basis]

theorem mulK0_basis_eq (a b : ℕ) :
    mulK0 (basisK0 a) (basisK0 b) = qBinom a b • basisK0 (a + b) := by
  rw [mulK0_basis, indClass_eq, basisK0_apply, DFinsupp.single_smul]

/-- The basis identification `ϑ^{(a)} ↦ [E^{(a)}]`, as a linear equivalence. -/
def basisEquiv : DivPowAlg ≃ₗ[L] K0ONH := DivPowAlg.basis.equiv basisK0 (Equiv.refl ℕ)

theorem basisEquiv_θ (a : ℕ) : basisEquiv (DivPowAlg.θ a) = basisK0 a := by
  rw [basisEquiv, ← DivPowAlg.basis_apply, Basis.equiv_apply, Equiv.refl_apply]

theorem mulK0_basisEquiv (x y : DivPowAlg) :
    mulK0 (basisEquiv x) (basisEquiv y) = basisEquiv (x * y) := by
  have h : mulK0.compl₁₂ basisEquiv.toLinearMap basisEquiv.toLinearMap =
      DivPowAlg.mulL.compr₂ basisEquiv.toLinearMap :=
    LinearMap.ext_basis DivPowAlg.basis DivPowAlg.basis fun a b => by
      simp only [LinearMap.compl₁₂_apply, LinearMap.compr₂_apply, LinearEquiv.coe_coe,
        DivPowAlg.basis_apply, basisEquiv_θ, mulK0_basis_eq, ← DivPowAlg.mul_def,
        DivPowAlg.θ_mul_θ, map_smul]
  exact DFunLike.congr_fun (DFunLike.congr_fun h x) y

instance : Mul K0ONH := ⟨fun x y => mulK0 x y⟩

instance : One K0ONH := ⟨basisK0 0⟩

theorem mul_def (x y : K0ONH) : x * y = mulK0 x y := rfl

theorem one_def : (1 : K0ONH) = basisK0 0 := rfl

theorem basisEquiv_mul (x y : DivPowAlg) :
    basisEquiv (x * y) = basisEquiv x * basisEquiv y :=
  (mulK0_basisEquiv x y).symm

theorem basisEquiv_one : basisEquiv 1 = 1 := by
  rw [DivPowAlg.one_def, basisEquiv_θ, one_def]

private theorem mul_assoc' (x y z : K0ONH) : x * y * z = x * (y * z) := by
  obtain ⟨x, rfl⟩ := basisEquiv.surjective x
  obtain ⟨y, rfl⟩ := basisEquiv.surjective y
  obtain ⟨z, rfl⟩ := basisEquiv.surjective z
  simp only [← basisEquiv_mul, mul_assoc]

private theorem mul_comm' (x y : K0ONH) : x * y = y * x := by
  obtain ⟨x, rfl⟩ := basisEquiv.surjective x
  obtain ⟨y, rfl⟩ := basisEquiv.surjective y
  rw [← basisEquiv_mul, ← basisEquiv_mul, mul_comm]

private theorem one_mul' (x : K0ONH) : 1 * x = x := by
  obtain ⟨x, rfl⟩ := basisEquiv.surjective x
  rw [← basisEquiv_one, ← basisEquiv_mul, one_mul]

instance : CommRing K0ONH :=
  { (inferInstance : AddCommGroup K0ONH) with
    mul := (· * ·)
    one := 1
    left_distrib := fun x y z => map_add (mulK0 x) y z
    right_distrib := fun x y z => by simp only [mul_def, map_add, LinearMap.add_apply]
    zero_mul := fun x => by simp only [mul_def, map_zero, LinearMap.zero_apply]
    mul_zero := fun x => map_zero (mulK0 x)
    mul_assoc := mul_assoc'
    one_mul := one_mul'
    mul_one := fun x => (mul_comm' x 1).trans (one_mul' x)
    mul_comm := mul_comm' }

instance : Algebra L K0ONH :=
  Algebra.ofModule (fun r x y => by simp only [mul_def, map_smul, LinearMap.smul_apply])
    (fun r x y => map_smul (mulK0 x) r y)

theorem basisK0_mul (a b : ℕ) : basisK0 a * basisK0 b = qBinom a b • basisK0 (a + b) :=
  mulK0_basis_eq a b

/-- The product on the basis: `[E^{(a)}] · [E^{(b)}] = [E^{(a)}E^{(b)}]`. -/
theorem single_mul_single (a b : ℕ) :
    (DFinsupp.single a (Eclass a) : K0ONH) * DFinsupp.single b (Eclass b) =
      DFinsupp.single (a + b) (indClass a b) := by
  rw [← basisK0_apply, ← basisK0_apply]
  exact mulK0_basis a b

/-! ### (6.3) -/

/-- **EKL (6.3)**: `U_q^+(sl_2)_A ≅ K₀(ONH)` as `A = ℤ[q,q⁻¹]`-algebras, in the presentation
`DivPowAlg` (free on `ϑ^{(a)}`, `ϑ^{(a)}ϑ^{(b)} = [a+b, a] ϑ^{(a+b)}`),
`ϑ^{(a)} ↦ [E^{(a)}]` (`eq_6_3_θ`). -/
def eq_6_3 : DivPowAlg ≃ₐ[L] K0ONH := DivPowAlg.liftEquiv basisK0 one_def.symm basisK0_mul

theorem eq_6_3_θ (a : ℕ) : eq_6_3 (DivPowAlg.θ a) = DFinsupp.single a (Eclass a) := by
  rw [eq_6_3, DivPowAlg.liftEquiv_θ, basisK0_apply]

/-- **EKL (6.3)** for Lusztig's integral form `U_q^+(sl_2)_A ⊆ ℚ(q)[E]`:
`E^{(a)} = E^a / [a]! ↦ [E^{(a)}]`. -/
def eq_6_3_UA : UA ≃ₐ[L] K0ONH := DivPowAlg.equivUA.symm.trans eq_6_3

theorem eq_6_3_UA_basis (a : ℕ) : eq_6_3_UA (UA.basis a) = DFinsupp.single a (Eclass a) := by
  rw [eq_6_3_UA, AlgEquiv.trans_apply, UA.basis_eq, AlgEquiv.symm_apply_apply, eq_6_3_θ]

end OddMath.Frontier.OddCategorification
