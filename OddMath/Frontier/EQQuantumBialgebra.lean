import OddMath.Frontier.OddBialgebraCoproduct
import OddMath.Frontier.EQQuantumBinomial

/-!
# Specialised divided power algebras and their twisted tensor squares

Ellis–Qi arXiv:1504.01712v2, §2.1, is about the specialisation at `q = √−1` of Lusztig's integral
form `U_A = U_q^+(sl₂)_A` (`QuantumSl2Plus.DivPowAlg`), with its twisted coproduct. Here we set up
the specialisation along an arbitrary ring map `φ : ℤ[q, q⁻¹] → R` (`R` commutative):

* `DP φ`: the free `R`-module on `E^{(a)}` (`DP.E φ a`), `a ∈ ℕ`, with
  `E^{(a)} E^{(b)} = φ[a+b, a] E^{(a+b)}` (a commutative `R`-algebra); `mapDP φ : U_A → DP φ` is the
  ring map `E^{(a)} ↦ E^{(a)}` which is `φ` on coefficients.
* `TT φ t`: the free `R`-module on `E^{(a)} ⊗ E^{(b)}` (`TT.tw a b`), with the twisted product
  `(E^{(a)} ⊗ E^{(b)})(E^{(c)} ⊗ E^{(d)}) = t^{bc} E^{(a)}E^{(c)} ⊗ E^{(b)}E^{(d)}`
  (`TT.tmul_mul_tmul`), i.e. the product of §2.1 with `|E^{(n)}| = n` and twist parameter `t`;
  `TT.tensorEquiv : TT φ t ≃ₗ[R] DP φ ⊗[R] DP φ`. For `φ Q = t`, `mapTT` is the ring map from the
  library's `OddBialgebra.TwTensor Q` (Ellis–Khovanov twisted tensor square, braiding `Q`).
* `rVal φ t n = ∑_{a+b=n} φ(q^{-ab}) E^{(a)} ⊗ E^{(b)}`. If `t = φ(q^{-2})` it is multiplicative
  (`rVal_mul`, transported from the library's `OddBialgebra.coprodVal_mul`), giving the algebra map
  `r : DP φ → TT φ t` (`r_E`, `r_mapDP`), coassociative (`coassoc`) with counit (`counit`,
  `counitLeft_r`, `counitRight_r`).
* `twist_eq_neg_one_of_sq_zero`: whatever `φ` is, if `φ[2, 1] = 0` (as at `q = √−1`) then an
  algebra map `f : DP φ → TT φ t` with `f(E^{(1)}) = E^{(1)} ⊗ 1 + 1 ⊗ E^{(1)}` exists only if
  `t = −1`: the coefficient of `E^{(1)} ⊗ E^{(1)}` in `f(E^{(1)})² = 0` is `1 + t`
  (`coeff_tw_sq`).
-/

noncomputable section
open Finset LaurentPolynomial
open scoped TensorProduct

namespace OddMath.Frontier.EQQuantum
open QuantumSl2Plus

local notation "A" => LaurentPolynomial ℤ

variable {R : Type*} [CommRing R]

/-! ### The specialised divided power algebra -/

/-- The divided power algebra `U_A` specialised along `φ : ℤ[q, q⁻¹] → R`: the free `R`-module on
symbols `E^{(a)}`, with `E^{(a)} E^{(b)} = φ[a+b, a] E^{(a+b)}`. -/
def DP (_φ : A →+* R) : Type _ := ℕ →₀ R

namespace DP

variable {φ : A →+* R}

instance : AddCommGroup (DP φ) := inferInstanceAs (AddCommGroup (ℕ →₀ R))

instance : Module R (DP φ) := inferInstanceAs (Module R (ℕ →₀ R))

variable (φ) in
/-- `r E^{(a)}`. -/
def single (a : ℕ) (r : R) : DP φ := Finsupp.single a r

variable (φ) in
/-- The divided power `E^{(a)}`. -/
def E (a : ℕ) : DP φ := single φ a 1

@[elab_as_elim]
theorem induction_linear {p : DP φ → Prop} (f : DP φ) (h0 : p 0)
    (hadd : ∀ f g, p f → p g → p (f + g)) (hs : ∀ a r, p (single φ a r)) : p f :=
  Finsupp.induction_linear (motive := p) f h0 hadd hs

theorem smul_single (c : R) (a : ℕ) (r : R) : c • single φ a r = single φ a (c * r) :=
  Finsupp.smul_single c a r

theorem single_eq_smul (a : ℕ) (r : R) : single φ a r = r • E φ a := by
  rw [E, smul_single, mul_one]

variable (φ) in
/-- The basis `{E^{(a)}}`. -/
def basis : Module.Basis ℕ R (DP φ) := Finsupp.basisSingleOne

@[simp] theorem basis_apply (a : ℕ) : basis φ a = E φ a := rfl

instance : Module.Free R (DP φ) := .of_basis (basis φ)

variable (φ) in
/-- The multiplication, as a bilinear map. -/
def mulL : DP φ →ₗ[R] DP φ →ₗ[R] DP φ :=
  (basis φ).constr R fun a => (basis φ).constr R fun b => φ (qBinom a b) • E φ (a + b)

theorem mulL_E (a b : ℕ) : mulL φ (E φ a) (E φ b) = φ (qBinom a b) • E φ (a + b) := by
  rw [mulL, ← basis_apply, Module.Basis.constr_basis, ← basis_apply, Module.Basis.constr_basis]

theorem mulL_single (a b : ℕ) (r s : R) :
    mulL φ (single φ a r) (single φ b s) = single φ (a + b) (φ (qBinom a b) * r * s) := by
  rw [single_eq_smul, single_eq_smul, map_smul, LinearMap.map_smul₂, mulL_E, smul_smul,
    smul_smul, single_eq_smul]
  congr 1
  ring

instance : Mul (DP φ) := ⟨fun f g => mulL φ f g⟩

instance : One (DP φ) := ⟨E φ 0⟩

theorem mul_def (f g : DP φ) : f * g = mulL φ f g := rfl

theorem one_def : (1 : DP φ) = E φ 0 := rfl

theorem single_mul_single (a b : ℕ) (r s : R) :
    single φ a r * single φ b s = single φ (a + b) (φ (qBinom a b) * r * s) :=
  mulL_single a b r s

/-- **(2.1)** `E^{(a)} E^{(b)} = φ[a+b, a] E^{(a+b)}`. -/
theorem E_mul_E (a b : ℕ) : E φ a * E φ b = φ (qBinom a b) • E φ (a + b) := mulL_E a b

private theorem mul_assoc' (f g h : DP φ) : f * g * h = f * (g * h) := by
  induction f using induction_linear with
  | h0 => simp [mul_def]
  | hadd f f' hf hf' => simp only [mul_def, map_add, LinearMap.add_apply] at *; rw [hf, hf']
  | hs a r =>
    induction g using induction_linear with
    | h0 => simp [mul_def]
    | hadd g g' hg hg' => simp only [mul_def, map_add, LinearMap.add_apply] at *; rw [hg, hg']
    | hs b s =>
      induction h using induction_linear with
      | h0 => simp [mul_def]
      | hadd h h' hh hh' => simp only [mul_def, map_add] at *; rw [hh, hh']
      | hs c u =>
        simp only [single_mul_single, add_assoc]
        apply congrArg (single φ (a + (b + c)))
        have h := congrArg φ (qBinom_assoc a b c)
        simp only [map_mul] at h
        linear_combination r * s * u * h

private theorem mul_comm' (f g : DP φ) : f * g = g * f := by
  induction f using induction_linear with
  | h0 => simp [mul_def]
  | hadd f f' hf hf' => simp only [mul_def, map_add, LinearMap.add_apply] at *; rw [hf, hf']
  | hs a r =>
    induction g using induction_linear with
    | h0 => simp [mul_def]
    | hadd g g' hg hg' => simp only [mul_def, map_add, LinearMap.add_apply] at *; rw [hg, hg']
    | hs b s =>
      rw [single_mul_single, single_mul_single, add_comm, qBinom_comm]
      ring_nf

private theorem one_mul' (f : DP φ) : 1 * f = f := by
  induction f using induction_linear with
  | h0 => simp [mul_def]
  | hadd f f' hf hf' => simp only [mul_def, map_add] at *; rw [hf, hf']
  | hs a r =>
    rw [one_def, E, single_mul_single, zero_add, qBinom_zero_left, map_one, one_mul, one_mul]

instance : CommRing (DP φ) :=
  { (inferInstance : AddCommGroup (DP φ)) with
    mul := (· * ·)
    one := 1
    left_distrib := fun f g h => map_add (mulL φ f) g h
    right_distrib := fun f g h => by simp only [mul_def, map_add, LinearMap.add_apply]
    zero_mul := fun f => by simp only [mul_def, map_zero, LinearMap.zero_apply]
    mul_zero := fun f => map_zero (mulL φ f)
    mul_assoc := mul_assoc'
    one_mul := one_mul'
    mul_one := fun f => (mul_comm' f 1).trans (one_mul' f)
    mul_comm := mul_comm' }

instance : Algebra R (DP φ) :=
  Algebra.ofModule (fun r f g => by simp only [mul_def, map_smul, LinearMap.smul_apply])
    (fun r f g => map_smul (mulL φ f) r g)

theorem E_zero : E φ 0 = 1 := rfl

variable (φ) in
/-- The coefficient of `E^{(a)}`. -/
def coeff (a : ℕ) : DP φ →ₗ[R] R := Finsupp.lapply a

theorem coeff_single (a b : ℕ) (r : R) : coeff φ a (single φ b r) = if b = a then r else 0 := by
  show Finsupp.single b r a = _
  rw [Finsupp.single_apply]

theorem coeff_E (a b : ℕ) : coeff φ a (E φ b) = if b = a then 1 else 0 := coeff_single a b 1

/-! #### Universal property -/

variable {B : Type*} [Semiring B] [Algebra R B]

/-- A linear map out of `DP φ` whose values on the `E^{(a)}` satisfy the product law (2.1) is
multiplicative. -/
theorem map_mul_of_law (f : DP φ →ₗ[R] B)
    (hmul : ∀ a b, f (E φ a) * f (E φ b) = φ (qBinom a b) • f (E φ (a + b))) (x y : DP φ) :
    f (x * y) = f x * f y := by
  induction x using induction_linear with
  | h0 => simp
  | hadd x x' hx hx' => rw [add_mul, map_add, map_add, hx, hx', add_mul]
  | hs a r =>
    induction y using induction_linear with
    | h0 => simp
    | hadd y y' hy hy' => rw [mul_add, map_add, map_add, hy, hy', mul_add]
    | hs b s =>
      rw [single_mul_single, single_eq_smul, single_eq_smul, single_eq_smul, map_smul, map_smul,
        map_smul, smul_mul_assoc, mul_smul_comm, hmul, smul_smul, smul_smul]
      apply congrArg (fun r : R => r • f (E φ (a + b)))
      ring

/-- The `R`-algebra map `E^{(a)} ↦ e a`, for `e` with `e 0 = 1` satisfying the product law. -/
def lift (e : ℕ → B) (h0 : e 0 = 1) (hmul : ∀ a b, e a * e b = φ (qBinom a b) • e (a + b)) :
    DP φ →ₐ[R] B :=
  AlgHom.ofLinearMap ((basis φ).constr R e)
    (by rw [one_def, ← basis_apply, Module.Basis.constr_basis, h0])
    (map_mul_of_law _ fun a b => by simp only [← basis_apply, Module.Basis.constr_basis, hmul])

@[simp] theorem lift_E (e : ℕ → B) (h0 : e 0 = 1)
    (hmul : ∀ a b, e a * e b = φ (qBinom a b) • e (a + b)) (a : ℕ) :
    lift e h0 hmul (E φ a) = e a := by
  rw [lift, AlgHom.ofLinearMap_apply, ← basis_apply, Module.Basis.constr_basis]

theorem algHom_ext {f g : DP φ →ₐ[R] B} (h : ∀ a, f (E φ a) = g (E φ a)) : f = g :=
  AlgHom.toLinearMap_injective ((basis φ).ext fun a => h a)

end DP

open DP

/-! ### Comparison with the generic integral form `U_A` -/

variable (φ : A →+* R)

/-- `U_A → DP φ`, `E^{(a)} ↦ E^{(a)}`, `φ` on coefficients (`R ⊗_A U_A ≅ DP φ`). -/
def mapDPAdd : DivPowAlg →+ DP φ :=
  (Finsupp.mapRange.addMonoidHom φ.toAddMonoidHom : (ℕ →₀ A) →+ (ℕ →₀ R))

theorem mapDPAdd_single (a : ℕ) (r : A) :
    mapDPAdd φ (DivPowAlg.single a r) = DP.single φ a (φ r) :=
  Finsupp.mapRange_single (hf := map_zero _)

/-- The ring map `U_A → DP φ`, `E^{(a)} ↦ E^{(a)}`, which is `φ` on coefficients. -/
def mapDP : DivPowAlg →+* DP φ where
  toFun := mapDPAdd φ
  map_zero' := map_zero _
  map_add' := map_add _
  map_one' := by
    rw [DivPowAlg.one_def, DivPowAlg.θ, mapDPAdd_single, map_one]
    rfl
  map_mul' x y := by
    induction x using DivPowAlg.induction_linear with
    | h0 => simp
    | hadd x x' hx hx' => rw [add_mul, map_add, map_add, hx, hx', add_mul]
    | hs a r =>
      induction y using DivPowAlg.induction_linear with
      | h0 => simp
      | hadd y y' hy hy' => rw [mul_add, map_add, map_add, hy, hy', mul_add]
      | hs b s =>
        rw [DivPowAlg.single_mul_single, mapDPAdd_single, mapDPAdd_single, mapDPAdd_single,
          DP.single_mul_single, map_mul, map_mul]

theorem mapDP_θ (a : ℕ) : mapDP φ (DivPowAlg.θ a) = E φ a := by
  show mapDPAdd φ (DivPowAlg.single a 1) = _
  rw [mapDPAdd_single, map_one]
  rfl

theorem mapDP_smul (c : A) (x : DivPowAlg) : mapDP φ (c • x) = φ c • mapDP φ x := by
  rw [Algebra.smul_def, map_mul, DivPowAlg.algebraMap_def]
  show mapDPAdd φ (DivPowAlg.single 0 c) * _ = _
  rw [mapDPAdd_single, DP.single_eq_smul, smul_mul_assoc, E_zero, one_mul]

/-! ### The twisted tensor square -/

variable {φ} in
/-- The free `R`-module on `E^{(a)} ⊗ E^{(b)}` with the twisted product of Ellis–Qi §2.1 (twist
parameter `t`, `|E^{(n)}| = n`):
`(E^{(a)} ⊗ E^{(b)})(E^{(c)} ⊗ E^{(d)}) = t^{bc} φ[a+c, a] φ[b+d, b] E^{(a+c)} ⊗ E^{(b+d)}`. -/
def TT (_φ : A →+* R) (_t : R) : Type _ := ℕ × ℕ →₀ R

namespace TT

variable {φ} {t : R}

instance : AddCommGroup (TT φ t) := inferInstanceAs (AddCommGroup (ℕ × ℕ →₀ R))

instance : Module R (TT φ t) := inferInstanceAs (Module R (ℕ × ℕ →₀ R))

variable (φ t) in
/-- `r E^{(a)} ⊗ E^{(b)}`. -/
def single (a b : ℕ) (r : R) : TT φ t := Finsupp.single (a, b) r

variable (φ t) in
/-- `E^{(a)} ⊗ E^{(b)}`. -/
def tw (a b : ℕ) : TT φ t := single φ t a b 1

variable (φ t) in
/-- The basis `E^{(a)} ⊗ E^{(b)}`. -/
def basis : Module.Basis (ℕ × ℕ) R (TT φ t) := Finsupp.basisSingleOne

theorem basis_apply (p : ℕ × ℕ) : basis φ t p = tw φ t p.1 p.2 := rfl

theorem single_eq_smul (a b : ℕ) (r : R) : single φ t a b r = r • tw φ t a b := by
  show Finsupp.single (a, b) r = r • Finsupp.single (a, b) (1 : R)
  rw [Finsupp.smul_single, smul_eq_mul, mul_one]

theorem induction_linear {p : TT φ t → Prop} (f : TT φ t) (h0 : p 0)
    (hadd : ∀ f g, p f → p g → p (f + g)) (hs : ∀ a b r, p (single φ t a b r)) : p f :=
  Finsupp.induction_linear f h0 hadd fun x r => hs x.1 x.2 r

variable (φ t) in
/-- The structure constant of `(E^{(a)} ⊗ E^{(b)})(E^{(c)} ⊗ E^{(d)})`. -/
def coeff (a b c d : ℕ) : R := t ^ (b * c) * φ (qBinom a c) * φ (qBinom b d)

variable (φ t) in
/-- The twisted product, as a bilinear map. -/
def mulL : TT φ t →ₗ[R] TT φ t →ₗ[R] TT φ t :=
  (basis φ t).constr R fun p => (basis φ t).constr R fun p' =>
    coeff φ t p.1 p.2 p'.1 p'.2 • tw φ t (p.1 + p'.1) (p.2 + p'.2)

instance : Mul (TT φ t) := ⟨fun x y => mulL φ t x y⟩

instance : One (TT φ t) := ⟨tw φ t 0 0⟩

theorem mul_def (x y : TT φ t) : x * y = mulL φ t x y := rfl

theorem one_def : (1 : TT φ t) = tw φ t 0 0 := rfl

theorem tw_mul_tw (a b c d : ℕ) :
    tw φ t a b * tw φ t c d = coeff φ t a b c d • tw φ t (a + c) (b + d) := by
  rw [mul_def, show tw φ t a b = basis φ t (a, b) from rfl,
    show tw φ t c d = basis φ t (c, d) from rfl, mulL, Module.Basis.constr_basis,
    Module.Basis.constr_basis]

theorem single_mul_single (a b c d : ℕ) (r s : R) :
    single φ t a b r * single φ t c d s =
      single φ t (a + c) (b + d) (coeff φ t a b c d * r * s) := by
  rw [single_eq_smul, single_eq_smul, single_eq_smul, mul_def, map_smul, map_smul,
    LinearMap.smul_apply, ← mul_def, tw_mul_tw, smul_smul, smul_smul]
  ring_nf

theorem coeff_assoc (a b c d e f : ℕ) :
    coeff φ t a b c d * coeff φ t (a + c) (b + d) e f =
      coeff φ t c d e f * coeff φ t a b (c + e) (d + f) := by
  have h1 := congrArg φ (qBinom_assoc a c e)
  have h2 := congrArg φ (qBinom_assoc b d f)
  simp only [map_mul] at h1 h2
  have ht : t ^ (b * c) * t ^ ((b + d) * e) = t ^ (d * e) * t ^ (b * (c + e)) := by
    rw [← pow_add, ← pow_add]
    congr 1
    ring
  simp only [coeff]
  linear_combination
    (t ^ (b * c) * t ^ ((b + d) * e) * φ (qBinom b d) * φ (qBinom (b + d) f)) * h1 +
    (t ^ (d * e) * φ (qBinom c e) * φ (qBinom a (c + e)) * t ^ (b * (c + e))) * h2 +
    (φ (qBinom a c) * φ (qBinom (a + c) e) * φ (qBinom b d) * φ (qBinom (b + d) f)) * ht

private theorem mul_assoc' (x y z : TT φ t) : x * y * z = x * (y * z) := by
  induction x using induction_linear with
  | h0 => simp [mul_def]
  | hadd x x' hx hx' => simp only [mul_def, map_add, LinearMap.add_apply] at *; rw [hx, hx']
  | hs a b r =>
    induction y using induction_linear with
    | h0 => simp [mul_def]
    | hadd y y' hy hy' => simp only [mul_def, map_add, LinearMap.add_apply] at *; rw [hy, hy']
    | hs c d s =>
      induction z using induction_linear with
      | h0 => simp [mul_def]
      | hadd z z' hz hz' => simp only [mul_def, map_add] at *; rw [hz, hz']
      | hs e f u =>
        simp only [single_mul_single, add_assoc]
        congr 1
        linear_combination r * s * u * coeff_assoc (φ := φ) (t := t) a b c d e f

private theorem one_mul' (x : TT φ t) : 1 * x = x := by
  induction x using induction_linear with
  | h0 => simp [mul_def]
  | hadd x x' hx hx' => simp only [mul_def, map_add] at *; rw [hx, hx']
  | hs a b r =>
    rw [one_def, tw, single_mul_single, zero_add, zero_add]
    simp [coeff]

private theorem mul_one' (x : TT φ t) : x * 1 = x := by
  induction x using induction_linear with
  | h0 => simp [mul_def]
  | hadd x x' hx hx' => simp only [mul_def, map_add, LinearMap.add_apply] at *; rw [hx, hx']
  | hs a b r =>
    rw [one_def, tw, single_mul_single, add_zero, add_zero]
    simp [coeff]

instance : Ring (TT φ t) :=
  { (inferInstance : AddCommGroup (TT φ t)) with
    mul := (· * ·)
    one := 1
    left_distrib := fun x y z => map_add (mulL φ t x) y z
    right_distrib := fun x y z => by simp only [mul_def, map_add, LinearMap.add_apply]
    zero_mul := fun x => by simp only [mul_def, map_zero, LinearMap.zero_apply]
    mul_zero := fun x => map_zero (mulL φ t x)
    mul_assoc := mul_assoc'
    one_mul := one_mul'
    mul_one := mul_one' }

instance : Algebra R (TT φ t) :=
  Algebra.ofModule (fun r x y => by simp only [mul_def, map_smul, LinearMap.smul_apply])
    (fun r x y => map_smul (mulL φ t x) r y)

variable (φ t) in
/-- The coefficient of `E^{(a)} ⊗ E^{(b)}`. -/
def coeffAt (p : ℕ × ℕ) : TT φ t →ₗ[R] R := Finsupp.lapply p

theorem coeffAt_single (p : ℕ × ℕ) (a b : ℕ) (r : R) :
    coeffAt φ t p (single φ t a b r) = if (a, b) = p then r else 0 := by
  show Finsupp.single (a, b) r p = _
  rw [Finsupp.single_apply]

theorem coeffAt_tw (p : ℕ × ℕ) (a b : ℕ) :
    coeffAt φ t p (tw φ t a b) = if (a, b) = p then 1 else 0 := coeffAt_single p a b 1

theorem smul_tw_ne_zero {c : R} (hc : c ≠ 0) (a b : ℕ) : c • tw φ t a b ≠ 0 := by
  intro h
  have := congrArg (coeffAt φ t (a, b)) h
  rw [map_smul, coeffAt_tw, ite_eq_left rfl, map_zero, smul_eq_mul, mul_one] at this
  exact hc this

/-! #### Identification with `DP φ ⊗_R DP φ` -/

variable (φ t) in
/-- `TT φ t ≃ DP φ ⊗_R DP φ`, `E^{(a)} ⊗ E^{(b)} ↦ E^{(a)} ⊗ₜ E^{(b)}`. -/
def tensorEquiv : TT φ t ≃ₗ[R] DP φ ⊗[R] DP φ :=
  ((DP.basis φ).tensorProduct (DP.basis φ)).repr.symm

theorem tensorEquiv_tw (a b : ℕ) : tensorEquiv φ t (tw φ t a b) = E φ a ⊗ₜ[R] E φ b := by
  rw [tensorEquiv, ← DP.basis_apply, ← DP.basis_apply, ← Module.Basis.tensorProduct_apply]
  exact ((DP.basis φ).tensorProduct (DP.basis φ)).repr_symm_single (a, b) 1 |>.trans (one_smul _ _)

variable (φ t) in
/-- `x ⊗ y ∈ TT φ t` for `x, y ∈ DP φ`. -/
def tmul (x y : DP φ) : TT φ t := (tensorEquiv φ t).symm (x ⊗ₜ[R] y)

theorem tmul_E (a b : ℕ) : tmul φ t (E φ a) (E φ b) = tw φ t a b := by
  rw [tmul, ← tensorEquiv_tw, LinearEquiv.symm_apply_apply]

theorem tmul_smul_left (c : R) (x y : DP φ) : tmul φ t (c • x) y = c • tmul φ t x y := by
  rw [tmul, ← TensorProduct.smul_tmul', map_smul, tmul]

theorem tmul_add_left (x x' y : DP φ) : tmul φ t (x + x') y = tmul φ t x y + tmul φ t x' y := by
  rw [tmul, TensorProduct.add_tmul, map_add, tmul, tmul]

theorem tmul_add_right (x y y' : DP φ) : tmul φ t x (y + y') = tmul φ t x y + tmul φ t x y' := by
  rw [tmul, TensorProduct.tmul_add, map_add, tmul, tmul]

theorem tmul_smul_right (c : R) (x y : DP φ) : tmul φ t x (c • y) = c • tmul φ t x y := by
  rw [tmul, TensorProduct.tmul_smul, map_smul, tmul]

/-- **The twisted product of §2.1** on `U ⊗ U`, for the homogeneous basis (`|E^{(n)}| = n`):
`(E^{(a)} ⊗ E^{(b)})(E^{(c)} ⊗ E^{(d)}) =
t^{|E^{(b)}||E^{(c)}|} (E^{(a)}E^{(c)}) ⊗ (E^{(b)}E^{(d)})`. -/
theorem tmul_mul_tmul (a b c d : ℕ) :
    tmul φ t (E φ a) (E φ b) * tmul φ t (E φ c) (E φ d) =
      t ^ (b * c) • tmul φ t (E φ a * E φ c) (E φ b * E φ d) := by
  rw [tmul_E, tmul_E, tw_mul_tw, DP.E_mul_E, DP.E_mul_E, tmul_smul_left, tmul_smul_right, tmul_E,
    smul_smul, smul_smul, coeff]

end TT

open TT

/-! ### Comparison with the library's twisted tensor square -/

section MapTT

open OddBialgebra

variable {t : R}

/-- `TwTensor Q → TT φ t` (for `φ Q = t`), `φ` on coefficients. -/
def mapTTAdd (Q : A) : TwTensor Q →+ TT φ t :=
  (Finsupp.mapRange.addMonoidHom φ.toAddMonoidHom : (ℕ × ℕ →₀ A) →+ (ℕ × ℕ →₀ R))

theorem mapTTAdd_single (Q : A) (a b : ℕ) (r : A) :
    mapTTAdd φ (t := t) Q (TwTensor.single a b r) = TT.single φ t a b (φ r) :=
  Finsupp.mapRange_single (hf := map_zero _)

/-- The ring map from Ellis–Khovanov's twisted tensor square `TwTensor Q` (over `ℤ[q, q⁻¹]`,
braiding
`Q`) to `TT φ t`, for `φ Q = t`. -/
def mapTT (Q : A) (h : φ Q = t) : TwTensor Q →+* TT φ t where
  toFun := mapTTAdd φ Q
  map_zero' := map_zero _
  map_add' := map_add _
  map_one' := by
    rw [TwTensor.one_def, TwTensor.tw, mapTTAdd_single, map_one]
    rfl
  map_mul' x y := by
    induction x using TwTensor.induction_linear with
    | h0 => simp
    | hadd x x' hx hx' => rw [add_mul, map_add, map_add, hx, hx', add_mul]
    | hs a b r =>
      induction y using TwTensor.induction_linear with
      | h0 => simp
      | hadd y y' hy hy' => rw [mul_add, map_add, map_add, hy, hy', mul_add]
      | hs c d s =>
        rw [TwTensor.single_mul_single, mapTTAdd_single, mapTTAdd_single, mapTTAdd_single,
          TT.single_mul_single, TwTensor.coeff, TT.coeff, map_mul, map_mul, map_mul, map_mul,
          map_pow, h]

theorem mapTT_tw (Q : A) (h : φ Q = t) (a b : ℕ) :
    mapTT φ Q h (TwTensor.tw a b) = TT.tw φ t a b := by
  show mapTTAdd φ Q (TwTensor.single a b 1) = _
  rw [mapTTAdd_single, map_one]
  rfl

private theorem mapRange_smul_aux {ι : Type*} (c : A) (x : ι →₀ A) :
    (Finsupp.mapRange.addMonoidHom φ.toAddMonoidHom : (ι →₀ A) →+ (ι →₀ R)) (c • x) =
      φ c • (Finsupp.mapRange.addMonoidHom φ.toAddMonoidHom : (ι →₀ A) →+ (ι →₀ R)) x := by
  ext p
  simp

theorem mapTT_smul (Q : A) (h : φ Q = t) (c : A) (x : TwTensor Q) :
    mapTT φ Q h (c • x) = φ c • mapTT φ Q h x := by
  exact mapRange_smul_aux φ c (show ℕ × ℕ →₀ A from x)

end MapTT

/-! ### The coproduct -/

variable (t : R)

/-- `r(E^{(n)}) = ∑_{a+b=n} φ(q^{-ab}) E^{(a)} ⊗ E^{(b)}`. -/
def rVal (n : ℕ) : TT φ t :=
  ∑ p ∈ antidiagonal n, φ (T (-((p.1 * p.2 : ℕ) : ℤ))) • TT.tw φ t p.1 p.2

variable {t}

theorem mapTT_coprodVal (ht : φ (T (-2)) = t) (n : ℕ) :
    mapTT φ (T (-2)) ht (OddBialgebra.coprodVal n) = rVal φ t n := by
  rw [OddBialgebra.coprodVal, map_sum, rVal]
  refine sum_congr rfl fun p _ => ?_
  rw [mapTT_smul, mapTT_tw]

theorem rVal_zero : rVal φ t 0 = 1 := by
  simp [rVal, TT.one_def]

/-- `r(E^{(a)}) r(E^{(b)}) = φ[a+b, a] r(E^{(a+b)})` in `TT φ t`, when `t = φ(q^{-2})`. -/
theorem rVal_mul (ht : φ (T (-2)) = t) (a b : ℕ) :
    rVal φ t a * rVal φ t b = φ (qBinom a b) • rVal φ t (a + b) := by
  rw [← mapTT_coprodVal φ ht, ← mapTT_coprodVal φ ht, ← mapTT_coprodVal φ ht, ← map_mul,
    OddBialgebra.coprodVal_mul, mapTT_smul]

/-- **The coproduct** `r : DP φ → TT φ t` (`t = φ(q^{-2})`), an `R`-algebra map with
`r(E^{(n)}) = ∑_{a+b=n} φ(q^{-ab}) E^{(a)} ⊗ E^{(b)}`. -/
def r (ht : φ (T (-2)) = t) : DP φ →ₐ[R] TT φ t :=
  DP.lift (rVal φ t) (rVal_zero φ) (rVal_mul φ ht)

theorem r_E (ht : φ (T (-2)) = t) (n : ℕ) : r φ ht (E φ n) = rVal φ t n := DP.lift_E _ _ _ _

/-- `r` is the specialisation along `φ` of the library's EKL coproduct
`OddBialgebra.coprod : U_A → TwTensor (q^{-2})`. -/
theorem r_mapDP (ht : φ (T (-2)) = t) (x : DivPowAlg) :
    r φ ht (mapDP φ x) = mapTT φ (T (-2)) ht (OddBialgebra.coprod x) := by
  induction x using DivPowAlg.induction_linear with
  | h0 => simp
  | hadd x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | hs a c =>
    rw [DivPowAlg.single_eq_smul, mapDP_smul, map_smul, mapDP_θ, r_E, map_smul, mapTT_smul,
      OddBialgebra.coprod_θ, mapTT_coprodVal]

theorem rVal_one : rVal φ t 1 = TT.tw φ t 1 0 + TT.tw φ t 0 1 := by
  rw [rVal, Nat.sum_antidiagonal_succ', HasAntidiagonal.antidiagonal_zero, sum_singleton]
  simp

/-! ### Counit and coassociativity -/

/-- The counit `ε(E^{(n)}) = δ_{n0}`. -/
def counit : DP φ →ₐ[R] R :=
  DP.lift (fun n => if n = 0 then 1 else 0) (by simp) fun a b => by
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · rcases Nat.eq_zero_or_pos b with rfl | hb
      · simp
      · simp [hb.ne']
    · simp [ha.ne']

theorem counit_E (n : ℕ) : counit φ (E φ n) = if n = 0 then 1 else 0 := DP.lift_E _ _ _ _

theorem constr_tw {M : Type*} [AddCommGroup M] [Module R M] (f : ℕ × ℕ → M) (a b : ℕ) :
    (TT.basis φ t).constr R f (TT.tw φ t a b) = f (a, b) := by
  rw [← TT.basis_apply (a, b), Module.Basis.constr_basis]

variable (t) in
/-- `ε ⊗ id : U ⊗ U → U`. -/
def counitLeft : TT φ t →ₗ[R] DP φ :=
  (TT.basis φ t).constr R fun p => counit φ (E φ p.1) • E φ p.2

variable (t) in
/-- `id ⊗ ε : U ⊗ U → U`. -/
def counitRight : TT φ t →ₗ[R] DP φ :=
  (TT.basis φ t).constr R fun p => counit φ (E φ p.2) • E φ p.1

/-- `(ε ⊗ id) ∘ r = id`. -/
theorem counitLeft_r (ht : φ (T (-2)) = t) (x : DP φ) : counitLeft φ t (r φ ht x) = x := by
  have h : counitLeft φ t ∘ₗ (r φ ht).toLinearMap = LinearMap.id :=
    (DP.basis φ).ext fun n => by
      rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply, DP.basis_apply, r_E, rVal, map_sum,
        LinearMap.id_apply]
      rw [sum_eq_single (0, n)]
      · rw [map_smul, counitLeft, constr_tw, counit_E, ite_eq_left rfl, one_smul]
        simp
      · rintro ⟨a, b⟩ _ hab
        rw [map_smul, counitLeft, constr_tw, counit_E, ite_eq_right, zero_smul, smul_zero]
        rintro rfl
        simp_all
      · intro h
        exact absurd (HasAntidiagonal.mem_antidiagonal.2 (zero_add n)) h
  exact DFunLike.congr_fun h x

/-- `(id ⊗ ε) ∘ r = id`. -/
theorem counitRight_r (ht : φ (T (-2)) = t) (x : DP φ) : counitRight φ t (r φ ht x) = x := by
  have h : counitRight φ t ∘ₗ (r φ ht).toLinearMap = LinearMap.id :=
    (DP.basis φ).ext fun n => by
      rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply, DP.basis_apply, r_E, rVal, map_sum,
        LinearMap.id_apply]
      rw [sum_eq_single (n, 0)]
      · rw [map_smul, counitRight, constr_tw, counit_E, ite_eq_left rfl, one_smul]
        simp
      · rintro ⟨a, b⟩ hab hne
        rw [map_smul, counitRight, constr_tw, counit_E, ite_eq_right, zero_smul, smul_zero]
        rintro rfl
        simp only [HasAntidiagonal.mem_antidiagonal, add_zero] at hab
        exact hne (Prod.ext hab rfl)
      · intro h
        exact absurd (HasAntidiagonal.mem_antidiagonal.2 (add_zero n)) h
  exact DFunLike.congr_fun h x

variable (R) in
/-- The free `R`-module on `E^{(a)} ⊗ E^{(b)} ⊗ E^{(c)}`. -/
abbrev Tw3 : Type _ := ℕ × ℕ × ℕ →₀ R

variable (t) in
/-- `r ⊗ id : U ⊗ U → U ⊗ U ⊗ U`. -/
def rLeft : TT φ t →ₗ[R] Tw3 R :=
  (TT.basis φ t).constr R fun p =>
    Finsupp.lmapDomain R R (fun q : ℕ × ℕ => (q.1, q.2, p.2)) (rVal φ t p.1)

variable (t) in
/-- `id ⊗ r : U ⊗ U → U ⊗ U ⊗ U`. -/
def rRight : TT φ t →ₗ[R] Tw3 R :=
  (TT.basis φ t).constr R fun p =>
    Finsupp.lmapDomain R R (fun q : ℕ × ℕ => (p.1, q.1, q.2)) (rVal φ t p.2)

theorem lmapDomain_tw (f : ℕ × ℕ → ℕ × ℕ × ℕ) (a b : ℕ) :
    Finsupp.lmapDomain R R f (TT.tw φ t a b) = Finsupp.single (f (a, b)) 1 :=
  Finsupp.mapDomain_single

/-- **Coassociativity** `(r ⊗ id) ∘ r = (id ⊗ r) ∘ r`. -/
theorem coassoc (ht : φ (T (-2)) = t) (x : DP φ) :
    rLeft φ t (r φ ht x) = rRight φ t (r φ ht x) := by
  have h : rLeft φ t ∘ₗ (r φ ht).toLinearMap = rRight φ t ∘ₗ (r φ ht).toLinearMap :=
    (DP.basis φ).ext fun n => by
      simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, DP.basis_apply, r_E, rVal,
        map_sum, map_smul, rLeft, rRight, constr_tw, lmapDomain_tw, smul_sum, smul_smul,
        sum_sigma']
      refine sum_nbij' (fun x => ⟨(x.2.1, x.2.2 + x.1.2), (x.2.2, x.1.2)⟩)
        (fun x => ⟨(x.1.1 + x.2.1, x.2.2), (x.1.1, x.2.1)⟩) ?_ ?_ ?_ ?_ ?_
      · rintro ⟨⟨a, b⟩, ⟨i, j⟩⟩ hx
        simp only [mem_sigma, HasAntidiagonal.mem_antidiagonal, and_true] at hx ⊢
        omega
      · rintro ⟨⟨a, b⟩, ⟨i, j⟩⟩ hx
        simp only [mem_sigma, HasAntidiagonal.mem_antidiagonal, and_true] at hx ⊢
        omega
      · rintro ⟨⟨a, b⟩, ⟨i, j⟩⟩ hx
        simp only [mem_sigma, HasAntidiagonal.mem_antidiagonal] at hx
        obtain ⟨h1, h2⟩ := hx
        subst h2
        rfl
      · rintro ⟨⟨a, b⟩, ⟨i, j⟩⟩ hx
        simp only [mem_sigma, HasAntidiagonal.mem_antidiagonal] at hx
        obtain ⟨h1, h2⟩ := hx
        subst h2
        rfl
      · rintro ⟨⟨a, b⟩, ⟨i, j⟩⟩ hx
        simp only [mem_sigma, HasAntidiagonal.mem_antidiagonal] at hx
        obtain ⟨rfl, rfl⟩ := hx
        simp only
        rw [← map_mul, ← map_mul, ← T_add, ← T_add]
        congr 3
        push_cast
        ring
  exact DFunLike.congr_fun h x

/-! ### The twist is forced when `[2] = 0` -/

/-- The coefficient of `E^{(1)} ⊗ E^{(1)}` in `(E^{(1)} ⊗ 1 + 1 ⊗ E^{(1)})²` is `1 + t`. -/
theorem coeff_tw_sq :
    coeffAt φ t (1, 1) ((TT.tw φ t 1 0 + TT.tw φ t 0 1) ^ 2) = 1 + t := by
  simp only [pow_two, add_mul, mul_add, tw_mul_tw, map_add, map_smul, smul_eq_mul, coeffAt_tw,
    TT.coeff]
  simp only [Prod.mk.injEq]
  norm_num
  ring

/-- If `φ[2, 1] = φ(q + q⁻¹) = 0`, an algebra map `f : DP φ → TT φ t` with
`f(E^{(1)}) = E^{(1)} ⊗ 1 + 1 ⊗ E^{(1)}` exists only for the twist `t = −1`
(`f(E^{(1)})² = f(E^{(1)}E^{(1)}) = 0`, while its `E^{(1)} ⊗ E^{(1)}`-coefficient is `1 + t`). -/
theorem twist_eq_neg_one_of_sq_zero (h2 : φ (qBinom 1 1) = 0) (f : DP φ →ₐ[R] TT φ t)
    (hf : f (E φ 1) = TT.tw φ t 1 0 + TT.tw φ t 0 1) : t = -1 := by
  have hsq : f (E φ 1) ^ 2 = 0 := by
    rw [← map_pow, pow_two, DP.E_mul_E, h2, zero_smul, map_zero]
  rw [hf] at hsq
  have := coeff_tw_sq (φ := φ) (t := t)
  rw [hsq, map_zero] at this
  linear_combination -this

end OddMath.Frontier.EQQuantum
