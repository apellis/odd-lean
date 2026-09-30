import OddMath.Frontier.EQSkewDifferential

/-!
# Odd partial derivatives and null-homotopies of `OPol_n(α)`

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
§3.4 (Lemma 3.12, Remark 3.13, Lemma 3.14, Corollary 3.15).

On `OPol_n = SkewPolynomial n` (integer coefficients, strands numbered from `0`):

* `pd n i`: the odd partial derivative `∂/∂x_i`, determined by `∂/∂x_i (x_j) = δ_{ij}` and the
  super Leibniz rule `∂/∂x_i (fg) = ∂/∂x_i (f) g + ι(f) ∂/∂x_i (g)` (`pd_generator`, `pd_mul`);
* **Lemma 3.12** (`pd_pd`, `pd_pd_add`, `d_eq_sum`): the `∂/∂x_i` generate an exterior algebra,
  `(∂/∂x_i)² = 0`, `∂/∂x_i ∂/∂x_j + ∂/∂x_j ∂/∂x_i = 0`, and `d = Σ_i x_i² ∂/∂x_i` on `OPol_n`;
* **Remark 3.13** (`dAlpha_eq_sum_iff`): `d_α = Σ_i x_i² ∂/∂x_i` on `OPol_n(α)` iff `α = 0`;
* **Lemma 3.14** (`lemma_3_14`): for `h_β = Σ β_i ∂/∂x_i`, `h_β d_α + d_α h_β = ⟨α, β⟩` on
  `OPol_n(α)`;
* **Corollary 3.15** (`cor_3_15`): if `α_i = 1`, then `∂/∂x_i` is a null-homotopy of the identity
  of `OPol_n(α)`: `∂/∂x_i d_α + d_α ∂/∂x_i = id`. Here `∂/∂x_i` acts on `OPol_n(α)` by
  `∂/∂x_i (f 1_α) = ∂/∂x_i (f) 1_α`; it is left `OPol_n`-linear in the super sense,
  `∂/∂x_i (g f 1_α) = ∂/∂x_i (g) f 1_α + ι(g) ∂/∂x_i (f 1_α)`, which is `pd_mul`.
-/

namespace OddMath.Frontier.EQSkewDifferential

open OddMath.SkewPolynomial (SkewPolynomial generator)
open scoped BigOperators

noncomputable section

/-- The ring structure of `OPol`, preferred over the pointwise `Finsupp` structure. -/
local instance (priority := high) opolNUNASemiring' (m : ℕ) :
    NonUnitalNonAssocSemiring (SkewPolynomial m) :=
  @NonAssocSemiring.toNonUnitalNonAssocSemiring _
    (@Semiring.toNonAssocSemiring _ (OddMath.PbwL3.instSemiring m))

local instance (priority := high) opolNUNARing' (m : ℕ) :
    NonUnitalNonAssocRing (SkewPolynomial m) :=
  @NonAssocRing.toNonUnitalNonAssocRing _ (@Ring.toNonAssocRing _ (OddMath.PbwL3.instRing m))

variable {n : ℕ}

/-! ## Odd derivations -/

/-- An additive map is an odd derivation if it satisfies the super Leibniz rule twisted by `ι`
and anticommutes with `ι`. -/
structure IsOddDeriv (D : SkewPolynomial n →+ SkewPolynomial n) : Prop where
  mul : ∀ f g, D (f * g) = D f * g + parityInv n f * D g
  parityInv : ∀ f, D (parityInv n f) = -parityInv n (D f)

/-- The anticommutator of two odd derivations is an (untwisted) derivation. -/
theorem IsOddDeriv.anticomm_mul {D E : SkewPolynomial n →+ SkewPolynomial n} (hD : IsOddDeriv D)
    (hE : IsOddDeriv E) (f g : SkewPolynomial n) :
    D (E (f * g)) + E (D (f * g)) =
      (D (E f) + E (D f)) * g + (RingHom.id _) f * (D (E g) + E (D g)) := by
  rw [hE.mul, hD.mul, map_add, map_add, hD.mul, hD.mul, hE.mul, hE.mul, hD.parityInv,
    hE.parityInv, RingHom.id_apply]
  simp only [add_mul, mul_add, neg_mul, parityInv_parityInv]
  abel

/-- The anticommutator of two odd derivations vanishing on all generators vanishes. -/
theorem IsOddDeriv.anticomm_eq_zero {D E : SkewPolynomial n →+ SkewPolynomial n}
    (hD : IsOddDeriv D) (hE : IsOddDeriv E)
    (h : ∀ j, D (E (generator j)) + E (D (generator j)) = 0) (f : SkewPolynomial n) :
    D (E f) + E (D f) = 0 := by
  have := twistedDeriv_ext (RingHom.id _) (D := D.comp E + E.comp D) (E := 0)
    (fun f g => by simpa using hD.anticomm_mul hE f g) (fun f g => by simp) (fun j => by simpa using h j) f
  simpa using this

theorem eq_zero_of_add_self {f : SkewPolynomial n} (h : f + f = 0) : f = 0 := by
  ext a
  have := congrArg (fun p : SkewPolynomial n => p a) h
  simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.coe_zero, Pi.zero_apply] at this ⊢
  omega

theorem isOddDeriv_d : IsOddDeriv (d n) := ⟨d_mul, d_parityInv⟩

/-! ## The odd partial derivatives -/

/-- The image of `x_j` encoding `(ι, ∂/∂x_i)`: `[[ι x_j, δ_{ij}], [0, x_j]]`. -/
def pdMat (i j : Fin n) : Matrix (Fin 2) (Fin 2) (SkewPolynomial n) :=
  !![-generator j, if i = j then 1 else 0; 0, generator j]

theorem pdMat_anticomm (i a b : Fin n) (h : a ≠ b) :
    pdMat i a * pdMat i b + pdMat i b * pdMat i a = 0 := by
  have hab := generator_anticomm a b h
  refine Matrix.ext fun r s => ?_
  fin_cases r <;> fin_cases s <;>
    simp [pdMat, hab] <;>
    split_ifs <;> simp

/-- The ring map `f ↦ [[ι f, ∂/∂x_i f], [0, f]]`. -/
def pdHom (n : ℕ) (i : Fin n) : SkewPolynomial n →+* Matrix (Fin 2) (Fin 2) (SkewPolynomial n) :=
  skewLift (pdMat i) (pdMat_anticomm i)

/-- The odd partial derivative `∂/∂x_i` of Ellis–Qi §3.4. -/
def pd (n : ℕ) (i : Fin n) : SkewPolynomial n →+ SkewPolynomial n :=
  (Matrix.entryAddMonoidHom (SkewPolynomial n) 0 1).comp (pdHom n i).toAddMonoidHom

theorem pd_apply (i : Fin n) (f : SkewPolynomial n) : pd n i f = pdHom n i f 0 1 := rfl

theorem pdHom_eq (i : Fin n) (f : SkewPolynomial n) :
    pdHom n i f = !![parityInv n f, pd n i f; 0, f] := by
  have key : pdHom n i f 1 0 = 0 ∧ pdHom n i f 1 1 = f ∧ pdHom n i f 0 0 = parityInv n f := by
    induction f using induction_generator with
    | hgen j => simp [pdHom, pdMat]
    | h0 => simp
    | h1 => simp
    | hadd f g hf hg => simp [hf.1, hg.1, hf.2.1, hg.2.1, hf.2.2, hg.2.2]
    | hneg f hf => simp [hf.1, hf.2.1, hf.2.2]
    | hmul f g hf hg =>
      simp [Matrix.mul_apply, Fin.sum_univ_two, hf.1, hg.1, hf.2.1, hg.2.1, hf.2.2, hg.2.2]
  refine Matrix.ext fun r s => ?_
  fin_cases r <;> fin_cases s <;> simp [key.1, key.2.1, key.2.2, pd_apply]

/-- The super Leibniz rule for `∂/∂x_i`. -/
theorem pd_mul (i : Fin n) (f g : SkewPolynomial n) :
    pd n i (f * g) = pd n i f * g + parityInv n f * pd n i g := by
  have h := congrFun (congrFun (map_mul (pdHom n i) f g) 0) 1
  rw [pdHom_eq, pdHom_eq, pdHom_eq] at h
  simpa [Matrix.mul_apply, Fin.sum_univ_two, add_comm] using h

theorem pd_generator (i j : Fin n) : pd n i (generator j) = if i = j then 1 else 0 := by
  simp [pd_apply, pdHom, pdMat]

theorem pd_parityInv (i : Fin n) (f : SkewPolynomial n) :
    pd n i (parityInv n f) = -parityInv n (pd n i f) := by
  induction f using induction_generator with
  | hgen j => rw [parityInv_generator, map_neg, pd_generator]; split_ifs <;> simp
  | h0 => simp
  | h1 => simp [D_one (parityInv n) (pd n i) (pd_mul i)]
  | hadd f g hf hg => simp [hf, hg, add_comm]
  | hneg f hf => simp [hf]
  | hmul f g hf hg => simp [pd_mul, hf, hg, parityInv_parityInv, add_comm]

theorem isOddDeriv_pd (i : Fin n) : IsOddDeriv (pd n i) := ⟨pd_mul i, pd_parityInv i⟩

/-! ## Lemma 3.12 -/

/-- **Ellis–Qi, Lemma 3.12 (1)**: `∂/∂x_i ∂/∂x_j + ∂/∂x_j ∂/∂x_i = 0`. -/
theorem pd_pd_add (i j : Fin n) (f : SkewPolynomial n) :
    pd n i (pd n j f) + pd n j (pd n i f) = 0 :=
  (isOddDeriv_pd i).anticomm_eq_zero (isOddDeriv_pd j)
    (fun k => by rw [pd_generator, pd_generator]; split_ifs <;>
      simp [D_one (parityInv n) (pd n i) (pd_mul i), D_one (parityInv n) (pd n j) (pd_mul j)]) f

/-- **Ellis–Qi, Lemma 3.12 (1)**: `(∂/∂x_i)² = 0`. -/
theorem pd_pd (i : Fin n) (f : SkewPolynomial n) : pd n i (pd n i f) = 0 :=
  eq_zero_of_add_self (pd_pd_add i i f)

/-- `x_i²` is central in `OPol_n`. -/
theorem generator_sq_comm (i : Fin n) (f : SkewPolynomial n) :
    generator i * generator i * f = f * (generator i * generator i) := by
  induction f using induction_generator with
  | hgen j =>
    by_cases h : i = j
    · subst h; rw [mul_assoc]
    · rw [mul_assoc, generator_anticomm i j h, mul_neg, ← mul_assoc, generator_anticomm i j h,
        neg_mul, neg_neg, mul_assoc]
  | h0 => simp
  | h1 => simp
  | hadd f g hf hg => rw [mul_add, add_mul, hf, hg]
  | hneg f hf => rw [mul_neg, neg_mul, hf]
  | hmul f g hf hg => rw [← mul_assoc, hf, mul_assoc, hg, mul_assoc]

/-- **Ellis–Qi, Lemma 3.12 (2)** (3.34): `d = Σ_i x_i² ∂/∂x_i` on `OPol_n`. -/
theorem d_eq_sum (f : SkewPolynomial n) :
    d n f = ∑ i, generator i * generator i * pd n i f := by
  let E : SkewPolynomial n →+ SkewPolynomial n :=
    ∑ i, (AddMonoidHom.mulLeft (generator i * generator i)).comp (pd n i)
  have hE : ∀ f, E f = ∑ i, generator i * generator i * pd n i f := fun f => by
    simp [E, AddMonoidHom.finsetSum_apply]
  rw [← hE]
  refine twistedDeriv_ext (parityInv n) d_mul (fun f g => ?_) (fun j => ?_) f
  · rw [hE, hE, hE, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have key : generator i * generator i * (parityInv n f * pd n i g) =
        parityInv n f * (generator i * generator i * pd n i g) := by
      rw [← mul_assoc, generator_sq_comm, mul_assoc]
    rw [pd_mul, mul_add, key, mul_assoc (generator i * generator i)]
  · rw [hE, d_generator, Finset.sum_eq_single j]
    · simp [pd_generator]
    · intro i _ hi; simp [pd_generator, hi]
    · simp

/-! ## Lemma 3.14 and Corollary 3.15 -/

/-- The odd directional derivative `h_β = Σ β_i ∂/∂x_i` (3.35). -/
def hBeta (β : Fin n → ℤ) : SkewPolynomial n →+ SkewPolynomial n := ∑ i, β i • pd n i

theorem hBeta_apply (β : Fin n → ℤ) (f : SkewPolynomial n) :
    hBeta β f = ∑ i, β i • pd n i f := by
  simp [hBeta, AddMonoidHom.finsetSum_apply]

theorem isOddDeriv_hBeta (β : Fin n → ℤ) : IsOddDeriv (hBeta β) where
  mul f g := by
    simp only [hBeta_apply, pd_mul, smul_add, Finset.sum_add_distrib, Finset.sum_mul,
      Finset.mul_sum, smul_mul_assoc, mul_smul_comm]
  parityInv f := by
    simp only [hBeta_apply, pd_parityInv, smul_neg, Finset.sum_neg_distrib, map_sum, map_zsmul]

theorem hBeta_generator (β : Fin n → ℤ) (j : Fin n) : hBeta β (generator j) = β j • 1 := by
  rw [hBeta_apply, Finset.sum_eq_single j]
  · simp [pd_generator]
  · intro i _ hi; simp [pd_generator, hi]
  · simp

theorem hBeta_sAlpha (α β : Fin n → ℤ) : hBeta β (sAlpha α) = (∑ i, α i * β i) • 1 := by
  simp only [sAlpha, map_sum, map_zsmul, hBeta_generator, smul_smul, Finset.sum_smul]

/-- `h_β d + d h_β = 0` on `OPol_n`. -/
theorem hBeta_d_add (β : Fin n → ℤ) (f : SkewPolynomial n) :
    hBeta β (d n f) + d n (hBeta β f) = 0 :=
  (isOddDeriv_hBeta β).anticomm_eq_zero isOddDeriv_d
    (fun j => by
      rw [d_generator, (isOddDeriv_hBeta β).mul, hBeta_generator, map_zsmul, d_one, smul_zero,
        parityInv_generator, smul_mul_assoc, one_mul, neg_mul, mul_smul_comm, mul_one, add_zero,
        add_neg_cancel]) f

/-- **Ellis–Qi, Lemma 3.14** (3.36): `h_β d_α + d_α h_β = ⟨α, β⟩` on `OPol_n(α)`. -/
theorem lemma_3_14 (α β : Fin n → ℤ) (f : SkewPolynomial n) :
    hBeta β (dAlpha α f) + dAlpha α (hBeta β f) = (∑ i, α i * β i) • f := by
  rw [dAlpha_apply, dAlpha_apply, map_add, (isOddDeriv_hBeta β).mul, parityInv_parityInv,
    (isOddDeriv_hBeta β).parityInv, hBeta_sAlpha, mul_smul_comm, mul_one]
  have := hBeta_d_add β f
  rw [← sub_eq_zero]
  rw [show hBeta β (d n f) = -d n (hBeta β f) from eq_neg_of_add_eq_zero_left this]
  simp only [neg_mul]
  abel

/-- **Ellis–Qi, Corollary 3.15**: if `α_i = 1` (for instance `α ∈ {0,1}ⁿ` not identically `0`),
then `∂/∂x_i` is a null-homotopy of the identity of the complex `OPol_n(α)`. -/
theorem cor_3_15 (α : Fin n → ℤ) (i : Fin n) (hi : α i = 1)
    (f : SkewPolynomial n) :
    pd n i (dAlpha α f) + dAlpha α (pd n i f) = f := by
  have h := lemma_3_14 α (fun j => if j = i then 1 else 0) f
  have hpd : hBeta (fun j => if j = i then (1 : ℤ) else 0) = pd n i := by
    refine AddMonoidHom.ext fun g => ?_
    rw [hBeta_apply, Finset.sum_eq_single i]
    · simp
    · intro j _ hj; simp [hj]
    · simp
  rw [hpd] at h
  rw [h]
  simp [hi]

/-- Consequently `OPol_n(α)` is acyclic when `α_i = 1`: every cocycle `f` is the coboundary of
`∂/∂x_i f`. -/
theorem acyclic (α : Fin n → ℤ) (i : Fin n) (hi : α i = 1)
    {f : SkewPolynomial n} (hf : dAlpha α f = 0) : dAlpha α (pd n i f) = f := by
  have h := cor_3_15 α i hi f
  rwa [hf, map_zero, zero_add] at h

/-- **Ellis–Qi, Remark 3.13**: `d_α = Σ_i x_i² ∂/∂x_i` on `OPol_n(α)` iff `α = 0`. -/
theorem dAlpha_eq_sum_iff (α : Fin n → ℤ) :
    (∀ f, dAlpha α f = ∑ i, generator i * generator i * pd n i f) ↔ α = 0 := by
  constructor
  · intro h
    have h1 := h 1
    simp only [dAlpha_apply, d_one, map_one, one_mul, zero_add] at h1
    have hz : sAlpha α = 0 := by
      rw [h1]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [D_one (parityInv n) (pd n i) (pd_mul i), mul_zero]
    funext i
    have h2 := congrArg (pd n i) hz
    rw [map_zero] at h2
    have h3 : pd n i (sAlpha α) = α i • (1 : SkewPolynomial n) := by
      simp only [sAlpha, map_sum, map_zsmul, pd_generator]
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj; simp [Ne.symm hj]
      · simp
    rw [h3] at h2
    have h4 := congrArg (fun p : SkewPolynomial n => p 0) h2
    simpa [show (1 : SkewPolynomial n) = Finsupp.single 0 1 from rfl] using h4
  · rintro rfl f
    rw [dAlpha_apply, d_eq_sum]
    simp [sAlpha]

end

end OddMath.Frontier.EQSkewDifferential
