import OddMath.Frontier.SmallRankONH
import OddMath.Frontier.ThickDots
import OddMath.Frontier.NilHeckeGrading

/-!
# Ranks `0` and `1`, continued: (2.42)–(2.45), (2.53), (4.17)–(4.22)

EKL arXiv:1111.1320v1, §2.2 and §4.1.3, completing `OddMath.Frontier.SmallRank*` in the ranks
`a ≤ 1`, where `S_a = {e}`, `D_a = x^δ = e_a = 1` and `OΛ_a = OPol_a`.

* (2.42), (2.43), (2.45) for `a ≤ 1` (`eq_2_42_small`, `eq_2_43_small`, `eq_2_45_small`): the only
  Schubert polynomial is `s_e = ∂_{w_0}(x^δ) = 1` (`schubertSmall_eq_one`), the only divided
  difference operator is `∂_e = id`, and all lengths vanish.
* (2.53) for `a ≤ 1` (`eq_2_53_small`): the degree-`d` right `OΛ_a`-linear endomorphisms of
  `OPol_a` have the rank of `(OΛ_a)_d`; `T ↦ T(1)` identifies them with `(OΛ_a)_d`
  (`endPieceSmallEquiv`).
* (4.17)–(4.22), Def 4.10 and the identity after it, for every rank `a`: `δ_a`, `χ^a_α` and
  `ŝ_α` in every rank (`deltaAll`, `chiAll`, `dualSchurAll`), (4.19) `schurAll_eq_all`, (4.20)
  `skewSign_delta_all`, (4.21) `proj_schur_proj_all`, (4.22) `proj_dualSchur_proj_all`. For
  `a ≥ 2` these are the `ThickDots` statements; for `a ≤ 1`, `χ = 0` (`chiAll_small`),
  `s_α = ŝ_α = x^α` and both sides are `x^α`.
-/

namespace OddMath.Frontier.SmallRank
open OddMath.SkewPolynomial (SkewPolynomial generator monomial)
open NilHeckeGradedEnd
open scoped BigOperators

noncomputable section

/-! The ring structure of `OPol`, preferred over the pointwise `Finsupp` structure. -/

local instance (priority := high) opolNUNASemiring (m : ℕ) :
    NonUnitalNonAssocSemiring (SkewPolynomial m) :=
  @NonAssocSemiring.toNonUnitalNonAssocSemiring _
    (@Semiring.toNonAssocSemiring _ (OddMath.PbwL3.instSemiring m))

local instance (priority := high) opolNUNARing (m : ℕ) :
    NonUnitalNonAssocRing (SkewPolynomial m) :=
  @NonAssocRing.toNonUnitalNonAssocRing _ (@Ring.toNonAssocRing _ (OddMath.PbwL3.instRing m))

/-! ## (2.42), (2.43), (2.45) for `a ≤ 1` -/

theorem perm_small {a : ℕ} (ha : a ≤ 1) (w : Equiv.Perm (Fin a)) : w = 1 :=
  Equiv.ext fun i => Fin.ext (by have := (w i).isLt; have := i.isLt; simp; omega)

theorem inversions_small {a : ℕ} (ha : a ≤ 1) (w : Equiv.Perm (Fin a)) :
    NilHeckeGrading.inversions w = 0 := by
  rw [perm_small ha w]
  simp only [NilHeckeGrading.inversions, Equiv.Perm.coe_one, id_eq]
  exact Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ =>
    if_neg fun h => absurd (h.1.trans h.2) (lt_irrefl _)

/-- The odd divided difference operator `∂_u` of EKL (2.36) in rank `a ≤ 1`: `u = e`, `∂_e = id`. -/
def dividedSmall (a : ℕ) (_u : Equiv.Perm (Fin a)) : SkewPolynomial a →ₗ[ℤ] SkewPolynomial a :=
  LinearMap.id

/-- The odd Schubert polynomial `s_w = ∂_{w^{-1} w_0}(x^δ)` of EKL (2.41) in rank `a ≤ 1`: here
`w = w_0 = e` and `∂_{w_0} = D_a`. -/
def schubertSmall (a : ℕ) (_w : Equiv.Perm (Fin a)) : SkewPolynomial a :=
  LongestDivided.D a (LongestDivided.staircase a)

theorem schubertSmall_eq_one {a : ℕ} (ha : a ≤ 1) (w : Equiv.Perm (Fin a)) :
    schubertSmall a w = 1 := by
  rw [schubertSmall, D_small ha, staircase_small ha]

/-- **EKL (2.42)**, `a ≤ 1`: `ℓ(w u^{-1}) + ℓ(u) = ℓ(w)` always holds, and
`∂_u s_w = s_{w u^{-1}}` (sign `+1`). For `a ≥ 2` see `OddSchubertAction.action_additive`. -/
theorem eq_2_42_small {a : ℕ} (ha : a ≤ 1) (u w : Equiv.Perm (Fin a)) :
    NilHeckeGrading.inversions (w * u⁻¹) + NilHeckeGrading.inversions u =
        NilHeckeGrading.inversions w ∧
      dividedSmall a u (schubertSmall a w) = schubertSmall a (w * u⁻¹) := by
  refine ⟨by rw [inversions_small ha, inversions_small ha, inversions_small ha], ?_⟩
  rw [dividedSmall, LinearMap.id_apply, schubertSmall_eq_one ha, schubertSmall_eq_one ha]

/-- **EKL (2.43)** (corrected selector; see ERRATA.md), `a ≤ 1`: `∂_w s_w = 1`; there are no `u ≠ w`
of equal or larger length. For `a ≥ 2` see `OddSchubertAction.action_self`. -/
theorem eq_2_43_small {a : ℕ} (ha : a ≤ 1) (w : Equiv.Perm (Fin a)) :
    dividedSmall a w (schubertSmall a w) = 1 ∧ ∀ u : Equiv.Perm (Fin a), u = w := by
  refine ⟨by rw [dividedSmall, LinearMap.id_apply, schubertSmall_eq_one ha], fun u => ?_⟩
  rw [perm_small ha u, perm_small ha w]

/-- **EKL (2.45)**, `a ≤ 1`: `(x^A ∂_e)(s_e) = (-1)^{C(a,3)} x^A`, where `s_e = D_a(x^δ)`. For
`a ≥ 2` see `EKLSectionTwo.schubert_identity_action`. -/
theorem eq_2_45_small {a : ℕ} (ha : a ≤ 1) (A : SkewPolynomial a) (w : Equiv.Perm (Fin a)) :
    A * dividedSmall a w (LongestDivided.D a (LongestDivided.staircase a)) =
      (-1 : ℤ) ^ a.choose 3 • A := by
  rw [dividedSmall, LinearMap.id_apply, D_small ha, staircase_small ha, mul_one,
    choose_three_small ha, pow_zero, one_smul]

/-! ## (2.53) for `a ≤ 1` -/

/-- Right `OΛ_N`-linear endomorphisms of `OPol_N` (for `N = n+2`:
`NilHeckeEndomorphism.rightKernelEnd n`). -/
def rightEndAll (N : ℕ) : Subring (Module.End ℤ (SkewPolynomial N)) where
  carrier := {T | ∀ (f : SkewPolynomial N) (k : OLam N), T (f * (k : SkewPolynomial N)) =
    T f * k}
  zero_mem' := by
    intro f k
    rw [LinearMap.zero_apply, LinearMap.zero_apply]
    exact (OddMath.SkewPolynomial.zero_mul (k : SkewPolynomial N)).symm
  one_mem' := fun _ _ => rfl
  add_mem' := by
    intro T U hT hU f k
    rw [LinearMap.add_apply, LinearMap.add_apply, hT f k, hU f k]
    exact (add_mul _ _ _).symm
  neg_mem' := by
    intro T hT f k
    rw [LinearMap.neg_apply, LinearMap.neg_apply, hT f k]
    exact (neg_mul _ _).symm
  mul_mem' := by
    intro T U hT hU f k
    rw [Module.End.mul_apply, Module.End.mul_apply, hU f k, hT (U f) k]

/-- Degree-`d` right `OΛ_N`-linear endomorphisms (for `N = n+2`: `EKLSectionTwo.endPiece n d`). -/
def endPieceAll (N : ℕ) (d : ℤ) : Submodule ℤ (rightEndAll N) where
  carrier := {T | ∀ e (f : SkewPolynomial N), f ∈ polynomialPiece N e →
    T.val f ∈ polynomialPiece N (e+d)}
  zero_mem' := fun _ _ _ => (polynomialPiece _ _).zero_mem
  add_mem' := fun {_ _} hT hU e f hf => (polynomialPiece _ _).add_mem (hT e f hf) (hU e f hf)
  smul_mem' := fun z _ hT e f hf => (polynomialPiece _ _).smul_mem z (hT e f hf)

/-- `(OΛ_N)_d` (for `N = n+2`: `NilHeckeGradedEnd.kernelPiece n d`). -/
def kernelPieceAll (N : ℕ) (d : ℤ) : Submodule ℤ (OLam N) where
  carrier := {k | (k : SkewPolynomial N) ∈ polynomialPiece N d}
  zero_mem' := (polynomialPiece _ _).zero_mem
  add_mem' := (polynomialPiece _ _).add_mem
  smul_mem' z _ hk := (polynomialPiece _ _).smul_mem z hk

theorem rightEnd_small_apply {N : ℕ} (hN : N ≤ 1) (T : rightEndAll N) (f : SkewPolynomial N) :
    T.val f = T.val 1 * f := by
  have hT : ∀ (g : SkewPolynomial N) (k : OLam N), T.val (g * k) = T.val g * k := T.2
  have := hT 1 ⟨f, mem_OLam_small hN f⟩
  rwa [one_mul] at this

/-- Left multiplication by `k ∈ OPol_N` is right `OΛ_N`-linear. -/
def mulLeftEnd (N : ℕ) (k : SkewPolynomial N) : rightEndAll N :=
  ⟨{ toFun := fun f => k * f
     map_add' := mul_add k
     map_smul' := fun c f => mul_smul_comm c k f },
   by
    intro f l
    show k * (f * (l : SkewPolynomial N)) = k * f * l
    exact (OddMath.SkewPolynomial.mul_assoc k f l).symm⟩

/-- `T ↦ T(1)`: degree-`d` endomorphisms `≅ (OΛ_N)_d` for `N ≤ 1`. -/
def endPieceSmallEquiv {N : ℕ} (hN : N ≤ 1) (d : ℤ) : endPieceAll N d ≃ₗ[ℤ] kernelPieceAll N d where
  toFun T := ⟨⟨T.1.1 1, mem_OLam_small hN _⟩, by
    have := T.2 0 1 (one_mem N)
    rwa [zero_add] at this⟩
  invFun k := ⟨mulLeftEnd N k.1.1, fun e f hf => by
    have := polynomial_mul k.2 hf
    rw [add_comm] at this
    exact this⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv T := by
    refine Subtype.ext (Subtype.ext (LinearMap.ext fun f => ?_))
    change T.1.1 1 * f = T.1.1 f
    rw [rightEnd_small_apply hN T.1 f]
  right_inv k := by
    refine Subtype.ext (Subtype.ext ?_)
    change (k : SkewPolynomial N) * 1 = k
    rw [mul_one]

/-- **EKL (2.53)**, `a ≤ 1`, for `A = OΛ_a`, `M = OPol_a` (free on `s_e = 1`, so `h(q) = 1`):
`rk (End^d) = Σ_{i,j ∈ S_a} rk (OΛ_a)_{d + 2ℓ(j) - 2ℓ(i)} = rk (OΛ_a)_d`. For `a ≥ 2` see
`EKLSectionTwo.eq_2_53`. -/
theorem eq_2_53_small {N : ℕ} (hN : N ≤ 1) (d : ℤ) :
    Module.finrank ℤ (endPieceAll N d) = ∑ i : Equiv.Perm (Fin N), ∑ j : Equiv.Perm (Fin N),
      Module.finrank ℤ (kernelPieceAll N (d + 2 * (NilHeckeGrading.inversions j : ℤ) -
        2 * (NilHeckeGrading.inversions i : ℤ))) := by
  have hu : ∀ w : Equiv.Perm (Fin N), w = 1 := perm_small hN
  haveI : Unique (Equiv.Perm (Fin N)) := ⟨⟨1⟩, hu⟩
  rw [Fintype.sum_unique, Fintype.sum_unique, inversions_small hN, Nat.cast_zero, mul_zero,
    add_zero, sub_zero, (endPieceSmallEquiv hN d).finrank_eq]

/-! ## (4.17)–(4.22) in every rank -/

/-- The staircase exponent `δ_a = (a-1, …, 1, 0)` (`ThickDots.delta` for `a ≥ 2`). -/
def deltaAll (N : ℕ) : Fin N → ℕ := fun i => N - 1 - i.val

/-- EKL (4.20): `χ^a_α = C(a,3) + |α| C(a,2) + Σ_j α_j C(a-j+1,2)` (`ThickDots.chi` for `a ≥ 2`). -/
def chiAll (N : ℕ) (α : Fin N → ℕ) : ℕ :=
  N.choose 3 + (∑ k, α k) * N.choose 2 + ∑ k, α k * (N - k.val).choose 2

/-- EKL Def 4.10: `ŝ_α = (-1)^{χ^a_α} (D_a(x_1^{α_a} x_2^{1+α_{a-1}} ⋯ x_a^{a-1+α_1}))^{w_0}`
(`ThickDots.dualSchur` for `a ≥ 2`). -/
def dualSchurAll (N : ℕ) (α : Fin N → ℕ) : SkewPolynomial N :=
  (-1 : ℤ)^(chiAll N α) • SignedPermutation.skewAction (LongestElementary.longest N)
    (LongestDivided.D N (monomial (fun k => k.val + α (Fin.rev k)) 1))

theorem chiAll_small {N : ℕ} (hN : N ≤ 1) (α : Fin N → ℕ) : chiAll N α = 0 := by
  rcases (by omega : N = 0 ∨ N = 1) with rfl | rfl
  · simp [chiAll]
  · simp [chiAll, Nat.choose_eq_zero_of_lt]

theorem deltaAll_small {N : ℕ} (hN : N ≤ 1) : deltaAll N = 0 :=
  funext fun i => by simp only [deltaAll, Pi.zero_apply]; have := i.isLt; omega

theorem dualSchurAll_small {N : ℕ} (hN : N ≤ 1) (α : Fin N → ℕ) :
    dualSchurAll N α = monomial α 1 := by
  rw [dualSchurAll, chiAll_small hN, pow_zero, one_smul, D_small hN,
    skewAction_longest_small hN]
  congr 1
  funext k
  have hk : k.val = 0 := by have := k.isLt; omega
  rw [hk, zero_add]
  congr 1
  exact Fin.ext (by rw [Fin.val_rev, hk]; omega)

/-- **EKL (4.19)**, every rank: `s_α = (-1)^{χ^a_α} (D_a(x^{α+δ}))^{w_0}`. For `a ≥ 2` this is
`ThickDots.schur_eq`. -/
theorem schurAll_eq_all (N : ℕ) (α : Fin N → ℕ) :
    schurAll N α = (-1 : ℤ)^(chiAll N α) • SignedPermutation.skewAction
      (LongestElementary.longest N) (LongestDivided.D N (monomial (α + deltaAll N) 1)) := by
  match N, α with
  | 0, α => rw [schurAll_small (by omega), chiAll_small (by omega), deltaAll_small (by omega),
      add_zero, pow_zero, one_smul, D_small (by omega), skewAction_longest_small (by omega)]
  | 1, α => rw [schurAll_small le_rfl, chiAll_small le_rfl, deltaAll_small le_rfl, add_zero,
      pow_zero, one_smul, D_small le_rfl, skewAction_longest_small le_rfl]
  | n+2, α => exact ThickDots.schur_eq α

/-- **EKL (4.20)**, every rank: `x^α x^δ = (-1)^{C(a,3) + χ^a_α} x^{α+δ}`, i.e. the normal-ordering
sign is `(-1)^{C(a,3) + χ^a_α}`. For `a ≥ 2` this is `ThickDots.skewSign_delta`. -/
theorem skewSign_delta_all (N : ℕ) (α : Fin N → ℕ) :
    OddMath.skewSign α (deltaAll N) = (-1 : ℤ)^(N.choose 3 + chiAll N α) := by
  match N, α with
  | 0, α => rw [skewSign_small (by omega), chiAll_small (by omega)]; rfl
  | 1, α => rw [skewSign_small le_rfl, chiAll_small le_rfl]; rfl
  | n+2, α => exact ThickDots.skewSign_delta α

/-- **EKL (4.21)**, every rank: `e_a s_α e_a = (-1)^{χ^a_α} e_a x^{α+δ} D_a`. For `a ≥ 2` this is
`ThickDots.projector_schur_projector`. -/
theorem proj_schur_proj_all (N : ℕ) (α : Fin N → ℕ) :
    proj N * polyHom N (schurAll N α) * proj N =
      (-1 : ℤ)^(chiAll N α) • (proj N * polyHom N (monomial (α + deltaAll N) 1) * DE N) := by
  match N, α with
  | 0, α => simp only [proj_small (by omega : 0 ≤ 1), DE_small (by omega : 0 ≤ 1),
      schurAll_small (by omega : 0 ≤ 1), chiAll_small (by omega : 0 ≤ 1),
      deltaAll_small (by omega : 0 ≤ 1), add_zero, pow_zero, one_smul, one_mul, mul_one]
  | 1, α => simp only [proj_small le_rfl, DE_small le_rfl, schurAll_small le_rfl,
      chiAll_small le_rfl, deltaAll_small le_rfl, add_zero, pow_zero, one_smul, one_mul, mul_one]
  | n+2, α => exact ThickDots.projector_schur_projector α

/-- **EKL (4.22)** and the identity after Def 4.10, every rank:
`e_a ŝ_α e_a = (-1)^{χ^a_α} e_a x_1^{α_a} x_2^{1+α_{a-1}} ⋯ x_a^{a-1+α_1} D_a`. For `a ≥ 2` this
is `ThickDots.projector_dualSchur_projector`. -/
theorem proj_dualSchur_proj_all (N : ℕ) (α : Fin N → ℕ) :
    proj N * polyHom N (dualSchurAll N α) * proj N = (-1 : ℤ)^(chiAll N α) •
      (proj N * polyHom N (monomial (fun k => k.val + α (Fin.rev k)) 1) * DE N) := by
  match N, α with
  | 0, α =>
    rw [dualSchurAll, chiAll_small (by omega), D_small (by omega),
      skewAction_longest_small (by omega), proj_small (by omega), DE_small (by omega)]
    simp only [pow_zero, one_smul, one_mul, mul_one]
  | 1, α =>
    rw [dualSchurAll, chiAll_small le_rfl, D_small le_rfl, skewAction_longest_small le_rfl,
      proj_small le_rfl, DE_small le_rfl]
    simp only [pow_zero, one_smul, one_mul, mul_one]
  | n+2, α => exact ThickDots.projector_dualSchur_projector α

end

end OddMath.Frontier.SmallRank
