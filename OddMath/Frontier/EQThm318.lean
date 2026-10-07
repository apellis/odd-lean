import OddMath.Frontier.EQOPolTensor
import OddMath.Frontier.EQK0Coproduct

/-!
# Ellis–Qi Theorem 3.18: `K₀(D(ONH)) ≅ u⁺` over a field

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
§3.6, the induction and restriction functors (3.35)–(3.38), the Künneth property (3.39) and
Theorem 3.18 (printed numbering). Conventions as in `OddMath.Frontier.EQThm417`: a field `K`
(scalar extension of the integral dg rings), half-graded dg modules (diagonal half-grading), `K₀` the
compact super Grothendieck group, a `ℤ[√−1]`-module.

`ONH_0 = OPol_0`, `ONH_1 = OPol_1` and `ONH_{n+2} = EQOnhDG.ONH n`. By `EQK0Field`,
`K₀(D(ONH_0)) ≅ K₀(D(ONH_1)) ≅ ℤ[√−1]` on the regular classes `1 = [ONH_0]`, `E = [ONH_1]`, and
`K₀(D(ONH_n)) = 0` for `n ≥ 2`; so `K₀(D(ONH)) = ⨁_n K₀(D(ONH_n))` is free on `1`, `E`, like
`u⁺ = ℤ[√−1][E]/(E²)`. The structure maps:

* `ι_{m,n} : ONH_m ⊗ ONH_n → ONH_{m+n}`: for `m + n ≤ 1` the isomorphism of dg rings
  `OPol_m ⊗ OPol_n ≅ OPol_{m+n}` (`EQFunctor.opolTensorDG`); `ι_{1,1}` is that map followed by the
  inclusion `OPol_2 ⊆ ONH_2` (`EQOnhDG.ONH.polyHom`).
* `kunneth m n`: the Künneth isomorphism (3.39) `K₀(ONH_m) ⊗ K₀(ONH_n) ≅ K₀(ONH_m ⊗ ONH_n)` for
  `m, n ≤ 1`, `[ONH_m] ⊗ [ONH_n] ↦ [ONH_m ⊗ ONH_n]` (for `m` or `n ≥ 2` both sides vanish).
* `ind m n`, `indTwo`: the symbol of `Ind_{m,n}` (3.35) (derived induction along `ι_{m,n}` on
  half-graded modules) after `kunneth`; `res m n`: the symbol of `Res_{m,n}` (3.36) followed by the
  inverse of `kunneth`. Restriction along the isomorphism `ι_{m,n}` (`m + n ≤ 1`) is derived induction
  along its inverse, which is how `res` is computed.

**Theorem 3.18** (`thm_3_18_*`): `1 · 1 = 1`, `1 · E = E · 1 = E`, `E · E = 0` (the target
`K₀(ONH_2)` vanishes), `r(1) = 1 ⊗ 1`, `r(E) = E ⊗ 1 + 1 ⊗ E` — the structure constants of `u⁺`
with `r(E) = E ⊗ 1 + 1 ⊗ E` (`EQQuantum.ru_eps`); all other components of `[Ind]`, `[Res]` have source
or target `0`. (No twisting sign occurs in degrees `≤ 1`.)
-/

noncomputable section

open CategoryTheory TensorProduct

namespace OddMath.Frontier.EQK0

open DG DG.HalfGradedDGRing
open OddMath.Frontier.EQSkewDifferential (OPol)
open OddMath.Frontier.EQFunctor (opolTensorDG opolTensorDG_bijective opolTensorEquiv)
open OddMath.Frontier.EQOnhDG (ONH)

/-- `OPol_m ⊗ OPol_n`, dg-lean's graded tensor product. -/
abbrev OPolT (m n : ℕ) : Type :=
  DGAlgebra.gradingSubmodule ℤ (OPol m) ᵍ⊗[ℤ] DGAlgebra.gradingSubmodule ℤ (OPol n)

/-- Connectedness over `ℤ` pulls back along injective morphisms of dg rings. -/
theorem IsConnectedInt.of_injective {A B : Type*} [Ring A] [DGAddCommGroup A] [DGRing A] [Ring B]
    [DGAddCommGroup B] [DGRing B] (f : A →ᵈᵍ+* B) (hf : Function.Injective f)
    (hB : IsConnectedInt B) : IsConnectedInt A where
  grading_neg n hn := eq_bot_iff.mpr fun x hx => (AddSubgroup.mem_bot).mpr (hf (by
    have h := f.map_mem hx
    rw [hB.grading_neg n hn] at h
    rw [(AddSubgroup.mem_bot).mp h, map_zero]))
  grading_zero x hx := by
    obtain ⟨m, hm⟩ := hB.grading_zero _ (f.map_mem hx)
    exact ⟨m, hf (by rw [map_intCast, hm])⟩
  intCast_injective m h := hB.intCast_injective m (by rw [← map_intCast f, h, map_zero])

theorem isConnectedInt_opolT (m n : ℕ) : IsConnectedInt (OPolT m n) :=
  IsConnectedInt.of_injective (opolTensorDG m n) opolTensorDG_bijective.1 (isConnectedInt_opol (m+n))

/-- The scalar extension `K ⊗ φ` of a morphism of dg rings. -/
def extendHom (K : Type) [Field K] {A B : Type} [Ring A] [DGAddCommGroup A] [DGRing A] [Ring B]
    [DGAddCommGroup B] [DGRing B] (φ : A →ᵈᵍ+* B) : ExtendScalars K A →ᵈᵍ+* ExtendScalars K B :=
  (GradedTensorProduct.map (DGAlgHom.id : DegreeZeroRing K →ᵈᵍₐ[ℤ] DegreeZeroRing K)
    (intDGAlgHom φ)).toDGRingHom

variable (K : Type) [Field K]
  [∀ N, HasDerivedCategory.{0, 0} (ExtendScalars K (OPol N))]
  [∀ N, CatModule.HasDerivedCategory.{0, 0}
    (WeightCategory (HalfGradedDGRing.ofDGRing (ExtendScalars K (OPol N))).Regraded)]
  [∀ m n, HasDerivedCategory.{0, 0} (ExtendScalars K (OPolT m n))]
  [∀ m n, CatModule.HasDerivedCategory.{0, 0}
    (WeightCategory (HalfGradedDGRing.ofDGRing (ExtendScalars K (OPolT m n))).Regraded)]

/-- `K₀(D(OPol_N))`; for `N ≤ 1` this is `K₀(D(ONH_N))`. -/
abbrev GK (N : ℕ) : Type 1 :=
  SuperK0c.{0, 0} (HalfGradedDGRing.ofDGRing (ExtendScalars K (OPol N)))

/-- `K₀(D(OPol_m ⊗ OPol_n))`. -/
abbrev TK (m n : ℕ) : Type 1 :=
  SuperK0c.{0, 0} (HalfGradedDGRing.ofDGRing (ExtendScalars K (OPolT m n)))

/-- The regular class `[OPol_N]`. -/
abbrev regG (N : ℕ) : GK K N :=
  superK0cMk.{0, 0} _ (Diagonal.mapCompactK0.{0, 0, 0} (ExtendScalars K (OPol N))
    (DGRing.K0.self (ExtendScalars K (OPol N))))

/-- The regular class `[OPol_m ⊗ OPol_n]`. -/
abbrev regT (m n : ℕ) : TK K m n :=
  superK0cMk.{0, 0} _ (Diagonal.mapCompactK0.{0, 0, 0} (ExtendScalars K (OPolT m n))
    (DGRing.K0.self (ExtendScalars K (OPolT m n))))

/-- `K₀(D(OPol_m ⊗ OPol_n)) ≅ ℤ[√−1]`. -/
def superK0OPolTEquiv (m n : ℕ) : TK K m n ≃ₗ[GaussianInt] GaussianInt :=
  superK0GaussianOfConnected K (isConnectedInt_opolT m n)

/-- **The Künneth isomorphism (3.39)** `K₀(ONH_m) ⊗ K₀(ONH_n) ≅ K₀(ONH_m ⊗ ONH_n)`, `m, n ≤ 1`,
with `[ONH_m] ⊗ [ONH_n] ↦ [ONH_m ⊗ ONH_n]` (`kunneth_reg`). -/
def kunneth (m n : ℕ) : GK K m ⊗[GaussianInt] GK K n ≃ₗ[GaussianInt] TK K m n :=
  tensorEquivOfGaussian (superK0OPolEquiv.{0} K m) (superK0OPolEquiv.{0} K n) (superK0OPolTEquiv K m n)

theorem kunneth_reg (m n : ℕ) : kunneth K m n (regG K m ⊗ₜ regG K n) = regT K m n :=
  tensorEquivOfGaussian_tmul _ _ _ (superK0OPolEquiv_self K m) (superK0OPolEquiv_self K n)
    (superK0GaussianOfConnected_self K (isConnectedInt_opolT m n))

/-- **The symbol of `Ind_{m,n}`** (3.35) for `m + n ≤ 1` (more generally into `K₀(D(OPol_{m+n}))`):
derived induction along `K ⊗ ι_{m,n}` on half-graded modules, after the Künneth isomorphism. -/
def ind (m n : ℕ) (t : GK K m ⊗[GaussianInt] GK K n) : GK K (m+n) :=
  superK0cMap _ _ (HalfGradedDGRing.Hom.ofDGRingHom (extendHom K (opolTensorDG m n))).K0Map
    (kunneth K m n t)

theorem ind_reg (m n : ℕ) : ind K m n (regG K m ⊗ₜ regG K n) = regG K (m+n) := by
  apply (superK0OPolEquiv.{0} K (m+n)).injective
  refine (superK0GaussianOfBase_superK0cMap _ _ _ (baseK0_map_eq _ _ _
    (baseK0EquivInt_self K (isConnectedInt_opolT m n))
    (baseK0EquivInt_self K (isConnectedInt_opol (m+n)))) _).trans ?_
  refine (congrArg (superK0OPolTEquiv K m n) (kunneth_reg K m n)).trans ?_
  exact (superK0GaussianOfConnected_self K (isConnectedInt_opolT m n)).trans
    (superK0OPolEquiv_self K (m+n)).symm

/-- **The symbol of `Res_{m,n}`** (3.36), `m + n ≤ 1` (restriction along the isomorphism `ι_{m,n}`, that
is derived induction along its inverse), followed by the inverse of the Künneth isomorphism. -/
def res (m n : ℕ) (s : GK K (m+n)) : GK K m ⊗[GaussianInt] GK K n :=
  (kunneth K m n).symm
    (superK0cMap _ _ (HalfGradedDGRing.Hom.ofDGRingHom
      (extendHom K (opolTensorEquiv m n).symm.toDGAlgHom.toDGRingHom)).K0Map s)

theorem res_reg (m n : ℕ) : res K m n (regG K (m+n)) = regG K m ⊗ₜ regG K n := by
  refine (LinearEquiv.symm_apply_eq _).mpr ((superK0OPolTEquiv K m n).injective ?_)
  refine (superK0GaussianOfBase_superK0cMap _ _ _ (baseK0_map_eq _ _ _
    (baseK0EquivInt_self K (isConnectedInt_opol (m+n)))
    (baseK0EquivInt_self K (isConnectedInt_opolT m n))) _).trans ?_
  refine (superK0OPolEquiv_self K (m+n)).trans ?_
  exact ((congrArg (superK0OPolTEquiv K m n) (kunneth_reg K m n)).trans
    (superK0GaussianOfConnected_self K (isConnectedInt_opolT m n))).symm

/-! ### Theorem 3.18 -/

/-- **Theorem 3.18**, `1 · 1 = 1`: `[Ind_{0,0}]([ONH_0] ⊗ [ONH_0]) = [ONH_0]`. -/
theorem thm_3_18_mul_one_one : ind K 0 0 (regG K 0 ⊗ₜ regG K 0) = regG K 0 := ind_reg K 0 0

/-- **Theorem 3.18**, `1 · E = E`: `[Ind_{0,1}]([ONH_0] ⊗ [ONH_1]) = [ONH_1]`. -/
theorem thm_3_18_mul_one_E : ind K 0 1 (regG K 0 ⊗ₜ regG K 1) = regG K 1 := ind_reg K 0 1

/-- **Theorem 3.18**, `E · 1 = E`: `[Ind_{1,0}]([ONH_1] ⊗ [ONH_0]) = [ONH_1]`. -/
theorem thm_3_18_mul_E_one : ind K 1 0 (regG K 1 ⊗ₜ regG K 0) = regG K 1 := ind_reg K 1 0

/-- **Theorem 3.18**, `r(1) = 1 ⊗ 1`. -/
theorem thm_3_18_comul_one : res K 0 0 (regG K 0) = regG K 0 ⊗ₜ regG K 0 := res_reg K 0 0

/-- **Theorem 3.18**, `r(E) = E ⊗ 1 + 1 ⊗ E`: the `(1, 0)`-component `[Res_{1,0}][ONH_1] = [ONH_1] ⊗ [ONH_0]`
(`thm_3_18_comul_E_left`) and the `(0, 1)`-component `[Res_{0,1}][ONH_1] = [ONH_0] ⊗ [ONH_1]`
(`thm_3_18_comul_E_right`). -/
theorem thm_3_18_comul_E_left : res K 1 0 (regG K 1) = regG K 1 ⊗ₜ regG K 0 := res_reg K 1 0

theorem thm_3_18_comul_E_right : res K 0 1 (regG K 1) = regG K 0 ⊗ₜ regG K 1 := res_reg K 0 1

section Rank2

variable [∀ n, HasDerivedCategory.{0, 0} (ExtendScalars K (ONH n))]
  [∀ n, CatModule.HasDerivedCategory.{0, 0}
    (WeightCategory (HalfGradedDGRing.ofDGRing (ExtendScalars K (ONH n))).Regraded)]

/-- `ι_{1,1} : ONH_1 ⊗ ONH_1 → ONH_2`, `OPol_1 ⊗ OPol_1 ≅ OPol_2 ⊆ ONH_2`. -/
def iotaOneOne : OPolT 1 1 →ᵈᵍ+* ONH 0 := (EQOnhDG.ONH.polyHom 0).comp (opolTensorDG 1 1)

/-- The symbol of `Ind_{1,1} : D(ONH_1 ⊗ ONH_1) → D(ONH_2)` after the Künneth isomorphism. -/
def indTwo (t : GK K 1 ⊗[GaussianInt] GK K 1) :
    SuperK0c.{0, 0} (HalfGradedDGRing.ofDGRing (ExtendScalars K (ONH 0))) :=
  superK0cMap _ _ (HalfGradedDGRing.Hom.ofDGRingHom (extendHom K iotaOneOne)).K0Map (kunneth K 1 1 t)

/-- **Theorem 3.18**, `E · E = 0`: `[Ind_{1,1}]([ONH_1] ⊗ [ONH_1]) = 0` in `K₀(D(ONH_2)) = 0`. -/
theorem thm_3_18_mul_E_E : indTwo K (regG K 1 ⊗ₜ regG K 1) = 0 :=
  (superK0c_onh_subsingleton.{0} K 0).elim _ _

end Rank2

end OddMath.Frontier.EQK0
