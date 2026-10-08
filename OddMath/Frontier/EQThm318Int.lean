import OddMath.Frontier.EQThm318
import OddMath.Frontier.EQSmallRankDG
import OddMath.Frontier.EQHalfGradedAcyclic
import DG.K0.ProjectiveRank
import DG.Category.Derived.TensorIso

/-!
# Ellis–Qi Theorem 3.18 over `ℤ`

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
§3.6, Theorem 3.18 and the Künneth property (3.39). `OddMath.Frontier.EQThm318` proves the theorem
over every field; this file proves it over the integers, with the integral dg rings `ONH_N`
themselves (no scalar extension), half-graded dg modules (diagonal half-grading) and the compact
super Grothendieck group, a `ℤ[√−1]`-module.

* `intUnit A : ℤ → A`, the unit of a dg ring as a morphism of dg rings (`ℤ` in degree `0`,
  `DG.DegreeZeroRing ℤ`).
* `intUnit_opol_isQuasiIso`: for `N ≤ 1` the unit `ℤ → OPol_N` is a quasi-isomorphism, by the
  integral cohomology computation `H(OPol_N) = ℤ · 1` (`EQSmallRankDG`, from Proposition A.2).
* `baseK0OPolInt`: hence `K₀(D(OPol_N)^c) ≃ K₀(D(ℤ)^c) ≃ ℤ`, `[OPol_N] ↦ 1` (invariance of `K₀` under
  quasi-isomorphisms, `DG.DGRing.K0.mapEquivOfIsQuasiIso`, and `K₀(ℤ) ≃ ℤ`,
  `DG.DGRing.K0.equivIntOfIsPrincipalIdealRing`); `superK0OPolIntEquiv`: the half-graded super
  Grothendieck group of `ONH_N = OPol_N` (`N ≤ 1`) is `ℤ[√−1]` on the regular class.
  For `N ≥ 2` it vanishes (`EQDiagonal.superK0c_eq_zero`, Proposition 3.16 (2)).
* `kunnethInt` (`m + n ≤ 1`): the Künneth isomorphism (3.39) on regular classes;
  `kunnethMapInt 1 1`: the `ℤ[√−1]`-linear map `[ONH_1] ⊗ [ONH_1] ↦ [ONH_1 ⊗ ONH_1]` (that it is an
  isomorphism over `ℤ` is not needed here, since its composite with `[Ind_{1,1}]` lands in
  `K₀(D(ONH_2)) = 0`; it is proved in `OddMath.Frontier.EQKunnethInt`).

**Theorem 3.18 over `ℤ`** (`thm_3_18_int_*`): `1 · 1 = 1`, `1 · E = E · 1 = E`, `E · E = 0`,
`r(1) = 1 ⊗ 1`, `r(E) = E ⊗ 1 + 1 ⊗ E` in `K₀(D(ONH)) = ⨁_N K₀(D(ONH_N))`, free over `ℤ[√−1]` on
`1 = [ONH_0]`, `E = [ONH_1]`. This is the integral statement of the footnote to §3.6 / §4.4
("everything works over ℤ") for Theorem 3.18; it does not use Corollary 2.6 (which needs a
semisimple degree-zero part), because in ranks `≤ 1` the dg rings are quasi-isomorphic to `ℤ` and in
ranks `≥ 2` they are acyclic.
-/

noncomputable section

open CategoryTheory TensorProduct

namespace OddMath.Frontier.EQK0

open DG DG.HalfGradedDGRing
open OddMath.Frontier.EQSkewDifferential (OPol)
open OddMath.Frontier.EQFunctor (opolTensorDG opolTensorEquiv)
open OddMath.Frontier.EQOnhDG (ONH)

/-! ### The unit `ℤ → A` -/

section Unit

variable (A : Type*) [Ring A] [DGAddCommGroup A] [DGRing A]

theorem intCast_mem_grading_zero (z : ℤ) : (z : A) ∈ grading (M := A) 0 := by
  rw [← zsmul_one]
  exact AddSubgroup.zsmul_mem _ one_mem_grading z

/-- The unit `ℤ → A` of a dg ring, `ℤ` concentrated in degree `0`. -/
def intUnit : DegreeZeroRing ℤ →ᵈᵍ+* A where
  toFun a := (((DegreeZeroRing.of ℤ).symm a : ℤ) : A)
  map_one' := by rw [map_one, Int.cast_one]
  map_mul' a b := by rw [map_mul, Int.cast_mul]
  map_zero' := by rw [map_zero, Int.cast_zero]
  map_add' a b := by rw [map_add, Int.cast_add]
  map_mem' {n} {a} ha := by
    by_cases hn : n = 0
    · subst hn
      exact intCast_mem_grading_zero A _
    · rw [DegreeZeroRing.eq_zero_of_mem_grading ℤ hn ha, map_zero, Int.cast_zero]
      exact zero_mem _
  map_d' a := by
    rw [DegreeZeroRing.d_eq_zero, map_zero, Int.cast_zero]
    exact (d_intCast _).symm

theorem intUnit_apply (z : ℤ) : intUnit A (DegreeZeroRing.of ℤ z) = (z : A) := rfl

end Unit

theorem cohomology_degreeZeroRing_eq_zero {n : ℤ} (hn : n ≠ 0)
    (x : cohomology (DegreeZeroRing ℤ) n) : x = 0 := by
  induction x using cohomology.induction_on with
  | h z =>
    have hz : (z : DegreeZeroRing ℤ) = 0 :=
      DegreeZeroRing.eq_zero_of_mem_grading ℤ hn (mem_cocycles.mp z.property).1
    rw [cohomology.mk_eq_zero_iff, hz]
    exact zero_mem _

/-- **`ℤ → OPol_N` is a quasi-isomorphism** for `N ≤ 1`: `H(OPol_N) = ℤ · 1` (Ellis–Qi,
Proposition A.2, empty partition; `EQSmallRankDG`). -/
theorem intUnit_opol_isQuasiIso {N : ℕ} (hN : N ≤ 1) : (intUnit (OPol N)).IsQuasiIso := by
  intro n
  by_cases hn : n = 0
  · subst hn
    constructor
    · rw [injective_iff_map_eq_zero]
      intro x hx
      induction x using cohomology.induction_on with
      | h z =>
        rw [DGRingHom.cohomologyMap_mk] at hx
        have h1 : (intUnit (OPol N)).cocyclesMap 0 z =
            EQSmallRankDG.intCocycles N ((DegreeZeroRing.of ℤ).symm (z : DegreeZeroRing ℤ)) :=
          Subtype.ext rfl
        rw [h1] at hx
        have h2 : (DegreeZeroRing.of ℤ).symm (z : DegreeZeroRing ℤ) = 0 :=
          EQSmallRankDG.intClass_injective hN (hx.trans (map_zero _).symm)
        have h3 : z = 0 := Subtype.ext h2
        rw [h3, map_zero]
    · intro y
      obtain ⟨z, rfl⟩ := EQSmallRankDG.intClass_surjective hN y
      refine ⟨cohomology.mk _ 0 ⟨DegreeZeroRing.of ℤ z, mem_cocycles.mpr
        ⟨DegreeZeroRing.mem_grading_zero ℤ _, DegreeZeroRing.d_eq_zero ℤ _⟩⟩, ?_⟩
      rw [DGRingHom.cohomologyMap_mk]
      rfl
  · constructor
    · intro x y _
      rw [cohomology_degreeZeroRing_eq_zero hn x, cohomology_degreeZeroRing_eq_zero hn y]
    · intro y
      exact ⟨0, by rw [map_zero, EQSmallRankDG.cohomology_eq_zero_of_ne_zero hN hn y]⟩

/-- `OPol_m ⊗ OPol_n → OPol_{m+n}` is a quasi-isomorphism (an isomorphism of dg rings). -/
theorem opolTensorDG_isQuasiIso (m n : ℕ) : (opolTensorDG m n).IsQuasiIso :=
  DGRingHom.isQuasiIso_of_leftInverse_rightInverse (opolTensorDG m n)
    (opolTensorEquiv m n).symm.toDGAlgHom.toDGRingHom
    (fun b => (opolTensorEquiv m n).symm_apply_apply b)
    (fun a => (opolTensorEquiv m n).apply_symm_apply a)

/-! ### `K₀ ≃ ℤ` along quasi-isomorphisms -/

section Base

instance : IsDomain (DegreeZeroRing ℤ) := inferInstanceAs (IsDomain ℤ)

instance : IsPrincipalIdealRing (DegreeZeroRing ℤ) := inferInstanceAs (IsPrincipalIdealRing ℤ)

/-- `K₀(D(ℤ)^c) ≃ ℤ`, `[ℤ] ↦ 1`. -/
def baseK0IntEquiv [HasDerivedCategory.{0, 0} (DegreeZeroRing ℤ)] :
    Diagonal.BaseK0.{0, 0} (DegreeZeroRing ℤ) ≃+ ℤ :=
  DGRing.K0.equivIntOfIsPrincipalIdealRing (DegreeZeroRing ℤ)

theorem baseK0IntEquiv_self [HasDerivedCategory.{0, 0} (DegreeZeroRing ℤ)] :
    baseK0IntEquiv (DGRing.K0.self (DegreeZeroRing ℤ)) = 1 :=
  DGRing.K0.equivIntOfIsPrincipalIdealRing_self (DegreeZeroRing ℤ)

variable {A B : Type} [Ring A] [DGAddCommGroup A] [DGRing A] [HasDerivedCategory.{0, 0} A]
  [Ring B] [DGAddCommGroup B] [DGRing B] [HasDerivedCategory.{0, 0} B]

/-- Transport of a trivialization `K₀(D(B)^c) ≃ ℤ` along a quasi-isomorphism `A → B`. -/
def baseK0EquivOfQuasiIso (φ : A →ᵈᵍ+* B) (hφ : φ.IsQuasiIso)
    (e : Diagonal.BaseK0.{0, 0} B ≃+ ℤ) : Diagonal.BaseK0.{0, 0} A ≃+ ℤ :=
  (DGRing.K0.mapEquivOfIsQuasiIso φ hφ).trans e

theorem baseK0EquivOfQuasiIso_self (φ : A →ᵈᵍ+* B) (hφ : φ.IsQuasiIso)
    (e : Diagonal.BaseK0.{0, 0} B ≃+ ℤ) (he : e (DGRing.K0.self B) = 1) :
    baseK0EquivOfQuasiIso φ hφ e (DGRing.K0.self A) = 1 := by
  rw [baseK0EquivOfQuasiIso, AddEquiv.trans_apply, DGRing.K0.mapEquivOfIsQuasiIso_apply,
    DGRing.K0.map_self, he]

/-- Transport of a trivialization `K₀(D(A)^c) ≃ ℤ` backwards along a quasi-isomorphism `A → B`. -/
def baseK0EquivOfQuasiIso' (φ : A →ᵈᵍ+* B) (hφ : φ.IsQuasiIso)
    (e : Diagonal.BaseK0.{0, 0} A ≃+ ℤ) : Diagonal.BaseK0.{0, 0} B ≃+ ℤ :=
  (DGRing.K0.mapEquivOfIsQuasiIso φ hφ).symm.trans e

theorem baseK0EquivOfQuasiIso'_self (φ : A →ᵈᵍ+* B) (hφ : φ.IsQuasiIso)
    (e : Diagonal.BaseK0.{0, 0} A ≃+ ℤ) (he : e (DGRing.K0.self A) = 1) :
    baseK0EquivOfQuasiIso' φ hφ e (DGRing.K0.self B) = 1 := by
  have h : (DGRing.K0.mapEquivOfIsQuasiIso φ hφ).symm (DGRing.K0.self B) = DGRing.K0.self A :=
    (AddEquiv.symm_apply_eq _).mpr (by rw [DGRing.K0.mapEquivOfIsQuasiIso_apply, DGRing.K0.map_self])
  rw [baseK0EquivOfQuasiIso', AddEquiv.trans_apply, h, he]

end Base

/-- **`K₀(D(OPol_N)^c) ≃ ℤ`** over `ℤ` for `N ≤ 1`, with `[OPol_N] ↦ 1`. -/
def baseK0OPolInt {N : ℕ} (hN : N ≤ 1) [HasDerivedCategory.{0, 0} (OPol N)] :
    Diagonal.BaseK0.{0, 0} (OPol N) ≃+ ℤ :=
  letI := HasDerivedCategory.small.{0, 0} (DegreeZeroRing ℤ)
  baseK0EquivOfQuasiIso' (intUnit (OPol N)) (intUnit_opol_isQuasiIso hN) baseK0IntEquiv

theorem baseK0OPolInt_self {N : ℕ} (hN : N ≤ 1) [HasDerivedCategory.{0, 0} (OPol N)] :
    baseK0OPolInt hN (DGRing.K0.self (OPol N)) = 1 :=
  letI := HasDerivedCategory.small.{0, 0} (DegreeZeroRing ℤ)
  baseK0EquivOfQuasiIso'_self _ _ _ baseK0IntEquiv_self

/-- `K₀(D(OPol_m ⊗ OPol_n)^c) ≃ ℤ` over `ℤ` for `m + n ≤ 1`, with `[OPol_m ⊗ OPol_n] ↦ 1`. -/
def baseK0OPolTInt {m n : ℕ} (hmn : m + n ≤ 1) [HasDerivedCategory.{0, 0} (OPol (m+n))]
    [HasDerivedCategory.{0, 0} (OPolT m n)] : Diagonal.BaseK0.{0, 0} (OPolT m n) ≃+ ℤ :=
  baseK0EquivOfQuasiIso (opolTensorDG m n) (opolTensorDG_isQuasiIso m n) (baseK0OPolInt hmn)

theorem baseK0OPolTInt_self {m n : ℕ} (hmn : m + n ≤ 1) [HasDerivedCategory.{0, 0} (OPol (m+n))]
    [HasDerivedCategory.{0, 0} (OPolT m n)] :
    baseK0OPolTInt hmn (DGRing.K0.self (OPolT m n)) = 1 :=
  baseK0EquivOfQuasiIso_self _ _ _ (baseK0OPolInt_self hmn)

/-! ### Super Grothendieck groups over `ℤ` -/

section Rank2Vanishing

variable [∀ n, CatModule.HasDerivedCategory.{0, 0} (WeightCategory (ofDGRing (ONH n)).Regraded)]

/-- **`K₀(D(ONH_{n+2})) = 0` over `ℤ`** (Proposition 3.16 (2)). -/
theorem superK0c_onh_int_eq_zero (n : ℕ) (x : SuperK0c.{0, 0} (ofDGRing (ONH n))) : x = 0 :=
  EQDiagonal.superK0c_eq_zero x

end Rank2Vanishing

variable [∀ N, HasDerivedCategory.{0, 0} (OPol N)]
  [∀ N, CatModule.HasDerivedCategory.{0, 0} (WeightCategory (ofDGRing (OPol N)).Regraded)]

/-- `K₀(D(OPol_N))` over `ℤ`; for `N ≤ 1` this is `K₀(D(ONH_N))`. -/
abbrev GZ (N : ℕ) : Type 1 :=
  SuperK0c.{0, 0} (ofDGRing (OPol N))

/-- The regular class `[OPol_N]`. -/
abbrev regGZ (N : ℕ) : GZ N :=
  superK0cMk.{0, 0} _ (Diagonal.mapCompactK0.{0, 0, 0} (OPol N) (DGRing.K0.self (OPol N)))

/-- **`K₀(D(ONH_N)) ≅ ℤ[√−1]` over `ℤ`** for `N ≤ 1` (`ONH_N = OPol_N`), on the regular class. -/
def superK0OPolIntEquiv {N : ℕ} (hN : N ≤ 1) : GZ N ≃ₗ[GaussianInt] GaussianInt :=
  superK0GaussianOfBase.{0, 0, 0} (OPol N) (baseK0OPolInt hN)

theorem superK0OPolIntEquiv_self {N : ℕ} (hN : N ≤ 1) : superK0OPolIntEquiv hN (regGZ N) = 1 := by
  rw [superK0OPolIntEquiv, superK0GaussianOfBase_mk, baseK0OPolInt_self, Int.cast_one]

section OPolT

variable [∀ m n, HasDerivedCategory.{0, 0} (OPolT m n)]
  [∀ m n, CatModule.HasDerivedCategory.{0, 0} (WeightCategory (ofDGRing (OPolT m n)).Regraded)]

/-- `K₀(D(OPol_m ⊗ OPol_n))` over `ℤ`. -/
abbrev TZ (m n : ℕ) : Type 1 :=
  SuperK0c.{0, 0} (ofDGRing (OPolT m n))

/-- The regular class `[OPol_m ⊗ OPol_n]`. -/
abbrev regTZ (m n : ℕ) : TZ m n :=
  superK0cMk.{0, 0} _ (Diagonal.mapCompactK0.{0, 0, 0} (OPolT m n) (DGRing.K0.self (OPolT m n)))

/-- `K₀(D(OPol_m ⊗ OPol_n)) ≅ ℤ[√−1]` over `ℤ` for `m + n ≤ 1`. -/
def superK0OPolTIntEquiv {m n : ℕ} (hmn : m + n ≤ 1) : TZ m n ≃ₗ[GaussianInt] GaussianInt :=
  superK0GaussianOfBase.{0, 0, 0} (OPolT m n) (baseK0OPolTInt hmn)

omit [∀ N, CatModule.HasDerivedCategory.{0, 0} (WeightCategory (ofDGRing (OPol N)).Regraded)] in
theorem superK0OPolTIntEquiv_self {m n : ℕ} (hmn : m + n ≤ 1) :
    superK0OPolTIntEquiv hmn (regTZ m n) = 1 := by
  rw [superK0OPolTIntEquiv, superK0GaussianOfBase_mk, baseK0OPolTInt_self, Int.cast_one]

/-- **The Künneth isomorphism (3.39) over `ℤ`**, `m + n ≤ 1`:
`K₀(ONH_m) ⊗ K₀(ONH_n) ≅ K₀(ONH_m ⊗ ONH_n)`, `[ONH_m] ⊗ [ONH_n] ↦ [ONH_m ⊗ ONH_n]`. -/
def kunnethInt {m n : ℕ} (hmn : m + n ≤ 1) :
    GZ m ⊗[GaussianInt] GZ n ≃ₗ[GaussianInt] TZ m n :=
  tensorEquivOfGaussian (superK0OPolIntEquiv (by omega : m ≤ 1))
    (superK0OPolIntEquiv (by omega : n ≤ 1)) (superK0OPolTIntEquiv hmn)

theorem kunnethInt_reg {m n : ℕ} (hmn : m + n ≤ 1) :
    kunnethInt hmn (regGZ m ⊗ₜ regGZ n) = regTZ m n :=
  tensorEquivOfGaussian_tmul _ _ _ (superK0OPolIntEquiv_self _) (superK0OPolIntEquiv_self _)
    (superK0OPolTIntEquiv_self hmn)

/-- The `ℤ[√−1]`-linear map `K₀(ONH_m) ⊗ K₀(ONH_n) → K₀(ONH_m ⊗ ONH_n)`, `m, n ≤ 1`, determined by
`[ONH_m] ⊗ [ONH_n] ↦ [ONH_m ⊗ ONH_n]` (the source is free on this element). -/
def kunnethMapInt {m n : ℕ} (hm : m ≤ 1) (hn : n ≤ 1) :
    GZ m ⊗[GaussianInt] GZ n →ₗ[GaussianInt] TZ m n :=
  (LinearMap.toSpanSingleton GaussianInt (TZ m n) (regTZ m n)).comp
    ((TensorProduct.lid GaussianInt GaussianInt).toLinearMap.comp
      (TensorProduct.map (superK0OPolIntEquiv hm).toLinearMap (superK0OPolIntEquiv hn).toLinearMap))

theorem kunnethMapInt_reg {m n : ℕ} (hm : m ≤ 1) (hn : n ≤ 1) :
    kunnethMapInt hm hn (regGZ m ⊗ₜ regGZ n) = regTZ m n := by
  rw [kunnethMapInt, LinearMap.comp_apply, LinearMap.comp_apply, TensorProduct.map_tmul]
  simp only [LinearEquiv.coe_coe]
  rw [superK0OPolIntEquiv_self, superK0OPolIntEquiv_self, TensorProduct.lid_tmul, one_smul,
    LinearMap.toSpanSingleton_apply, one_smul]

/-- The symbol of `Ind_{m,n}` (3.35) over `ℤ`, `m + n ≤ 1`: derived induction along
`ι_{m,n} : ONH_m ⊗ ONH_n ≅ ONH_{m+n}` on half-graded modules, after the Künneth isomorphism. -/
def indInt {m n : ℕ} (hmn : m + n ≤ 1) (t : GZ m ⊗[GaussianInt] GZ n) : GZ (m+n) :=
  superK0cMap _ _ (HalfGradedDGRing.Hom.ofDGRingHom (opolTensorDG m n)).K0Map (kunnethInt hmn t)

theorem indInt_reg {m n : ℕ} (hmn : m + n ≤ 1) :
    indInt hmn (regGZ m ⊗ₜ regGZ n) = regGZ (m+n) := by
  apply (superK0OPolIntEquiv hmn).injective
  refine (superK0GaussianOfBase_superK0cMap _ _ _ (baseK0_map_eq _ _ _
    (baseK0OPolTInt_self hmn) (baseK0OPolInt_self hmn)) _).trans ?_
  refine (congrArg (superK0OPolTIntEquiv hmn) (kunnethInt_reg hmn)).trans ?_
  exact (superK0OPolTIntEquiv_self hmn).trans (superK0OPolIntEquiv_self hmn).symm

/-- The symbol of `Res_{m,n}` (3.36) over `ℤ`, `m + n ≤ 1` (restriction along the isomorphism
`ι_{m,n}`, i.e. derived induction along its inverse), followed by the inverse Künneth isomorphism. -/
def resInt {m n : ℕ} (hmn : m + n ≤ 1) (s : GZ (m+n)) : GZ m ⊗[GaussianInt] GZ n :=
  (kunnethInt hmn).symm
    (superK0cMap _ _ (HalfGradedDGRing.Hom.ofDGRingHom
      (opolTensorEquiv m n).symm.toDGAlgHom.toDGRingHom).K0Map s)

theorem resInt_reg {m n : ℕ} (hmn : m + n ≤ 1) :
    resInt hmn (regGZ (m+n)) = regGZ m ⊗ₜ regGZ n := by
  refine (LinearEquiv.symm_apply_eq _).mpr ((superK0OPolTIntEquiv hmn).injective ?_)
  refine (superK0GaussianOfBase_superK0cMap _ _ _ (baseK0_map_eq _ _ _
    (baseK0OPolInt_self hmn) (baseK0OPolTInt_self hmn)) _).trans ?_
  refine (superK0OPolIntEquiv_self hmn).trans ?_
  exact ((congrArg (superK0OPolTIntEquiv hmn) (kunnethInt_reg hmn)).trans
    (superK0OPolTIntEquiv_self hmn)).symm

/-! ### Theorem 3.18 over `ℤ` -/

/-- **Theorem 3.18** over `ℤ`, `1 · 1 = 1`. -/
theorem thm_3_18_int_mul_one_one :
    indInt (m := 0) (n := 0) (by omega) (regGZ 0 ⊗ₜ regGZ 0) = regGZ 0 := indInt_reg _

/-- **Theorem 3.18** over `ℤ`, `1 · E = E`. -/
theorem thm_3_18_int_mul_one_E :
    indInt (m := 0) (n := 1) (by omega) (regGZ 0 ⊗ₜ regGZ 1) = regGZ 1 := indInt_reg _

/-- **Theorem 3.18** over `ℤ`, `E · 1 = E`. -/
theorem thm_3_18_int_mul_E_one :
    indInt (m := 1) (n := 0) (by omega) (regGZ 1 ⊗ₜ regGZ 0) = regGZ 1 := indInt_reg _

/-- **Theorem 3.18** over `ℤ`, `r(1) = 1 ⊗ 1`. -/
theorem thm_3_18_int_comul_one :
    resInt (m := 0) (n := 0) (by omega) (regGZ 0) = regGZ 0 ⊗ₜ regGZ 0 := resInt_reg _

/-- **Theorem 3.18** over `ℤ`, `r(E) = E ⊗ 1 + 1 ⊗ E`: the `(1, 0)`-component. -/
theorem thm_3_18_int_comul_E_left :
    resInt (m := 1) (n := 0) (by omega) (regGZ 1) = regGZ 1 ⊗ₜ regGZ 0 := resInt_reg _

/-- **Theorem 3.18** over `ℤ`, `r(E) = E ⊗ 1 + 1 ⊗ E`: the `(0, 1)`-component. -/
theorem thm_3_18_int_comul_E_right :
    resInt (m := 0) (n := 1) (by omega) (regGZ 1) = regGZ 0 ⊗ₜ regGZ 1 := resInt_reg _

section Rank2

variable [∀ n, CatModule.HasDerivedCategory.{0, 0} (WeightCategory (ofDGRing (ONH n)).Regraded)]

/-- The symbol of `Ind_{1,1} : D(ONH_1 ⊗ ONH_1) → D(ONH_2)` over `ℤ`, after `kunnethMapInt`. -/
def indTwoInt (t : GZ 1 ⊗[GaussianInt] GZ 1) : SuperK0c.{0, 0} (ofDGRing (ONH 0)) :=
  superK0cMap _ _ (HalfGradedDGRing.Hom.ofDGRingHom iotaOneOne).K0Map
    (kunnethMapInt le_rfl le_rfl t)

/-- **Theorem 3.18** over `ℤ`, `E · E = 0`: `[Ind_{1,1}]([ONH_1] ⊗ [ONH_1]) = 0`. -/
theorem thm_3_18_int_mul_E_E : indTwoInt (regGZ 1 ⊗ₜ regGZ 1) = 0 :=
  superK0c_onh_int_eq_zero 0 _

end Rank2

end OPolT

end OddMath.Frontier.EQK0
