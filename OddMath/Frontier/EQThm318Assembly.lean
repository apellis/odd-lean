import OddMath.Frontier.EQThm318Int
import OddMath.Frontier.EQThm417
import OddMath.Frontier.EQK0AssemblySmall

/-!
# Ellis–Qi Theorem 3.18 as one twisted-bialgebra isomorphism `u⁺ ≅ K₀(D(ONH))`

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
§3.6, (3.40)–(3.44) and Theorem 3.18 (printed numbering). Conventions as in
`OddMath.Frontier.EQThm318` (over a field `K`) and `OddMath.Frontier.EQThm318Int` (over `ℤ`):
half-graded dg modules, `K₀` the compact super Grothendieck group, a `ℤ[√−1]`-module, the twist `−1`
on `u⁺ ⊗ u⁺` (ERRATA [EQ] 1).

* `K0ONH K N`: `K₀(D(ONH_N))` over `K` (`K₀(D(OPol_N))` for `N ≤ 1`, `ONH_N = OPol_N`;
  `K₀(D(ONH_{n+2}))`, which is `0`, for `N = n + 2`); `K0ONHSum K = ⨁_N K0ONH K N = K₀(D(ONH))`.
* `mult318 K a b`: the symbol of `Ind_{a,b}` (3.40) after the Künneth isomorphism (3.44) (`EQK0.ind`,
  `EQK0.indTwo`); in the components with `a ≥ 2` or `b ≥ 2` the source `K₀(D(ONH_a)) ⊗ K₀(D(ONH_b))`
  is `0` and the map is `0`.
* `comult318 K a b n h`: the symbol of `Res_{a,b}` (3.41) followed by the inverse Künneth isomorphism
  (`EQK0.res`) for `n = a + b ≤ 1`; for `n ≥ 2` the source `K₀(D(ONH_n))` is `0`.
* **Theorem 3.18** (`thm_3_18_equiv K : u⁺ ≃ₗ[ℤ[√−1]] K₀(D(ONH))`, `1 ↦ [ONH_0]`, `E ↦ [ONH_1]`;
  `thm_3_18_mul`: `φ(x y) = [Ind](φ x, φ y)`; `thm_3_18_comul`: `[Res](φ x) = (φ ⊗ φ)(r x)` with `r`
  the coproduct of `u⁺`, `EQK0.AssemblySmall.ruT`, which is `EQQuantum.ru` (twist `−1`) read in
  `u⁺ ⊗ u⁺` (`AssemblySmall.tensorIota_ruT`)): `φ` is an isomorphism of twisted bialgebras.
* The same over `ℤ`: `K0ONHInt`, `mult318Int`, `comult318Int`, `thm_3_18_int_equiv`,
  `thm_3_18_int_mul`, `thm_3_18_int_comul`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open CategoryTheory TensorProduct DirectSum

namespace OddMath.Frontier.EQK0

open DG DG.HalfGradedDGRing
open OddMath.Frontier.EQSkewDifferential (OPol)
open OddMath.Frontier.EQFunctor (opolTensorDG opolTensorEquiv)
open OddMath.Frontier.EQOnhDG (ONH)
open OddMath.Frontier.EQQuantum (uPlus)

/-! ### Over a field -/

section Field

variable (K : Type) [Field K]
  [∀ N, HasDerivedCategory.{0, 0} (ExtendScalars K (OPol N))]
  [∀ N, CatModule.HasDerivedCategory.{0, 0}
    (WeightCategory (HalfGradedDGRing.ofDGRing (ExtendScalars K (OPol N))).Regraded)]
  [∀ m n, HasDerivedCategory.{0, 0} (ExtendScalars K (OPolT m n))]
  [∀ m n, CatModule.HasDerivedCategory.{0, 0}
    (WeightCategory (HalfGradedDGRing.ofDGRing (ExtendScalars K (OPolT m n))).Regraded)]
  [∀ n, HasDerivedCategory.{0, 0} (ExtendScalars K (ONH n))]
  [∀ n, CatModule.HasDerivedCategory.{0, 0}
    (WeightCategory (HalfGradedDGRing.ofDGRing (ExtendScalars K (ONH n))).Regraded)]

/-- `K₀(D(ONH_N))` over `K`: `K₀(D(OPol_N))` for `N ≤ 1`, `K₀(D(ONH_{n+2}))` for `N = n + 2`. -/
def K0ONH : ℕ → Type 1
  | 0 => GK K 0
  | 1 => GK K 1
  | n + 2 => SuperK0c.{0, 0} (HalfGradedDGRing.ofDGRing (ExtendScalars K (ONH n)))

instance instAddCommGroupK0ONH : ∀ N, AddCommGroup (K0ONH K N)
  | 0 => inferInstanceAs (AddCommGroup (GK K 0))
  | 1 => inferInstanceAs (AddCommGroup (GK K 1))
  | n + 2 => inferInstanceAs
      (AddCommGroup (SuperK0c.{0, 0} (HalfGradedDGRing.ofDGRing (ExtendScalars K (ONH n)))))

instance instModuleK0ONH : ∀ N, Module GaussianInt (K0ONH K N)
  | 0 => inferInstanceAs (Module GaussianInt (GK K 0))
  | 1 => inferInstanceAs (Module GaussianInt (GK K 1))
  | n + 2 => inferInstanceAs
      (Module GaussianInt (SuperK0c.{0, 0} (HalfGradedDGRing.ofDGRing (ExtendScalars K (ONH n)))))

/-- **`K₀(D(ONH)) = ⨁_N K₀(D(ONH_N))`** over `K`. -/
abbrev K0ONHSum : Type 1 := ⨁ N, K0ONH K N

/-- The regular classes `[ONH_N]` (`0` for `N ≥ 2`, where `K₀(D(ONH_N)) = 0`). -/
def regONH : ∀ N, K0ONH K N
  | 0 => regG K 0
  | 1 => regG K 1
  | _ + 2 => 0

/-- The symbol of `Ind_{m,n}` (`m + n ≤ 1`) as a `ℤ[√−1]`-linear map (`EQK0.ind`). -/
def indLin (m n : ℕ) : GK K m ⊗[GaussianInt] GK K n →ₗ[GaussianInt] GK K (m + n) :=
  superK0cGaussianMap (HalfGradedDGRing.Hom.ofDGRingHom (extendHom K (opolTensorDG m n))).K0Map ∘ₗ
    (kunneth K m n).toLinearMap

theorem indLin_apply (m n : ℕ) (t : GK K m ⊗[GaussianInt] GK K n) : indLin K m n t = ind K m n t :=
  rfl

/-- The symbol of `Ind_{1,1}` as a `ℤ[√−1]`-linear map (`EQK0.indTwo`; its target is `0`). -/
def indTwoLin : GK K 1 ⊗[GaussianInt] GK K 1 →ₗ[GaussianInt]
    SuperK0c.{0, 0} (HalfGradedDGRing.ofDGRing (ExtendScalars K (ONH 0))) :=
  superK0cGaussianMap (HalfGradedDGRing.Hom.ofDGRingHom (extendHom K iotaOneOne)).K0Map ∘ₗ
    (kunneth K 1 1).toLinearMap

/-- The symbol of `Res_{m,n}` (`m + n ≤ 1`) as a `ℤ[√−1]`-linear map (`EQK0.res`). -/
def resLin (m n : ℕ) : GK K (m + n) →ₗ[GaussianInt] GK K m ⊗[GaussianInt] GK K n :=
  (kunneth K m n).symm.toLinearMap ∘ₗ superK0cGaussianMap (HalfGradedDGRing.Hom.ofDGRingHom
    (extendHom K (opolTensorEquiv m n).symm.toDGAlgHom.toDGRingHom)).K0Map

theorem resLin_apply (m n : ℕ) (s : GK K (m + n)) : resLin K m n s = res K m n s := rfl

/-- **The multiplication `[Ind]` on `K₀(D(ONH))`**, componentwise: the symbol of `Ind_{a,b}` after the
Künneth isomorphism (3.44); `0` where the source vanishes (`a ≥ 2` or `b ≥ 2`). -/
def mult318 : ∀ a b, K0ONH K a ⊗[GaussianInt] K0ONH K b →ₗ[GaussianInt] K0ONH K (a + b)
  | 0, 0 => indLin K 0 0
  | 0, 1 => indLin K 0 1
  | 1, 0 => indLin K 1 0
  | 1, 1 => indTwoLin K
  | _, _ => 0

/-- **The comultiplication `[Res]` on `K₀(D(ONH))`**, componentwise: the symbol of `Res_{a,b}`
followed by the inverse Künneth isomorphism for `a + b ≤ 1`; `0` where the source vanishes
(`a + b ≥ 2`). -/
def comult318 : ∀ a b n, a + b = n → (K0ONH K n →ₗ[GaussianInt] K0ONH K a ⊗[GaussianInt] K0ONH K b)
  | 0, 0, 0, _ => resLin K 0 0
  | 0, 1, 1, _ => resLin K 0 1
  | 1, 0, 1, _ => resLin K 1 0
  | _, _, _, _ => 0

theorem K0ONH_subsingleton (n : ℕ) : Subsingleton (K0ONH K (n + 2)) :=
  superK0c_onh_subsingleton.{0} K n

theorem mult318_00 : mult318 K 0 0 (regONH K 0 ⊗ₜ regONH K 0) = regONH K 0 := ind_reg K 0 0

theorem mult318_01 : mult318 K 0 1 (regONH K 0 ⊗ₜ regONH K 1) = regONH K 1 := ind_reg K 0 1

theorem mult318_10 : mult318 K 1 0 (regONH K 1 ⊗ₜ regONH K 0) = regONH K 1 := ind_reg K 1 0

theorem comult318_reg (a b n : ℕ) (h : a + b = n) (hn : n ≤ 1) :
    comult318 K a b n h (regONH K n) = regONH K a ⊗ₜ regONH K b := by
  subst h
  match a, b, hn with
  | 0, 0, _ => exact res_reg K 0 0
  | 0, 1, _ => exact res_reg K 0 1
  | 1, 0, _ => exact res_reg K 1 0
  | 1, 1, hn => exact absurd hn (by omega)
  | 0, _ + 2, hn => exact absurd hn (by omega)
  | 1, _ + 2, hn => exact absurd hn (by omega)
  | _ + 2, _, hn => exact absurd hn (by omega)

/-- **Theorem 3.18, the isomorphism** `u⁺ ≅ K₀(D(ONH))` of `ℤ[√−1]`-modules, `1 ↦ [ONH_0]`,
`E ↦ [ONH_1]`. -/
def thm_3_18_equiv : uPlus ≃ₗ[GaussianInt] K0ONHSum K :=
  AssemblySmall.equiv (M := K0ONH K) (superK0OPolEquiv.{0} K 0) (superK0OPolEquiv.{0} K 1)
    (K0ONH_subsingleton K) (regONH K) (superK0OPolEquiv_self K 0) (superK0OPolEquiv_self K 1)

theorem thm_3_18_equiv_one : thm_3_18_equiv K 1 = lof GaussianInt ℕ (K0ONH K) 0 (regONH K 0) :=
  AssemblySmall.equiv_one _ _ _ _ _ _

theorem thm_3_18_equiv_eps :
    thm_3_18_equiv K DualNumber.eps = lof GaussianInt ℕ (K0ONH K) 1 (regONH K 1) :=
  AssemblySmall.equiv_eps _ _ _ _ _ _

/-- The multiplication `[Ind]` on `K₀(D(ONH))`. -/
def multK0ONH : K0ONHSum K →ₗ[GaussianInt] K0ONHSum K →ₗ[GaussianInt] K0ONHSum K :=
  Assembly.mulMap (mult318 K)

/-- The comultiplication `[Res]` on `K₀(D(ONH))`. -/
def comultK0ONH : K0ONHSum K →ₗ[GaussianInt] K0ONHSum K ⊗[GaussianInt] K0ONHSum K :=
  Assembly.comulMap (comult318 K)

/-- **Theorem 3.18, multiplication**: `φ(x y) = [Ind](φ x, φ y)`. -/
theorem thm_3_18_mul (x y : uPlus) :
    thm_3_18_equiv K (x * y) = multK0ONH K (thm_3_18_equiv K x) (thm_3_18_equiv K y) :=
  AssemblySmall.equiv_mul _ _ _ _ _ _ (mult318 K) (mult318_00 K) (mult318_01 K) (mult318_10 K) x y

/-- **Theorem 3.18, comultiplication**: `[Res](φ x) = (φ ⊗ φ)(r x)`, `r` the coproduct of `u⁺`. -/
theorem thm_3_18_comul (x : uPlus) :
    comultK0ONH K (thm_3_18_equiv K x) =
      TensorProduct.map (thm_3_18_equiv K).toLinearMap (thm_3_18_equiv K).toLinearMap
        (AssemblySmall.ruT x) :=
  AssemblySmall.equiv_comul _ _ _ _ _ _ (comult318 K) (comult318_reg K) x

end Field

/-! ### Over `ℤ` -/

section Int

variable [∀ N, HasDerivedCategory.{0, 0} (OPol N)]
  [∀ N, CatModule.HasDerivedCategory.{0, 0} (WeightCategory (ofDGRing (OPol N)).Regraded)]
  [∀ m n, HasDerivedCategory.{0, 0} (OPolT m n)]
  [∀ m n, CatModule.HasDerivedCategory.{0, 0} (WeightCategory (ofDGRing (OPolT m n)).Regraded)]
  [∀ n, CatModule.HasDerivedCategory.{0, 0} (WeightCategory (ofDGRing (ONH n)).Regraded)]

/-- `K₀(D(ONH_N))` over `ℤ`. -/
def K0ONHInt : ℕ → Type 1
  | 0 => GZ 0
  | 1 => GZ 1
  | n + 2 => SuperK0c.{0, 0} (ofDGRing (ONH n))

instance instAddCommGroupK0ONHInt : ∀ N, AddCommGroup (K0ONHInt N)
  | 0 => inferInstanceAs (AddCommGroup (GZ 0))
  | 1 => inferInstanceAs (AddCommGroup (GZ 1))
  | n + 2 => inferInstanceAs (AddCommGroup (SuperK0c.{0, 0} (ofDGRing (ONH n))))

instance instModuleK0ONHInt : ∀ N, Module GaussianInt (K0ONHInt N)
  | 0 => inferInstanceAs (Module GaussianInt (GZ 0))
  | 1 => inferInstanceAs (Module GaussianInt (GZ 1))
  | n + 2 => inferInstanceAs (Module GaussianInt (SuperK0c.{0, 0} (ofDGRing (ONH n))))

/-- **`K₀(D(ONH)) = ⨁_N K₀(D(ONH_N))`** over `ℤ`. -/
abbrev K0ONHIntSum : Type 1 := ⨁ N, K0ONHInt N

/-- The regular classes `[ONH_N]` over `ℤ`. -/
def regONHInt : ∀ N, K0ONHInt N
  | 0 => regGZ 0
  | 1 => regGZ 1
  | _ + 2 => 0

/-- The symbol of `Ind_{m,n}` over `ℤ` (`m + n ≤ 1`) as a `ℤ[√−1]`-linear map (`EQK0.indInt`). -/
def indIntLin {m n : ℕ} (hmn : m + n ≤ 1) : GZ m ⊗[GaussianInt] GZ n →ₗ[GaussianInt] GZ (m + n) :=
  superK0cGaussianMap (HalfGradedDGRing.Hom.ofDGRingHom (opolTensorDG m n)).K0Map ∘ₗ
    (kunnethInt hmn).toLinearMap

theorem indIntLin_apply {m n : ℕ} (hmn : m + n ≤ 1) (t : GZ m ⊗[GaussianInt] GZ n) :
    indIntLin hmn t = indInt hmn t := rfl

/-- The symbol of `Ind_{1,1}` over `ℤ` (`EQK0.indTwoInt`; its target is `0`). -/
def indTwoIntLin : GZ 1 ⊗[GaussianInt] GZ 1 →ₗ[GaussianInt] SuperK0c.{0, 0} (ofDGRing (ONH 0)) :=
  superK0cGaussianMap (HalfGradedDGRing.Hom.ofDGRingHom iotaOneOne).K0Map ∘ₗ
    kunnethMapInt le_rfl le_rfl

/-- The symbol of `Res_{m,n}` over `ℤ` (`m + n ≤ 1`) as a `ℤ[√−1]`-linear map (`EQK0.resInt`). -/
def resIntLin {m n : ℕ} (hmn : m + n ≤ 1) : GZ (m + n) →ₗ[GaussianInt] GZ m ⊗[GaussianInt] GZ n :=
  (kunnethInt hmn).symm.toLinearMap ∘ₗ superK0cGaussianMap (HalfGradedDGRing.Hom.ofDGRingHom
    (opolTensorEquiv m n).symm.toDGAlgHom.toDGRingHom).K0Map

theorem resIntLin_apply {m n : ℕ} (hmn : m + n ≤ 1) (s : GZ (m + n)) :
    resIntLin hmn s = resInt hmn s := rfl

/-- The multiplication `[Ind]` on `K₀(D(ONH))` over `ℤ`, componentwise. -/
def mult318Int : ∀ a b, K0ONHInt a ⊗[GaussianInt] K0ONHInt b →ₗ[GaussianInt] K0ONHInt (a + b)
  | 0, 0 => indIntLin (m := 0) (n := 0) (by omega)
  | 0, 1 => indIntLin (m := 0) (n := 1) (by omega)
  | 1, 0 => indIntLin (m := 1) (n := 0) (by omega)
  | 1, 1 => indTwoIntLin
  | _, _ => 0

/-- The comultiplication `[Res]` on `K₀(D(ONH))` over `ℤ`, componentwise. -/
def comult318Int :
    ∀ a b n, a + b = n → (K0ONHInt n →ₗ[GaussianInt] K0ONHInt a ⊗[GaussianInt] K0ONHInt b)
  | 0, 0, 0, _ => resIntLin (m := 0) (n := 0) (by omega)
  | 0, 1, 1, _ => resIntLin (m := 0) (n := 1) (by omega)
  | 1, 0, 1, _ => resIntLin (m := 1) (n := 0) (by omega)
  | _, _, _, _ => 0

theorem K0ONHInt_subsingleton (n : ℕ) : Subsingleton (K0ONHInt (n + 2)) :=
  ⟨fun x y => (superK0c_onh_int_eq_zero n x).trans (superK0c_onh_int_eq_zero n y).symm⟩

theorem mult318Int_00 : mult318Int 0 0 (regONHInt 0 ⊗ₜ regONHInt 0) = regONHInt 0 :=
  indInt_reg (m := 0) (n := 0) (by omega)

theorem mult318Int_01 : mult318Int 0 1 (regONHInt 0 ⊗ₜ regONHInt 1) = regONHInt 1 :=
  indInt_reg (m := 0) (n := 1) (by omega)

theorem mult318Int_10 : mult318Int 1 0 (regONHInt 1 ⊗ₜ regONHInt 0) = regONHInt 1 :=
  indInt_reg (m := 1) (n := 0) (by omega)

theorem comult318Int_reg (a b n : ℕ) (h : a + b = n) (hn : n ≤ 1) :
    comult318Int a b n h (regONHInt n) = regONHInt a ⊗ₜ regONHInt b := by
  subst h
  match a, b, hn with
  | 0, 0, _ => exact resInt_reg (m := 0) (n := 0) (by omega)
  | 0, 1, _ => exact resInt_reg (m := 0) (n := 1) (by omega)
  | 1, 0, _ => exact resInt_reg (m := 1) (n := 0) (by omega)
  | 1, 1, hn => exact absurd hn (by omega)
  | 0, _ + 2, hn => exact absurd hn (by omega)
  | 1, _ + 2, hn => exact absurd hn (by omega)
  | _ + 2, _, hn => exact absurd hn (by omega)

/-- **Theorem 3.18 over `ℤ`, the isomorphism** `u⁺ ≅ K₀(D(ONH))`, `1 ↦ [ONH_0]`, `E ↦ [ONH_1]`. -/
def thm_3_18_int_equiv : uPlus ≃ₗ[GaussianInt] K0ONHIntSum :=
  AssemblySmall.equiv (M := K0ONHInt) (superK0OPolIntEquiv (N := 0) (by omega))
    (superK0OPolIntEquiv (N := 1) le_rfl) K0ONHInt_subsingleton regONHInt
    (superK0OPolIntEquiv_self _) (superK0OPolIntEquiv_self _)

theorem thm_3_18_int_equiv_one : thm_3_18_int_equiv 1 = lof GaussianInt ℕ K0ONHInt 0 (regONHInt 0) :=
  AssemblySmall.equiv_one _ _ _ _ _ _

theorem thm_3_18_int_equiv_eps :
    thm_3_18_int_equiv DualNumber.eps = lof GaussianInt ℕ K0ONHInt 1 (regONHInt 1) :=
  AssemblySmall.equiv_eps _ _ _ _ _ _

/-- The multiplication `[Ind]` on `K₀(D(ONH))` over `ℤ`. -/
def multK0ONHInt : K0ONHIntSum →ₗ[GaussianInt] K0ONHIntSum →ₗ[GaussianInt] K0ONHIntSum :=
  Assembly.mulMap mult318Int

/-- The comultiplication `[Res]` on `K₀(D(ONH))` over `ℤ`. -/
def comultK0ONHInt : K0ONHIntSum →ₗ[GaussianInt] K0ONHIntSum ⊗[GaussianInt] K0ONHIntSum :=
  Assembly.comulMap comult318Int

/-- **Theorem 3.18 over `ℤ`, multiplication**: `φ(x y) = [Ind](φ x, φ y)`. -/
theorem thm_3_18_int_mul (x y : uPlus) :
    thm_3_18_int_equiv (x * y) = multK0ONHInt (thm_3_18_int_equiv x) (thm_3_18_int_equiv y) :=
  AssemblySmall.equiv_mul _ _ _ _ _ _ mult318Int mult318Int_00 mult318Int_01 mult318Int_10 x y

/-- **Theorem 3.18 over `ℤ`, comultiplication**: `[Res](φ x) = (φ ⊗ φ)(r x)`. -/
theorem thm_3_18_int_comul (x : uPlus) :
    comultK0ONHInt (thm_3_18_int_equiv x) =
      TensorProduct.map thm_3_18_int_equiv.toLinearMap thm_3_18_int_equiv.toLinearMap
        (AssemblySmall.ruT x) :=
  AssemblySmall.equiv_comul _ _ _ _ _ _ comult318Int comult318Int_reg x

end Int

end OddMath.Frontier.EQK0
