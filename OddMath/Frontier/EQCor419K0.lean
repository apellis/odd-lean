import OddMath.Frontier.EQThm318Assembly
import OddMath.Frontier.EQThm417Int
import OddMath.Frontier.EQFunctorEmbeddingSmall

/-!
# Ellis–Qi Corollary 4.19 on Grothendieck groups: `J` categorifies `u⁺ ⊂ U⁺`

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
§4.4, Definition 4.18 and Corollary 4.19 (second sentence: "On the level of Grothendieck groups, this
categorifies the embedding of `u⁺` inside `U⁺` as a sub-twisted bialgebra"), with Theorem 3.18
(`OddMath.Frontier.EQThm318Assembly`) and Theorem 4.17 (`OddMath.Frontier.EQThm417`,
`OddMath.Frontier.EQThm417Int`). Conventions as there: half-graded dg modules, `K₀` the compact super
Grothendieck group (a `ℤ[√−1]`-module), twist `−1` (ERRATA [EQ] 1).

**The functor.** `J_N = Z_N^∨ ⊗^L_{ONH_N} (-)` (Definition 4.18). On half-graded modules it is the
derived tensor product with the diagonally regraded bimodule (`DG.Diagonal.derivedTensor`). Since
`D(ONH_N) = 0` for `N ≥ 2` (Proposition 3.16), only `N ≤ 1` matters, where `ONH_N = OPol_N` and
`J_N = Z_N^∨ ⊗^L_{OPol_N} (-)` (`EQFunctor.JSmall`); over a field `K` the bimodule is base changed,
`K ⊗ Z_N^∨`.

* `jZHalf N`, `jKHalf K N`: `J_N` on half-graded modules over `ℤ` and over `K`; `jZHalfK0`, `jKHalfK0`:
  their symbols on `K₀`. Under `K₀ ≅ ℤ[√−1]` they are the identity for `N ≤ 1`
  (`superK0OsymIntEquiv_jZHalfK0`, `superK0OsymEquiv_jKHalfK0`): `[J_N(ONH_N)] = [Z_N^∨] = [OΛ_N]`,
  `Z_N^∨ ≅ OΛ_N` for `N ≤ 1`.
* `jK0Int : K₀(D(ONH)) → K₀(D(OΛ))`, componentwise `[J_N]` (`0` on `K₀(D(ONH_N)) = 0`, `N ≥ 2`), and
  `jK0 K` over `K`.

**Corollary 4.19 on `K₀`** (`cor_4_19_int_K0`, `cor_4_19_K0`): under the isomorphisms of Theorem 3.18
(`u⁺ ≅ K₀(D(ONH))`) and Theorem 4.17 (`U⁺ ≅ K₀(D(OΛ))`), `[J]` is the inclusion `ι : u⁺ ↪ U⁺`,
`E ↦ E^{(1)}` (`EQQuantum.iota`). Consequently `[J]` is injective (`cor_4_19_int_injective`) and a
map of twisted bialgebras: it intertwines `[Ind]` with `[I]` (`cor_4_19_int_mul`) and `[Res]` with
`[R]` (`cor_4_19_int_comul`); likewise over every field (`cor_4_19_injective`, `cor_4_19_mul`,
`cor_4_19_comul`).
-/

noncomputable section

set_option linter.unusedSectionVars false

open CategoryTheory TensorProduct DirectSum

namespace OddMath.Frontier.EQK0

open DG DG.HalfGradedDGRing MulOpposite
open OddMath.Frontier.EQSkewDifferential (OPol osymDG Zn)
open OddMath.Frontier.EQOnhDG (ONH)
open OddMath.Frontier.EQFunctor (znDual_isKProjective znDualTriangular znDualEquiv)
open OddMath.Frontier.EQQuantum (uPlus UPlus iota ru rU evI)
open OddMath.Frontier.EQK0Int (K0nInt K0OLamInt superK0OsymIntEquiv ePowClassInt thm_4_17_int_equiv
  multK0OLamInt comultK0OLamInt baseK0OsymInt)

/-! ### The coproducts of `u⁺` and `U⁺` -/

/-- `(ι ⊗ ι)(r x) = r(ι x)` in `U⁺ ⊗ U⁺`: the coproduct of `u⁺` in `u⁺ ⊗ u⁺` (`AssemblySmall.ruT`)
maps to the coproduct (2.2) of `U⁺` (twist `−1`). -/
theorem map_iota_ruT (x : uPlus) :
    TensorProduct.map iota.toLinearMap iota.toLinearMap (AssemblySmall.ruT x) =
      EQQuantum.TT.tensorEquiv evI (-1) (rU (iota x)) := by
  have h := AssemblySmall.tensorIota_ruT x
  rw [EQQuantum.tensorIota, LinearMap.comp_apply, LinearEquiv.coe_coe] at h
  rw [EQQuantum.rU_iota, ← h, LinearEquiv.apply_symm_apply]

section Generic

variable {M P : Type*} [AddCommGroup M] [Module GaussianInt M] [AddCommGroup P] [Module GaussianInt P]
  (j : M →ₗ[GaussianInt] P) (φ : uPlus ≃ₗ[GaussianInt] M) (ψ : UPlus ≃ₗ[GaussianInt] P)
  (hj : ∀ x, j (φ x) = ψ (iota x))

include hj in
/-- If `j ∘ φ = ψ ∘ ι` for isomorphisms `φ : u⁺ ≅ M`, `ψ : U⁺ ≅ P`, then `j` is injective. -/
theorem injective_of_iota : Function.Injective j := by
  intro s t h
  obtain ⟨x, rfl⟩ := φ.surjective s
  obtain ⟨y, rfl⟩ := φ.surjective t
  rw [hj, hj] at h
  rw [EQQuantum.iota_injective (ψ.injective h)]

include hj in
/-- If `j ∘ φ = ψ ∘ ι` and `φ`, `ψ` intertwine the products of `u⁺`, `U⁺` with `mM`, `mP`, then
`j` intertwines `mM` and `mP`. -/
theorem mul_of_iota (mM : M →ₗ[GaussianInt] M →ₗ[GaussianInt] M)
    (mP : P →ₗ[GaussianInt] P →ₗ[GaussianInt] P) (hφ : ∀ x y, φ (x * y) = mM (φ x) (φ y))
    (hψ : ∀ x y, ψ (x * y) = mP (ψ x) (ψ y)) (s t : M) : j (mM s t) = mP (j s) (j t) := by
  obtain ⟨x, rfl⟩ := φ.surjective s
  obtain ⟨y, rfl⟩ := φ.surjective t
  rw [← hφ, hj, hj, hj, map_mul, hψ]

include hj in
/-- If `j ∘ φ = ψ ∘ ι` and `φ`, `ψ` intertwine the coproducts of `u⁺`, `U⁺` with `cM`, `cP`, then
`j` intertwines `cM` and `cP`. -/
theorem comul_of_iota (cM : M →ₗ[GaussianInt] M ⊗[GaussianInt] M)
    (cP : P →ₗ[GaussianInt] P ⊗[GaussianInt] P)
    (hφ : ∀ x, cM (φ x) = TensorProduct.map φ.toLinearMap φ.toLinearMap (AssemblySmall.ruT x))
    (hψ : ∀ x, cP (ψ x) =
      TensorProduct.map ψ.toLinearMap ψ.toLinearMap (EQQuantum.TT.tensorEquiv evI (-1) (rU x)))
    (s : M) : cP (j s) = TensorProduct.map j j (cM s) := by
  obtain ⟨x, rfl⟩ := φ.surjective s
  have h : j ∘ₗ φ.toLinearMap = ψ.toLinearMap ∘ₗ iota.toLinearMap := LinearMap.ext fun y => hj y
  rw [hj, hψ, hφ, ← LinearMap.comp_apply (TensorProduct.map j j), ← TensorProduct.map_comp, h,
    TensorProduct.map_comp, LinearMap.comp_apply, map_iota_ruT]

end Generic

/-! ### `Z_N^∨ ≅ OΛ_N` for `N ≤ 1` -/

section Dual

variable {N : ℕ} (hN : N ≤ 1)

/-- For `N ≤ 1`, `Z_N^∨ ≅ OΛ_N` as left dg `OΛ_N`-modules (evaluation at the generator `1_z`). -/
def znDualDGEquiv : RightDual (osymDG N) (Zn N) ≃ᵈᵍ[osymDG N] osymDG N where
  toFun := znDualEquiv hN
  invFun := (znDualEquiv hN).symm
  left_inv := (znDualEquiv hN).left_inv
  right_inv := (znDualEquiv hN).right_inv
  map_add' := map_add _
  map_smul' a f := EQFunctor.znDualEquiv_smul hN a f
  map_mem' hm := (EQFunctor.znDualEquiv_mem_iff hN).mpr hm
  map_d' f := EQFunctor.znDualEquiv_d hN f

theorem isCompact_znDual [DG.HasDerivedCategory.{0, 0} (osymDG N)] :
    IsCompact.{0} (DG.DerivedCategory.Q.obj (DGModuleCat.of (osymDG N) (RightDual (osymDG N) (Zn N)))) :=
  (znDualTriangular N).finiteCellFiltration.isCompact_Q_obj

end Dual

/-! ### `J_N` over `ℤ` -/

section Int

variable [∀ N, CatModule.HasDerivedCategory.{0, 0} (SingleObj (OPol N))]
  [∀ N, CatModule.HasDerivedCategory.{0, 0} (SingleObj (osymDG N))]
  [∀ N, DG.HasDerivedCategory.{0, 0} (OPol N)] [∀ N, DG.HasDerivedCategory.{0, 0} (osymDG N)]
  [∀ N, CatModule.HasDerivedCategory.{0, 0} (WeightCategory (ofDGRing (OPol N)).Regraded)]
  [∀ N, CatModule.HasDerivedCategory.{0, 0} (WeightCategory (ofDGRing (osymDG N)).Regraded)]

variable (N : ℕ)

/-- The symbol of `J_N = Z_N^∨ ⊗^L_{OPol_N} (-)` (`EQFunctor.JSmall`) on `K₀` of compact objects. -/
def K0JZ : DGRing.K0.{0, 0} (OPol N) →+ DGRing.K0.{0, 0} (osymDG N) :=
  DG.K0.mapCompact (EQFunctor.JSmall.{0, 0, 0} N) fun _ h =>
    DGBimodule.isCompact_derivedTensor_obj _ isCompact_znDual h

variable {N}

/-- `[J_N(OPol_N)] = [Z_N^∨] = [OΛ_N]` for `N ≤ 1`. -/
theorem K0JZ_self (hN : N ≤ 1) : K0JZ N (DGRing.K0.self (OPol N)) = DGRing.K0.self (osymDG N) := by
  rw [DGRing.K0.self, K0JZ, DG.K0.mapCompact_mk]
  have e := DGBimodule.derivedTensorSelfIso (osymDG N) (OPol N) (RightDual (osymDG N) (Zn N))
    (znDual_isKProjective N)
  exact mk_eq_of_iso' (P := compactSubcategory.{0} (DG.DerivedCategory.{0, 0} (osymDG N))) _ _
    (e ≪≫ DG.DerivedCategory.Q.mapIso (znDualDGEquiv hN).toDGModuleCatIso)

/-- Under `K₀ ≅ ℤ`, the symbol of `J_N` is the identity, `N ≤ 1`. -/
theorem baseK0OsymInt_K0JZ (hN : N ≤ 1) (y : DGRing.K0.{0, 0} (OPol N)) :
    baseK0OsymInt N (K0JZ N y) = (1 : ℤ) * baseK0OPolInt hN y := by
  have hy : y = baseK0OPolInt hN y • DGRing.K0.self (OPol N) := by
    apply (baseK0OPolInt hN).injective
    rw [map_zsmul, baseK0OPolInt_self, smul_eq_mul, mul_one]
  conv_lhs => rw [hy]
  rw [map_zsmul, K0JZ_self hN, map_zsmul, EQK0Int.baseK0OsymInt_self, smul_eq_mul, mul_one, one_mul]

variable (N)

/-- **Definition 4.18 on half-graded modules**, rank `N ≤ 1` (over `ℤ`): `J_N = (Z_N^∨)ᵈ ⊗^L (-)`, the
derived tensor product with the diagonally regraded bimodule. -/
abbrev jZHalf :=
  Diagonal.derivedTensor (osymDG N) (OPol N) (RightDual (osymDG N) (Zn N)) (znDual_isKProjective N)

/-- The symbol of the half-graded `J_N` on `K₀` of compact objects. -/
def jZHalfK0Map :=
  Diagonal.derivedTensorK0 (osymDG N) (OPol N) (RightDual (osymDG N) (Zn N))
    (znDual_isKProjective N) isCompact_znDual

/-- The symbol `[J_N] : K₀(D(ONH_N)) → K₀(D(OΛ_N))` of the half-graded `J_N`, `ℤ[√−1]`-linear. -/
def jZHalfK0 : GZ N →ₗ[GaussianInt] K0nInt N := superK0cGaussianMap (jZHalfK0Map N)

variable {N}

/-- **Under `K₀ ≅ ℤ[√−1]`, `[J_N]` is the identity** (`N ≤ 1`). -/
theorem superK0OsymIntEquiv_jZHalfK0 (hN : N ≤ 1) (s : GZ N) :
    superK0OsymIntEquiv N (jZHalfK0 N s) = superK0OPolIntEquiv hN s := by
  have h := superK0GaussianOfBase_of_lTensor _ _ _ (K0JZ N) 1
    (fun s => Diagonal.superK0LinearEquiv_derivedTensor _ _ _ _ isCompact_znDual s)
    (baseK0OsymInt_K0JZ hN) s
  rw [Int.cast_one, one_mul] at h
  exact h

variable [∀ m n, HasDerivedCategory.{0, 0} (OPolT m n)]
  [∀ m n, CatModule.HasDerivedCategory.{0, 0} (WeightCategory (ofDGRing (OPolT m n)).Regraded)]
  [∀ n, CatModule.HasDerivedCategory.{0, 0} (WeightCategory (ofDGRing (ONH n)).Regraded)]

/-- The components of `[J]` over `ℤ`: `[J_N]` for `N ≤ 1`, `0` on `K₀(D(ONH_N)) = 0` for `N ≥ 2`. -/
def jK0IntComp : ∀ N, K0ONHInt N →ₗ[GaussianInt] K0nInt N
  | 0 => jZHalfK0 0
  | 1 => jZHalfK0 1
  | _ + 2 => 0

/-- **`[J] : K₀(D(ONH)) → K₀(D(OΛ))`** over `ℤ`, componentwise the symbol of `J_N` (Definition 4.18). -/
def jK0Int : K0ONHIntSum →ₗ[GaussianInt] K0OLamInt :=
  toModule GaussianInt ℕ K0OLamInt fun N => lof GaussianInt ℕ K0nInt N ∘ₗ jK0IntComp N

theorem jK0Int_lof_zero (s : K0ONHInt 0) :
    jK0Int (lof GaussianInt ℕ K0ONHInt 0 s) = lof GaussianInt ℕ K0nInt 0 (jZHalfK0 0 s) :=
  toModule_lof GaussianInt (0 : ℕ) s

theorem jK0Int_lof_one (s : K0ONHInt 1) :
    jK0Int (lof GaussianInt ℕ K0ONHInt 1 s) = lof GaussianInt ℕ K0nInt 1 (jZHalfK0 1 s) :=
  toModule_lof GaussianInt (1 : ℕ) s

theorem jZHalfK0_reg {N : ℕ} (hN : N ≤ 1) : jZHalfK0 N (regGZ N) = ePowClassInt N := by
  apply (superK0OsymIntEquiv N).injective
  rw [superK0OsymIntEquiv_jZHalfK0 hN, superK0OPolIntEquiv_self, EQK0Int.superK0OsymIntEquiv_ePowClassInt]
  have h : N.choose 2 = 0 := Nat.choose_eq_zero_of_lt (by omega)
  simp [h]

theorem jK0Int_one : jK0Int (thm_3_18_int_equiv 1) = thm_4_17_int_equiv (iota 1) :=
  calc jK0Int (thm_3_18_int_equiv 1) = jK0Int (lof GaussianInt ℕ K0ONHInt 0 (regONHInt 0)) :=
        congrArg _ thm_3_18_int_equiv_one
    _ = lof GaussianInt ℕ K0nInt 0 (jZHalfK0 0 (regONHInt 0)) := jK0Int_lof_zero _
    _ = lof GaussianInt ℕ K0nInt 0 (ePowClassInt 0) := congrArg _ (jZHalfK0_reg (Nat.zero_le 1))
    _ = thm_4_17_int_equiv (EQQuantum.DP.E evI 0) := (EQK0Int.thm_4_17_int_equiv_E 0).symm
    _ = thm_4_17_int_equiv (iota 1) := congrArg _ (map_one iota).symm

theorem jK0Int_eps :
    jK0Int (thm_3_18_int_equiv DualNumber.eps) = thm_4_17_int_equiv (iota DualNumber.eps) :=
  calc jK0Int (thm_3_18_int_equiv DualNumber.eps)
        = jK0Int (lof GaussianInt ℕ K0ONHInt 1 (regONHInt 1)) := congrArg _ thm_3_18_int_equiv_eps
    _ = lof GaussianInt ℕ K0nInt 1 (jZHalfK0 1 (regONHInt 1)) := jK0Int_lof_one _
    _ = lof GaussianInt ℕ K0nInt 1 (ePowClassInt 1) := congrArg _ (jZHalfK0_reg le_rfl)
    _ = thm_4_17_int_equiv (EQQuantum.DP.E evI 1) := (EQK0Int.thm_4_17_int_equiv_E 1).symm
    _ = thm_4_17_int_equiv (iota DualNumber.eps) := congrArg _ EQQuantum.iota_eps.symm

/-- **Ellis–Qi, Corollary 4.19 on `K₀`, over `ℤ`**: under Theorem 3.18 and Theorem 4.17, `[J]` is
`ι : u⁺ ↪ U⁺`, `E ↦ E^{(1)}`. -/
theorem cor_4_19_int_K0 (x : uPlus) : jK0Int (thm_3_18_int_equiv x) = thm_4_17_int_equiv (iota x) := by
  have hx := AssemblySmall.uPlus_decomp x
  calc jK0Int (thm_3_18_int_equiv x)
        = x.fst • jK0Int (thm_3_18_int_equiv 1) + x.snd • jK0Int (thm_3_18_int_equiv DualNumber.eps) := by
          conv_lhs => rw [hx]
          simp only [map_add, map_smul]
    _ = x.fst • thm_4_17_int_equiv (iota 1) + x.snd • thm_4_17_int_equiv (iota DualNumber.eps) := by
          simp only [jK0Int_one, jK0Int_eps]
    _ = thm_4_17_int_equiv (iota x) := by
          conv_rhs => rw [hx]
          simp only [map_add, map_smul]

/-- `[J]` is injective (`u⁺ ↪ U⁺`). -/
theorem cor_4_19_int_injective : Function.Injective jK0Int :=
  injective_of_iota jK0Int thm_3_18_int_equiv thm_4_17_int_equiv cor_4_19_int_K0

variable [∀ a b, DG.HasDerivedCategory.{0, 0} (EQFunctor.osymABDG a b)]
  [∀ a b, CatModule.HasDerivedCategory.{0, 0} (WeightCategory (ofDGRing (EQFunctor.osymABDG a b)).Regraded)]

/-- **Ellis–Qi, Corollary 4.19 on `K₀`, over `ℤ`, comultiplication**: `[R] ∘ [J] = ([J] ⊗ [J]) ∘ [Res]`. -/
theorem cor_4_19_int_comul (s : K0ONHIntSum) :
    comultK0OLamInt (jK0Int s) = TensorProduct.map jK0Int jK0Int (comultK0ONHInt s) :=
  comul_of_iota jK0Int thm_3_18_int_equiv thm_4_17_int_equiv cor_4_19_int_K0 comultK0ONHInt
    comultK0OLamInt thm_3_18_int_comul EQK0Int.thm_4_17_int_comul s

variable [∀ a b, CatModule.HasDerivedCategory.{0, 0} (SingleObj (EQFunctor.osymABDG a b))]

/-- **Ellis–Qi, Corollary 4.19 on `K₀`, over `ℤ`, multiplication**: `[J] ∘ [Ind] = [I] ∘ ([J] × [J])`. -/
theorem cor_4_19_int_mul (s t : K0ONHIntSum) :
    jK0Int (multK0ONHInt s t) = multK0OLamInt (jK0Int s) (jK0Int t) :=
  mul_of_iota jK0Int thm_3_18_int_equiv thm_4_17_int_equiv cor_4_19_int_K0 multK0ONHInt
    multK0OLamInt thm_3_18_int_mul EQK0Int.thm_4_17_int_mul s t

end Int

/-! ### `J_N` over a field -/

section Field

variable (K : Type) [Field K] (N : ℕ)

/-- `K ⊗_ℤ Z_N^∨` is K-projective as a left dg `K ⊗ OΛ_N`-module. -/
theorem znDualK_isKProjective :
    IsKProjective.{0} (ExtendScalars K (osymDG N)) (DegreeZeroRing K ⊗[ℤ] RightDual (osymDG N) (Zn N)) :=
  ExtendScalars.isKProjective_tensor (B := OPol N) K (znDual_isKProjective N)

variable [∀ N, CatModule.HasDerivedCategory.{0, 0} (SingleObj (ExtendScalars K (OPol N)))]
  [∀ N, CatModule.HasDerivedCategory.{0, 0} (SingleObj (ExtendScalars K (osymDG N)))]
  [∀ N, CatModule.HasDerivedCategory.{0, 0} (SingleObj (OPol N))]
  [∀ N, CatModule.HasDerivedCategory.{0, 0} (SingleObj (osymDG N))]
  [∀ N, DG.HasDerivedCategory.{0, 0} (OPol N)] [∀ N, DG.HasDerivedCategory.{0, 0} (osymDG N)]
  [∀ N, HasDerivedCategory.{0, 0} (ExtendScalars K (OPol N))]
  [∀ N, CatModule.HasDerivedCategory.{0, 0}
    (WeightCategory (HalfGradedDGRing.ofDGRing (ExtendScalars K (OPol N))).Regraded)]
  [∀ n, HasDerivedCategory.{0, 0} (ExtendScalars K (osymDG n))]
  [∀ n, CatModule.HasDerivedCategory.{0, 0}
    (WeightCategory (HalfGradedDGRing.ofDGRing (ExtendScalars K (osymDG n))).Regraded)]

/-- `K ⊗_ℤ Z_N^∨` is compact in `D(K ⊗ OΛ_N)`. -/
theorem isCompact_znDualK :
    IsCompact.{0} (DG.DerivedCategory.Q.obj
      ((ExtendScalars.baseChange K (osymDG N)).obj
        (DGModuleCat.of (osymDG N) (RightDual (osymDG N) (Zn N))))) :=
  ExtendScalars.isCompact_Q_baseChange_obj K (znDual_isKProjective N) isCompact_znDual

/-- **`J_N` over `K`**, `(K ⊗ Z_N^∨) ⊗^L_{K ⊗ OPol_N} (-)`. -/
abbrev jK : DG.DerivedCategory.{0, 0} (ExtendScalars K (OPol N)) ⥤
    DG.DerivedCategory.{0, 0} (ExtendScalars K (osymDG N)) :=
  DGBimodule.derivedTensor.{0, 0, 0, 0} (ExtendScalars K (osymDG N)) (ExtendScalars K (OPol N))
    (DegreeZeroRing K ⊗[ℤ] RightDual (osymDG N) (Zn N)) (znDualK_isKProjective K N)

/-- The symbol of `J_N` over `K` on `K₀` of compact objects. -/
def K0JK : DGRing.K0.{0, 0} (ExtendScalars K (OPol N)) →+ DGRing.K0.{0, 0} (ExtendScalars K (osymDG N)) :=
  DG.K0.mapCompact (jK K N) fun _ h => DGBimodule.isCompact_derivedTensor_obj _ (isCompact_znDualK K N) h

variable {N}

/-- `[J_N(K ⊗ OPol_N)] = [K ⊗ OΛ_N]` for `N ≤ 1`. -/
theorem K0JK_self (hN : N ≤ 1) :
    K0JK K N (DGRing.K0.self (ExtendScalars K (OPol N))) = DGRing.K0.self (ExtendScalars K (osymDG N)) := by
  rw [DGRing.K0.self, K0JK, DG.K0.mapCompact_mk]
  refine (ExtendScalars.K0_mk_derivedTensor_self K (znDual_isKProjective N) isCompact_znDual).trans ?_
  have e := DGBimodule.derivedTensorSelfIso (osymDG N) (OPol N) (RightDual (osymDG N) (Zn N))
    (znDual_isKProjective N)
  rw [mk_eq_of_iso' (P := compactSubcategory.{0} (DG.DerivedCategory.{0, 0} (osymDG N))) _ _
    (e ≪≫ DG.DerivedCategory.Q.mapIso (znDualDGEquiv hN).toDGModuleCatIso)]
  exact DGRing.K0.map_self _

/-- Under `K₀ ≅ ℤ`, the symbol of `J_N` over `K` is the identity, `N ≤ 1`. -/
theorem baseK0EquivInt_K0JK (hN : N ≤ 1) (y : DGRing.K0.{0, 0} (ExtendScalars K (OPol N))) :
    baseK0EquivInt K (isConnectedInt_dgSubring (osymDG N)) (K0JK K N y) =
      (1 : ℤ) * baseK0EquivInt K (isConnectedInt_opol N) y := by
  set eA := baseK0EquivInt K (isConnectedInt_opol N)
  have hy : y = eA y • DGRing.K0.self (ExtendScalars K (OPol N)) := by
    apply eA.injective
    rw [map_zsmul, baseK0EquivInt_self, smul_eq_mul, mul_one]
  conv_lhs => rw [hy]
  rw [map_zsmul, K0JK_self K hN, map_zsmul, baseK0EquivInt_self, smul_eq_mul, mul_one, one_mul]

variable (N)

/-- **Definition 4.18 on half-graded modules over `K`**, rank `N ≤ 1`: `(K ⊗ Z_N^∨)ᵈ ⊗^L (-)`. -/
abbrev jKHalf :=
  Diagonal.derivedTensor (ExtendScalars K (osymDG N)) (ExtendScalars K (OPol N))
    (DegreeZeroRing K ⊗[ℤ] RightDual (osymDG N) (Zn N)) (znDualK_isKProjective K N)

/-- The symbol of the half-graded `J_N` over `K` on `K₀` of compact objects. -/
def jKHalfK0Map :=
  Diagonal.derivedTensorK0 (ExtendScalars K (osymDG N)) (ExtendScalars K (OPol N))
    (DegreeZeroRing K ⊗[ℤ] RightDual (osymDG N) (Zn N)) (znDualK_isKProjective K N)
    (isCompact_znDualK K N)

/-- The symbol `[J_N] : K₀(D(ONH_N)) → K₀(D(OΛ_N))` over `K`, `ℤ[√−1]`-linear. -/
def jKHalfK0 : GK K N →ₗ[GaussianInt] K0n K N := superK0cGaussianMap (jKHalfK0Map K N)

variable {N}

/-- **Under `K₀ ≅ ℤ[√−1]`, `[J_N]` over `K` is the identity** (`N ≤ 1`). -/
theorem superK0OsymEquiv_jKHalfK0 (hN : N ≤ 1) (s : GK K N) :
    superK0OsymEquiv.{0} K N (jKHalfK0 K N s) = superK0OPolEquiv.{0} K N s := by
  have h := superK0GaussianOfBase_of_lTensor _ _ _ (K0JK K N) 1
    (fun s => Diagonal.superK0LinearEquiv_derivedTensor _ _ _ _ (isCompact_znDualK K N) s)
    (baseK0EquivInt_K0JK K hN) s
  rw [Int.cast_one, one_mul] at h
  exact h

variable [∀ m n, HasDerivedCategory.{0, 0} (ExtendScalars K (OPolT m n))]
  [∀ m n, CatModule.HasDerivedCategory.{0, 0}
    (WeightCategory (HalfGradedDGRing.ofDGRing (ExtendScalars K (OPolT m n))).Regraded)]
  [∀ n, HasDerivedCategory.{0, 0} (ExtendScalars K (ONH n))]
  [∀ n, CatModule.HasDerivedCategory.{0, 0}
    (WeightCategory (HalfGradedDGRing.ofDGRing (ExtendScalars K (ONH n))).Regraded)]

/-- The components of `[J]` over `K`. -/
def jK0Comp : ∀ N, K0ONH K N →ₗ[GaussianInt] K0n K N
  | 0 => jKHalfK0 K 0
  | 1 => jKHalfK0 K 1
  | _ + 2 => 0

/-- **`[J] : K₀(D(ONH)) → K₀(D(OΛ))`** over `K`, componentwise the symbol of `J_N`. -/
def jK0 : K0ONHSum K →ₗ[GaussianInt] K0OLam K :=
  toModule GaussianInt ℕ (K0OLam K) fun N => lof GaussianInt ℕ (K0n K) N ∘ₗ jK0Comp K N

theorem jK0_lof_zero (s : K0ONH K 0) :
    jK0 K (lof GaussianInt ℕ (K0ONH K) 0 s) = lof GaussianInt ℕ (K0n K) 0 (jKHalfK0 K 0 s) :=
  toModule_lof GaussianInt (0 : ℕ) s

theorem jK0_lof_one (s : K0ONH K 1) :
    jK0 K (lof GaussianInt ℕ (K0ONH K) 1 s) = lof GaussianInt ℕ (K0n K) 1 (jKHalfK0 K 1 s) :=
  toModule_lof GaussianInt (1 : ℕ) s

theorem jKHalfK0_reg {N : ℕ} (hN : N ≤ 1) : jKHalfK0 K N (regG K N) = ePowClass K N := by
  apply (superK0OsymEquiv.{0} K N).injective
  rw [superK0OsymEquiv_jKHalfK0 K hN, superK0OPolEquiv_self, superK0OsymEquiv_ePowClass]
  have h : N.choose 2 = 0 := Nat.choose_eq_zero_of_lt (by omega)
  simp [h]

theorem jK0_one : jK0 K (thm_3_18_equiv K 1) = thm_4_17_equiv K (iota 1) :=
  calc jK0 K (thm_3_18_equiv K 1) = jK0 K (lof GaussianInt ℕ (K0ONH K) 0 (regONH K 0)) :=
        congrArg _ (thm_3_18_equiv_one K)
    _ = lof GaussianInt ℕ (K0n K) 0 (jKHalfK0 K 0 (regONH K 0)) := jK0_lof_zero K _
    _ = lof GaussianInt ℕ (K0n K) 0 (ePowClass K 0) := congrArg _ (jKHalfK0_reg K (Nat.zero_le 1))
    _ = thm_4_17_equiv K (EQQuantum.DP.E evI 0) := (thm_4_17_equiv_E K 0).symm
    _ = thm_4_17_equiv K (iota 1) := congrArg _ (map_one iota).symm

theorem jK0_eps : jK0 K (thm_3_18_equiv K DualNumber.eps) = thm_4_17_equiv K (iota DualNumber.eps) :=
  calc jK0 K (thm_3_18_equiv K DualNumber.eps)
        = jK0 K (lof GaussianInt ℕ (K0ONH K) 1 (regONH K 1)) := congrArg _ (thm_3_18_equiv_eps K)
    _ = lof GaussianInt ℕ (K0n K) 1 (jKHalfK0 K 1 (regONH K 1)) := jK0_lof_one K _
    _ = lof GaussianInt ℕ (K0n K) 1 (ePowClass K 1) := congrArg _ (jKHalfK0_reg K le_rfl)
    _ = thm_4_17_equiv K (EQQuantum.DP.E evI 1) := (thm_4_17_equiv_E K 1).symm
    _ = thm_4_17_equiv K (iota DualNumber.eps) := congrArg _ EQQuantum.iota_eps.symm

/-- **Ellis–Qi, Corollary 4.19 on `K₀`** over a field `K`: under Theorem 3.18 and Theorem 4.17,
`[J]` is `ι : u⁺ ↪ U⁺`, `E ↦ E^{(1)}`. -/
theorem cor_4_19_K0 (x : uPlus) : jK0 K (thm_3_18_equiv K x) = thm_4_17_equiv K (iota x) := by
  have hx := AssemblySmall.uPlus_decomp x
  calc jK0 K (thm_3_18_equiv K x)
        = x.fst • jK0 K (thm_3_18_equiv K 1) + x.snd • jK0 K (thm_3_18_equiv K DualNumber.eps) := by
          conv_lhs => rw [hx]
          simp only [map_add, map_smul]
    _ = x.fst • thm_4_17_equiv K (iota 1) + x.snd • thm_4_17_equiv K (iota DualNumber.eps) := by
          simp only [jK0_one, jK0_eps]
    _ = thm_4_17_equiv K (iota x) := by
          conv_rhs => rw [hx]
          simp only [map_add, map_smul]

/-- `[J]` is injective over `K`. -/
theorem cor_4_19_injective : Function.Injective (jK0 K) :=
  injective_of_iota (jK0 K) (thm_3_18_equiv K) (thm_4_17_equiv K) (cor_4_19_K0 K)

variable [∀ a b, HasDerivedCategory.{0, 0} (ExtendScalars K (EQFunctor.osymABDG a b))]
  [∀ a b, CatModule.HasDerivedCategory.{0, 0}
    (WeightCategory (HalfGradedDGRing.ofDGRing (ExtendScalars K (EQFunctor.osymABDG a b))).Regraded)]

/-- **Ellis–Qi, Corollary 4.19 on `K₀` over `K`, comultiplication**: `[R] ∘ [J] = ([J] ⊗ [J]) ∘ [Res]`. -/
theorem cor_4_19_comul (s : K0ONHSum K) :
    comultK0OLam K (jK0 K s) = TensorProduct.map (jK0 K) (jK0 K) (comultK0ONH K s) :=
  comul_of_iota (jK0 K) (thm_3_18_equiv K) (thm_4_17_equiv K) (cor_4_19_K0 K) (comultK0ONH K)
    (comultK0OLam K) (thm_3_18_comul K) (thm_4_17_comul K) s

variable [∀ a b, CatModule.HasDerivedCategory.{0, 0} (SingleObj (ExtendScalars K (EQFunctor.osymABDG a b)))]
  [∀ a b, CatModule.HasDerivedCategory.{0, 0} (SingleObj (EQFunctor.osymABDG a b))]
  [∀ a b, DG.HasDerivedCategory.{0, 0} (EQFunctor.osymABDG a b)]

/-- **Ellis–Qi, Corollary 4.19 on `K₀` over `K`, multiplication**: `[J] ∘ [Ind] = [I] ∘ ([J] × [J])`. -/
theorem cor_4_19_mul (s t : K0ONHSum K) :
    jK0 K (multK0ONH K s t) = multK0OLam K (jK0 K s) (jK0 K t) :=
  mul_of_iota (jK0 K) (thm_3_18_equiv K) (thm_4_17_equiv K) (cor_4_19_K0 K) (multK0ONH K)
    (multK0OLam K) (thm_3_18_mul K) (thm_4_17_mul K) s t

end Field

end OddMath.Frontier.EQK0
