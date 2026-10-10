import OddMath.Frontier.EQThm318Int
import OddMath.Frontier.EQK0Int

/-!
# The Künneth isomorphism (3.44) over `ℤ` in bidegree `(1, 1)`

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
§3.6, the Künneth property (3.44) and Theorem 3.18.

`OddMath.Frontier.EQThm318Int` proves Theorem 3.18 over `ℤ` using the map
`kunnethMapInt 1 1 : K₀(D(ONH_1)) ⊗ K₀(D(ONH_1)) → K₀(D(ONH_1 ⊗ ONH_1))`,
`[ONH_1] ⊗ [ONH_1] ↦ [ONH_1 ⊗ ONH_1]`, without knowing whether it is an isomorphism over `ℤ`. It is:

* `OPol_1` has `Z¹ = 0` and `H² = 0` over `ℤ` (`opol_cocycle_one`, `opol_cocycle_two`, from
  `H(OPol_1) = ℤ · 1`, `EQSmallRankDG`), and its degree-`1` part is a finitely generated free abelian group;
* hence `OPol_1 ⊗ OPol_1` (`EQK0.OPolT 1 1`) has `Z¹ = 0` and torsion-free `H²` (dg-lean's
  `DG.ConnectedTensor`), and `K₀(D(OPol_1 ⊗ OPol_1)^c) ≃ ℤ`, `[OPol_1 ⊗ OPol_1] ↦ 1`
  (`baseK0OPolTOneOneInt`, dg-lean's `DG.DGRing.K0.equivIntOfIsConnectedInt`);
* `kunnethOneOneInt`: the Künneth isomorphism `K₀(D(ONH_1)) ⊗ K₀(D(ONH_1)) ≅ K₀(D(ONH_1 ⊗ ONH_1))`
  over `ℤ`, and `kunnethMapInt_one_one_eq`: it is `kunnethMapInt 1 1`.

Together with `kunnethInt` (`m + n ≤ 1`), the Künneth isomorphism (3.44) holds over `ℤ` in every
bidegree `(m, n)` with `m, n ≤ 1`, i.e. for all the `ONH_m ⊗ ONH_n` with nonzero `K₀`.
-/

noncomputable section

open CategoryTheory TensorProduct

namespace OddMath.Frontier.EQK0Int

open DG DG.HalfGradedDGRing
open OddMath.Frontier.EQK0
open OddMath.Frontier.EQSkewDifferential (OPol grading)

/-! ### Low-degree cohomology of `OPol_1` -/

theorem opol_cocycle_one {N : ℕ} (hN : N ≤ 1) :
    ∀ x ∈ DG.grading (M := OPol N) 1, DG.d x = 0 → x = 0 := by
  intro x hx hdx
  obtain ⟨y, hy, rfl⟩ := (DG.cohomology.mkOf_eq_zero_iff hx hdx).mp
    (EQSmallRankDG.cohomology_eq_zero_of_ne_zero hN one_ne_zero _)
  obtain ⟨m, rfl⟩ := (isConnectedInt_of (isConnectedInt_opol N)).exists_intCast y (by simpa using hy)
  exact DG.d_intCast m

theorem opol_cocycle_two {N : ℕ} (hN : N ≤ 1) :
    ∀ x ∈ DG.grading (M := OPol N) 2, DG.d x = 0 →
      ∃ y ∈ DG.grading (M := OPol N) 1, x = DG.d y := by
  intro x hx hdx
  obtain ⟨y, hy, rfl⟩ := (DG.cohomology.mkOf_eq_zero_iff hx hdx).mp
    (EQSmallRankDG.cohomology_eq_zero_of_ne_zero hN two_ne_zero _)
  exact ⟨y, by simpa using hy, rfl⟩

/-- The coefficients of the linear monomials in `OPol_N`. -/
def opolLinCoeff (N : ℕ) : DG.grading (M := OPol N) 1 →ₗ[ℤ] (Fin N → ℤ) where
  toFun x i := ((OPol.equiv N).symm (x : OPol N) : OddMath.SkewPolynomial.SkewPolynomial N)
    (Pi.single i 1)
  map_add' x y := by
    funext i
    simp only [AddMemClass.coe_add, map_add, Finsupp.add_apply, Pi.add_apply]
  map_smul' m x := by
    funext i
    change _ = m * _
    rw [show ((m • x : DG.grading (M := OPol N) 1) : OPol N) = m • (x : OPol N) from rfl,
      map_zsmul, Finsupp.smul_apply, smul_eq_mul]

theorem opolLinCoeff_injective (N : ℕ) : Function.Injective (opolLinCoeff N) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  have hgr : (OPol.equiv N).symm (x : OPol N) ∈ grading N 1 := x.2
  apply Subtype.ext
  apply (OPol.equiv N).symm.injective
  rw [show ((0 : DG.grading (M := OPol N) 1) : OPol N) = 0 from rfl, map_zero]
  ext e
  by_cases he : e ∈ ((OPol.equiv N).symm (x : OPol N) :
      OddMath.SkewPolynomial.SkewPolynomial N).support
  · obtain ⟨i, rfl⟩ := exists_eq_single_of_totalDeg_eq_one (hgr e he)
    exact congrFun hx i
  · rw [Finsupp.notMem_support_iff] at he
    exact he

instance (N : ℕ) : Module.Finite ℤ (DG.grading (M := OPol N) 1) :=
  Module.Finite.of_injective (opolLinCoeff N) (opolLinCoeff_injective N)

instance (N : ℕ) : Module.Free ℤ (DG.grading (M := OPol N) 1) := by
  have : NoZeroSMulDivisors ℤ (DG.grading (M := OPol N) 1) :=
    Function.Injective.noZeroSMulDivisors _ (opolLinCoeff_injective N) (map_zero _)
      (fun m x => map_zsmul _ m x)
  exact Module.free_of_finite_type_torsion_free'

/-! ### `OPol_1 ⊗ OPol_1` -/

theorem isConnectedInt_opolT (m n : ℕ) : DG.IsConnectedInt (OPolT m n) :=
  isConnectedInt_of (EQK0.isConnectedInt_opolT m n)

theorem opolT_cohomology_one (x : DG.cohomology (OPolT 1 1) 1) : x = 0 := by
  induction x using DG.cohomology.induction_on with
  | h z =>
    rw [show z = 0 from Subtype.ext (ConnectedTensor.cocycle_one_eq_zero
      (isConnectedInt_of (isConnectedInt_opol 1)) (isConnectedInt_of (isConnectedInt_opol 1))
      (opol_cocycle_one le_rfl) (opol_cocycle_one le_rfl) (DG.cocycles.mem_grading z)
      (DG.cocycles.d_eq_zero z)), map_zero]

theorem opolT_cohomology_two_torsionFree (m : ℤ) (hm : m ≠ 0)
    (x : DG.cohomology (OPolT 1 1) 2) (hx : m • x = 0) : x = 0 := by
  induction x using DG.cohomology.induction_on with
  | h z =>
    rw [← map_zsmul, DG.cohomology.mk_eq_zero_iff] at hx
    obtain ⟨w, hw, hdw⟩ := DG.mem_coboundaries.mp hx
    obtain ⟨c, hc, hzc⟩ := ConnectedTensor.exists_eq_d_of_zsmul_eq_d
      (isConnectedInt_of (isConnectedInt_opol 1)) (isConnectedInt_of (isConnectedInt_opol 1))
      (opol_cocycle_one le_rfl)
      (fun _ _ α hα hdα _ _ _ => opol_cocycle_two le_rfl α hα hdα)
      (fun _ _ β hβ hdβ _ _ _ => opol_cocycle_two le_rfl β hβ hdβ)
      (Module.Free.chooseBasis ℤ (DG.grading (M := OPol 1) 1)) hm
      (DG.cocycles.mem_grading z) (DG.cocycles.d_eq_zero z) (by simpa using hw) hdw.symm
    rw [DG.cohomology.mk_eq_zero_iff]
    exact DG.mem_coboundaries.mpr ⟨c, by simpa using hc, hzc.symm⟩

/-- **`K₀(D(OPol_1 ⊗ OPol_1)^c) ≃ ℤ`** over `ℤ`, `[OPol_1 ⊗ OPol_1] ↦ 1`. -/
def baseK0OPolTOneOneInt [DG.HasDerivedCategory.{0, 0} (OPolT 1 1)] :
    DGRing.K0.{0, 0} (OPolT 1 1) ≃+ ℤ :=
  DGRing.K0.equivIntOfIsConnectedInt (isConnectedInt_opolT 1 1) opolT_cohomology_one
    opolT_cohomology_two_torsionFree

theorem baseK0OPolTOneOneInt_self [DG.HasDerivedCategory.{0, 0} (OPolT 1 1)] :
    baseK0OPolTOneOneInt (DGRing.K0.self (OPolT 1 1)) = 1 :=
  DGRing.K0.equivIntOfIsConnectedInt_self _ _ _

variable [∀ N, DG.HasDerivedCategory.{0, 0} (OPol N)]
  [∀ N, CatModule.HasDerivedCategory.{0, 0} (WeightCategory (ofDGRing (OPol N)).Regraded)]
  [∀ m n, DG.HasDerivedCategory.{0, 0} (OPolT m n)]
  [∀ m n, CatModule.HasDerivedCategory.{0, 0} (WeightCategory (ofDGRing (OPolT m n)).Regraded)]

/-- `K₀(D(ONH_1 ⊗ ONH_1)) ≅ ℤ[√−1]` over `ℤ`, on the regular class. -/
def superK0OPolTOneOneIntEquiv : TZ 1 1 ≃ₗ[GaussianInt] GaussianInt :=
  superK0GaussianOfBase.{0, 0, 0} (OPolT 1 1) baseK0OPolTOneOneInt

omit [∀ N, DG.HasDerivedCategory.{0, 0} (OPol N)]
  [∀ N, CatModule.HasDerivedCategory.{0, 0} (WeightCategory (ofDGRing (OPol N)).Regraded)] in
theorem superK0OPolTOneOneIntEquiv_self : superK0OPolTOneOneIntEquiv (regTZ 1 1) = 1 := by
  rw [superK0OPolTOneOneIntEquiv, superK0GaussianOfBase_mk, baseK0OPolTOneOneInt_self, Int.cast_one]

/-- **The Künneth isomorphism (3.44) over `ℤ` in bidegree `(1, 1)`**:
`K₀(D(ONH_1)) ⊗_{ℤ[√−1]} K₀(D(ONH_1)) ≅ K₀(D(ONH_1 ⊗ ONH_1))`. -/
def kunnethOneOneInt : GZ 1 ⊗[GaussianInt] GZ 1 ≃ₗ[GaussianInt] TZ 1 1 :=
  tensorEquivOfGaussian (superK0OPolIntEquiv le_rfl) (superK0OPolIntEquiv le_rfl)
    superK0OPolTOneOneIntEquiv

theorem kunnethOneOneInt_reg : kunnethOneOneInt (regGZ 1 ⊗ₜ regGZ 1) = regTZ 1 1 :=
  tensorEquivOfGaussian_tmul _ _ _ (superK0OPolIntEquiv_self _) (superK0OPolIntEquiv_self _)
    superK0OPolTOneOneIntEquiv_self

/-- The map `kunnethMapInt 1 1` used for Theorem 3.18 over `ℤ` is the Künneth isomorphism. -/
theorem kunnethMapInt_one_one_eq :
    kunnethMapInt le_rfl le_rfl = (kunnethOneOneInt : GZ 1 ⊗[GaussianInt] GZ 1 →ₗ[GaussianInt] TZ 1 1) := by
  refine TensorProduct.ext' fun x y => ?_
  have hx : x = superK0OPolIntEquiv le_rfl x • regGZ 1 := by
    apply (superK0OPolIntEquiv le_rfl).injective
    rw [LinearEquiv.map_smul, superK0OPolIntEquiv_self, smul_eq_mul, mul_one]
  have hy : y = superK0OPolIntEquiv le_rfl y • regGZ 1 := by
    apply (superK0OPolIntEquiv le_rfl).injective
    rw [LinearEquiv.map_smul, superK0OPolIntEquiv_self, smul_eq_mul, mul_one]
  rw [hx, hy, TensorProduct.smul_tmul_smul, LinearMap.map_smul, LinearMap.map_smul,
    kunnethMapInt_reg, LinearEquiv.coe_coe, kunnethOneOneInt_reg]

theorem kunnethMapInt_one_one_bijective : Function.Bijective (kunnethMapInt le_rfl le_rfl) := by
  rw [kunnethMapInt_one_one_eq]
  exact kunnethOneOneInt.bijective

end OddMath.Frontier.EQK0Int
