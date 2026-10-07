import DG.HalfGraded.DiagonalK0
import DG.HalfGraded.DiagonalInduction
import DG.HalfGraded.Field
import DG.Positive.ScalarExtension

/-!
# Super Grothendieck groups of diagonal half-graded dg rings equal to `ℤ[√−1]`

Let `A` be a dg ring and `H = ofDGRing A` its diagonal half-graded dg ring (an element of degree `k`
placed in bidegree `(2k, k mod 2)`). The compact super Grothendieck group `SuperK0c H` is a module over
`ℤ[√−1]`, with `√−1` acting by the internal shift `⟨1⟩` (`DG.HalfGradedDGRing.superK0cGaussianModule`),
and `SuperK0c H ≃ ℤ[q, q⁻¹]/(1 + q²) ⊗ K₀(D(A)^c)` (`DG.Diagonal.superK0LinearEquiv`).

* `superK0GaussianOfBase A e`: if `e : K₀(D(A)^c) ≃ ℤ`, then `SuperK0c H ≃ ℤ[√−1]` as
  `ℤ[√−1]`-modules, sending the class of the diagonal image `ι X` of a compact `X` to `e [X]`
  (`superK0GaussianOfBase_mk`); the internal shift `⟨n⟩` acts by `(√−1)ⁿ`
  (`superK0GaussianOfBase_internalShift`).
* `superK0GaussianOfConnected K A`: for a field `K` and a dg ring `A` connected over `ℤ`
  (`Aⁿ = 0` for `n < 0`, `A⁰ = ℤ · 1`, `1` of infinite additive order), the diagonal half-graded
  dg ring of the scalar extension `K ⊗ A` (`DG.ExtendScalars K A`) has
  `SuperK0c ≃ₗ[ℤ[√−1]] ℤ[√−1]`, with the class of the image of the regular module equal to `1`
  (`superK0GaussianOfConnected_self`).
* `superK0c_subsingleton_of_base`: if `K₀(D(A)^c) = 0` then `SuperK0c H = 0`.

This is the computation `K₀ ≅ ℤ[√−1]` used for the components of the Grothendieck groups in
Ellis–Qi, arXiv:1504.01712v2, Theorem 3.18 and Theorem 4.17 (the paper takes a field as ground ring
in §4.4); `OddMath.Frontier.EQK0Field` applies it to the odd symmetric and odd nilHecke dg rings.
-/

noncomputable section

open CategoryTheory LaurentPolynomial TensorProduct

universe w' w v u

namespace OddMath.Frontier.EQK0

open DG DG.HalfGradedDGRing

/-! ### The general reduction -/

section Base

variable (A : Type u) [Ring A] [DGAddCommGroup A] [DGRing A]
  [HasDerivedCategory.{w, max u v} A]
  [CatModule.HasDerivedCategory.{w', max u v} (WeightCategory (ofDGRing A).Regraded)]

/-- `ℤ[q, q⁻¹] ⧸ (1 + q²)`. -/
local notation "Q" => LaurentPolynomial ℤ ⧸ HalfGradedDGRing.superIdeal 2

/-- `SuperK0c (ofDGRing A) ≃ₗ[ℤ[q, q⁻¹]] ℤ[q, q⁻¹] ⧸ (1 + q²)`, given `K₀(D(A)^c) ≃ ℤ`. -/
def superK0QuotOfBase (e : Diagonal.BaseK0.{w, v} A ≃+ ℤ) :
    SuperK0c.{w', v} (ofDGRing A) ≃ₗ[LaurentPolynomial ℤ] Q :=
  (Diagonal.superK0LinearEquiv.{w', w, v} A).trans
    ((AlgebraTensorModule.congr (LinearEquiv.refl (LaurentPolynomial ℤ) Q)
      e.toIntLinearEquiv).trans (AlgebraTensorModule.rid ℤ (LaurentPolynomial ℤ) Q))

theorem superK0QuotOfBase_mk (e : Diagonal.BaseK0.{w, v} A ≃+ ℤ) (y : Diagonal.BaseK0.{w, v} A) :
    superK0QuotOfBase.{w', w, v} A e
        (superK0cMk.{w', v} _ (Diagonal.mapCompactK0.{w', w, max u v} A y)) =
      (e y : ℤ) • (Diagonal.πS 1) := by
  rw [superK0QuotOfBase, LinearEquiv.trans_apply,
    Diagonal.superK0LinearEquiv_superK0cMk_mapCompactK0, LinearEquiv.trans_apply,
    AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply, AlgebraTensorModule.rid_tmul]
  rfl

/-- **`SuperK0c (ofDGRing A) ≃ ℤ[√−1]`** as `ℤ[√−1]`-modules, given `K₀(D(A)^c) ≃ ℤ`. -/
def superK0GaussianOfBase (e : Diagonal.BaseK0.{w, v} A ≃+ ℤ) :
    SuperK0c.{w', v} (ofDGRing A) ≃ₗ[GaussianInt] GaussianInt where
  toAddEquiv := (superK0QuotOfBase.{w', w, v} A e).toAddEquiv.trans
    GaussianQuot.equivGaussianInt.toAddEquiv
  map_smul' z x := by
    obtain ⟨p, rfl⟩ := GaussianQuot.evalI_surjective z
    change GaussianQuot.equivGaussianInt (superK0QuotOfBase.{w', w, v} A e
        (GaussianQuot.evalI p • x)) =
      GaussianQuot.evalI p * GaussianQuot.equivGaussianInt (superK0QuotOfBase.{w', w, v} A e x)
    rw [superK0c_evalI_smul, LinearEquiv.map_smul]
    obtain ⟨q, hq⟩ := Ideal.Quotient.mk_surjective (superK0QuotOfBase.{w', w, v} A e x)
    rw [← hq]
    change GaussianQuot.equivGaussianInt (Ideal.Quotient.mk _ (p * q)) =
      GaussianQuot.evalI p * GaussianQuot.equivGaussianInt (Ideal.Quotient.mk _ q)
    rw [GaussianQuot.equivGaussianInt_mk, GaussianQuot.equivGaussianInt_mk, map_mul]

theorem superK0GaussianOfBase_apply (e : Diagonal.BaseK0.{w, v} A ≃+ ℤ)
    (x : SuperK0c.{w', v} (ofDGRing A)) :
    superK0GaussianOfBase.{w', w, v} A e x =
      GaussianQuot.equivGaussianInt (superK0QuotOfBase.{w', w, v} A e x) := rfl

/-- The class of the diagonal image of a compact object `X` is `e [X]`. -/
theorem superK0GaussianOfBase_mk (e : Diagonal.BaseK0.{w, v} A ≃+ ℤ)
    (y : Diagonal.BaseK0.{w, v} A) :
    superK0GaussianOfBase.{w', w, v} A e
        (superK0cMk.{w', v} _ (Diagonal.mapCompactK0.{w', w, max u v} A y)) = (e y : GaussianInt) := by
  rw [superK0GaussianOfBase_apply, superK0QuotOfBase_mk, map_zsmul]
  change (e y : ℤ) • GaussianQuot.evalI 1 = _
  rw [map_one, zsmul_eq_mul, mul_one]

/-- The internal shift `⟨n⟩` acts by `(√−1)ⁿ`. -/
theorem superK0GaussianOfBase_internalShift (e : Diagonal.BaseK0.{w, v} A ≃+ ℤ) (n : ℤ)
    (X : (compactSubcategory.{max u v}
      (CatModule.DerivedCategory.{w', max u v} (WeightCategory (ofDGRing A).Regraded))).FullSubcategory) :
    superK0GaussianOfBase.{w', w, v} A e
        (K0Rel.mk (((CatModule.DerivedCategory.compactInternalShiftAction
          (ofDGRing A).Regraded).functor n).obj X)) =
      ((GaussianQuot.unitI ^ n : GaussianIntˣ) : GaussianInt) *
        superK0GaussianOfBase.{w', w, v} A e (K0Rel.mk X) := by
  rw [← gaussian_zpow_smul_superK0c_mk, LinearEquiv.map_smul, smul_eq_mul]

/-- If `K₀(D(A)^c) = 0`, then `SuperK0c (ofDGRing A) = 0`. -/
theorem superK0c_subsingleton_of_base [Subsingleton (Diagonal.BaseK0.{w, v} A)] :
    Subsingleton (SuperK0c.{w', v} (ofDGRing A)) :=
  (Diagonal.superK0LinearEquiv.{w', w, v} A).toEquiv.subsingleton

end Base

/-! ### Tensor products of free rank-one `ℤ[√−1]`-modules -/

section Tensor

variable {M N P : Type*} [AddCommGroup M] [Module GaussianInt M] [AddCommGroup N]
  [Module GaussianInt N] [AddCommGroup P] [Module GaussianInt P]

/-- `M ⊗_{ℤ[√−1]} N ≃ P` for `M`, `N`, `P` free of rank one, given trivializations. -/
def tensorEquivOfGaussian (eM : M ≃ₗ[GaussianInt] GaussianInt) (eN : N ≃ₗ[GaussianInt] GaussianInt)
    (eP : P ≃ₗ[GaussianInt] GaussianInt) : M ⊗[GaussianInt] N ≃ₗ[GaussianInt] P :=
  (TensorProduct.congr eM eN).trans ((TensorProduct.lid GaussianInt GaussianInt).trans eP.symm)

theorem tensorEquivOfGaussian_tmul (eM : M ≃ₗ[GaussianInt] GaussianInt)
    (eN : N ≃ₗ[GaussianInt] GaussianInt) (eP : P ≃ₗ[GaussianInt] GaussianInt) {m : M} {n : N} {p : P}
    (hm : eM m = 1) (hn : eN n = 1) (hp : eP p = 1) :
    tensorEquivOfGaussian eM eN eP (m ⊗ₜ n) = p := by
  rw [tensorEquivOfGaussian, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    TensorProduct.congr_tmul, hm, hn, TensorProduct.lid_tmul, one_smul, LinearEquiv.symm_apply_eq,
    hp]

theorem apply_tensorEquivOfGaussian_tmul (eM : M ≃ₗ[GaussianInt] GaussianInt)
    (eN : N ≃ₗ[GaussianInt] GaussianInt) (eP : P ≃ₗ[GaussianInt] GaussianInt) (m : M) (n : N) :
    eP (tensorEquivOfGaussian eM eN eP (m ⊗ₜ n)) = eM m * eN n := by
  rw [tensorEquivOfGaussian, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply, TensorProduct.congr_tmul, TensorProduct.lid_tmul, smul_eq_mul]

end Tensor

/-! ### Morphisms of dg rings -/

section Morphism

variable {A B : Type u} [Ring A] [DGAddCommGroup A] [DGRing A] [HasDerivedCategory.{u, u} A]
  [Ring B] [DGAddCommGroup B] [DGRing B] [HasDerivedCategory.{u, u} B] (φ : A →ᵈᵍ+* B)

/-- A morphism of dg rings as a morphism of dg `ℤ`-algebras. -/
def intDGAlgHom : A →ᵈᵍₐ[ℤ] B where
  toAlgHom := φ.toRingHom.toIntAlgHom
  map_mem' ha := φ.map_mem ha
  map_d' a := φ.map_d a

omit [DGRing A] [HasDerivedCategory.{u, u} A] [DGRing B] [HasDerivedCategory.{u, u} B] in
@[simp]
theorem intDGAlgHom_apply (a : A) : intDGAlgHom φ a = φ a := rfl

/-- If `K₀(D(A)^c) ≃ ℤ` and `K₀(D(B)^c) ≃ ℤ` both send the regular class to `1`, then
`K₀(φ)` is the identity of `ℤ`. -/
theorem baseK0_map_eq (eA : Diagonal.BaseK0.{u, u} A ≃+ ℤ) (eB : Diagonal.BaseK0.{u, u} B ≃+ ℤ)
    (hA : eA (DGRing.K0.self A) = 1) (hB : eB (DGRing.K0.self B) = 1)
    (y : Diagonal.BaseK0.{u, u} A) : eB (DGRing.K0.map φ y) = eA y := by
  have hy : y = eA y • DGRing.K0.self A := by
    apply eA.injective
    rw [map_zsmul, hA, smul_eq_mul, mul_one]
  conv_lhs => rw [hy]
  rw [map_zsmul, map_zsmul, DGRing.K0.map_self, hB, smul_eq_mul, mul_one]

variable [CatModule.HasDerivedCategory.{u, u} (WeightCategory (ofDGRing A).Regraded)]
  [CatModule.HasDerivedCategory.{u, u} (WeightCategory (ofDGRing B).Regraded)]

/-- Derived induction along the morphism of diagonal half-graded dg rings induced by `φ` is the
identity of `ℤ[√−1]` under the trivializations, when `K₀(φ)` is the identity of `ℤ`. -/
theorem superK0GaussianOfBase_superK0cMap (eA : Diagonal.BaseK0.{u, u} A ≃+ ℤ)
    (eB : Diagonal.BaseK0.{u, u} B ≃+ ℤ) (h : ∀ y, eB (DGRing.K0.map φ y) = eA y)
    (s : SuperK0c.{u, u} (ofDGRing A)) :
    superK0GaussianOfBase.{u, u, u} B eB
        (superK0cMap _ _ (HalfGradedDGRing.Hom.ofDGRingHom φ).K0Map s) =
      superK0GaussianOfBase.{u, u, u} A eA s := by
  rw [superK0GaussianOfBase_apply, superK0GaussianOfBase_apply, superK0QuotOfBase,
    superK0QuotOfBase]
  simp only [LinearEquiv.trans_apply]
  rw [Diagonal.superK0LinearEquiv_superK0cMap_ofDGRingHom]
  congr 1
  generalize Diagonal.superK0LinearEquiv.{u, u, u} A s = t
  induction t using TensorProduct.inductionOn with
  | tmul p y =>
    rw [LinearMap.lTensor_tmul, AlgebraTensorModule.congr_tmul, AlgebraTensorModule.congr_tmul,
      AlgebraTensorModule.rid_tmul, AlgebraTensorModule.rid_tmul]
    exact congrArg (· • _) (h y)
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, map_add, map_add]

end Morphism

/-! ### Scalar extensions of dg rings connected over `ℤ` -/

section Connected

variable (K : Type u) [Field K] (A : Type u) [Ring A] [DGAddCommGroup A] [DGRing A]
  [HasDerivedCategory.{u, u} (ExtendScalars K A)]
  [CatModule.HasDerivedCategory.{w', u} (WeightCategory (ofDGRing (ExtendScalars K A)).Regraded)]

/-- A dg ring is *connected over `ℤ`* if it vanishes in negative degrees, its degree-`0` part is
`ℤ · 1`, and `1` has infinite additive order. -/
structure IsConnectedInt : Prop where
  grading_neg : ∀ n < 0, grading (M := A) n = ⊥
  grading_zero : ∀ a ∈ grading (M := A) 0, ∃ m : ℤ, (m : A) = a
  intCast_injective : ∀ m : ℤ, (m : A) = 0 → m = 0

variable {A}

/-- `K₀(D(K ⊗ A)^c) ≃ ℤ` with `[K ⊗ A] ↦ 1`, for `A` connected over `ℤ`
(`DG.ExtendScalars.K0EquivInt`). -/
def baseK0EquivInt (hA : IsConnectedInt A) : Diagonal.BaseK0.{u, u} (ExtendScalars K A) ≃+ ℤ :=
  letI := HasDerivedCategory.small.{u, u}
    (ExtendScalars.isPositive (K := K) hA.grading_neg hA.grading_zero).degreeZeroDGSubring
  ExtendScalars.K0EquivInt hA.grading_neg hA.grading_zero hA.intCast_injective

omit [CatModule.HasDerivedCategory.{w', u}
  (WeightCategory (ofDGRing (ExtendScalars K A)).Regraded)] in
theorem baseK0EquivInt_self (hA : IsConnectedInt A) :
    baseK0EquivInt K hA (DGRing.K0.self (ExtendScalars K A)) = 1 :=
  letI := HasDerivedCategory.small.{u, u}
    (ExtendScalars.isPositive (K := K) hA.grading_neg hA.grading_zero).degreeZeroDGSubring
  ExtendScalars.K0EquivInt_self hA.grading_neg hA.grading_zero hA.intCast_injective

/-- **`K₀ ≅ ℤ[√−1]`**: for a field `K` and a dg ring `A` connected over `ℤ`, the compact super
Grothendieck group of the diagonal half-graded dg ring of `K ⊗ A` is `ℤ[√−1]`, as a
`ℤ[√−1]`-module (`√−1` acting by the internal shift `⟨1⟩`). -/
def superK0GaussianOfConnected (hA : IsConnectedInt A) :
    SuperK0c.{w', u} (ofDGRing (ExtendScalars K A)) ≃ₗ[GaussianInt] GaussianInt :=
  superK0GaussianOfBase.{w', u, u} (ExtendScalars K A) (baseK0EquivInt K hA)

/-- The class of the diagonal image of the regular module `K ⊗ A` is `1`. -/
theorem superK0GaussianOfConnected_self (hA : IsConnectedInt A) :
    superK0GaussianOfConnected K hA
        (superK0cMk.{w', u} _ (Diagonal.mapCompactK0.{w', u, u} (ExtendScalars K A)
          (DGRing.K0.self (ExtendScalars K A)))) = 1 := by
  rw [superK0GaussianOfConnected, superK0GaussianOfBase_mk, baseK0EquivInt_self, Int.cast_one]

end Connected

end OddMath.Frontier.EQK0
