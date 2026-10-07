import OddMath.Frontier.EQFunctorDerived
import OddMath.Frontier.EQK0Coproduct
import OddMath.Frontier.EQQuantumBinomial
import DG.Positive.ScalarExtensionTensor
import DG.HalfGraded.DiagonalTransport

/-!
# The multiplication functor of Definition 4.14 over a field

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
§4.4, Definition 4.14 and the proof of Theorem 4.17 (printed numbering; §4.4 fixes a field `K`).

The dual bimodule `Z_{a,b}^∨` (`EQFunctor.ZDual a b`, a dg `(OΛ_{a+b}, OΛ_{a,b})`-bimodule, K-projective
and compact as a left dg `OΛ_{a+b}`-module by Corollary 4.11) is base changed to `K`
(`K ⊗_ℤ Z_{a,b}^∨`, a dg `(K ⊗ OΛ_{a+b}, K ⊗ OΛ_{a,b})`-bimodule, `DG.ExtendScalars.instDGBimodule`):

* `multK K a b = (K ⊗ Z_{a,b}^∨) ⊗^L_{K ⊗ OΛ_{a,b}} (-) : D(K ⊗ OΛ_{a,b}) → D(K ⊗ OΛ_{a+b})`,
  triangulated (`DG.DGBimodule.derivedTensor`) and preserving compact objects;
* `K0MultK K a b`, its symbol on `K₀`, and `K0MultK_self`:
  `[I_{a,b}(K ⊗ OΛ_{a,b})] = Σ_{μ ∈ Par(b,a)} (-1)^{|μ|} [K ⊗ OΛ_{a+b}]`, the base change of `K0Mult_self`;
* `baseK0EquivInt_K0MultK`: under `K₀(D(K ⊗ OΛ)) ≅ ℤ` (`EQK0.baseK0EquivInt`) the symbol is
  multiplication by `Σ_{μ ∈ Par(b,a)} (-1)^{|μ|}`.

On half-graded dg modules (the setting of Ellis–Qi §2.2.4 and Theorem 4.17) the multiplication functor
is dg-lean's diagonal transport of `multK` (`DG.Diagonal.transport`, acting by `multK` on the four
weight blocks, triangulated and commuting with the internal shift; `multKHalf`), and:

* `multK0 K a b : K₀(D(OΛ_a)) ⊗_{ℤ[√−1]} K₀(D(OΛ_b)) → K₀(D(OΛ_{a+b}))`, its symbol composed with the
  Künneth isomorphism of Lemma 4.16;
* `multK0_ePowClass`: **`E^{(a)} E^{(b)} = [a+b, a]_{q = √−1} E^{(a+b)}`**, equation (2.1), with
  `E^{(n)} = [OΛ_n⟨-binom(n,2)⟩]`.

The Künneth isomorphism of Lemma 4.16 is the one of the printed proof (`[OΛ_a] ⊗ [OΛ_b] ↦ [OΛ_{a,b}]`);
its agreement with the derived external tensor product is proved in the `ℤ`-graded setting
(`EQFunctor.K0MultBox`, from `DG.DerivedCategory.K0ExternalTensor`), not for half-graded modules.
-/

open CategoryTheory
open scoped TensorProduct

namespace OddMath.Frontier.EQK0

open DG
open OddMath.Frontier.EQSkewDifferential (osymDG totalDeg)
open OddMath.Frontier.EQFunctor (osymABDG ZDual zdual_isKProjective zdualFiniteCellFiltration)
open OddMath.Frontier.EQFix (ParIdx)

noncomputable section

/-- `[X] = [Y]` in `K₀` for isomorphic compact objects, with the objects given by the isomorphism. -/
theorem mk_eq_of_iso' {T : Type*} [Category T] [Limits.HasZeroObject T] [HasShift T ℤ]
    [Preadditive T] [∀ n : ℤ, (shiftFunctor T n).Additive] [Pretriangulated T]
    {P : ObjectProperty T} [P.IsTriangulated] {X Y : T} (hX : P X) (hY : P Y) (e : X ≅ Y) :
    DG.K0.mk (⟨X, hX⟩ : P.FullSubcategory) = DG.K0.mk (⟨Y, hY⟩ : P.FullSubcategory) :=
  DG.K0.mk_eq_of_iso_obj e

variable (K : Type) [Field K] (a b : ℕ)

/-- `K ⊗_ℤ Z_{a,b}^∨` is K-projective as a left dg `K ⊗ OΛ_{a+b}`-module. -/
theorem zdualK_isKProjective :
    IsKProjective.{0} (ExtendScalars K (osymDG (a+b))) (DegreeZeroRing K ⊗[ℤ] ZDual a b) :=
  ExtendScalars.isKProjective_tensor (B := osymABDG a b) K zdual_isKProjective

variable [CatModule.HasDerivedCategory.{0, 0} (SingleObj (ExtendScalars K (osymABDG a b)))]
  [CatModule.HasDerivedCategory.{0, 0} (SingleObj (ExtendScalars K (osymDG (a+b))))]
  [DG.HasDerivedCategory.{0, 0} (ExtendScalars K (osymABDG a b))]
  [DG.HasDerivedCategory.{0, 0} (ExtendScalars K (osymDG (a+b)))]

/-- **The multiplication functor over `K`**, `(K ⊗ Z_{a,b}^∨) ⊗^L_{K ⊗ OΛ_{a,b}} (-)`. -/
abbrev multK : DG.DerivedCategory.{0, 0} (ExtendScalars K (osymABDG a b)) ⥤
    DG.DerivedCategory.{0, 0} (ExtendScalars K (osymDG (a+b))) :=
  DGBimodule.derivedTensor.{0, 0, 0, 0} (ExtendScalars K (osymDG (a+b)))
    (ExtendScalars K (osymABDG a b)) (DegreeZeroRing K ⊗[ℤ] ZDual a b) (zdualK_isKProjective K a b)

variable [CatModule.HasDerivedCategory.{0, 0} (SingleObj (osymDG (a+b)))]
  [CatModule.HasDerivedCategory.{0, 0} (SingleObj (osymABDG a b))]
  [DG.HasDerivedCategory.{0, 0} (osymDG (a+b))] [DG.HasDerivedCategory.{0, 0} (osymABDG a b)]

omit [CatModule.HasDerivedCategory.{0, 0} (SingleObj (osymDG (a+b)))]
  [CatModule.HasDerivedCategory.{0, 0} (SingleObj (osymABDG a b))]
  [DG.HasDerivedCategory.{0, 0} (osymABDG a b)]
  [CatModule.HasDerivedCategory.{0, 0} (SingleObj (ExtendScalars K (osymABDG a b)))]
  [CatModule.HasDerivedCategory.{0, 0} (SingleObj (ExtendScalars K (osymDG (a+b))))]
  [DG.HasDerivedCategory.{0, 0} (ExtendScalars K (osymABDG a b))] in
/-- `K ⊗_ℤ Z_{a,b}^∨` is compact in `D(K ⊗ OΛ_{a+b})`. -/
theorem isCompact_zdualK :
    IsCompact.{0} (DG.DerivedCategory.Q.obj
      ((ExtendScalars.baseChange K (osymDG (a+b))).obj
        (DGModuleCat.of (osymDG (a+b)) (ZDual a b)))) :=
  ExtendScalars.isCompact_Q_baseChange_obj K zdual_isKProjective
    (zdualFiniteCellFiltration a b).isCompact_Q_obj

omit [CatModule.HasDerivedCategory.{0, 0} (SingleObj (osymDG (a+b)))]
  [CatModule.HasDerivedCategory.{0, 0} (SingleObj (osymABDG a b))]
  [DG.HasDerivedCategory.{0, 0} (osymABDG a b)] in
/-- `I_{a,b}` over `K` preserves compact objects. -/
theorem isCompact_multK_obj {X : DG.DerivedCategory.{0, 0} (ExtendScalars K (osymABDG a b))}
    (hX : IsCompact.{0} X) : IsCompact.{0} ((multK K a b).obj X) :=
  DGBimodule.isCompact_derivedTensor_obj _ (isCompact_zdualK K a b) hX

omit [CatModule.HasDerivedCategory.{0, 0} (SingleObj (osymDG (a+b)))]
  [CatModule.HasDerivedCategory.{0, 0} (SingleObj (osymABDG a b))]
  [DG.HasDerivedCategory.{0, 0} (osymABDG a b)] in
/-- The symbol `K₀(K ⊗ OΛ_{a,b}) → K₀(K ⊗ OΛ_{a+b})` of the multiplication functor over `K`. -/
def K0MultK : DGRing.K0.{0, 0} (ExtendScalars K (osymABDG a b)) →+
    DGRing.K0.{0, 0} (ExtendScalars K (osymDG (a+b))) :=
  DG.K0.mapCompact (multK K a b) fun _ h => isCompact_multK_obj K a b h

/-- **`[I_{a,b}(K ⊗ OΛ_{a,b})] = Σ_{μ ∈ Par(b,a)} (-1)^{|μ|} [K ⊗ OΛ_{a+b}]`** (Ellis–Qi, proof of
Theorem 4.17, `ℤ`-graded, over `K`). -/
theorem K0MultK_self :
    K0MultK K a b (DGRing.K0.self (ExtendScalars K (osymABDG a b))) =
      ∑ μ : ParIdx a b, (totalDeg μ.1).negOnePow •
        DGRing.K0.self (ExtendScalars K (osymDG (a+b))) := by
  rw [DGRing.K0.self, K0MultK, DG.K0.mapCompact_mk]
  refine (ExtendScalars.K0_mk_derivedTensor_self K zdual_isKProjective
    (zdualFiniteCellFiltration a b).isCompact_Q_obj).trans ?_
  have e := DGBimodule.derivedTensorSelfIso (osymDG (a+b)) (osymABDG a b) (ZDual a b)
    zdual_isKProjective
  have h2 := (mk_eq_of_iso' (P := compactSubcategory.{0} (DG.DerivedCategory.{0, 0} (osymDG (a+b))))
    ((zdualFiniteCellFiltration a b).isCompact_Q_obj.of_iso e)
    (zdualFiniteCellFiltration a b).isCompact_Q_obj e).trans (EQFunctor.K0_zdual a b)
  rw [h2, map_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Units.smul_def, Units.smul_def, map_zsmul, DGRing.K0.map_self]

/-- The integer `Σ_{μ ∈ Par(b,a)} (-1)^{|μ|}`. -/
def signSum : ℤ := ∑ μ : ParIdx a b, ((totalDeg μ.1).negOnePow : ℤ)

/-- Under `K₀(D(K ⊗ OΛ)) ≅ ℤ`, the symbol of `I_{a,b}` is multiplication by `signSum a b`. -/
theorem baseK0EquivInt_K0MultK (y : Diagonal.BaseK0.{0, 0} (ExtendScalars K (osymABDG a b))) :
    baseK0EquivInt K (isConnectedInt_dgSubring (osymDG (a+b))) (K0MultK K a b y) =
      signSum a b * baseK0EquivInt K (isConnectedInt_dgSubring (osymABDG a b)) y := by
  set eA := baseK0EquivInt K (isConnectedInt_dgSubring (osymABDG a b))
  set eB := baseK0EquivInt K (isConnectedInt_dgSubring (osymDG (a+b)))
  have hy : y = eA y • DGRing.K0.self (ExtendScalars K (osymABDG a b)) := by
    apply eA.injective
    rw [map_zsmul, baseK0EquivInt_self, smul_eq_mul, mul_one]
  conv_lhs => rw [hy]
  rw [map_zsmul, K0MultK_self, map_zsmul, map_sum, smul_eq_mul, mul_comm, signSum]
  congr 1
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Units.smul_def, map_zsmul, baseK0EquivInt_self, smul_eq_mul, mul_one]

end

/-! ### The multiplication on half-graded dg modules -/

noncomputable section

section HalfGraded

variable {A B : Type} [Ring A] [DGAddCommGroup A] [DGRing A] [DG.HasDerivedCategory.{0, 0} A]
  [CatModule.HasDerivedCategory.{0, 0} (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)]
  [Ring B] [DGAddCommGroup B] [DGRing B] [DG.HasDerivedCategory.{0, 0} B]
  [CatModule.HasDerivedCategory.{0, 0} (WeightCategory (HalfGradedDGRing.ofDGRing B).Regraded)]

/-- A map of compact super Grothendieck groups which is `id ⊗ g` under
`Diagonal.superK0LinearEquiv`, with `g` multiplication by `c` under trivializations
`K₀ ≃ ℤ`, is multiplication by `c` on `ℤ[√−1]`. -/
theorem superK0GaussianOfBase_of_lTensor (eA : Diagonal.BaseK0.{0, 0} A ≃+ ℤ)
    (eB : Diagonal.BaseK0.{0, 0} B ≃+ ℤ)
    (M : HalfGradedDGRing.SuperK0c.{0, 0} (HalfGradedDGRing.ofDGRing A) →
      HalfGradedDGRing.SuperK0c.{0, 0} (HalfGradedDGRing.ofDGRing B))
    (g : Diagonal.BaseK0.{0, 0} A →+ Diagonal.BaseK0.{0, 0} B) (c : ℤ)
    (hM : ∀ s, Diagonal.superK0LinearEquiv.{0, 0, 0} B (M s) =
      LinearMap.lTensor _ g.toIntLinearMap (Diagonal.superK0LinearEquiv.{0, 0, 0} A s))
    (hg : ∀ y, eB (g y) = c * eA y) (s : HalfGradedDGRing.SuperK0c.{0, 0} (HalfGradedDGRing.ofDGRing A)) :
    superK0GaussianOfBase.{0, 0, 0} B eB (M s) = c * superK0GaussianOfBase.{0, 0, 0} A eA s := by
  rw [superK0GaussianOfBase_apply, superK0GaussianOfBase_apply, superK0QuotOfBase,
    superK0QuotOfBase]
  simp only [LinearEquiv.trans_apply]
  rw [hM]
  have key : ∀ t, (TensorProduct.AlgebraTensorModule.rid ℤ (LaurentPolynomial ℤ) _)
      ((TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl (LaurentPolynomial ℤ)
        (LaurentPolynomial ℤ ⧸ HalfGradedDGRing.superIdeal 2)) eB.toIntLinearEquiv)
        (LinearMap.lTensor _ g.toIntLinearMap t)) =
      c • (TensorProduct.AlgebraTensorModule.rid ℤ (LaurentPolynomial ℤ) _)
        ((TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl (LaurentPolynomial ℤ)
          (LaurentPolynomial ℤ ⧸ HalfGradedDGRing.superIdeal 2)) eA.toIntLinearEquiv) t) := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul p y =>
      rw [LinearMap.lTensor_tmul, TensorProduct.AlgebraTensorModule.congr_tmul, TensorProduct.AlgebraTensorModule.congr_tmul,
        TensorProduct.AlgebraTensorModule.rid_tmul, TensorProduct.AlgebraTensorModule.rid_tmul, smul_smul]
      exact congrArg (· • _) (hg y)
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, map_add, map_add, smul_add]
  rw [key, map_zsmul, zsmul_eq_mul]

end HalfGraded

section HalfGradedMult

variable (K : Type) [Field K] (a b : ℕ)
  [CatModule.HasDerivedCategory.{0, 0} (SingleObj (ExtendScalars K (osymABDG a b)))]
  [CatModule.HasDerivedCategory.{0, 0} (SingleObj (ExtendScalars K (osymDG (a+b))))]
  [DG.HasDerivedCategory.{0, 0} (ExtendScalars K (osymABDG a b))]
  [DG.HasDerivedCategory.{0, 0} (ExtendScalars K (osymDG (a+b)))]
  [CatModule.HasDerivedCategory.{0, 0}
    (WeightCategory (HalfGradedDGRing.ofDGRing (ExtendScalars K (osymABDG a b))).Regraded)]
  [CatModule.HasDerivedCategory.{0, 0}
    (WeightCategory (HalfGradedDGRing.ofDGRing (ExtendScalars K (osymDG (a+b)))).Regraded)]
  [CatModule.HasDerivedCategory.{0, 0} (SingleObj (osymDG (a+b)))]
  [CatModule.HasDerivedCategory.{0, 0} (SingleObj (osymABDG a b))]
  [DG.HasDerivedCategory.{0, 0} (osymDG (a+b))] [DG.HasDerivedCategory.{0, 0} (osymABDG a b)]

/-- **The multiplication functor on half-graded dg modules** over `K`: the diagonal transport of
`multK K a b`. -/
abbrev multKHalf :=
  Diagonal.transport.{0, 0, 0, 0, 0, 0, 0, 0} (ExtendScalars K (osymABDG a b))
    (ExtendScalars K (osymDG (a+b))) (multK K a b)

/-- Its symbol on compact super Grothendieck groups. -/
def multKHalfK0 (s : HalfGradedDGRing.SuperK0c.{0, 0}
      (HalfGradedDGRing.ofDGRing (ExtendScalars K (osymABDG a b)))) :
    HalfGradedDGRing.SuperK0c.{0, 0} (HalfGradedDGRing.ofDGRing (ExtendScalars K (osymDG (a+b)))) :=
  HalfGradedDGRing.superK0cMap _ _
    (Diagonal.transportK0 _ _ (multK K a b) fun _ h => isCompact_multK_obj K a b h) s

/-- Under `K₀ ≅ ℤ[√−1]`, the symbol of the half-graded multiplication functor is multiplication by
`Σ_{μ ∈ Par(b,a)} (-1)^{|μ|}`. -/
theorem superK0OsymEquiv_multKHalfK0 (s : HalfGradedDGRing.SuperK0c.{0, 0}
      (HalfGradedDGRing.ofDGRing (ExtendScalars K (osymABDG a b)))) :
    superK0OsymEquiv.{0} K (a+b) (multKHalfK0 K a b s) =
      (signSum a b : GaussianInt) * superK0OsymABEquiv.{0} K a b s :=
  superK0GaussianOfBase_of_lTensor _ _ _ (K0MultK K a b) (signSum a b)
    (fun s => Diagonal.superK0LinearEquiv_transport _ _ (multK K a b) _ s)
    (baseK0EquivInt_K0MultK K a b) s

end HalfGradedMult

end

end OddMath.Frontier.EQK0

/-! ### Equation (2.1) on `K₀` -/

namespace OddMath.Frontier.EQK0

open DG
open OddMath.Frontier.EQSkewDifferential (osymDG totalDeg)
open OddMath.Frontier.EQFunctor (osymABDG)
open OddMath.Frontier.EQFix (ParIdx)
open OddMath.Frontier.QuantumSl2Plus (qBinom)
open LaurentPolynomial DG.HalfGradedDGRing

noncomputable section

theorem unitI_zpow_four_mul (m : ℤ) : (GaussianQuot.unitI ^ (4 * m) : GaussianIntˣ) = 1 := by
  have h4 : (GaussianQuot.unitI ^ (4 : ℤ) : GaussianIntˣ) = 1 := Units.ext (by decide)
  rw [zpow_mul, h4, one_zpow]

theorem unitI_zpow_add_four_mul (x m : ℤ) :
    (GaussianQuot.unitI ^ (x + 4 * m) : GaussianIntˣ) = GaussianQuot.unitI ^ x := by
  rw [zpow_add, unitI_zpow_four_mul, mul_one]

theorem negOnePow_cast_eq (k : ℤ) :
    ((k.negOnePow : ℤ) : GaussianInt) = ((GaussianQuot.unitI ^ (2 * k) : GaussianIntˣ) : GaussianInt) := by
  have h2 : ((GaussianQuot.unitI ^ (2 : ℤ) : GaussianIntˣ) : GaussianInt) = -1 := by decide
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
  · rw [Int.negOnePow_two_mul, show 2 * (2 * m) = 4 * m by ring, unitI_zpow_four_mul]
    rfl
  · rw [Int.negOnePow_two_mul_add_one, show 2 * (2 * m + 1) = 2 + 4 * m by ring,
      unitI_zpow_add_four_mul, h2]
    rfl

theorem evI_T_eq (n : ℤ) :
    EQQuantum.evI (T n) = ((GaussianQuot.unitI ^ n : GaussianIntˣ) : GaussianInt) := by
  have hu : EQQuantum.iiUnit = GaussianQuot.unitI := Units.ext rfl
  rw [EQQuantum.evI, eval₂_T, hu]

/-- `Σ_{μ ∈ Par(b,a)} (-1)^{|μ|} = Σ_{α} (√−1)^{2|α|}` over the box partitions. -/
theorem signSum_cast (a b : ℕ) :
    ((signSum a b : ℤ) : GaussianInt) = ∑ α ∈ BoxPartitionCount.box b a,
      ((GaussianQuot.unitI ^ (2 * ((∑ i, α i : ℕ) : ℤ)) : GaussianIntˣ) : GaussianInt) := by
  rw [signSum, Int.cast_sum]
  refine (Finset.sum_coe_sort (BoxPartitionCount.box b a) (fun α =>
    (((totalDeg α).negOnePow : ℤ) : GaussianInt))).trans (Finset.sum_congr rfl fun α _ => ?_)
  rw [negOnePow_cast_eq, totalDeg]
  push_cast
  rfl

theorem evI_qBinom_eq_sum (a b : ℕ) :
    EQQuantum.evI (qBinom a b) = ∑ α ∈ BoxPartitionCount.box b a,
      ((GaussianQuot.unitI ^ (2 * ((∑ i, α i : ℕ) : ℤ) - b * a) : GaussianIntˣ) : GaussianInt) := by
  rw [QuantumSl2Plus.qBinom_comm, QuantumSl2Plus.qBinom_eq_sum_box, map_sum]
  exact Finset.sum_congr rfl fun α _ => evI_T_eq _

/-- The scalar identity behind (2.1): `Σ_μ (-1)^{|μ|} · (√−1)^{-binom(a,2) - binom(b,2)} =
[a+b, a]_{√−1} · (√−1)^{-binom(a+b,2)}`. -/
theorem signSum_mul_unitI (a b : ℕ) :
    ((signSum a b : ℤ) : GaussianInt) *
        (((GaussianQuot.unitI ^ (-(a.choose 2 : ℤ)) : GaussianIntˣ) : GaussianInt) *
          ((GaussianQuot.unitI ^ (-(b.choose 2 : ℤ)) : GaussianIntˣ) : GaussianInt)) =
      EQQuantum.evI (qBinom a b) *
        ((GaussianQuot.unitI ^ (-((a + b).choose 2 : ℤ)) : GaussianIntˣ) : GaussianInt) := by
  by_cases hab : Odd a ∧ Odd b
  · have h0 := (EQQuantum.evI_qBinom_eq_zero_iff a b).mpr hab
    have hS : ((signSum a b : ℤ) : GaussianInt) = 0 := by
      rw [signSum_cast]
      have := congrArg (· * ((GaussianQuot.unitI ^ ((b * a : ℕ) : ℤ) : GaussianIntˣ) : GaussianInt))
        ((evI_qBinom_eq_sum a b).symm.trans h0)
      simp only [zero_mul, Finset.sum_mul, ← Units.val_mul, ← zpow_add] at this
      rw [← this]
      refine Finset.sum_congr rfl fun α _ => ?_
      congr 2
      push_cast
      ring
    rw [hS, h0, zero_mul, zero_mul]
  · have he : Even (a * b) := by
      rcases Nat.even_or_odd a with ha | ha
      · exact ha.mul_right b
      · rcases Nat.even_or_odd b with hb | hb
        · exact hb.mul_left a
        · exact absurd ⟨ha, hb⟩ hab
    obtain ⟨m, hm⟩ := he
    rw [signSum_cast, evI_qBinom_eq_sum, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [← Units.val_mul, ← Units.val_mul, ← Units.val_mul, ← zpow_add, ← zpow_add, ← zpow_add,
      choose_two_add]
    congr 1
    have hm' : ((a * b : ℕ) : ℤ) = 2 * (m : ℤ) := by rw [hm]; push_cast; ring
    rw [show 2 * ((∑ i, α i : ℕ) : ℤ) - (b : ℤ) * a +
        -((a.choose 2 + b.choose 2 + a * b : ℕ) : ℤ) =
        (2 * ((∑ i, α i : ℕ) : ℤ) + (-(a.choose 2 : ℤ) + -(b.choose 2 : ℤ))) + 4 * (-(m : ℤ)) by
      push_cast at hm' ⊢; linear_combination (-2 : ℤ) * hm']
    exact (unitI_zpow_add_four_mul _ _).symm

section Product

variable (K : Type) [Field K] (a b : ℕ)
  [HasDerivedCategory.{0, 0} (ExtendScalars K (osymDG a))]
  [CatModule.HasDerivedCategory.{0, 0}
    (WeightCategory (HalfGradedDGRing.ofDGRing (ExtendScalars K (osymDG a))).Regraded)]
  [HasDerivedCategory.{0, 0} (ExtendScalars K (osymDG b))]
  [CatModule.HasDerivedCategory.{0, 0}
    (WeightCategory (HalfGradedDGRing.ofDGRing (ExtendScalars K (osymDG b))).Regraded)]
  [CatModule.HasDerivedCategory.{0, 0} (SingleObj (ExtendScalars K (osymABDG a b)))]
  [CatModule.HasDerivedCategory.{0, 0} (SingleObj (ExtendScalars K (osymDG (a+b))))]
  [DG.HasDerivedCategory.{0, 0} (ExtendScalars K (osymABDG a b))]
  [DG.HasDerivedCategory.{0, 0} (ExtendScalars K (osymDG (a+b)))]
  [CatModule.HasDerivedCategory.{0, 0}
    (WeightCategory (HalfGradedDGRing.ofDGRing (ExtendScalars K (osymABDG a b))).Regraded)]
  [CatModule.HasDerivedCategory.{0, 0}
    (WeightCategory (HalfGradedDGRing.ofDGRing (ExtendScalars K (osymDG (a+b)))).Regraded)]
  [CatModule.HasDerivedCategory.{0, 0} (SingleObj (osymDG (a+b)))]
  [CatModule.HasDerivedCategory.{0, 0} (SingleObj (osymABDG a b))]
  [DG.HasDerivedCategory.{0, 0} (osymDG (a+b))] [DG.HasDerivedCategory.{0, 0} (osymABDG a b)]

/-- **The `(a, b)`-component of the multiplication `[I]`** (Ellis–Qi, Definition 4.14 and
Lemma 4.16): the Künneth isomorphism followed by the symbol of the half-graded multiplication
functor. -/
def multK0 (t : HalfGradedDGRing.SuperK0c.{0, 0} (HalfGradedDGRing.ofDGRing (ExtendScalars K (osymDG a)))
      ⊗[GaussianInt]
      HalfGradedDGRing.SuperK0c.{0, 0} (HalfGradedDGRing.ofDGRing (ExtendScalars K (osymDG b)))) :
    HalfGradedDGRing.SuperK0c.{0, 0} (HalfGradedDGRing.ofDGRing (ExtendScalars K (osymDG (a+b)))) :=
  multKHalfK0 K a b (lemma_4_16.{0} K a b t)

/-- **Theorem 4.17, multiplication**: `E^{(a)} E^{(b)} = [a+b, a]_{q = √−1} E^{(a+b)}` in
`K₀(D(OΛ))`, equation (2.1), with `E^{(n)} = [OΛ_n⟨-binom(n,2)⟩]` (`ePowClass`). -/
theorem multK0_ePowClass :
    multK0 K a b (ePowClass K a ⊗ₜ[GaussianInt] ePowClass K b) =
      EQQuantum.evI (qBinom a b) • ePowClass K (a+b) := by
  apply (superK0OsymEquiv.{0} K (a+b)).injective
  have h1 : superK0OsymABEquiv.{0} K a b (lemma_4_16.{0} K a b
      (ePowClass K a ⊗ₜ[GaussianInt] ePowClass K b)) =
      ((GaussianQuot.unitI ^ (-(a.choose 2 : ℤ)) : GaussianIntˣ) : GaussianInt) *
        ((GaussianQuot.unitI ^ (-(b.choose 2 : ℤ)) : GaussianIntˣ) : GaussianInt) :=
    (apply_tensorEquivOfGaussian_tmul _ _ _ _ _).trans
      (congrArg₂ (· * ·) (superK0OsymEquiv_ePowClass K a) (superK0OsymEquiv_ePowClass K b))
  have h2 : superK0OsymEquiv.{0} K (a+b) (EQQuantum.evI (qBinom a b) • ePowClass K (a+b)) =
      EQQuantum.evI (qBinom a b) *
        ((GaussianQuot.unitI ^ (-((a + b).choose 2 : ℤ)) : GaussianIntˣ) : GaussianInt) := by
    rw [LinearEquiv.map_smul, superK0OsymEquiv_ePowClass, smul_eq_mul]
  exact (superK0OsymEquiv_multKHalfK0 K a b _).trans
    ((congrArg (_ * ·) h1).trans ((signSum_mul_unitI a b).trans h2.symm))

end Product

end

end OddMath.Frontier.EQK0
