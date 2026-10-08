import OddMath.Frontier.EQThm417
import OddMath.Frontier.EQK0Int

/-!
# Ellis–Qi Theorem 4.17 over `ℤ`

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2
(printed numbering): §4.4 and its footnote (everything works over `ℤ`), Definitions 4.14, 4.15,
Lemma 4.16 and Theorem 4.17. Conventions as in `OddMath.Frontier.EQThm417` (compact super
Grothendieck groups of half-graded dg modules, §2.2.4; twist `−1`, ERRATA [EQ] 1), but with the dg
rings `OΛ_n` and `OΛ_{a,b}` themselves, over `ℤ`, instead of their base changes to a field.

The only field-specific input of the proof over a field is `K₀(D(K ⊗ OΛ_n)^c) ≅ ℤ`, `[OΛ_n] ↦ 1`
(Corollary 2.6, which needs a semisimple degree-`0` part). Over `ℤ` it is
`EQK0Int.baseK0OsymInt` / `baseK0OsymABInt`, from the low-degree cohomology of `OΛ_n` and `OΛ_{a,b}`
(`H⁰ = ℤ`, `H¹ = 0`, `H²` torsion-free) and dg-lean's `DG.DGRing.K0.equivIntOfIsConnectedInt`. The
rest of the argument is unchanged:

* `superK0OsymIntEquiv n : K₀(D(OΛ_n)) ≃ ℤ[√−1]`, `[OΛ_n] ↦ 1`; the same for `OΛ_{a,b}`;
* `lemma_4_16_int`: Lemma 4.16 over `ℤ`;
* `comultK0Int_ePowClass`: `[R]_{a,b}(E^{(a+b)}) = (-√−1)^{ab} E^{(a)} ⊗ E^{(b)}`, `R_{a,b}` derived
  induction along `OΛ_{a+b} ⊆ OΛ_{a,b}` on half-graded modules;
* `multK0Int_ePowClass`: `E^{(a)} E^{(b)} = [a+b, a]_{√−1} E^{(a+b)}`, the multiplication functor
  `I_{a,b}` being `(Z_{a,b}^∨)ᵈ ⊗^L (-)` on half-graded modules (`DG.Diagonal.derivedTensor`);
* **Theorem 4.17 over `ℤ`**: `thm_4_17_int_equiv : U⁺ ≃ K₀(D(OΛ))` (`E^{(n)} ↦ [OΛ_n⟨-binom(n,2)⟩]`),
  `thm_4_17_int_mul`, `thm_4_17_int_comul`.
-/

noncomputable section

open CategoryTheory TensorProduct

namespace OddMath.Frontier.EQK0Int

open DG DG.HalfGradedDGRing
open OddMath.Frontier.EQK0
open OddMath.Frontier.EQSkewDifferential (osymDG totalDeg)
open OddMath.Frontier.EQFunctor (osymABDG inclDG ZDual zdual_isKProjective zdualFiniteCellFiltration)
open OddMath.Frontier.EQFix (ParIdx)
open OddMath.Frontier.QuantumSl2Plus (qBinom)
open OddMath.Frontier.EQQuantum (UPlus evI rU)

/-! ### `K₀ ≅ ℤ[√−1]` and Lemma 4.16 over `ℤ` -/

section Gaussian

variable (n : ℕ) [DG.HasDerivedCategory.{0, 0} (osymDG n)]
  [CatModule.HasDerivedCategory.{0, 0} (WeightCategory (ofDGRing (osymDG n)).Regraded)]

/-- **`K₀(D(OΛ_n)) ≅ ℤ[√−1]`** over `ℤ`, as `ℤ[√−1]`-modules. -/
def superK0OsymIntEquiv : SuperK0c.{0, 0} (ofDGRing (osymDG n)) ≃ₗ[GaussianInt] GaussianInt :=
  superK0GaussianOfBase.{0, 0, 0} (osymDG n) (baseK0OsymInt n)

/-- The class `[OΛ_n]` of the regular module. -/
abbrev regClassInt : SuperK0c.{0, 0} (ofDGRing (osymDG n)) :=
  superK0cMk.{0, 0} _ (Diagonal.mapCompactK0.{0, 0, 0} (osymDG n) (DGRing.K0.self (osymDG n)))

theorem superK0OsymIntEquiv_self : superK0OsymIntEquiv n (regClassInt n) = 1 := by
  rw [superK0OsymIntEquiv, superK0GaussianOfBase_mk, baseK0OsymInt_self, Int.cast_one]

/-- `E^{(n)} = [OΛ_n⟨-binom(n,2)⟩] = (√−1)^{-binom(n,2)} [OΛ_n]` over `ℤ`. -/
def ePowClassInt : SuperK0c.{0, 0} (ofDGRing (osymDG n)) :=
  ((GaussianQuot.unitI ^ (-(n.choose 2 : ℤ)) : GaussianIntˣ) : GaussianInt) • regClassInt n

theorem superK0OsymIntEquiv_ePowClassInt :
    superK0OsymIntEquiv n (ePowClassInt n) =
      ((GaussianQuot.unitI ^ (-(n.choose 2 : ℤ)) : GaussianIntˣ) : GaussianInt) := by
  rw [ePowClassInt, LinearEquiv.map_smul, superK0OsymIntEquiv_self, smul_eq_mul, mul_one]

end Gaussian

section GaussianAB

variable (a b : ℕ) [DG.HasDerivedCategory.{0, 0} (osymABDG a b)]
  [CatModule.HasDerivedCategory.{0, 0} (WeightCategory (ofDGRing (osymABDG a b)).Regraded)]

/-- `K₀(D(OΛ_{a,b})) ≅ ℤ[√−1]` over `ℤ`. -/
def superK0OsymABIntEquiv :
    SuperK0c.{0, 0} (ofDGRing (osymABDG a b)) ≃ₗ[GaussianInt] GaussianInt :=
  superK0GaussianOfBase.{0, 0, 0} (osymABDG a b) (baseK0OsymABInt a b)

variable [DG.HasDerivedCategory.{0, 0} (osymDG a)]
  [CatModule.HasDerivedCategory.{0, 0} (WeightCategory (ofDGRing (osymDG a)).Regraded)]
  [DG.HasDerivedCategory.{0, 0} (osymDG b)]
  [CatModule.HasDerivedCategory.{0, 0} (WeightCategory (ofDGRing (osymDG b)).Regraded)]

/-- **Lemma 4.16 over `ℤ`**: `K₀(D(OΛ_a)) ⊗_{ℤ[√−1]} K₀(D(OΛ_b)) ≅ K₀(D(OΛ_{a,b}))`,
`[OΛ_a] ⊗ [OΛ_b] ↦ [OΛ_{a,b}]` (`lemma_4_16_int_tmul_self`). -/
def lemma_4_16_int :
    SuperK0c.{0, 0} (ofDGRing (osymDG a)) ⊗[GaussianInt] SuperK0c.{0, 0} (ofDGRing (osymDG b))
      ≃ₗ[GaussianInt] SuperK0c.{0, 0} (ofDGRing (osymABDG a b)) :=
  tensorEquivOfGaussian (superK0OsymIntEquiv a) (superK0OsymIntEquiv b) (superK0OsymABIntEquiv a b)

theorem lemma_4_16_int_tmul_self :
    lemma_4_16_int a b (regClassInt a ⊗ₜ[GaussianInt] regClassInt b) =
      superK0cMk.{0, 0} _ (Diagonal.mapCompactK0.{0, 0, 0} (osymABDG a b)
        (DGRing.K0.self (osymABDG a b))) :=
  tensorEquivOfGaussian_tmul _ _ _ (superK0OsymIntEquiv_self a) (superK0OsymIntEquiv_self b)
    (by rw [superK0OsymABIntEquiv, superK0GaussianOfBase_mk, baseK0OsymABInt_self, Int.cast_one])

theorem superK0OsymABIntEquiv_lemma_4_16_int_ePow :
    superK0OsymABIntEquiv a b (lemma_4_16_int a b (ePowClassInt a ⊗ₜ[GaussianInt] ePowClassInt b)) =
      ((GaussianQuot.unitI ^ (-(a.choose 2 : ℤ)) : GaussianIntˣ) : GaussianInt) *
        ((GaussianQuot.unitI ^ (-(b.choose 2 : ℤ)) : GaussianIntˣ) : GaussianInt) :=
  (apply_tensorEquivOfGaussian_tmul _ _ _ _ _).trans
    (congrArg₂ (· * ·) (superK0OsymIntEquiv_ePowClassInt a) (superK0OsymIntEquiv_ePowClassInt b))

end GaussianAB

/-! ### The comultiplication over `ℤ` -/

section Comult

variable (a b : ℕ) [DG.HasDerivedCategory.{0, 0} (osymDG (a+b))]
  [CatModule.HasDerivedCategory.{0, 0} (WeightCategory (ofDGRing (osymDG (a+b))).Regraded)]
  [DG.HasDerivedCategory.{0, 0} (osymABDG a b)]
  [CatModule.HasDerivedCategory.{0, 0} (WeightCategory (ofDGRing (osymABDG a b)).Regraded)]

/-- The symbol of `R_{a,b}` (derived induction along `OΛ_{a+b} ⊆ OΛ_{a,b}`) on half-graded dg
modules over `ℤ` is the identity of `ℤ[√−1]`. -/
theorem superK0OsymABIntEquiv_comult (s : SuperK0c.{0, 0} (ofDGRing (osymDG (a+b)))) :
    superK0OsymABIntEquiv a b
        (superK0cMap _ _ (HalfGradedDGRing.Hom.ofDGRingHom (inclDG a b)).K0Map s) =
      superK0OsymIntEquiv (a+b) s :=
  superK0GaussianOfBase_superK0cMap _ _ _
    (baseK0_map_eq _ _ _ (baseK0OsymInt_self _) (baseK0OsymABInt_self a b)) s

variable [DG.HasDerivedCategory.{0, 0} (osymDG a)]
  [CatModule.HasDerivedCategory.{0, 0} (WeightCategory (ofDGRing (osymDG a)).Regraded)]
  [DG.HasDerivedCategory.{0, 0} (osymDG b)]
  [CatModule.HasDerivedCategory.{0, 0} (WeightCategory (ofDGRing (osymDG b)).Regraded)]

/-- **The `(a, b)`-component of `[R]` over `ℤ`**: the symbol of `R_{a,b}` followed by the inverse of
Lemma 4.16. -/
def comultK0Int (s : SuperK0c.{0, 0} (ofDGRing (osymDG (a+b)))) :
    SuperK0c.{0, 0} (ofDGRing (osymDG a)) ⊗[GaussianInt] SuperK0c.{0, 0} (ofDGRing (osymDG b)) :=
  (lemma_4_16_int a b).symm
    (superK0cMap _ _ (HalfGradedDGRing.Hom.ofDGRingHom (inclDG a b)).K0Map s)

/-- **`[R]_{a,b}(E^{(a+b)}) = (-√−1)^{ab} E^{(a)} ⊗ E^{(b)}`** over `ℤ`. -/
theorem comultK0Int_ePowClass :
    comultK0Int a b (ePowClassInt (a+b)) =
      ((-EQQuantum.ii) ^ (a * b) : GaussianInt) •
        (ePowClassInt a ⊗ₜ[GaussianInt] ePowClassInt b) := by
  have hL := (superK0OsymABIntEquiv_comult a b (ePowClassInt (a+b))).trans
    (superK0OsymIntEquiv_ePowClassInt (a+b))
  have hR : superK0OsymABIntEquiv a b (lemma_4_16_int a b
      (((-EQQuantum.ii) ^ (a * b) : GaussianInt) •
        (ePowClassInt a ⊗ₜ[GaussianInt] ePowClassInt b))) =
      ((-EQQuantum.ii) ^ (a * b) : GaussianInt) *
        (((GaussianQuot.unitI ^ (-(a.choose 2 : ℤ)) : GaussianIntˣ) : GaussianInt) *
          ((GaussianQuot.unitI ^ (-(b.choose 2 : ℤ)) : GaussianIntˣ) : GaussianInt)) := by
    rw [LinearEquiv.map_smul, LinearEquiv.map_smul, smul_eq_mul]
    exact congrArg (_ * ·) (superK0OsymABIntEquiv_lemma_4_16_int_ePow a b)
  refine (LinearEquiv.symm_apply_eq _).mpr ((superK0OsymABIntEquiv a b).injective ?_)
  refine hL.trans (Eq.trans ?_ hR.symm)
  rw [neg_ii_eq, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← Units.val_mul]
  congr 1
  rw [← zpow_natCast, ← zpow_neg_one, ← zpow_mul, ← zpow_add, ← zpow_add, choose_two_add]
  congr 1
  push_cast
  ring

end Comult

/-! ### The multiplication over `ℤ` -/

section Mult

variable (a b : ℕ)
  [CatModule.HasDerivedCategory.{0, 0} (SingleObj (osymDG (a+b)))]
  [CatModule.HasDerivedCategory.{0, 0} (SingleObj (osymABDG a b))]
  [DG.HasDerivedCategory.{0, 0} (osymDG (a+b))] [DG.HasDerivedCategory.{0, 0} (osymABDG a b)]

omit [CatModule.HasDerivedCategory.{0, 0} (SingleObj (osymDG (a+b)))]
  [CatModule.HasDerivedCategory.{0, 0} (SingleObj (osymABDG a b))]
  [DG.HasDerivedCategory.{0, 0} (osymABDG a b)] in
/-- `Z_{a,b}^∨` is compact in `D(OΛ_{a+b})` (Corollary 4.11). -/
theorem isCompact_zdual :
    IsCompact.{0} (DG.DerivedCategory.Q.obj (DGModuleCat.of (osymDG (a+b)) (ZDual a b))) :=
  (zdualFiniteCellFiltration a b).isCompact_Q_obj

/-- **The multiplication functor `I_{a,b}` over `ℤ`**, `Z_{a,b}^∨ ⊗^L_{OΛ_{a,b}} (-)`. -/
abbrev multZ : DG.DerivedCategory.{0, 0} (osymABDG a b) ⥤ DG.DerivedCategory.{0, 0} (osymDG (a+b)) :=
  DGBimodule.derivedTensor.{0, 0, 0, 0} (osymDG (a+b)) (osymABDG a b) (ZDual a b) zdual_isKProjective

/-- The symbol of `I_{a,b}` on `K₀` of compact objects. -/
def K0MultZ : DGRing.K0.{0, 0} (osymABDG a b) →+ DGRing.K0.{0, 0} (osymDG (a+b)) :=
  DG.K0.mapCompact (multZ a b) fun _ h =>
    DGBimodule.isCompact_derivedTensor_obj _ (isCompact_zdual a b) h

/-- `[I_{a,b}(OΛ_{a,b})] = Σ_{μ ∈ Par(b,a)} (-1)^{|μ|} [OΛ_{a+b}]`. -/
theorem K0MultZ_self :
    K0MultZ a b (DGRing.K0.self (osymABDG a b)) =
      ∑ μ : ParIdx a b, (totalDeg μ.1).negOnePow • DGRing.K0.self (osymDG (a+b)) := by
  rw [DGRing.K0.self, K0MultZ, DG.K0.mapCompact_mk]
  have e := DGBimodule.derivedTensorSelfIso (osymDG (a+b)) (osymABDG a b) (ZDual a b)
    zdual_isKProjective
  exact (mk_eq_of_iso' (P := compactSubcategory.{0} (DG.DerivedCategory.{0, 0} (osymDG (a+b))))
    ((isCompact_zdual a b).of_iso e) (isCompact_zdual a b) e).trans (EQFunctor.K0_zdual a b)

/-- Under `K₀ ≅ ℤ`, the symbol of `I_{a,b}` is multiplication by `signSum a b`. -/
theorem baseK0OsymInt_K0MultZ (y : DGRing.K0.{0, 0} (osymABDG a b)) :
    baseK0OsymInt (a+b) (K0MultZ a b y) = signSum a b * baseK0OsymABInt a b y := by
  set eA := baseK0OsymABInt a b
  set eB := baseK0OsymInt (a+b)
  have hy : y = eA y • DGRing.K0.self (osymABDG a b) := by
    apply eA.injective
    rw [map_zsmul, baseK0OsymABInt_self, smul_eq_mul, mul_one]
  conv_lhs => rw [hy]
  rw [map_zsmul, K0MultZ_self, map_zsmul, map_sum, smul_eq_mul, mul_comm, signSum]
  congr 1
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Units.smul_def, map_zsmul, baseK0OsymInt_self, smul_eq_mul, mul_one]

variable [CatModule.HasDerivedCategory.{0, 0} (WeightCategory (ofDGRing (osymDG (a+b))).Regraded)]
  [CatModule.HasDerivedCategory.{0, 0} (WeightCategory (ofDGRing (osymABDG a b)).Regraded)]

/-- **The multiplication functor on half-graded dg modules over `ℤ`**: `(Z_{a,b}^∨)ᵈ ⊗^L (-)`. -/
abbrev multZHalf :=
  Diagonal.derivedTensor (osymDG (a+b)) (osymABDG a b) (ZDual a b) zdual_isKProjective

/-- Its symbol on `K₀` of compact objects. -/
def multZHalfK0Map :=
  Diagonal.derivedTensorK0 (osymDG (a+b)) (osymABDG a b) (ZDual a b) zdual_isKProjective
    (isCompact_zdual a b)

/-- Under `K₀ ≅ ℤ[√−1]`, the symbol of the half-graded multiplication functor is multiplication by
`Σ_{μ ∈ Par(b,a)} (-1)^{|μ|}`. -/
theorem superK0OsymIntEquiv_multZHalf (s : SuperK0c.{0, 0} (ofDGRing (osymABDG a b))) :
    superK0OsymIntEquiv (a+b) (superK0cMap _ _ (multZHalfK0Map a b) s) =
      (signSum a b : GaussianInt) * superK0OsymABIntEquiv a b s :=
  superK0GaussianOfBase_of_lTensor _ _ _ (K0MultZ a b) (signSum a b)
    (fun s => Diagonal.superK0LinearEquiv_derivedTensor _ _ _ _ (isCompact_zdual a b) s)
    (baseK0OsymInt_K0MultZ a b) s

variable [DG.HasDerivedCategory.{0, 0} (osymDG a)]
  [CatModule.HasDerivedCategory.{0, 0} (WeightCategory (ofDGRing (osymDG a)).Regraded)]
  [DG.HasDerivedCategory.{0, 0} (osymDG b)]
  [CatModule.HasDerivedCategory.{0, 0} (WeightCategory (ofDGRing (osymDG b)).Regraded)]

/-- **The `(a, b)`-component of `[I]` over `ℤ`**: Lemma 4.16 followed by the symbol of the
half-graded multiplication functor. -/
def multK0Int (t : SuperK0c.{0, 0} (ofDGRing (osymDG a)) ⊗[GaussianInt]
      SuperK0c.{0, 0} (ofDGRing (osymDG b))) :
    SuperK0c.{0, 0} (ofDGRing (osymDG (a+b))) :=
  superK0cMap _ _ (multZHalfK0Map a b) (lemma_4_16_int a b t)

/-- **`E^{(a)} E^{(b)} = [a+b, a]_{√−1} E^{(a+b)}`** over `ℤ`, equation (2.1). -/
theorem multK0Int_ePowClass :
    multK0Int a b (ePowClassInt a ⊗ₜ[GaussianInt] ePowClassInt b) =
      EQQuantum.evI (qBinom a b) • ePowClassInt (a+b) := by
  apply (superK0OsymIntEquiv (a+b)).injective
  have h2 : superK0OsymIntEquiv (a+b) (EQQuantum.evI (qBinom a b) • ePowClassInt (a+b)) =
      EQQuantum.evI (qBinom a b) *
        ((GaussianQuot.unitI ^ (-((a + b).choose 2 : ℤ)) : GaussianIntˣ) : GaussianInt) := by
    rw [LinearEquiv.map_smul, superK0OsymIntEquiv_ePowClassInt, smul_eq_mul]
  exact (superK0OsymIntEquiv_multZHalf a b _).trans
    ((congrArg (_ * ·) (superK0OsymABIntEquiv_lemma_4_16_int_ePow a b)).trans
      ((signSum_mul_unitI a b).trans h2.symm))

end Mult

/-! ### Theorem 4.17 over `ℤ` -/

open DirectSum

variable [∀ n, DG.HasDerivedCategory.{0, 0} (osymDG n)]
  [∀ n, CatModule.HasDerivedCategory.{0, 0} (WeightCategory (ofDGRing (osymDG n)).Regraded)]

/-- `K₀(D(OΛ_n))` over `ℤ`. -/
abbrev K0nInt (n : ℕ) : Type 1 := SuperK0c.{0, 0} (ofDGRing (osymDG n))

/-- **`K₀(D(OΛ)) = ⨁_n K₀(D(OΛ_n))`** over `ℤ`. -/
abbrev K0OLamInt : Type 1 := ⨁ n, K0nInt n

/-- **Theorem 4.17 over `ℤ`, the isomorphism** `U⁺ ≅ K₀(D(OΛ))` of `ℤ[√−1]`-modules,
`E^{(n)} ↦ [OΛ_n⟨-binom(n,2)⟩]`. -/
def thm_4_17_int_equiv : UPlus ≃ₗ[GaussianInt] K0OLamInt :=
  Assembly.equiv (fun n => superK0OsymIntEquiv n) (fun n => ePowClassInt n)
    (fun n => superK0OsymIntEquiv_ePowClassInt n)

theorem thm_4_17_int_equiv_E (n : ℕ) :
    thm_4_17_int_equiv (EQQuantum.DP.E evI n) = lof GaussianInt ℕ K0nInt n (ePowClassInt n) :=
  Assembly.equiv_E _ _ _ n

section Comultiplication

variable [∀ a b, DG.HasDerivedCategory.{0, 0} (osymABDG a b)]
  [∀ a b, CatModule.HasDerivedCategory.{0, 0} (WeightCategory (ofDGRing (osymABDG a b)).Regraded)]

/-- The `(a, b)`-component of `[R]` on `K₀(D(OΛ_n))`, `n = a + b`, over `ℤ`. -/
def comultK0IntLin (a b n : ℕ) (h : a + b = n) :
    K0nInt n →ₗ[GaussianInt] K0nInt a ⊗[GaussianInt] K0nInt b := by
  subst h
  exact (lemma_4_16_int a b).symm.toLinearMap ∘ₗ
    superK0cGaussianMap (HalfGradedDGRing.Hom.ofDGRingHom (inclDG a b)).K0Map

/-- **The comultiplication `[R]` on `K₀(D(OΛ))` over `ℤ`**. -/
def comultK0OLamInt : K0OLamInt →ₗ[GaussianInt] K0OLamInt ⊗[GaussianInt] K0OLamInt :=
  Assembly.comulMap comultK0IntLin

/-- **Theorem 4.17 over `ℤ`, comultiplication**: `[R](φ x) = (φ ⊗ φ)(r x)`. -/
theorem thm_4_17_int_comul (x : UPlus) :
    comultK0OLamInt (thm_4_17_int_equiv x) =
      TensorProduct.map thm_4_17_int_equiv.toLinearMap thm_4_17_int_equiv.toLinearMap
        (EQQuantum.TT.tensorEquiv evI (-1) (rU x)) :=
  Assembly.equiv_comul _ _ _ comultK0IntLin
    (fun a b n h => by subst h; exact comultK0Int_ePowClass a b) x

section Multiplication

variable [∀ n, CatModule.HasDerivedCategory.{0, 0} (SingleObj (osymDG n))]
  [∀ a b, CatModule.HasDerivedCategory.{0, 0} (SingleObj (osymABDG a b))]

/-- The `(a, b)`-component of `[I]` over `ℤ`, as a `ℤ[√−1]`-linear map. -/
def multK0IntLin (a b : ℕ) : K0nInt a ⊗[GaussianInt] K0nInt b →ₗ[GaussianInt] K0nInt (a+b) :=
  superK0cGaussianMap (multZHalfK0Map a b) ∘ₗ (lemma_4_16_int a b).toLinearMap

/-- **The multiplication `[I]` on `K₀(D(OΛ))` over `ℤ`**. -/
def multK0OLamInt : K0OLamInt →ₗ[GaussianInt] K0OLamInt →ₗ[GaussianInt] K0OLamInt :=
  Assembly.mulMap multK0IntLin

/-- **Theorem 4.17 over `ℤ`, multiplication**: `φ(x y) = [I](φ x, φ y)`. -/
theorem thm_4_17_int_mul (x y : UPlus) :
    thm_4_17_int_equiv (x * y) = multK0OLamInt (thm_4_17_int_equiv x) (thm_4_17_int_equiv y) :=
  Assembly.equiv_mul _ _ _ multK0IntLin (fun a b => multK0Int_ePowClass a b) x y

end Multiplication

end Comultiplication

end OddMath.Frontier.EQK0Int
