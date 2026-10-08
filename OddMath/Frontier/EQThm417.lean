import OddMath.Frontier.EQK0Mult
import OddMath.Frontier.EQK0Assembly

/-!
# Ellis–Qi Theorem 4.17: `K₀(D(OΛ)) ≅ U⁺` as twisted bialgebras

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2
(printed numbering): §2.1, §4.4, Definitions 4.14, 4.15, Lemma 4.16 and Theorem 4.17. Ellis–Qi fix a
field `K` in §4.4; the conventions are those recorded in the repository: `K₀` of the half-graded
derived category is the compact super Grothendieck group (classes up to isomorphisms of either
parity, §2.2.4), a `ℤ[√−1]`-module with `√−1` acting by the internal shift `⟨1⟩`, and the twisted
product on `U⁺ ⊗ U⁺` has twist `−1` (ERRATA [EQ] 1).

* `K0OLam K = ⨁_n K₀(D(OΛ_n))` (`D(OΛ_n)`: half-graded dg modules over `K ⊗ OΛ_n`).
* `thm_4_17_equiv K : U⁺ ≃ₗ[ℤ[√−1]] K₀(D(OΛ))`, `E^{(n)} ↦ [OΛ_n⟨-binom(n,2)⟩]`
  (`thm_4_17_equiv_E`).
* `multK0OLam K`: the multiplication `[I]` on `K₀(D(OΛ))`, componentwise the Künneth isomorphism of
  Lemma 4.16 followed by the symbol of the multiplication functor `I_{a,b}` (`EQK0.multK0`);
  `thm_4_17_mul`: `φ(x y) = [I](φ x, φ y)`.
* `comultK0OLam K`: the comultiplication `[R]`, componentwise the symbol of `R_{a,b}` followed by
  the inverse of Lemma 4.16 (`EQK0.comultK0`); `thm_4_17_comul`: `[R](φ x) = (φ ⊗ φ)(r x)`, with
  `r = EQQuantum.rU` the coproduct (2.2) for the twist `−1`, viewed in `U⁺ ⊗ U⁺`
  (`EQQuantum.TT.tensorEquiv`).

Since `U⁺` with `r` is a twisted bialgebra (`EQQuantum.rU` is an algebra map for the twist-`−1`
product), so is `K₀(D(OΛ))` with `[I]` and `[R]`, and `thm_4_17_equiv` is an isomorphism of twisted
bialgebras. The derived categories of the dg rings are arbitrary chosen models (instance arguments).
-/

noncomputable section

open CategoryTheory TensorProduct Finset

namespace OddMath.Frontier.EQK0

open DG DG.HalfGradedDGRing
open OddMath.Frontier.EQSkewDifferential (osymDG)
open OddMath.Frontier.EQFunctor (osymABDG)
open OddMath.Frontier.QuantumSl2Plus (qBinom)
open OddMath.Frontier.EQQuantum (UPlus evI rU)
open DirectSum

variable (K : Type) [Field K]
  [∀ n, HasDerivedCategory.{0, 0} (ExtendScalars K (osymDG n))]
  [∀ n, CatModule.HasDerivedCategory.{0, 0}
    (WeightCategory (HalfGradedDGRing.ofDGRing (ExtendScalars K (osymDG n))).Regraded)]

/-- `K₀(D(OΛ_n))`. -/
abbrev K0n (n : ℕ) : Type 1 :=
  HalfGradedDGRing.SuperK0c.{0, 0} (HalfGradedDGRing.ofDGRing (ExtendScalars K (osymDG n)))

/-- **`K₀(D(OΛ)) = ⨁_n K₀(D(OΛ_n))`**. -/
abbrev K0OLam : Type 1 := ⨁ n, K0n K n

/-! ### Theorem 4.17 -/

/-- **Theorem 4.17, the isomorphism** `U⁺ ≅ K₀(D(OΛ))` of `ℤ[√−1]`-modules,
`E^{(n)} ↦ [OΛ_n⟨-binom(n,2)⟩]` (`thm_4_17_equiv_E`). -/
def thm_4_17_equiv : UPlus ≃ₗ[GaussianInt] K0OLam K :=
  Assembly.equiv (fun n => superK0OsymEquiv.{0} K n) (fun n => ePowClass K n)
    (fun n => superK0OsymEquiv_ePowClass K n)

theorem thm_4_17_equiv_E (n : ℕ) :
    thm_4_17_equiv K (EQQuantum.DP.E evI n) = lof GaussianInt ℕ (K0n K) n (ePowClass K n) :=
  Assembly.equiv_E _ _ _ n

/-! ### `ℤ[√−1]`-linear symbols -/

/-- A Laurent-linear map of compact Grothendieck groups induces a `ℤ[√−1]`-linear map of compact
super Grothendieck groups. -/
def superK0cGaussianMap {A B : Type} [Ring A] [DGAddCommGroup A] [DGRing A]
    [CatModule.HasDerivedCategory.{0, 0} (WeightCategory (HalfGradedDGRing.ofDGRing A).Regraded)]
    [Ring B] [DGAddCommGroup B] [DGRing B]
    [CatModule.HasDerivedCategory.{0, 0} (WeightCategory (HalfGradedDGRing.ofDGRing B).Regraded)]
    (f : CompactK0.{0, 0} (HalfGradedDGRing.ofDGRing A) →ₗ[LaurentPolynomial ℤ]
      CompactK0.{0, 0} (HalfGradedDGRing.ofDGRing B)) :
    SuperK0c.{0, 0} (HalfGradedDGRing.ofDGRing A) →ₗ[GaussianInt]
      SuperK0c.{0, 0} (HalfGradedDGRing.ofDGRing B) where
  toFun := superK0cMap _ _ f
  map_add' := map_add _
  map_smul' z x := (superK0cQuotientMap _ _ f).map_smul (GaussianQuot.equivGaussianInt.symm z) x

section Comultiplication

variable [∀ a b, HasDerivedCategory.{0, 0} (ExtendScalars K (osymABDG a b))]
  [∀ a b, CatModule.HasDerivedCategory.{0, 0}
    (WeightCategory (HalfGradedDGRing.ofDGRing (ExtendScalars K (osymABDG a b))).Regraded)]

/-- The `(a, b)`-component of `[R]` on `K₀(D(OΛ_n))`, `n = a + b`: the symbol of `R_{a,b}` followed by
the inverse of Lemma 4.16 (`EQK0.comultK0`), as a `ℤ[√−1]`-linear map. -/
def comultK0Lin (a b n : ℕ) (h : a + b = n) :
    K0n K n →ₗ[GaussianInt] K0n K a ⊗[GaussianInt] K0n K b := by
  subst h
  exact (lemma_4_16.{0} K a b).symm.toLinearMap ∘ₗ
    superK0cGaussianMap (HalfGradedDGRing.Hom.ofDGRingHom (extendInclDG K a b)).K0Map

/-- **The comultiplication `[R]` on `K₀(D(OΛ))`**: on `K₀(D(OΛ_n))`, `Σ_{a+b=n}` of the symbol of
`R_{a,b}` (Definition 4.15) followed by the inverse of Lemma 4.16. -/
def comultK0OLam : K0OLam K →ₗ[GaussianInt] K0OLam K ⊗[GaussianInt] K0OLam K :=
  Assembly.comulMap (comultK0Lin K)

/-- **Theorem 4.17, comultiplication**: `[R](φ x) = (φ ⊗ φ)(r x)`, `r` the coproduct (2.2) for the
twist `−1`. -/
theorem thm_4_17_comul (x : UPlus) :
    comultK0OLam K (thm_4_17_equiv K x) =
      TensorProduct.map (thm_4_17_equiv K).toLinearMap (thm_4_17_equiv K).toLinearMap
        (EQQuantum.TT.tensorEquiv evI (-1) (rU x)) :=
  Assembly.equiv_comul _ _ _ (comultK0Lin K)
    (fun a b n h => by subst h; exact comultK0_ePowClass K a b) x

section Multiplication

variable [∀ a b, CatModule.HasDerivedCategory.{0, 0} (SingleObj (ExtendScalars K (osymABDG a b)))]
  [∀ n, CatModule.HasDerivedCategory.{0, 0} (SingleObj (ExtendScalars K (osymDG n)))]
  [∀ n, CatModule.HasDerivedCategory.{0, 0} (SingleObj (osymDG n))]
  [∀ a b, CatModule.HasDerivedCategory.{0, 0} (SingleObj (osymABDG a b))]
  [∀ n, DG.HasDerivedCategory.{0, 0} (osymDG n)] [∀ a b, DG.HasDerivedCategory.{0, 0} (osymABDG a b)]

/-- The `(a, b)`-component of `[I]`: Lemma 4.16 followed by the symbol of the half-graded
multiplication functor (`EQK0.multK0`), as a `ℤ[√−1]`-linear map. -/
def multK0Lin (a b : ℕ) : K0n K a ⊗[GaussianInt] K0n K b →ₗ[GaussianInt] K0n K (a+b) :=
  (superK0cGaussianMap (Diagonal.transportK0 _ _ (multK K a b)
    fun _ h => isCompact_multK_obj K a b h)) ∘ₗ (lemma_4_16.{0} K a b).toLinearMap

/-- **The multiplication `[I]` on `K₀(D(OΛ))`**: on the `(a, b)`-component, the Künneth isomorphism
of Lemma 4.16 followed by the symbol of the multiplication functor `I_{a,b}` (Definition 4.14). -/
def multK0OLam : K0OLam K →ₗ[GaussianInt] K0OLam K →ₗ[GaussianInt] K0OLam K :=
  Assembly.mulMap (multK0Lin K)

/-- **Theorem 4.17, multiplication**: `φ(x y) = [I](φ x, φ y)`. -/
theorem thm_4_17_mul (x y : UPlus) :
    thm_4_17_equiv K (x * y) = multK0OLam K (thm_4_17_equiv K x) (thm_4_17_equiv K y) :=
  Assembly.equiv_mul _ _ _ (multK0Lin K) (fun a b => multK0_ePowClass K a b) x y

end Multiplication

end Comultiplication

end OddMath.Frontier.EQK0
