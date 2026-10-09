import OddMath.Frontier.EQK0Field
import OddMath.Frontier.EQQuantumGroups
import OddMath.Frontier.EQInductionPoly

/-!
# The comultiplication of Ellis–Qi Theorem 4.17 on `K₀`

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2
(printed numbering): §2.1 (2.2), Definition 4.15, Lemma 4.16 and the proof of Theorem 4.17.

Over a field `K`, write `H_n` for the diagonal half-graded dg ring of `K ⊗ OΛ_n` and `H_{a,b}` for that
of `K ⊗ OΛ_{a,b}`; `K₀(D(OΛ_n)) = SuperK0c H_n ≅ ℤ[√−1]` (`EQK0.superK0OsymEquiv`). Ellis–Qi
identify `E^{(n)}` with the class of the rank-one free module `OΛ_n⟨-binom(n,2)⟩`
(`EQK0.ePowClass K n`, `√−1` acting by the internal shift `⟨1⟩`).

The comultiplication functor `R_{a,b}` of Definition 4.15 is derived induction along the block swap
`OΛ_{a+b} → OΛ_{a,b}`, `f(x, y) ↦ f(y, x)` (`EQFunctor.comult`, with `Z^♮_{a,b} ≅ OΛ_{a,b}`, the right
action forced by Corollary 4.21); on half-graded dg modules it is derived induction along the induced
morphism of half-graded dg rings `H_{a+b} → H_{a,b}` (`DG.HalfGradedDGRing.Hom.ofDGRingHom` of
`K ⊗ swapOsym a b`, `EQK0.extendSwapDG`). Its symbol, followed by
the Künneth isomorphism of Lemma 4.16, is the `(a, b)`-component
`EQK0.comultK0 K a b : K₀(D(OΛ_{a+b})) → K₀(D(OΛ_a)) ⊗_{ℤ[√−1]} K₀(D(OΛ_b))` of the comultiplication
`[R]`.

* `comultK0_ePowClass`: `[R]_{a,b}(E^{(a+b)}) = (-√−1)^{ab} E^{(a)} ⊗ E^{(b)}`, the `(a, b)`-term of (2.2)
  `r(E^{(n)}) = Σ_{c=0}^{n} (-√−1)^{c(n-c)} E^{(c)} ⊗ E^{(n-c)}`, which is the coproduct for the
  twist `−1` (ERRATA [EQ] 1; `EQQuantum.rU`, `EQQuantum.eq_2_2`).
-/

noncomputable section

open CategoryTheory TensorProduct

namespace OddMath.Frontier.EQK0

open DG DG.HalfGradedDGRing
open OddMath.Frontier.EQSkewDifferential (osymDG)
open OddMath.Frontier.EQFunctor (osymABDG swapOsym)

variable (K : Type) [Field K]

/-- `K ⊗ OΛ_{a+b} → K ⊗ OΛ_{a,b}`, the scalar extension of the block swap `OΛ_{a+b} → OΛ_{a,b}`. -/
def extendSwapDG (a b : ℕ) : ExtendScalars K (osymDG (a+b)) →ᵈᵍ+* ExtendScalars K (osymABDG a b) :=
  (GradedTensorProduct.map (DGAlgHom.id : DegreeZeroRing K →ᵈᵍₐ[ℤ] DegreeZeroRing K)
    (intDGAlgHom (swapOsym a b))).toDGRingHom

/-- The class `[OΛ_n] ∈ K₀(D(OΛ_n))` of the regular module (its diagonal image). -/
abbrev regClass (n : ℕ) [HasDerivedCategory.{0, 0} (ExtendScalars K (osymDG n))]
    [CatModule.HasDerivedCategory.{0, 0}
      (WeightCategory (ofDGRing (ExtendScalars K (osymDG n))).Regraded)] :
    SuperK0c.{0, 0} (ofDGRing (ExtendScalars K (osymDG n))) :=
  superK0cMk.{0, 0} _ (Diagonal.mapCompactK0.{0, 0, 0} (ExtendScalars K (osymDG n))
    (DGRing.K0.self (ExtendScalars K (osymDG n))))

/-- `E^{(n)} = [OΛ_n⟨-binom(n,2)⟩] = (√−1)^{-binom(n,2)} [OΛ_n]` (Ellis–Qi, Theorem 4.17). By
`DG.HalfGradedDGRing.gaussian_zpow_smul_superK0c_mk` the scalar is the internal shift
`⟨-binom(n,2)⟩`. -/
def ePowClass (n : ℕ) [HasDerivedCategory.{0, 0} (ExtendScalars K (osymDG n))]
    [CatModule.HasDerivedCategory.{0, 0}
      (WeightCategory (ofDGRing (ExtendScalars K (osymDG n))).Regraded)] :
    SuperK0c.{0, 0} (ofDGRing (ExtendScalars K (osymDG n))) :=
  ((GaussianQuot.unitI ^ (-(n.choose 2 : ℤ)) : GaussianIntˣ) : GaussianInt) • regClass K n

theorem superK0OsymEquiv_ePowClass (n : ℕ) [HasDerivedCategory.{0, 0} (ExtendScalars K (osymDG n))]
    [CatModule.HasDerivedCategory.{0, 0}
      (WeightCategory (ofDGRing (ExtendScalars K (osymDG n))).Regraded)] :
    superK0OsymEquiv.{0} K n (ePowClass K n) =
      ((GaussianQuot.unitI ^ (-(n.choose 2 : ℤ)) : GaussianIntˣ) : GaussianInt) := by
  rw [ePowClass, LinearEquiv.map_smul, superK0OsymEquiv_self, smul_eq_mul, mul_one]

theorem choose_two_add (a b : ℕ) : (a + b).choose 2 = a.choose 2 + b.choose 2 + a * b := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [← add_assoc, Nat.choose_succ_succ', Nat.choose_one_right, ih, Nat.choose_succ_succ',
      Nat.choose_one_right]
    ring

variable (a b : ℕ) [HasDerivedCategory.{0, 0} (ExtendScalars K (osymDG (a+b)))]
  [CatModule.HasDerivedCategory.{0, 0}
    (WeightCategory (ofDGRing (ExtendScalars K (osymDG (a+b)))).Regraded)]
  [HasDerivedCategory.{0, 0} (ExtendScalars K (osymABDG a b))]
  [CatModule.HasDerivedCategory.{0, 0}
    (WeightCategory (ofDGRing (ExtendScalars K (osymABDG a b))).Regraded)]

/-- The symbol of `R_{a,b}` on half-graded dg modules is the identity of `ℤ[√−1]`:
`[R_{a,b}] [OΛ_{a+b}] = [OΛ_{a,b}]`. -/
theorem superK0OsymABEquiv_comult (s : SuperK0c.{0, 0} (ofDGRing (ExtendScalars K (osymDG (a+b))))) :
    superK0OsymABEquiv.{0} K a b
        (superK0cMap _ _ (HalfGradedDGRing.Hom.ofDGRingHom (extendSwapDG K a b)).K0Map s) =
      superK0OsymEquiv.{0} K (a+b) s :=
  superK0GaussianOfBase_superK0cMap _ _ _
    (baseK0_map_eq _ _ _ (baseK0EquivInt_self K _) (baseK0EquivInt_self K _)) s

variable [HasDerivedCategory.{0, 0} (ExtendScalars K (osymDG a))]
  [CatModule.HasDerivedCategory.{0, 0}
    (WeightCategory (ofDGRing (ExtendScalars K (osymDG a))).Regraded)]
  [HasDerivedCategory.{0, 0} (ExtendScalars K (osymDG b))]
  [CatModule.HasDerivedCategory.{0, 0}
    (WeightCategory (ofDGRing (ExtendScalars K (osymDG b))).Regraded)]

/-- **The `(a, b)`-component of the comultiplication `[R]`** (Ellis–Qi, Definition 4.15 and
Lemma 4.16): the symbol of `R_{a,b}` on `K₀(D(OΛ_{a+b}))`, followed by the inverse of the Künneth
isomorphism `K₀(D(OΛ_a)) ⊗_{ℤ[√−1]} K₀(D(OΛ_b)) ≅ K₀(D(OΛ_{a,b}))`. -/
def comultK0 (s : SuperK0c.{0, 0} (ofDGRing (ExtendScalars K (osymDG (a+b))))) :
    SuperK0c.{0, 0} (ofDGRing (ExtendScalars K (osymDG a))) ⊗[GaussianInt]
      SuperK0c.{0, 0} (ofDGRing (ExtendScalars K (osymDG b))) :=
  (lemma_4_16.{0} K a b).symm
    (superK0cMap _ _ (HalfGradedDGRing.Hom.ofDGRingHom (extendSwapDG K a b)).K0Map s)

theorem neg_ii_eq : (-EQQuantum.ii : GaussianInt) = ((GaussianQuot.unitI⁻¹ : GaussianIntˣ) : GaussianInt) :=
  rfl

/-- **Theorem 4.17, comultiplication**: `[R]_{a,b}(E^{(a+b)}) = (-√−1)^{ab} E^{(a)} ⊗ E^{(b)}`, the
`(a, b)`-term of (2.2). -/
theorem comultK0_ePowClass :
    comultK0 K a b (ePowClass K (a+b)) =
      ((-EQQuantum.ii) ^ (a * b) : GaussianInt) • (ePowClass K a ⊗ₜ[GaussianInt] ePowClass K b) := by
  have hL := (superK0OsymABEquiv_comult K a b (ePowClass K (a+b))).trans
    (superK0OsymEquiv_ePowClass K (a+b))
  have hR : superK0OsymABEquiv.{0} K a b (lemma_4_16.{0} K a b
      (((-EQQuantum.ii) ^ (a * b) : GaussianInt) • (ePowClass K a ⊗ₜ[GaussianInt] ePowClass K b))) =
      ((-EQQuantum.ii) ^ (a * b) : GaussianInt) *
        (((GaussianQuot.unitI ^ (-(a.choose 2 : ℤ)) : GaussianIntˣ) : GaussianInt) *
          ((GaussianQuot.unitI ^ (-(b.choose 2 : ℤ)) : GaussianIntˣ) : GaussianInt)) := by
    rw [LinearEquiv.map_smul, LinearEquiv.map_smul, smul_eq_mul]
    refine congrArg (_ * ·) ?_
    refine (apply_tensorEquivOfGaussian_tmul _ _ _ _ _).trans ?_
    exact congrArg₂ (· * ·) (superK0OsymEquiv_ePowClass K a) (superK0OsymEquiv_ePowClass K b)
  refine (LinearEquiv.symm_apply_eq _).mpr ((superK0OsymABEquiv.{0} K a b).injective ?_)
  refine hL.trans (Eq.trans ?_ hR.symm)
  rw [neg_ii_eq, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← Units.val_mul]
  congr 1
  rw [← zpow_natCast, ← zpow_neg_one, ← zpow_mul, ← zpow_add, ← zpow_add, choose_two_add]
  congr 1
  push_cast
  ring

end OddMath.Frontier.EQK0
