import OddMath.Frontier.EQFunctorDual
import OddMath.Frontier.EQFunctorBimodule

/-!
# The multiplication and comultiplication functors on derived categories

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
§4.4, Definition 4.14, Definition 4.15 and the proof of Theorem 4.17, with Corollary 4.11
(printed numbering).

All dg rings are over `ℤ` and graded by half the Ellis–Qi `q`-degree (the grading of
`OddMath.Frontier.EQSkewDifferential.OPol`); `D(A)` is the derived category of the `DG` library
(`DG.DerivedCategory`) of dg modules with this `ℤ`-grading, and `K₀(A)` is the Grothendieck group
`DG.DGRing.K0` of its compact objects, in which `[M⟦1⟧] = -[M]`. Write `OΛ_{a,b} = OΛ_a ⊗ OΛ_b`
(`EQFunctor.osymABDG a b`).

## The multiplication functor (Definition 4.14)

`I_{a,b} = Z_{a,b}^∨ ⊗^L_{OΛ_{a,b}} (-) : D(OΛ_{a,b}) → D(OΛ_{a+b})`, the derived tensor product
with the dual bimodule `Z_{a,b}^∨ = HOM_{OΛ_{a+b}}(Z_{a,b}, OΛ_{a+b})` (`EQFunctor.ZDual a b`),
which is K-projective as a left dg `OΛ_{a+b}`-module by Corollary 4.11. Ellis–Qi compose it with
`(M, N) ↦ M ⊠ N`; the functor out of `D(OΛ_{a,b})` is the one formalized here.

* `mult a b`: `I_{a,b}`, a triangulated functor;
* `multSelfIso`: `I_{a,b}(OΛ_{a,b}) ≅ Z_{a,b}^∨`;
* `isCompact_mult_obj`: `I_{a,b}` preserves compact objects, and `K0Mult a b : K₀(OΛ_{a,b}) → K₀(OΛ_{a+b})`
  is the induced map;
* `K0_zdual`, `K0Mult_self`: `[I_{a,b}(OΛ_{a,b})] = [Z_{a,b}^∨] = Σ_{μ ∈ Par(b,a)} (-1)^{|μ|} [OΛ_{a+b}]`
  (the `ℤ`-graded form of `[I(OΛ_a ⊠ OΛ_b)] = [a+b choose a] [OΛ_{a+b}]` in the proof of
  Theorem 4.17; the cell of `δ_μ` is `OΛ_{a+b}` shifted by `|μ|`).

## The comultiplication functor (Definition 4.15)

Ellis–Qi's `Z^♮_{a,b} = (OΛ̃_a ⊗ OΛ̃_b) · z^♮`, `d(z^♮) = 0`, is free of rank one as a left dg
module over `OΛ_{a,b}` on a closed generator of degree `0`; its right `OΛ_{a+b}`-action is not
printed, and the proof of Corollary 4.21 uses `Z^♮_{a,b} ≅ OΛ_a ⊗ OΛ_b`. We take this as the
definition: `Z^♮_{a,b}` is `OΛ_{a,b}` as an `(OΛ_{a,b}, OΛ_{a+b})`-bimodule through the block swap
`OΛ_{a+b} → OΛ_{a,b}`, `f(x, y) ↦ f(y, x)` (`EQFunctor.swapOsym`), the right action for which the
restriction half of Corollary 4.21 holds (`EQFunctor.resIsoA`, ERRATA [EQ] 24). Then `R_{a,b} = Z^♮_{a,b} ⊗^L_{OΛ_{a+b}} (-)` is derived
induction along this map. (The printed Definition 4.15(2) writes `M ↦ Z^♮_{a,b} ⊗^L_{OΛ_{a,b}} M`;
the tensor product is over `OΛ_{a+b}`, as in the displayed functor.)

* `comult a b`: `R_{a,b} : D(OΛ_{a+b}) → D(OΛ_{a,b})` (`DG.DGRingHom.derivedInduction`), a triangulated
  functor; `comultIsoDerivedTensor`: it is the derived tensor product with the bimodule `OΛ_{a,b}`;
  `comultAdjunction`: it is left adjoint to restriction of scalars;
* `comultSelfIso`: `R_{a,b}(OΛ_{a+b}) ≅ OΛ_{a,b}`;
* `isCompact_comult_obj`, `K0Comult a b`, `K0Comult_self`: `R_{a,b}` preserves compact objects and
  `[R_{a,b}(OΛ_{a+b})] = [OΛ_{a,b}]` (the `(a,b)`-component of `[R(OΛ_n)] = Σ_{a+b=n} [Z^♮_{a,b}]`).

## Comparison with the printed setting

Ellis–Qi work over a field in §4.4 (footnote 5 extends this to `ℤ`), with `ℤ × ℤ/2`-graded dg modules
and `K₀` a `ℤ[√−1]`-module. Here the rings are over `ℤ`, the dg modules are `ℤ`-graded with parity the
degree mod `2`, and the statements are the `ℤ`-graded counterparts of Definitions 4.14 and 4.15 and of
the two `K₀` computations in the proof of Theorem 4.17.
-/

open CategoryTheory Limits

universe w₁ w₂ w₃ w₄

namespace OddMath.Frontier.EQFunctor

open OddMath.Frontier.EQSkewDifferential (osymDG totalDeg)
open OddMath.Frontier.EQFix (ParIdx)
open DG

noncomputable section

variable (a b : ℕ)

/-! ## The multiplication functor `I_{a,b}` (Definition 4.14) -/

section Multiplication

variable [CatModule.HasDerivedCategory.{w₁, 0} (SingleObj (osymABDG a b))]
  [CatModule.HasDerivedCategory.{w₂, 0} (SingleObj (osymDG (a+b)))]
  [DG.HasDerivedCategory.{w₃, 0} (osymABDG a b)] [DG.HasDerivedCategory.{w₄, 0} (osymDG (a+b))]

/-- **The multiplication functor** `I_{a,b} = Z_{a,b}^∨ ⊗^L_{OΛ_{a,b}} (-) :
D(OΛ_a ⊗ OΛ_b) → D(OΛ_{a+b})` (Ellis–Qi, Definition 4.14): the derived tensor product with the dual
bimodule `Z_{a,b}^∨`, which is K-projective as a left dg `OΛ_{a+b}`-module (Corollary 4.11). -/
abbrev mult : DG.DerivedCategory (osymABDG a b) ⥤ DG.DerivedCategory (osymDG (a+b)) :=
  DGBimodule.derivedTensor.{w₁, w₂, w₃, w₄} (osymDG (a+b)) (osymABDG a b) (ZDual a b)
    zdual_isKProjective

/-- `I_{a,b}(OΛ_a ⊗ OΛ_b) ≅ Z_{a,b}^∨` in `D(OΛ_{a+b})`. -/
def multSelfIso :
    (mult.{w₁, w₂, w₃, w₄} a b).obj
        (DG.DerivedCategory.Q.obj (DGModuleCat.of (osymABDG a b) (osymABDG a b))) ≅
      DG.DerivedCategory.Q.obj (DGModuleCat.of (osymDG (a+b)) (ZDual a b)) :=
  DGBimodule.derivedTensorSelfIso _ _ _ _

/-- `I_{a,b}(OΛ_a ⊗ OΛ_b) ≅ Z_{a,b}^∨` is compact (Corollary 4.11: `Z_{a,b}^∨` is finite-cell). -/
theorem isCompact_mult_self :
    IsCompact.{0} ((mult.{w₁, w₂, w₃, w₄} a b).obj
      (DG.DerivedCategory.Q.obj (DGModuleCat.of (osymABDG a b) (osymABDG a b)))) :=
  (zdualFiniteCellFiltration a b).isCompact_Q_obj.of_iso (multSelfIso a b)

end Multiplication

/-- **The class of `Z_{a,b}^∨`** (Ellis–Qi, Corollary 4.11 and the proof of Theorem 4.17):
`[Z_{a,b}^∨] = Σ_{μ ∈ Par(b,a)} (-1)^{|μ|} [OΛ_{a+b}]` in `K₀(OΛ_{a+b})`. -/
theorem K0_zdual [DG.HasDerivedCategory.{w₄, 0} (osymDG (a+b))] :
    DG.K0.mk (⟨DG.DerivedCategory.Q.obj (DGModuleCat.of (osymDG (a+b)) (ZDual a b)),
        (zdualFiniteCellFiltration a b).isCompact_Q_obj⟩ :
          PerfectDerivedCategory.{w₄, 0} (osymDG (a+b))) =
      ∑ μ : ParIdx a b, (totalDeg μ.1).negOnePow • DGRing.K0.self.{w₄} (osymDG (a+b)) := by
  rw [DG.TriangularBasis.K0_mk (zdualTriangular a b)]
  refine ((DG.FreeBasis.order fun μ : ParIdx a b => -(-totalDeg μ.1)).sum_comp
    (fun μ : ParIdx a b => (-totalDeg μ.1).negOnePow • DGRing.K0.self.{w₄} (osymDG (a+b)))).trans ?_
  simp only [Int.negOnePow_neg]

section MultiplicationK0

variable [CatModule.HasDerivedCategory.{w₁, 0} (SingleObj (osymABDG a b))]
  [CatModule.HasDerivedCategory.{w₂, 0} (SingleObj (osymDG (a+b)))]
  [DG.HasDerivedCategory.{0, 0} (osymABDG a b)] [DG.HasDerivedCategory.{0, 0} (osymDG (a+b))]

/-- `I_{a,b}` preserves compact objects. -/
theorem isCompact_mult_obj {X : DG.DerivedCategory.{0, 0} (osymABDG a b)} (hX : IsCompact.{0} X) :
    IsCompact.{0} ((mult.{w₁, w₂, 0, 0} a b).obj X) :=
  DG.DerivedCategory.isCompact_obj_of_isCompact_self _ (isCompact_mult_self a b) hX

/-- The map `K₀(OΛ_a ⊗ OΛ_b) → K₀(OΛ_{a+b})` induced by the multiplication functor `I_{a,b}`. -/
def K0Mult : DGRing.K0.{0, 0} (osymABDG a b) →+ DGRing.K0.{0, 0} (osymDG (a+b)) :=
  DG.K0.mapCompact (mult.{w₁, w₂, 0, 0} a b) fun _ h => isCompact_mult_obj a b h

/-- **`[I_{a,b}(OΛ_a ⊗ OΛ_b)] = Σ_{μ ∈ Par(b,a)} (-1)^{|μ|} [OΛ_{a+b}]`** (Ellis–Qi, proof of
Theorem 4.17). -/
theorem K0Mult_self :
    K0Mult.{w₁, w₂} a b (DGRing.K0.self (osymABDG a b)) =
      ∑ μ : ParIdx a b, (totalDeg μ.1).negOnePow • DGRing.K0.self (osymDG (a+b)) := by
  rw [DGRing.K0.self, K0Mult, DG.K0.mapCompact_mk, ← K0_zdual a b]
  exact DG.K0.mk_eq_of_iso_obj (multSelfIso a b)

end MultiplicationK0

/-! ## The comultiplication functor `R_{a,b}` (Definition 4.15) -/

section Comultiplication

variable [CatModule.HasDerivedCategory.{w₁, 0} (SingleObj (osymDG (a+b)))]
  [CatModule.HasDerivedCategory.{w₂, 0} (SingleObj (osymABDG a b))]
  [DG.HasDerivedCategory.{w₃, 0} (osymDG (a+b))] [DG.HasDerivedCategory.{w₄, 0} (osymABDG a b)]

/-- **The comultiplication functor** `R_{a,b} = Z^♮_{a,b} ⊗^L_{OΛ_{a+b}} (-) :
D(OΛ_{a+b}) → D(OΛ_a ⊗ OΛ_b)` (Ellis–Qi, Definition 4.15): derived induction along the block swap
`OΛ_{a+b} → OΛ_a ⊗ OΛ_b`, `f(x, y) ↦ f(y, x)`. -/
abbrev comult : DG.DerivedCategory (osymDG (a+b)) ⥤ DG.DerivedCategory (osymABDG a b) :=
  (swapOsym a b).derivedInduction.{w₁, w₂, w₃, w₄}

/-- `R_{a,b}` is the derived tensor product with the `(OΛ_{a,b}, OΛ_{a+b})`-bimodule
`Z^♮_{a,b} = OΛ_{a,b}`. -/
def comultIsoDerivedTensor :
    comult.{w₁, w₂, w₃, w₄} a b ≅
      (CatModule.DerivedCategory.singleObjEquivalence (osymDG (a+b))).inverse ⋙
        CatModule.DerivedCategory.derivedTensor.{w₁, w₂, 0}
          (CatBimodule.ofFunctor (swapOsym a b).singleObjFunctor)
          (CatBimodule.isKProjective_ofFunctor_left (swapOsym a b).singleObjFunctor) ⋙
        (CatModule.DerivedCategory.singleObjEquivalence (osymABDG a b)).functor :=
  (swapOsym a b).derivedInductionIsoDerivedTensor

/-- `R_{a,b}` is left adjoint to restriction of scalars along the block swap. -/
def comultAdjunction : comult.{w₁, w₂, w₃, w₄} a b ⊣ (swapOsym a b).derivedRestriction :=
  (swapOsym a b).derivedInductionAdjunction

end Comultiplication

section ComultiplicationSelf

variable [CatModule.HasDerivedCategory.{0, 0} (SingleObj (osymDG (a+b)))]
  [CatModule.HasDerivedCategory.{w₂, 0} (SingleObj (osymABDG a b))]
  [DG.HasDerivedCategory.{w₃, 0} (osymDG (a+b))] [DG.HasDerivedCategory.{w₄, 0} (osymABDG a b)]

/-- `R_{a,b}(OΛ_{a+b}) ≅ OΛ_a ⊗ OΛ_b` in `D(OΛ_a ⊗ OΛ_b)`. -/
def comultSelfIso :
    (comult.{0, w₂, w₃, w₄} a b).obj
        (DG.DerivedCategory.Q.obj (DGModuleCat.of (osymDG (a+b)) (osymDG (a+b)))) ≅
      DG.DerivedCategory.Q.obj (DGModuleCat.of (osymABDG a b) (osymABDG a b)) :=
  derivedInductionSelfIso (swapOsym a b)

end ComultiplicationSelf

section ComultiplicationK0

variable [CatModule.HasDerivedCategory.{0, 0} (SingleObj (osymDG (a+b)))]
  [CatModule.HasDerivedCategory.{w₂, 0} (SingleObj (osymABDG a b))]
  [DG.HasDerivedCategory.{0, 0} (osymDG (a+b))] [DG.HasDerivedCategory.{0, 0} (osymABDG a b)]

/-- `R_{a,b}` preserves compact objects. -/
theorem isCompact_comult_obj {X : DG.DerivedCategory.{0, 0} (osymDG (a+b))}
    (hX : IsCompact.{0} X) : IsCompact.{0} ((comult.{0, w₂, 0, 0} a b).obj X) :=
  DG.DerivedCategory.isCompact_obj_of_isCompact_self _
    (DG.DerivedCategory.isCompact_Q_self.of_iso (comultSelfIso a b)) hX

/-- The map `K₀(OΛ_{a+b}) → K₀(OΛ_a ⊗ OΛ_b)` induced by the comultiplication functor `R_{a,b}`. -/
def K0Comult : DGRing.K0.{0, 0} (osymDG (a+b)) →+ DGRing.K0.{0, 0} (osymABDG a b) :=
  DG.K0.mapCompact (comult.{0, w₂, 0, 0} a b) fun _ h => isCompact_comult_obj a b h

/-- **`[R_{a,b}(OΛ_{a+b})] = [OΛ_a ⊗ OΛ_b]`** (Ellis–Qi, proof of Theorem 4.17). -/
theorem K0Comult_self :
    K0Comult.{w₂} a b (DGRing.K0.self (osymDG (a+b))) = DGRing.K0.self (osymABDG a b) := by
  rw [DGRing.K0.self, K0Comult, DG.K0.mapCompact_mk]
  exact DG.K0.mk_eq_of_iso_obj (comultSelfIso a b)

end ComultiplicationK0

end

end OddMath.Frontier.EQFunctor
