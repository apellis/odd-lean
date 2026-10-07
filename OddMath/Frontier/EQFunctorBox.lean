import OddMath.Frontier.EQFunctorDerived
import OddMath.Frontier.EQFunctorRingTensor
import DG.K0.ExternalTensor
import DG.Derived.ExternalTensorOver

/-!
# The multiplication functor of Definition 4.14 on `D(OΛ_a) × D(OΛ_b)`

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
§4.4, Definition 4.14 and the proof of Theorem 4.17 (printed numbering).

Ellis–Qi define the multiplication functor on pairs of dg modules,
`(M, N) ↦ Z_{a,b}^∨ ⊗^L_{OΛ_{a,b}} (M ⊠ N)`. Here, with the `ℤ`-graded derived categories of the `DG`
library:

* `M ⊠ N` is dg-lean's derived external tensor product `D(OΛ_a) ⥤ D(OΛ_b) ⥤ D(OΛ_a ⊗ OΛ_b)`
  (`DG.DerivedCategory.externalTensor`, over the graded tensor product of dg rings), followed by
  derived induction along the isomorphism of dg rings `OΛ_a ⊗ OΛ_b ≅ OΛ_{a,b}`
  (`EQFunctor.tensorToOsymAB`, `f ⊗ g ↦ f(x) g(y)`): `boxFunctor a b`;
* `multBox a b = Z_{a,b}^∨ ⊗^L_{OΛ_{a,b}} (- ⊠ -)`, the functor of Definition 4.14 (`mult a b` is the
  functor out of `D(OΛ_{a,b})`);
* `multBoxSelfIso`: `I_{a,b}(OΛ_a, OΛ_b) ≅ Z_{a,b}^∨` (first display in the proof of Theorem 4.17);
* `K0MultBox a b : K₀(OΛ_a) →+ K₀(OΛ_b) →+ K₀(OΛ_{a+b})`, `[M] ⊗ [N] ↦ [I_{a,b}(M, N)]`
  (`K0MultBox_mk`), and `K0MultBox_self`:
  `[I_{a,b}(OΛ_a, OΛ_b)] = Σ_{μ ∈ Par(b,a)} (-1)^{|μ|} [OΛ_{a+b}]`.

All dg rings are over `ℤ` and graded by half the Ellis–Qi `q`-degree.
-/

open CategoryTheory Limits
open scoped TensorProduct

namespace OddMath.Frontier.EQFunctor

open OddMath.Frontier.EQSkewDifferential (osymDG totalDeg)
open OddMath.Frontier.EQFix (ParIdx)
open DG

noncomputable section

variable (a b : ℕ)

variable [DG.HasDerivedCategory.{0, 0} (osymDG a)] [DG.HasDerivedCategory.{0, 0} (osymDG b)]
  [DG.HasDerivedCategory.{0, 0} (DGAlgebra.gradingSubmodule ℤ (osymDG a) ᵍ⊗[ℤ] DGAlgebra.gradingSubmodule ℤ (osymDG b))] [DG.HasDerivedCategory.{0, 0} (osymABDG a b)]
  [DG.HasDerivedCategory.{0, 0} (osymDG (a+b))]
  [CatModule.HasDerivedCategory.{0, 0} (SingleObj (DGAlgebra.gradingSubmodule ℤ (osymDG a) ᵍ⊗[ℤ] DGAlgebra.gradingSubmodule ℤ (osymDG b)))]
  [CatModule.HasDerivedCategory.{0, 0} (SingleObj (osymABDG a b))]
  [CatModule.HasDerivedCategory.{0, 0} (SingleObj (osymDG (a+b)))]

/-- Derived induction along `OΛ_a ⊗ OΛ_b ≅ OΛ_{a,b}`. -/
abbrev tensorInduction : DG.DerivedCategory.{0, 0} (DGAlgebra.gradingSubmodule ℤ (osymDG a) ᵍ⊗[ℤ] DGAlgebra.gradingSubmodule ℤ (osymDG b)) ⥤ DG.DerivedCategory.{0, 0} (osymABDG a b) :=
  (tensorToOsymAB a b).derivedInduction.{0, 0, 0, 0}

/-- **`M ⊠ N`** in `D(OΛ_{a,b})`: the derived external tensor product followed by derived induction
along `OΛ_a ⊗ OΛ_b ≅ OΛ_{a,b}`. -/
def boxFunctor : DG.DerivedCategory.{0, 0} (osymDG a) ⥤ DG.DerivedCategory.{0, 0} (osymDG b) ⥤
    DG.DerivedCategory.{0, 0} (osymABDG a b) :=
  DG.DerivedCategory.externalTensor (osymDG a) (osymDG b) ⋙
    (Functor.whiskeringRight _ _ _).obj (tensorInduction a b)

/-- **The multiplication functor of Definition 4.14**,
`(M, N) ↦ Z_{a,b}^∨ ⊗^L_{OΛ_{a,b}} (M ⊠ N)`. -/
def multBox : DG.DerivedCategory.{0, 0} (osymDG a) ⥤ DG.DerivedCategory.{0, 0} (osymDG b) ⥤
    DG.DerivedCategory.{0, 0} (osymDG (a+b)) :=
  boxFunctor a b ⋙ (Functor.whiskeringRight _ _ _).obj (mult.{0, 0, 0, 0} a b)

theorem multBox_obj_obj (X : DG.DerivedCategory.{0, 0} (osymDG a))
    (Y : DG.DerivedCategory.{0, 0} (osymDG b)) :
    ((multBox a b).obj X).obj Y = (mult.{0, 0, 0, 0} a b).obj ((tensorInduction a b).obj
      (((DG.DerivedCategory.externalTensor (osymDG a) (osymDG b)).obj X).obj Y)) := rfl

/-- `OΛ_a ⊠ OΛ_b ≅ OΛ_{a,b}` in `D(OΛ_{a,b})`. -/
def boxSelfIso :
    ((boxFunctor a b).obj (DG.DerivedCategory.Q.obj (DGModuleCat.of (osymDG a) (osymDG a)))).obj
        (DG.DerivedCategory.Q.obj (DGModuleCat.of (osymDG b) (osymDG b))) ≅
      DG.DerivedCategory.Q.obj (DGModuleCat.of (osymABDG a b) (osymABDG a b)) :=
  (tensorInduction a b).mapIso
      (DG.DerivedCategory.externalTensorRegularIso (A := osymDG a) (B := osymDG b)) ≪≫
    derivedInductionSelfIso (tensorToOsymAB a b)

/-- **`I_{a,b}(OΛ_a, OΛ_b) ≅ Z_{a,b}^∨`** in `D(OΛ_{a+b})` (Ellis–Qi, proof of Theorem 4.17). -/
def multBoxSelfIso :
    ((multBox a b).obj (DG.DerivedCategory.Q.obj (DGModuleCat.of (osymDG a) (osymDG a)))).obj
        (DG.DerivedCategory.Q.obj (DGModuleCat.of (osymDG b) (osymDG b))) ≅
      DG.DerivedCategory.Q.obj (DGModuleCat.of (osymDG (a+b)) (ZDual a b)) :=
  (mult.{0, 0, 0, 0} a b).mapIso (boxSelfIso a b) ≪≫ multSelfIso a b

omit [DG.HasDerivedCategory.{0, 0} (osymDG (a+b))]
  [CatModule.HasDerivedCategory.{0, 0} (SingleObj (osymDG (a+b)))] in
/-- `M ⊠ N` is compact for compact `M`, `N`. -/
theorem isCompact_boxFunctor {X : DG.DerivedCategory.{0, 0} (osymDG a)}
    {Y : DG.DerivedCategory.{0, 0} (osymDG b)} (hX : IsCompact.{0} X) (hY : IsCompact.{0} Y) :
    IsCompact.{0} (((boxFunctor a b).obj X).obj Y) :=
  DG.DGRingHom.isCompact_derivedInduction_obj (tensorToOsymAB a b)
    (DG.DerivedCategory.isCompact_externalTensor hX hY)

/-- The map `K₀(OΛ_a ⊗ OΛ_b) → K₀(OΛ_{a,b})` induced by derived induction. -/
def K0TensorInduction : DGRing.K0.{0, 0} (DGAlgebra.gradingSubmodule ℤ (osymDG a) ᵍ⊗[ℤ] DGAlgebra.gradingSubmodule ℤ (osymDG b)) →+ DGRing.K0.{0, 0} (osymABDG a b) :=
  DG.K0.mapCompact (tensorInduction a b) fun _ h =>
    DG.DGRingHom.isCompact_derivedInduction_obj (tensorToOsymAB a b) h

/-- **The symbol of the multiplication functor**, `[M] ⊗ [N] ↦ [I_{a,b}(M, N)]`
(`K0MultBox_mk`). -/
def K0MultBox : DGRing.K0.{0, 0} (osymDG a) →+ DGRing.K0.{0, 0} (osymDG b) →+
    DGRing.K0.{0, 0} (osymDG (a+b)) :=
  (DG.DerivedCategory.K0ExternalTensor (osymDG a) (osymDG b)).compr₂
    ((K0Mult.{0, 0} a b).comp (K0TensorInduction a b))

theorem K0MultBox_mk (X : PerfectDerivedCategory.{0, 0} (osymDG a))
    (Y : PerfectDerivedCategory.{0, 0} (osymDG b)) :
    K0MultBox a b (DG.K0.mk X) (DG.K0.mk Y) =
      DG.K0.mk (⟨((multBox a b).obj X.obj).obj Y.obj, isCompact_mult_obj a b
        (isCompact_boxFunctor a b X.2 Y.2)⟩ : PerfectDerivedCategory.{0, 0} (osymDG (a+b))) := by
  rw [K0MultBox, AddMonoidHom.compr₂_apply, DG.DerivedCategory.K0ExternalTensor_mk,
    AddMonoidHom.comp_apply, K0TensorInduction, DG.K0.mapCompact_mk, K0Mult, DG.K0.mapCompact_mk]
  rfl

/-- **`[I_{a,b}(OΛ_a, OΛ_b)] = Σ_{μ ∈ Par(b,a)} (-1)^{|μ|} [OΛ_{a+b}]`** (Ellis–Qi, proof of
Theorem 4.17, in the `ℤ`-graded setting). -/
theorem K0MultBox_self :
    K0MultBox a b (DGRing.K0.self (osymDG a)) (DGRing.K0.self (osymDG b)) =
      ∑ μ : ParIdx a b, (totalDeg μ.1).negOnePow • DGRing.K0.self (osymDG (a+b)) := by
  rw [DGRing.K0.self, DGRing.K0.self, K0MultBox_mk, ← K0_zdual a b]
  exact DG.K0.mk_eq_of_iso_obj (multBoxSelfIso a b)

end

end OddMath.Frontier.EQFunctor
