import DG.Derived.ConnectedK0
import OddMath.Frontier.EQFunctorDual
import DG.Derived.KProjective
import DG.Homotopy.HomShift

/-!
# Ellis–Qi, Proposition 4.12 (1): `END` computes `R END` for `Z_{a,b}` and `Z_{a,b}^∨`

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
§4.3.2, Proposition 4.12 (1).

* `DG.DerivedCategory.homShiftAddEquivOfIsKProjective` (dg-lean): for a K-projective dg module `P` over a dg ring `A`
  and any `N`, `Hom_{D(A)}(Q P, (Q N)⟦n⟧) ≃+ Hⁿ(HOM_A(P, N))` for every `n`.
* **Proposition 4.12 (1)**: `prop_4_12_one`: `Hom_{D(OΛ_{a+b}ᵒᵖ)}(Z_{a,b}, Z_{a,b}⟦n⟧)` is the
  `n`-th cohomology of the graded endomorphism complex `END_{OΛ_{a+b}ᵒᵖ}(Z_{a,b})`, i.e.
  `R END(Z_{a,b}) ≅ END(Z_{a,b})` on cohomology in every degree, from Corollary 4.8
  (`EQFix.zab_isKProjective`); `prop_4_12_one_dual`: the same for the left dg `OΛ_{a+b}`-module
  `Z_{a,b}^∨`, from Corollary 4.11 (`EQFunctor.zdual_isKProjective`).

Proposition 4.12 (2) is in `OddMath.Frontier.EQZabEndRankOne` (`prop_4_12_two`: `END(Z_{a,b})` is the
algebra `E_{a,b}` spanned by the trace-pairing maps; `prop_4_12_two_dual`:
`END(Z_{a,b}) ≅ END(Z^∨_{a,b})`).
-/

open CategoryTheory DG

universe w v u

namespace OddMath.Frontier.EQZabREnd


attribute [local instance] EQFix.zabOpModule EQFix.zabOpDGModule

variable (a b : ℕ)

/-- **Ellis–Qi, Proposition 4.12 (1)** for `Z_{a,b}`: for every `n`,
`Hom_{D(OΛ_{a+b}ᵒᵖ)}(Z_{a,b}, Z_{a,b}⟦n⟧) ≃+ Hⁿ(END_{OΛ_{a+b}ᵒᵖ}(Z_{a,b}))`. -/
noncomputable def prop_4_12_one [DG.HasDerivedCategory.{w, 0} (EQFix.OsymOp (a+b))] (n : ℤ) :
    (DG.DerivedCategory.Q.obj (DGModuleCat.of (EQFix.OsymOp (a+b)) (EQFix.Zab a b)) ⟶
        (DG.DerivedCategory.Q.obj (DGModuleCat.of (EQFix.OsymOp (a+b)) (EQFix.Zab a b)))⟦n⟧) ≃+
      cohomology (DGModule.HOM (EQFix.OsymOp (a+b)) (EQFix.Zab a b) (EQFix.Zab a b)) n :=
  DG.DerivedCategory.homShiftAddEquivOfIsKProjective EQFix.zab_isKProjective _ n

/-- **Ellis–Qi, Proposition 4.12 (1)** for `Z_{a,b}^∨`: for every `n`,
`Hom_{D(OΛ_{a+b})}(Z_{a,b}^∨, Z_{a,b}^∨⟦n⟧) ≃+ Hⁿ(END_{OΛ_{a+b}}(Z_{a,b}^∨))`. -/
noncomputable def prop_4_12_one_dual
    [DG.HasDerivedCategory.{w, 0} (EQSkewDifferential.osymDG (a+b))] (n : ℤ) :
    (DG.DerivedCategory.Q.obj (DGModuleCat.of (EQSkewDifferential.osymDG (a+b))
          (EQFunctor.ZDual a b)) ⟶
        (DG.DerivedCategory.Q.obj (DGModuleCat.of (EQSkewDifferential.osymDG (a+b))
          (EQFunctor.ZDual a b)))⟦n⟧) ≃+
      cohomology (DGModule.HOM (EQSkewDifferential.osymDG (a+b)) (EQFunctor.ZDual a b)
        (EQFunctor.ZDual a b)) n :=
  DG.DerivedCategory.homShiftAddEquivOfIsKProjective EQFunctor.zdual_isKProjective _ n

end OddMath.Frontier.EQZabREnd
