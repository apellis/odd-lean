import OddMath.Frontier.EQFunctorDual
import DG.Derived.KProjective
import DG.Homotopy.HomShift

/-!
# Ellis–Qi, Proposition 4.12 (1): `END` computes `R END` for `Z_{a,b}` and `Z_{a,b}^∨`

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
§4.3.2, Proposition 4.12 (1).

* `homShiftAddEquivOfIsKProjective` (generic): for a K-projective dg module `P` over a dg ring `A`
  and any `N`, `Hom_{D(A)}(Q P, (Q N)⟦n⟧) ≃+ Hⁿ(HOM_A(P, N))` for every `n`.
* **Proposition 4.12 (1)**: `prop_4_12_one`: `Hom_{D(OΛ_{a+b}ᵒᵖ)}(Z_{a,b}, Z_{a,b}⟦n⟧)` is the
  `n`-th cohomology of the graded endomorphism complex `END_{OΛ_{a+b}ᵒᵖ}(Z_{a,b})`, i.e.
  `R END(Z_{a,b}) ≅ END(Z_{a,b})` on cohomology in every degree, from Corollary 4.8
  (`EQFix.zab_isKProjective`); `prop_4_12_one_dual`: the same for the left dg `OΛ_{a+b}`-module
  `Z_{a,b}^∨`, from Corollary 4.11 (`EQFunctor.zdual_isKProjective`).

Proposition 4.12 (2), the identification of `END(Z_{a,b})` with the diagrammatic algebra
`E_{a,b}`, is not formalized here: the source defines `E_{a,b}` only through the diagrams `φ` of
the paragraph before the proposition.
-/

open CategoryTheory DG

universe w v u

namespace OddMath.Frontier.EQZabREnd

section Generic

variable {A : Type u} [Ring A] [DGAddCommGroup A] [DGRing A] [DG.HasDerivedCategory.{w, v} A]

/-- For `P` K-projective, `Hom_{D(A)}(Q P, (Q N)⟦n⟧) ≃+ Hⁿ(HOM_A(P, N))`: the derived Hom
complex out of `P` is computed by the dg Hom complex. -/
noncomputable def homShiftAddEquivOfIsKProjective {P : DGModuleCat.{v} A}
    (hP : IsKProjective.{v} A P) (N : DGModuleCat.{v} A) (n : ℤ) :
    (DG.DerivedCategory.Q.obj P ⟶ (DG.DerivedCategory.Q.obj N)⟦n⟧) ≃+
      cohomology (DGModule.HOM A P N) n :=
  let Y := ((DG.HomotopyCategory.quotient A).obj N)⟦n⟧
  let e : DG.DerivedCategory.Qh.obj Y ≅ (DG.DerivedCategory.Q.obj N)⟦n⟧ :=
    (DG.DerivedCategory.Qh.commShiftIso n).app ((DG.HomotopyCategory.quotient A).obj N)
  let c : (DG.DerivedCategory.Qh.obj ((DG.HomotopyCategory.quotient A).obj P) ⟶
      DG.DerivedCategory.Qh.obj Y) ≃+
      (DG.DerivedCategory.Qh.obj ((DG.HomotopyCategory.quotient A).obj P) ⟶
        (DG.DerivedCategory.Q.obj N)⟦n⟧) :=
    { toFun := fun f => f ≫ e.hom
      invFun := fun g => g ≫ e.inv
      left_inv := fun f => by simp
      right_inv := fun g => by simp
      map_add' := fun f g => Preadditive.add_comp _ _ _ _ _ _ }
  ((AddEquiv.ofBijective (DG.DerivedCategory.Qh.mapAddHom
      (X := (DG.HomotopyCategory.quotient A).obj P) (Y := Y))
      (DG.DerivedCategory.Qh_map_bijective_of_isKProjective hP Y)).trans c).symm.trans
    (DG.HomotopyCategory.homShiftAddEquivCohomology P N n)

end Generic

attribute [local instance] EQFix.zabOpModule EQFix.zabOpDGModule

variable (a b : ℕ)

/-- **Ellis–Qi, Proposition 4.12 (1)** for `Z_{a,b}`: for every `n`,
`Hom_{D(OΛ_{a+b}ᵒᵖ)}(Z_{a,b}, Z_{a,b}⟦n⟧) ≃+ Hⁿ(END_{OΛ_{a+b}ᵒᵖ}(Z_{a,b}))`. -/
noncomputable def prop_4_12_one [DG.HasDerivedCategory.{w, 0} (EQFix.OsymOp (a+b))] (n : ℤ) :
    (DG.DerivedCategory.Q.obj (DGModuleCat.of (EQFix.OsymOp (a+b)) (EQFix.Zab a b)) ⟶
        (DG.DerivedCategory.Q.obj (DGModuleCat.of (EQFix.OsymOp (a+b)) (EQFix.Zab a b)))⟦n⟧) ≃+
      cohomology (DGModule.HOM (EQFix.OsymOp (a+b)) (EQFix.Zab a b) (EQFix.Zab a b)) n :=
  homShiftAddEquivOfIsKProjective EQFix.zab_isKProjective _ n

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
  homShiftAddEquivOfIsKProjective EQFunctor.zdual_isKProjective _ n

end OddMath.Frontier.EQZabREnd
