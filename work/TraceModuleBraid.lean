import OddMath.QuiverHecke.CyclotomicAction.ELVWeightMixedModulePolynomial
import Lean
open Lean Meta in
partial def traceExprDifference (a b : Expr) (path : String) : MetaM Bool := do
  let a := a.consumeMData
  let b := b.consumeMData
  if a == b then return false
  if a.isLet then return ← traceExprDifference (← whnf a) b (path ++ ".zetaA")
  if b.isLet then return ← traceExprDifference a (← whnf b) (path ++ ".zetaB")
  if a.isApp && b.isApp then
    let af := a.getAppFn
    let bf := b.getAppFn
    if af != bf then
      let aw ← whnf a
      let bw ← whnf b
      if aw != a || bw != b then return ← traceExprDifference aw bw (path ++ ".whnf")
      if ← traceExprDifference af bf (path ++ ".head") then return true
    let aa := a.getAppArgs
    let ba := b.getAppArgs
    if aa.size == ba.size then
      for n in [:aa.size] do
        if ← traceExprDifference aa[n]! ba[n]! (path ++ ".arg" ++ toString n) then return true
      return false
  match a, b with
  | .forallE _ aTy aBody _, .forallE _ bTy bBody _
  | .lam _ aTy aBody _, .lam _ bTy bBody _ =>
    if ← traceExprDifference aTy bTy (path ++ ".dom") then return true
    return ← traceExprDifference aBody bBody (path ++ ".body")
  | _, _ => pure ()
  let aw ← whnf a
  let bw ← whnf b
  if aw != a || bw != b then return ← traceExprDifference aw bw (path ++ ".reduce")
  logInfo m!"FIRST DIFFERENCE {path}: {a}\nVERSUS {b}"
  return true


/-! # The corrected braid on the prescribed weight action

Brundan--Ellis (1.9), repeated outer colour. The given six crossings and
three positioned dots satisfy the ordered original-parameter correction
as supernatural maps, including every absent predecessor sector.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVOld
universe u
section Evaluation
variable {k : Type u} [CommRing k]
    {C : Type*} [Category* C] [Preadditive C] [Linear k C] [Supercategory k C]
    {J : Type u} {A : J → Type u}
    [∀ j, Category.{u} (A j)] [∀ j, Preadditive (A j)]
    [∀ j, Linear k (A j)] [∀ j, Supercategory k (A j)]
    {F G H : Superfunctor k C (∀ j, Superfunctor k (A j) (SVec k))}
private theorem family_correction_of_module_components
    {I X : Type u} [AddCommGroup X] (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
    (i j : I) (a₀ : F ⟶ G) (a₁ : End G) (a₂ : G ⟶ F)
    (b₀ : F ⟶ H) (b₁ : End H) (b₂ : H ⟶ F) (x₀ x₁ x₂ : End F)
    (h : ∀ M t,
      a₀.total M t ≫ a₁.total M t ≫ a₂.total M t -
        b₀.total M t ≫ b₁.total M t ≫ b₂.total M t =
      tripleDotCorrectionPolynomial (R := End (F.obj M t)) D Sc i j
        (x₀.total M t) (x₁.total M t) (x₂.total M t)) :
    a₀ ≫ a₁ ≫ a₂ - b₀ ≫ b₁ ≫ b₂ =
      tripleDotCorrectionPolynomial (R := End F) D Sc i j x₀ x₁ x₂ := by
  apply supernatural_hom_ext_total
  intro M
  funext t
  let ev := (piEndEvaluation (F.obj M) t).comp (supernaturalEndEvaluation F M)
  have hp := tripleDotCorrectionPolynomial_map D Sc ev i j x₀ x₁ x₂
  have he : (a₀ ≫ a₁ ≫ a₂ - b₀ ≫ b₁ ≫ b₂).total M t =
      a₀.total M t ≫ a₁.total M t ≫ a₂.total M t -
        b₀.total M t ≫ b₁.total M t ≫ b₂.total M t := by
    have hs := (supernaturalTotalLinearMap F F M).map_sub
      (a₀ ≫ a₁ ≫ a₂) (b₀ ≫ b₁ ≫ b₂)
    change (a₀ ≫ a₁ ≫ a₂ - b₀ ≫ b₁ ≫ b₂).total M =
      (a₀ ≫ a₁ ≫ a₂).total M - (b₀ ≫ b₁ ≫ b₂).total M at hs
    rw [Superfunctor.comp_total, Superfunctor.comp_total,
      Superfunctor.comp_total, Superfunctor.comp_total] at hs
    exact congrFun hs t
  exact he.trans ((h M t).trans hp.symm)
end Evaluation

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i j : I) (Λ : X) {a b c d e f : X}
  (hab : a + D.α i = b) (haf : a + D.α j = f) (hbc : b + D.α j = c)
  (hbe : b + D.α i = e) (hfc : f + D.α i = c) (hcd : c + D.α i = d)
  (hed : e + D.α j = d)
local notation "Sc'" => parameterTwist D Sc
local notation "F₀" => elvE D Sc' cutoff bound i Λ hab ≫ elvE D Sc' cutoff bound j Λ hbc ≫ elvE D Sc' cutoff bound i Λ hcd
local notation "a₀" => elvWeightSuffixCross D Sc' cutoff bound i j i Λ hab hbc hcd hbe hed
local notation "a₁" => elvWeightPrefixCross D Sc' cutoff bound j i i Λ hab hbe hab hbe hed
local notation "a₂" => elvWeightSuffixCross D Sc' cutoff bound j i i Λ hab hbe hed hbc hcd
local notation "b₀" => elvWeightPrefixCross D Sc' cutoff bound i j i Λ hab hbc haf hfc hcd
local notation "b₁" => elvWeightSuffixCross D Sc' cutoff bound i i j Λ haf hfc hcd hfc hcd
local notation "b₂" => elvWeightPrefixCross D Sc' cutoff bound i i j Λ haf hfc hab hbc hcd
local notation "x₀" => elvWeightTripleFirstDot D Sc' cutoff bound i j i Λ hab hbc hcd
local notation "x₁" => elvWeightTripleMiddleDot D Sc' cutoff bound i j i Λ hab hbc hcd
local notation "x₂" => elvWeightTripleLastDot D Sc' cutoff bound i j i Λ hab hbc hcd

/-- The corrected braid for the literal given weight crossings and dots.
The coefficients are Sc while the acting scalar family is parameterTwist Sc. -/
theorem elvActionCross_mixedBraid (hij : i ≠ j) :
    a₀ ≫ a₁ ≫ a₂ - b₀ ≫ b₁ ≫ b₂ =
      tripleDotCorrectionPolynomial (R := End F₀) D Sc i j x₀ x₁ x₂ := by
  apply family_correction_of_module_components D Sc i j a₀ a₁ a₂ b₀ b₁ b₂ x₀ x₁ x₂
  intro M ε
  by_cases hs : ∃ β, elvBlockSucc₃ D i j i Λ hab hbc hcd β = ε
  · obtain ⟨β, rfl⟩ := hs
    have h := elvWeightMixedBraid_module_polynomial D Sc cutoff bound i j Λ
      hab haf hbc hbe hfc hcd hed β hij M
    run_tac Lean.Elab.Tactic.withMainContext do
      let mut eh := Lean.Expr.const `True []
      for decl in ← Lean.getLCtx do
        eh := Lean.mkFVar decl.fvarId
      let et ← Lean.Meta.inferType eh
      let et ← Lean.instantiateMVars et
      let gt ← Lean.Elab.Tactic.getMainTarget
      let gt ← Lean.instantiateMVars gt
      let _ ← traceExprDifference et gt "root"
    fail "module endpoint diagnostic complete"
  · have hz := elvEFunctor_comp₃_isZero D Sc' cutoff bound i j i Λ hab hbc hcd ε hs M
    exact hz.eq_of_src _ _

end OddMath.QuiverHecke.ELVOld
