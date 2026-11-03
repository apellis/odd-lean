import OddMath.QuiverHecke.CyclotomicAction.ELVContentCoefficientCaps
import OddMath.QuiverHecke.CyclotomicAction.ELVContentUpperCharts
import OddMath.QuiverHecke.CyclotomicAction.ELVUnitCoefficientRows

/-! # The given coefficient-cap window on the old empty-content category

The empty local inverse in Brundan's Theorem 4.3 uses the ordinary unit
columns and the given inverse coefficients over the full old coefficient
algebra. The selected native charts retain that window on every input
module; no scalar-evaluation or regular-module restriction is imposed.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open BalancedInduction CyclotomicCrossingTensor CyclotomicCrossingTensor.TensorMatrixCoordinates
universe u

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

private theorem coefficient_unitDot_window
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (i : I)
    (t : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (t.word : Multiset I))
    (r : Fin (contentUnitCount D cutoff i (t.word : Multiset I)))
    (a : ℕ) (ha : a < contentUnitCount D cutoff i (t.word : Multiset I)) (b : M.obj t) :
    moduleUnitCoefficient D Sc cutoff M i t hh r
      (unitDotLinear (append D Sc cutoff i) (oldAppendDot_supernatural D Sc cutoff i) M a t b) =
      if a = r.val then b else 0 := by
  have h := moduleUnitCoefficient_dot_window D Sc cutoff M i t hh r a ha b
  change moduleUnitCoefficient D Sc cutoff M i t hh r
    (((actualInductionDot D Sc cutoff i M ((append D Sc cutoff i).obj t)) ^ a)
      (((adjunctionUnit (append D Sc cutoff i)).app M).total t b)) = _ at h
  rw [adjunctionUnit_total_apply] at h
  exact h

private theorem coefficient_map_unitDot_window
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (i : I)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (([] : List I) : Multiset I))
    (r : Fin (contentUnitCount D cutoff i (([] : List I) : Multiset I)))
    (a : ℕ) (ha : a < contentUnitCount D cutoff i (([] : List I) : Multiset I))
    (b : M.obj (OldCategory.mk [])) :
    (contentUnitCoefficientMap D Sc cutoff M i [] hh r).total
      (OldContentCategory.mk (OldCategory.mk []) (List.Perm.refl []))
      (unitDotLinear (append D Sc cutoff i) (oldAppendDot_supernatural D Sc cutoff i) M a
        (OldCategory.mk []) b) = if a = r.val then b else 0 := by
  have hr := contentUnitCoefficientMap_vacuum_total D Sc cutoff M i hh r
    (unitDotLinear (append D Sc cutoff i) (oldAppendDot_supernatural D Sc cutoff i) M a
      (OldCategory.mk []) b)
  have hw := coefficient_unitDot_window D Sc cutoff M i (OldCategory.mk []) hh r a ha b
  run_tac do
    let hr ← getLocalDeclFromUserName `hr
    let hw ← getLocalDeclFromUserName `hw
    let th ← instantiateMVars (← inferType hr.toExpr)
    let tw ← instantiateMVars (← inferType hw.toExpr)
    let rec diff (fuel : Nat) (a b : Lean.Expr) (path : String) : Lean.Meta.MetaM Unit := do
      if a == b then return
      match fuel with
      | 0 => logInfo m!"DIFF depth {path}: {a} / {b}"
      | n+1 =>
        match a, b with
        | .app f x, .app g y =>
          if f == g then diff n x y (path ++ ".arg") else diff n f g (path ++ ".fn")
        | .mdata _ x, _ => diff n x b path
        | _, .mdata _ y => diff n a y path
        | .lam _ t x _, .lam _ u y _ =>
          if t == u then diff n x y (path ++ ".body") else diff n t u (path ++ ".type")
        | .const n _, .const m _ => logInfo m!"DIFF {path}: const {n} / {m}"
        | _, _ => logInfo m!"DIFF {path}: {a} / {b}"
    diff 200 th.getAppArgs[2]! tw.getAppArgs[1]! "rhs/lhs"
  exact hr.trans hw

variable (N : Superfunctor k (OldContentCategory D Sc cutoff []) (SVec k)) (i : I)
local notation "K" => oldContentAppend D Sc cutoff [] i
local notation "Q" => oldContentInclusion D Sc cutoff []
local notation "J" => append D Sc cutoff i
local notation "G" => induced Q N
local notation "count" => contentUnitCount D cutoff i (([] : List I) : Multiset I)

private theorem vacuum_height : 0 ≤ contentCrossingHeight D cutoff i (([] : List I) : Multiset I) := by
  simp [contentCrossingHeight]

/-- Over the full old coefficient algebra, the selected native coefficient
cap extracts its given unit/dot column on every empty-content input module. -/
theorem contentVacuumCoefficientCap_unitDot (w : OldContentCategory D Sc cutoff [])
    (r : Fin count) (a : ℕ) (ha : a < count) (b : N.obj w) :
    (contentCoefficientCap D Sc cutoff [] i N (vacuum_height D cutoff i) r).total w
      (unitDotLinear K (oldContentAppendDot_supernatural D Sc cutoff [] i) N a w b) =
      if a = r.val then b else 0 := by
  rcases w with ⟨⟨word⟩, hw⟩
  have hn : word = [] := List.perm_nil.mp hw
  subst word
  let w : OldContentCategory D Sc cutoff [] := ⟨⟨[]⟩, hw⟩
  let v := oldContentValueChart D Sc cutoff [] N w
  let e := oldContentFEChart D Sc cutoff [] i N w
  apply v.injective
  have hc := LinearMap.congr_fun
    (contentCoefficientCap_total D Sc cutoff [] i N (vacuum_height D cutoff i) r w)
    (unitDotLinear K (oldContentAppendDot_supernatural D Sc cutoff [] i) N a w b)
  change (contentCoefficientCap D Sc cutoff [] i N (vacuum_height D cutoff i) r).total w _ =
    v.symm ((contentUnitCoefficientMap D Sc cutoff G i [] (vacuum_height D cutoff i) r).total w
      (e (unitDotLinear K (oldContentAppendDot_supernatural D Sc cutoff [] i) N a w b))) at hc
  rw [hc, LinearEquiv.apply_symm_apply]
  have he := oldContentFEChart_unitDot D Sc cutoff [] i N w a b
  change e (unitDotLinear K (oldContentAppendDot_supernatural D Sc cutoff [] i) N a w b) =
    unitDotLinear J (oldAppendDot_supernatural D Sc cutoff i) G a w.obj (v b) at he
  rw [he]
  have h := coefficient_map_unitDot_window D Sc cutoff G i
    (vacuum_height D cutoff i) r a ha (v b)
  by_cases har : a = r.val
  · simpa only [har, ↓reduceIte] using h
  · simpa only [har, ↓reduceIte, map_zero] using h

end OddMath.QuiverHecke.ELVOld
