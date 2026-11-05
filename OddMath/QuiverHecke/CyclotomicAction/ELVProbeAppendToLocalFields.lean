import OddMath.QuiverHecke.CyclotomicAction.ELVProbeReindexMate
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeAppendToAdjunction
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeAppendToDotUnit
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionGridRouquierFields

/-! # Chosen local fields at stored probe representatives

Brundan–Ellis (1.7)–(1.8), (1.13)–(1.14): the stored-target evaluated
append functors retain the physical dots, negative crossing and ordered
ordinary-adjunction mate. All homogeneous components are identified with
the specified OLD module maps.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction CyclotomicAction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (ν : List I) (i : I) {ν₁ ν₂ : List I}
  (h₁ : (i :: ν).Perm ν₁) (h₂ : (i :: ν₁).Perm ν₂)
local notation "cut" => probeCutoff D m
local notation "J" => oldContentAppendTo D Sc cut ν i ν₁ h₁
local notation "K" => oldContentAppendTo D Sc cut ν₁ i ν₂ h₂
local notation "hγ" => oldAppendToEqualCross_supernatural D Sc cut ν i h₁ h₂
local notation "P₀" => ProbeEvaluatesCoefficients D m Sc ν
local notation "P₁" => ProbeEvaluatesCoefficients D m Sc ν₁
local notation "P₂" => ProbeEvaluatesCoefficients D m Sc ν₂
local notation "E₀" => probeEvaluatedAppendTo D Sc m ν i ν₁ h₁
local notation "E₁" => probeEvaluatedAppendTo D Sc m ν₁ i ν₂ h₂

private theorem appendPair_closed
    (N : Superfunctor k (OldContentCategory D Sc cut ν) (SVec k)) (hN : P₀ N) :
    P₂ (((inductionModuleCell (k := k) J) ≫ inductionModuleCell (k := k) K).obj N) :=
  ((E₀ ⋙ E₁).obj ⟨N, hN⟩).property

/-- The chosen negative crossing at two actual stored-target append functors. -/
def probeAppendToEqualCross :
    End (⟨E₀ ⋙ E₁⟩ : Superfunctor k (ProbeEvaluatedModules D Sc m ν)
      (ProbeEvaluatedModules D Sc m ν₂)) :=
  fullLiftTrans P₀ P₂ (appendPair_closed D Sc m ν i h₁ h₂)
    (appendPair_closed D Sc m ν i h₁ h₂) (inductionModuleCross J K hγ)

theorem probeAppendToEqualCross_total (N : ProbeEvaluatedModules D Sc m ν) :
    ((probeAppendToEqualCross D Sc m ν i h₁ h₂).total N).hom =
      (inductionModuleCross J K hγ).total N.obj := rfl

theorem probeAppendToInductionDot_app (q : ZMod 2) (N : ProbeEvaluatedModules D Sc m ν) :
    ((probeAppendToInductionDot D Sc m ν i ν₁ h₁).app q N).hom =
      (inductionModuleDot J (probeAppendToDot_supernatural D Sc m ν i ν₁ h₁)).app q N.obj := by
  change (if q = D.parity i then probeAppendToDotComponent D Sc m ν i ν₁ h₁ N else 0).hom =
    if q = D.parity i then transformComponent (probeAppendToDot_supernatural D Sc m ν i ν₁ h₁) N.obj else 0
  split_ifs <;> rfl

/-- Ordered powers of the chosen dot on stored-target evaluated induction. -/
abbrev probeAppendToDotPower (n : ℕ) :
    End (⟨E₀⟩ : Superfunctor k (ProbeEvaluatedModules D Sc m ν) (ProbeEvaluatedModules D Sc m ν₁)) :=
  SKM.rouquierPower (a := probeEvaluatedTarget D Sc m ν) (b := probeEvaluatedTarget D Sc m ν₁)
    (E := probeAppendToE D Sc m ν i ν₁ h₁) (probeAppendToInductionDot D Sc m ν i ν₁ h₁) n

/-- The corresponding ordered powers in the OLD module categories. -/
abbrev oldAppendToDotPower (n : ℕ) : End (inductionModuleCell (k := k) J) :=
  SKM.rouquierPower
    (a := inductionModulePiCategory (k := k) (OldContentCategory D Sc cut ν))
    (b := inductionModulePiCategory (k := k) (OldContentCategory D Sc cut ν₁))
    (E := inductionModuleCell (k := k) J)
    (inductionModuleDot J (probeAppendToDot_supernatural D Sc m ν i ν₁ h₁)) n

/-- Every homogeneous component of every ordered dot power is retained. -/
theorem probeAppendToDotPower_app (n : ℕ) (q : ZMod 2) (N : ProbeEvaluatedModules D Sc m ν) :
    ((probeAppendToDotPower D Sc m ν i h₁ n).app q N).hom =
      (oldAppendToDotPower D Sc m ν i h₁ n).app q N.obj := by
  induction n generalizing q with
  | zero =>
    change (if q = 0 then 𝟙 ((E₀).obj N) else 0).hom =
      if q = 0 then 𝟙 ((inductionModuleCell (k := k) J).obj N.obj) else 0
    split_ifs <;> rfl
  | succ n ih =>
    change ((probeAppendToDotPower D Sc m ν i h₁ n).app 0 N).hom ≫
        ((probeAppendToInductionDot D Sc m ν i ν₁ h₁).app q N).hom +
      ((probeAppendToDotPower D Sc m ν i h₁ n).app 1 N).hom ≫
        ((probeAppendToInductionDot D Sc m ν i ν₁ h₁).app (q + 1) N).hom =
      (oldAppendToDotPower D Sc m ν i h₁ n).app 0 N.obj ≫
        (inductionModuleDot J (probeAppendToDot_supernatural D Sc m ν i ν₁ h₁)).app q N.obj +
      (oldAppendToDotPower D Sc m ν i h₁ n).app 1 N.obj ≫
        (inductionModuleDot J (probeAppendToDot_supernatural D Sc m ν i ν₁ h₁)).app (q + 1) N.obj
    rw [ih 0, ih 1, probeAppendToInductionDot_app, probeAppendToInductionDot_app]

local notation "R₀" => probeEvaluatedTarget D Sc m ν
local notation "R₁" => probeEvaluatedTarget D Sc m ν₁
local notation "R₂" => probeEvaluatedTarget D Sc m ν₂
local notation "e₀" => probeAppendToE D Sc m ν i ν₁ h₁
local notation "f₀" => probeAppendToF D Sc m ν i ν₁ h₁
local notation "e₁" => probeAppendToE D Sc m ν₁ i ν₂ h₂
local notation "f₁" => probeAppendToF D Sc m ν₁ i ν₂ h₂
local notation "A₀" => probeAppendToRightAdjunction D Sc m ν i ν₁ h₁
local notation "A₁" => probeAppendToRightAdjunction D Sc m ν₁ i ν₂ h₂

/-- The ordered mate of the selected negative crossing and selected right adjunctions. -/
def probeAppendToMate :
    (⟨probeEvaluatedRestrictTo D Sc m ν i ν₁ h₁ ⋙ E₀⟩ :
      Superfunctor k (ProbeEvaluatedModules D Sc m ν₁) (ProbeEvaluatedModules D Sc m ν₁)) ⟶
    ⟨E₁ ⋙ probeEvaluatedRestrictTo D Sc m ν₁ i ν₂ h₂⟩ :=
  SKM.rouquierMate (a := R₀) (b := R₁) (c := R₂)
    («E₁» := e₀) («F₁» := f₀) («E₂» := e₁) («F₂» := f₁)
    A₀ A₁ (probeAppendToEqualCross D Sc m ν i h₁ h₂)

/-- Every component of the ordered mate is the prescribed OLD component. -/
theorem probeAppendToMate_app (q : ZMod 2) (N : ProbeEvaluatedModules D Sc m ν₁) :
    ((probeAppendToMate D Sc m ν i h₁ h₂).app q N).hom =
      (SKM.rouquierMate (inductionModuleAdjunction (k := k) J)
        (inductionModuleAdjunction (k := k) K) (inductionModuleCross J K hγ)).app q N.obj := by
  unfold probeAppendToMate
  erw [SKM.rouquierMate_piscat_app, SKM.rouquierMate_piscat_app]
  rfl

end OddMath.QuiverHecke
