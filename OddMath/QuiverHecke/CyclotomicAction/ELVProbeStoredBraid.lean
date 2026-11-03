import OddMath.QuiverHecke.CyclotomicAction.ELVInductionBraidCube
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeReindexCrossing
import OddMath.QuiverHecke.CyclotomicAction.ELVOldMulticolourBraid

/-! # The uncorrected probe braid at twelve stored append edges

Brundan–Ellis (1.9): arbitrary representatives at all eight content
vertices retain the literal quotient braid. Each equal pair is negative
and each distinct pair positive. No braid or comparison premise is added.
-/
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction ELVOld.CyclotomicCrossingTensor
universe u
private theorem cube_degree_congr
    {k C E : Type u} [CommRing k]
    [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
    {F G : C ⥤ E} {p q : ZMod 2} (hp : p = q)
    {γ : ∀ s, F.obj s ⟶ G.obj s} (hγ : IsSupernatural k p γ) : IsSupernatural k q γ := by
  cases hp
  exact hγ
private theorem cube_scaled_paths {k : Type u} [CommRing k]
    {C : Type*} [Category* C] [Preadditive C] [Linear k C]
    {X₀ X₁ X₂ X₃ X₄ X₅ : C} (a b c : k)
    (f₀ : X₀ ⟶ X₁) (f₁ : X₁ ⟶ X₂) (f₂ : X₂ ⟶ X₃)
    (g₀ : X₀ ⟶ X₄) (g₁ : X₄ ⟶ X₅) (g₂ : X₅ ⟶ X₃)
    (hb : f₀ ≫ f₁ ≫ f₂ = g₀ ≫ g₁ ≫ g₂) :
    (a • f₀) ≫ (b • f₁) ≫ (c • f₂) = (c • g₀) ≫ (b • g₁) ≫ (a • g₂) := by
  simp only [Linear.smul_comp, Linear.comp_smul, smul_smul]
  rw [hb]
  congr 1
  ring

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (ν : List I) (i j l : I) {νi νj νl νij νil νjl νt : List I}
  (hI : (i :: ν).Perm νi) (hJ : (j :: ν).Perm νj) (hL : (l :: ν).Perm νl)
  (hIJ : (j :: νi).Perm νij) (hJI : (i :: νj).Perm νij)
  (hIL : (l :: νi).Perm νil) (hLI : (i :: νl).Perm νil)
  (hJL : (l :: νj).Perm νjl) (hLJ : (j :: νl).Perm νjl)
  (hTopL : (l :: νij).Perm νt) (hTopJ : (j :: νil).Perm νt) (hTopI : (i :: νjl).Perm νt)
local notation "Sc'" => parameterTwist D Sc
local notation "cut" => probeCutoff D m
local notation "Ai" => oldContentAppendTo D Sc' cut ν i νi hI
local notation "Aj" => oldContentAppendTo D Sc' cut ν j νj hJ
local notation "Al" => oldContentAppendTo D Sc' cut ν l νl hL
local notation "Bij_i" => oldContentAppendTo D Sc' cut νi j νij hIJ
local notation "Bij_j" => oldContentAppendTo D Sc' cut νj i νij hJI
local notation "Bil_i" => oldContentAppendTo D Sc' cut νi l νil hIL
local notation "Bil_l" => oldContentAppendTo D Sc' cut νl i νil hLI
local notation "Bjl_j" => oldContentAppendTo D Sc' cut νj l νjl hJL
local notation "Bjl_l" => oldContentAppendTo D Sc' cut νl j νjl hLJ
local notation "Cl" => oldContentAppendTo D Sc' cut νij l νt hTopL
local notation "Cj" => oldContentAppendTo D Sc' cut νil j νt hTopJ
local notation "Ci" => oldContentAppendTo D Sc' cut νjl i νt hTopI
local notation "α₀" => oldAppendToCross D Sc' cut ν j i hI hJ hIJ hJI
local notation "hα₀" => cube_degree_congr (mul_comm (D.parity j) (D.parity i))
  (oldAppendToCross_supernatural D Sc' cut ν j i hI hJ hIJ hJI)
local notation "α₁" => oldAppendToCross D Sc' cut νj l i hJI hJL hTopL hTopI
local notation "hα₁" => cube_degree_congr (mul_comm (D.parity l) (D.parity i))
  (oldAppendToCross_supernatural D Sc' cut νj l i hJI hJL hTopL hTopI)
local notation "α₂" => oldAppendToCross D Sc' cut ν l j hJ hL hJL hLJ
local notation "hα₂" => cube_degree_congr (mul_comm (D.parity l) (D.parity j))
  (oldAppendToCross_supernatural D Sc' cut ν l j hJ hL hJL hLJ)
local notation "β₀" => oldAppendToCross D Sc' cut νi l j hIJ hIL hTopL hTopJ
local notation "hβ₀" => cube_degree_congr (mul_comm (D.parity l) (D.parity j))
  (oldAppendToCross_supernatural D Sc' cut νi l j hIJ hIL hTopL hTopJ)
local notation "β₁" => oldAppendToCross D Sc' cut ν l i hI hL hIL hLI
local notation "hβ₁" => cube_degree_congr (mul_comm (D.parity l) (D.parity i))
  (oldAppendToCross_supernatural D Sc' cut ν l i hI hL hIL hLI)
local notation "β₂" => oldAppendToCross D Sc' cut νl j i hLI hLJ hTopJ hTopI
local notation "hβ₂" => cube_degree_congr (mul_comm (D.parity j) (D.parity i))
  (oldAppendToCross_supernatural D Sc' cut νl j i hLI hLJ hTopJ hTopI)

/-- The twelve certificates retain the quotient's literal source equation. -/
theorem probeStoredBraid_source (hb : ¬ (i = l ∧ i ≠ j))
    (s : OldContentCategory D Sc' cut ν) :
    (Cl).map (α₀ s) ≫ α₁ ((Aj).obj s) ≫ (Ci).map (α₂ s) =
      β₀ ((Ai).obj s) ≫ (Cj).map (β₁ s) ≫ β₂ ((Al).obj s) := by
  change triplePrefix D Sc' cut i j l s.obj ≫ tripleSuffix D Sc' cut j i l s.obj ≫
      triplePrefix D Sc' cut j l i s.obj =
    tripleSuffix D Sc' cut i j l s.obj ≫ triplePrefix D Sc' cut i l j s.obj ≫
      tripleSuffix D Sc' cut l i j s.obj
  exact ELVOld.CyclotomicCrossingTensor.tripleCross_braid D Sc' cut i j l hb s.obj

/-- The first path uses the three separately normalized stored pair crossings. -/
def probeOldStoredBraidLeft (N : Superfunctor k (OldContentCategory D Sc' cut ν) (SVec k)) :
    induced Ci (induced Bjl_l (induced Al N)) ⟶ induced Cl (induced Bij_i (induced Ai N)) :=
  ((if j = l then (-1 : k) else 1) •
    (induction Ci).map (rectangularCrossComponent Aj Al Bjl_j Bjl_l hα₂ N)) ≫
  ((if i = l then (-1 : k) else 1) •
    rectangularCrossComponent Bij_j Bjl_j Cl Ci hα₁ ((induction Aj).obj N)) ≫
  ((if i = j then (-1 : k) else 1) •
    (induction Cl).map (rectangularCrossComponent Ai Aj Bij_i Bij_j hα₀ N))

/-- The reverse three-pair path uses the other intermediate stored vertices. -/
def probeOldStoredBraidRight (N : Superfunctor k (OldContentCategory D Sc' cut ν) (SVec k)) :
    induced Ci (induced Bjl_l (induced Al N)) ⟶ induced Cl (induced Bij_i (induced Ai N)) :=
  ((if i = j then (-1 : k) else 1) •
    rectangularCrossComponent Bil_l Bjl_l Cj Ci hβ₂ ((induction Al).obj N)) ≫
  ((if i = l then (-1 : k) else 1) •
    (induction Cj).map (rectangularCrossComponent Ai Al Bil_i Bil_l hβ₁ N)) ≫
  ((if j = l then (-1 : k) else 1) •
    rectangularCrossComponent Bij_i Bil_i Cl Cj hβ₀ ((induction Ai).obj N))

/-- Arbitrary stored representatives preserve the uncorrected normalized braid. -/
theorem probeOldStoredBraid (hb : ¬ (i = l ∧ i ≠ j))
    (N : Superfunctor k (OldContentCategory D Sc' cut ν) (SVec k)) :
    probeOldStoredBraidLeft D Sc m ν i j l hI hJ hL hIJ hJI hJL hLJ hTopL hTopI N =
      probeOldStoredBraidRight D Sc m ν i j l hI hL hIJ hIL hLI hLJ hTopL hTopJ hTopI N := by
  have hpos := inductionCube_braid Ai Aj Al Bij_i Bij_j Bil_i Bil_l Bjl_j Bjl_l Cl Cj Ci
    hα₀ hα₁ hα₂ hβ₀ hβ₁ hβ₂
    (probeStoredBraid_source D Sc m ν i j l hI hJ hL hIJ hJI hIL hLI hJL hLJ hTopL hTopJ hTopI hb) N
  exact cube_scaled_paths (if j = l then (-1 : k) else 1) (if i = l then (-1 : k) else 1)
    (if i = j then (-1 : k) else 1) _ _ _ _ _ _ hpos

end OddMath.QuiverHecke
