import OddMath.QuiverHecke.CyclotomicAction.ELVProbeStoredBraid

/-! # The uncorrected evaluated braid at arbitrary stored representatives

Brundan–Ellis (1.9): the twelve chosen evaluated append edges retain the
normalized OLD braid, with independently negative equal pair crossings.
All maps are the prescribed probe crossing components; no relation premise
is supplied in the final statement.
-/
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction ELVOld.CyclotomicCrossingTensor
universe u
private theorem rectangle_degree_congr
    {k C A B E : Type u} [CommRing k]
    [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
    [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
    [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    (K : C ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
    (L : A ⥤ E) [L.Additive] [L.Linear k] [IsSuperfunctor k L]
    (M : B ⥤ E) [M.Additive] [M.Linear k] [IsSuperfunctor k M]
    {p q : ZMod 2} (hp : p = q) {γ : ∀ s, (J ⋙ L).obj s ⟶ (K ⋙ M).obj s}
    (hγ : IsSupernatural k p γ) (hδ : IsSupernatural k q γ)
    (N : Superfunctor k C (SVec k)) :
    rectangularCrossComponent J K L M hγ N = rectangularCrossComponent J K L M hδ N := by
  cases hp
  rfl

private theorem appendTo_obj_obj
    {I X k : Type u} [AddCommGroup X] [CommRing k]
    (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
    (ν : List I) (i : I) (μ : List I) (h : (i :: ν).Perm μ)
    (N : ProbeEvaluatedModules D Sc m ν) :
    ((probeEvaluatedAppendTo D Sc m ν i μ h).obj N).obj =
      induced (oldContentAppendTo D Sc (probeCutoff D m) ν i μ h) N.obj := rfl

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
local notation "EAi" => probeEvaluatedAppendTo D Sc' m ν i νi hI
local notation "EAj" => probeEvaluatedAppendTo D Sc' m ν j νj hJ
local notation "EAl" => probeEvaluatedAppendTo D Sc' m ν l νl hL
local notation "EBij_i" => probeEvaluatedAppendTo D Sc' m νi j νij hIJ
local notation "EBij_j" => probeEvaluatedAppendTo D Sc' m νj i νij hJI
local notation "EBil_i" => probeEvaluatedAppendTo D Sc' m νi l νil hIL
local notation "EBil_l" => probeEvaluatedAppendTo D Sc' m νl i νil hLI
local notation "EBjl_j" => probeEvaluatedAppendTo D Sc' m νj l νjl hJL
local notation "EBjl_l" => probeEvaluatedAppendTo D Sc' m νl j νjl hLJ
local notation "ECl" => probeEvaluatedAppendTo D Sc' m νij l νt hTopL
local notation "ECj" => probeEvaluatedAppendTo D Sc' m νil j νt hTopJ
local notation "ECi" => probeEvaluatedAppendTo D Sc' m νjl i νt hTopI

/-- The first literal evaluated three-crossing path. -/
def probeStoredBraidLeft (N : ProbeEvaluatedModules D Sc' m ν) :
    (ECi).obj ((EBjl_l).obj ((EAl).obj N)) ⟶ (ECl).obj ((EBij_i).obj ((EAi).obj N)) :=
  ((if j = l then (-1 : k) else 1) • (ECi).map
    (probeAppendToCrossComponent D Sc' m ν l j hJ hL hJL hLJ N)) ≫
  ((if i = l then (-1 : k) else 1) •
    probeAppendToCrossComponent D Sc' m νj l i hJI hJL hTopL hTopI ((EAj).obj N)) ≫
  ((if i = j then (-1 : k) else 1) • (ECl).map
    (probeAppendToCrossComponent D Sc' m ν j i hI hJ hIJ hJI N))

/-- The second path has independent intermediate representatives at the other cube vertices. -/
def probeStoredBraidRight (N : ProbeEvaluatedModules D Sc' m ν) :
    (ECi).obj ((EBjl_l).obj ((EAl).obj N)) ⟶ (ECl).obj ((EBij_i).obj ((EAi).obj N)) :=
  ((if i = j then (-1 : k) else 1) •
    probeAppendToCrossComponent D Sc' m νl j i hLI hLJ hTopJ hTopI ((EAl).obj N)) ≫
  ((if i = l then (-1 : k) else 1) • (ECj).map
    (probeAppendToCrossComponent D Sc' m ν l i hI hL hIL hLI N)) ≫
  ((if j = l then (-1 : k) else 1) •
    probeAppendToCrossComponent D Sc' m νi l j hIJ hIL hTopL hTopJ ((EAi).obj N))

/-- The first evaluated path retains the entire OLD module map. -/
theorem probeStoredBraidLeft_eq (N : ProbeEvaluatedModules D Sc' m ν) :
    (probeStoredBraidLeft D Sc m ν i j l hI hJ hL hIJ hJI hJL hLJ hTopL hTopI N).hom =
      probeOldStoredBraidLeft D Sc m ν i j l hI hJ hL hIJ hJI hJL hLJ hTopL hTopI N.obj := by
  simp only [probeStoredBraidLeft, appendTo_obj_obj]
  unfold probeOldStoredBraidLeft
  apply congrArg₂ (fun f g => f ≫ g)
  · exact congrArg (fun f => (if j = l then (-1 : k) else 1) • (induction Ci).map f)
      (rectangle_degree_congr Aj Al Bjl_j Bjl_l (mul_comm (D.parity l) (D.parity j)) _ _ _)
  · apply congrArg₂ (fun f g => f ≫ g)
    · exact congrArg (fun f => (if i = l then (-1 : k) else 1) • f)
        (rectangle_degree_congr Bij_j Bjl_j Cl Ci (mul_comm (D.parity l) (D.parity i)) _ _ _)
    · exact congrArg (fun f => (if i = j then (-1 : k) else 1) • (induction Cl).map f)
        (rectangle_degree_congr Ai Aj Bij_i Bij_j (mul_comm (D.parity j) (D.parity i)) _ _ _)

/-- The second evaluated path retains the same independent OLD arrows. -/
theorem probeStoredBraidRight_eq (N : ProbeEvaluatedModules D Sc' m ν) :
    (probeStoredBraidRight D Sc m ν i j l hI hL hIJ hIL hLI hLJ hTopL hTopJ hTopI N).hom =
      probeOldStoredBraidRight D Sc m ν i j l hI hL hIJ hIL hLI hLJ hTopL hTopJ hTopI N.obj := by
  simp only [probeStoredBraidRight, appendTo_obj_obj]
  unfold probeOldStoredBraidRight
  apply congrArg₂ (fun f g => f ≫ g)
  · exact congrArg (fun f => (if i = j then (-1 : k) else 1) • f)
      (rectangle_degree_congr Bil_l Bjl_l Cj Ci (mul_comm (D.parity j) (D.parity i)) _ _ _)
  · apply congrArg₂ (fun f g => f ≫ g)
    · exact congrArg (fun f => (if i = l then (-1 : k) else 1) • (induction Cj).map f)
        (rectangle_degree_congr Ai Al Bil_i Bil_l (mul_comm (D.parity l) (D.parity i)) _ _ _)
    · exact congrArg (fun f => (if j = l then (-1 : k) else 1) • f)
        (rectangle_degree_congr Bij_i Bil_i Cl Cj (mul_comm (D.parity l) (D.parity j)) _ _ _)

/-- The prescribed evaluated crossing components satisfy the uncorrected braid. -/
theorem probeStoredBraid (hb : ¬ (i = l ∧ i ≠ j)) (N : ProbeEvaluatedModules D Sc' m ν) :
    probeStoredBraidLeft D Sc m ν i j l hI hJ hL hIJ hJI hJL hLJ hTopL hTopI N =
      probeStoredBraidRight D Sc m ν i j l hI hL hIJ hIL hLI hLJ hTopL hTopJ hTopI N := by
  apply InducedCategory.hom_ext
  rw [probeStoredBraidLeft_eq, probeStoredBraidRight_eq]
  exact probeOldStoredBraid D Sc m ν i j l hI hJ hL hIJ hJI hIL hLI hJL hLJ hTopL hTopJ hTopI hb N.obj

end OddMath.QuiverHecke
