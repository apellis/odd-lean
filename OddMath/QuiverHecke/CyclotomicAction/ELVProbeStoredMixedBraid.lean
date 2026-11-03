/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionCorrectedGrid
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeReindexCrossing
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeAppendToDotUnit
import OddMath.QuiverHecke.CyclotomicAction.ELVOldTriplePolynomial

/-! # The corrected probe braid with seven prescribed stored append edges

Brundan–Ellis (1.9): the actual OLD fixed-content induction grid uses
arbitrary stored representatives at all six vertices. The literal OLD
coefficient braid supplies the source equation and the original-Sc
ordered correction uses the three independent chosen append dots.
No braid, naturality, comparison or inverse premise is supplied.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction ELVOld.CyclotomicCrossingTensor
universe u

private theorem stored_degree_congr
    {k C E : Type u} [CommRing k]
    [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
    {F G : C ⥤ E} {p q : ZMod 2} (hp : p = q)
    {γ : ∀ s, F.obj s ⟶ G.obj s} (hγ : IsSupernatural k p γ) : IsSupernatural k q γ := by
  cases hp
  exact hγ

private def storedEndForget
    {I X k : Type u} [AddCommGroup X] [CommRing k]
    (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cut : I → ℕ) (ν : List I)
    (v : OldContentCategory D Sc cut ν) : End v →ₐ[k] End v.obj :=
  AlgHom.ofLinearMap
    { toFun := fun f => f
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    rfl (fun _ _ => rfl)

private theorem storedEndForget_injective
    {I X k : Type u} [AddCommGroup X] [CommRing k]
    (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cut : I → ℕ) (ν : List I)
    (v : OldContentCategory D Sc cut ν) : Function.Injective (storedEndForget D Sc cut ν v) :=
  fun _ _ h => h

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (ν : List I) (i j : I) {νi νj νii νij νt : List I}
  (hI : (i :: ν).Perm νi) (hJ : (j :: ν).Perm νj)
  (hII : (i :: νi).Perm νii) (hIJ : (j :: νi).Perm νij) (hJI : (i :: νj).Perm νij)
  (hTopJ : (j :: νii).Perm νt) (hTopI : (i :: νij).Perm νt)
local notation "Sc'" => parameterTwist D Sc
local notation "cut" => probeCutoff D m
local notation "J" => oldContentAppendTo D Sc' cut ν i νi hI
local notation "K" => oldContentAppendTo D Sc' cut ν j νj hJ
local notation "U" => oldContentAppendTo D Sc' cut νi i νii hII
local notation "V" => oldContentAppendTo D Sc' cut νi j νij hIJ
local notation "W" => oldContentAppendTo D Sc' cut νj i νij hJI
local notation "L" => oldContentAppendTo D Sc' cut νii j νt hTopJ
local notation "M" => oldContentAppendTo D Sc' cut νij i νt hTopI
local notation "F₀" => (J ⋙ V) ⋙ M
local notation "σ" => oldAppendToCross D Sc' cut ν j i hI hJ hIJ hJI
local notation "σ'" => oldAppendToCross D Sc' cut ν i j hJ hI hJI hIJ
local notation "τ" => oldAppendToCross D Sc' cut ν i i hI hI hII hII
local notation "ρ" => oldAppendToCross D Sc' cut νi i j hIJ hII hTopI hTopJ
local notation "ρ'" => oldAppendToCross D Sc' cut νi j i hII hIJ hTopJ hTopI
local notation "ξ" => oldAppendToCross D Sc' cut νj i i hJI hJI hTopI hTopI
local notation "hσ" => stored_degree_congr (mul_comm (D.parity j) (D.parity i))
  (oldAppendToCross_supernatural D Sc' cut ν j i hI hJ hIJ hJI)
local notation "hσ'" => stored_degree_congr (mul_comm (D.parity i) (D.parity j))
  (oldAppendToCross_supernatural D Sc' cut ν i j hJ hI hJI hIJ)
local notation "hτ" => oldAppendToCross_supernatural D Sc' cut ν i i hI hI hII hII
local notation "hρ" => stored_degree_congr (mul_comm (D.parity i) (D.parity j))
  (oldAppendToCross_supernatural D Sc' cut νi i j hIJ hII hTopI hTopJ)
local notation "hρ'" => stored_degree_congr (mul_comm (D.parity j) (D.parity i))
  (oldAppendToCross_supernatural D Sc' cut νi j i hII hIJ hTopJ hTopI)
local notation "hξ" => oldAppendToCross_supernatural D Sc' cut νj i i hJI hJI hTopI hTopI
local notation "hα" => probeAppendToDot_supernatural D Sc' m ν i νi hI
local notation "hβ" => probeAppendToDot_supernatural D Sc' m νi j νij hIJ
local notation "hγ" => probeAppendToDot_supernatural D Sc' m νij i νt hTopI

/-- The stored content certificates disappear under the faithful full OLD inclusion. -/
theorem probeStoredMixedBraid_source (hne : i ≠ j) (s : OldContentCategory D Sc' cut ν) :
    (show End ((F₀).obj s) from (M).map (σ s) ≫ ξ ((K).obj s) ≫ (M).map (σ' s)) -
      (show End ((F₀).obj s) from ρ ((J).obj s) ≫ (L).map (τ s) ≫ ρ' ((J).obj s)) =
      tripleDotCorrectionPolynomial D Sc' (R := End ((F₀).obj s)) i j
        (probeAppendToDot D Sc' m νij i νt hTopI ((J ⋙ V).obj s))
        ((M).map (probeAppendToDot D Sc' m νi j νij hIJ ((J).obj s)))
        ((M).map ((V).map (probeAppendToDot D Sc' m ν i νi hI s))) := by
  apply storedEndForget_injective D Sc' cut νt ((F₀).obj s)
  rw [map_sub, tripleDotCorrectionPolynomial_map]
  change (triplePrefix D Sc' cut i j i s.obj ≫ tripleSuffix D Sc' cut j i i s.obj ≫
      triplePrefix D Sc' cut j i i s.obj) -
    (tripleSuffix D Sc' cut i j i s.obj ≫ triplePrefix D Sc' cut i i j s.obj ≫
      tripleSuffix D Sc' cut i i j s.obj) =
    tripleDotCorrectionPolynomial D Sc'
      (R := End ((tripleAppend D Sc' cut i j i).obj s.obj)) i j
      (tripleLastDot D Sc' cut i j s.obj) (tripleMiddleDot D Sc' cut i j s.obj)
      (tripleFirstDot D Sc' cut i j s.obj)
  exact (ELVOld.CyclotomicCrossingTensor.tripleCross_braid_correction D Sc' cut i j hne s.obj).trans
    (tripleCorrection_tripleDots D Sc' cut i j s.obj)

/-- The actual seven-edge OLD probe grid at its prescribed stored lists. -/
def probeOldStoredMixedBraid
    (N : Superfunctor k (OldContentCategory D Sc' cut ν) (SVec k)) :
    End (induced M (induced V (induced J N))) :=
  gridMixedBraid J K U V W L M D i j hσ hσ' hτ hρ hρ' hξ N

/-- The whole stored-target probe braid has the original-Sc correction in its three independent dots. -/
theorem probeOldStoredMixedBraid_polynomial (hne : i ≠ j)
    (N : Superfunctor k (OldContentCategory D Sc' cut ν) (SVec k)) :
    probeOldStoredMixedBraid D Sc m ν i j hI hJ hII hIJ hJI hTopJ hTopI N =
      tripleDotCorrectionPolynomial D Sc (R := End (induced M (induced V (induced J N)))) i j
        ((induction M).map ((induction V).map (dotEnd J hα N)))
        ((induction M).map (dotEnd V hβ ((induction J).obj N)))
        (dotEnd M hγ ((induction V).obj ((induction J).obj N))) :=
  gridMixedBraid_polynomial J K U V W L M D Sc i j hσ hσ' hτ hρ hρ' hξ hα hβ hγ hne
    (probeStoredMixedBraid_source D Sc m ν i j hI hJ hII hIJ hJI hTopJ hTopI hne) N

end OddMath.QuiverHecke
