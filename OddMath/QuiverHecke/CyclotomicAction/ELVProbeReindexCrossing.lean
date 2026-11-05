import OddMath.QuiverHecke.CyclotomicAction.ELVProbeReindexPair
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeCanonicalContent
import OddMath.QuiverHecke.CyclotomicAction.ELVContentDistinctMate
import OddMath.QuiverHecke.CyclotomicAction.ELVRectangularMateIso
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeAppendToAdjunction
import OddMath.QuiverHecke.CyclotomicAction.ELVPiSCatRectangularMate
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightCrossMate

/-! # The chosen OLD crossing under pair representative changes

Brundan–Ellis (1.7)–(1.8), (1.12): compare the positive rectangular
crossing through the selected lower/upper append comparisons. The
coefficient crossing is the same OLD quotient arrow at every stored list.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction ELVOld.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (ν : List I) (i j : I) {νj νi ν₂ : List I}
  (hj : (j :: ν).Perm νj) (hi : (i :: ν).Perm νi)
  (hL : (i :: νj).Perm ν₂) (hM : (j :: νi).Perm ν₂)
local notation "J" => oldContentAppendTo D Sc cutoff ν j νj hj
local notation "K" => oldContentAppendTo D Sc cutoff ν i νi hi
local notation "L" => oldContentAppendTo D Sc cutoff νj i ν₂ hL
local notation "M" => oldContentAppendTo D Sc cutoff νi j ν₂ hM

/-- The physical positive crossing at four prescribed stored contents. -/
def oldAppendToCross (s : OldContentCategory D Sc cutoff ν) :
    ((J) ⋙ (L)).obj s ⟶ ((K) ⋙ (M)).obj s :=
  Distinct.crossComponent D Sc cutoff i j s.obj

theorem oldAppendToCross_supernatural :
    IsSupernatural k (D.parity i * D.parity j) (oldAppendToCross D Sc cutoff ν i j hj hi hL hM) where
  mem s := (Distinct.cross_supernatural D Sc cutoff i j).mem s.obj
  naturality hf := (Distinct.cross_supernatural D Sc cutoff i j).naturality hf
local notation "hc" => oldAppendToCross_supernatural D Sc cutoff ν i j hj hi hL hM

/-- The prescribed flatten-cross-expand map in its fixed two coend carriers. -/
def oldAppendToCrossLinear
    (N : Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k))
    (w : OldContentCategory D Sc cutoff ν₂) :
    Obj M (induced K N).toFunctor w →ₗ[k] Obj L (induced J N).toFunctor w :=
  (rectangularCrossComponent J K L M hc N).total w

local notation "r₀" => List.Perm.refl ν
local notation "rj" => List.Perm.refl (j :: ν)
local notation "ri" => List.Perm.refl (i :: ν)
local notation "rL" => List.Perm.refl (i :: j :: ν)
local notation "rM" => List.Perm.swap i j ν
local notation "h₂" => List.Perm.trans (List.Perm.cons i hj) hL
local notation "J₀" => oldContentAppendTo D Sc cutoff ν j (j :: ν) rj
local notation "K₀" => oldContentAppendTo D Sc cutoff ν i (i :: ν) ri
local notation "L₀" => oldContentAppendTo D Sc cutoff (j :: ν) i (i :: j :: ν) rL
local notation "M₀" => oldContentAppendTo D Sc cutoff (i :: ν) j (i :: j :: ν) rM
local notation "Q₀" => oldContentReindex D Sc cutoff r₀
local notation "Qi" => oldContentReindex D Sc cutoff hi
local notation "Q₂inv" => oldContentReindex D Sc cutoff (List.Perm.symm h₂)
local notation "R₀" => oldModuleReindex D Sc cutoff r₀
local notation "χ₀" => oldAppendToCrossLinear D Sc cutoff ν i j rj ri rL rM
local notation "α₀" => oldAppendToCross D Sc cutoff ν i j rj ri rL rM
local notation "S" => oldAppendPairReindexLinear D Sc cutoff r₀ i j ri hi hi rM hM h₂
local notation "T" => oldAppendPairReindexLinear D Sc cutoff r₀ j i rj hj hj rL hL h₂

attribute [local irreducible] oldAppendToCrossLinear oldAppendPairReindexLinear
  oldAppendReindexIso oldAppendPairReindexIso

local notation "eS" => oldAppendPairReindexIso D Sc cutoff r₀ i j ri hi hi rM hM h₂
local notation "eT" => oldAppendPairReindexIso D Sc cutoff r₀ j i rj hj hj rL hL h₂
local notation "hc₀" => oldAppendToCross_supernatural D Sc cutoff ν i j rj ri rL rM

end OddMath.QuiverHecke

namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction CyclotomicAction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (ν : List I) (i j : I) {νj νi ν₂ : List I}
  (hj : (j :: ν).Perm νj) (hi : (i :: ν).Perm νi)
  (hL : (i :: νj).Perm ν₂) (hM : (j :: νi).Perm ν₂)
local notation "cut" => probeCutoff D m
local notation "J" => oldContentAppendTo D Sc cut ν j νj hj
local notation "K" => oldContentAppendTo D Sc cut ν i νi hi
local notation "L" => oldContentAppendTo D Sc cut νj i ν₂ hL
local notation "M" => oldContentAppendTo D Sc cut νi j ν₂ hM
local notation "hc" => oldAppendToCross_supernatural D Sc cut ν i j hj hi hL hM
local notation "Src" => probeEvaluatedAppendTo D Sc m ν i νi hi ⋙
  probeEvaluatedAppendTo D Sc m νi j ν₂ hM
local notation "Tgt" => probeEvaluatedAppendTo D Sc m ν j νj hj ⋙
  probeEvaluatedAppendTo D Sc m νj i ν₂ hL

/-- The prescribed positive crossing component in the full evaluated categories. -/
def probeAppendToCrossComponent (N : ProbeEvaluatedModules D Sc m ν) : (Src).obj N ⟶ (Tgt).obj N :=
  ⟨rectangularCrossComponent J K L M hc N.obj⟩

private theorem appendToCrossSource_closed
    (N : Superfunctor k (OldContentCategory D Sc cut ν) (SVec k))
    (hN : ProbeEvaluatesCoefficients D m Sc ν N) :
    ProbeEvaluatesCoefficients D m Sc ν₂ ((induction K ⋙ induction M).obj N) :=
  ((Src).obj ⟨N, hN⟩).property

private theorem appendToCrossTarget_closed
    (N : Superfunctor k (OldContentCategory D Sc cut ν) (SVec k))
    (hN : ProbeEvaluatesCoefficients D m Sc ν N) :
    ProbeEvaluatesCoefficients D m Sc ν₂ ((induction J ⋙ induction L).obj N) :=
  ((Tgt).obj ⟨N, hN⟩).property

/-- The whole positive stored-target crossing, natural on even and odd input maps. -/
def probeAppendToCross :
    (⟨Src⟩ : Superfunctor k (ProbeEvaluatedModules D Sc m ν) (ProbeEvaluatedModules D Sc m ν₂)) ⟶
      (⟨Tgt⟩ : Superfunctor k (ProbeEvaluatedModules D Sc m ν) (ProbeEvaluatedModules D Sc m ν₂)) :=
  fullLiftTrans (ProbeEvaluatesCoefficients D m Sc ν) (ProbeEvaluatesCoefficients D m Sc ν₂)
    (appendToCrossSource_closed D Sc m ν i j hi hM)
    (appendToCrossTarget_closed D Sc m ν i j hj hL)
    (rectangularCrossComponent_supernatural J K L M hc).toSuperNatTrans

theorem probeAppendToCross_native_total (N : ProbeEvaluatedModules D Sc m ν) :
    ((probeAppendToCross D Sc m ν i j hj hi hL hM).total N).hom =
      rectangularCrossComponent J K L M hc N.obj := by
  change (rectangularCrossComponent_supernatural J K L M hc).toSuperNatTrans.total N.obj = _
  exact HomogeneousSuperfunctorIso.homogeneous_total
    (F := (⟨induction K ⋙ induction M⟩ : Superfunctor k
      (Superfunctor k (OldContentCategory D Sc cut ν) (SVec k))
      (Superfunctor k (OldContentCategory D Sc cut ν₂) (SVec k))))
    (G := (⟨induction J ⋙ induction L⟩ : Superfunctor k
      (Superfunctor k (OldContentCategory D Sc cut ν) (SVec k))
      (Superfunctor k (OldContentCategory D Sc cut ν₂) (SVec k))))
    (rectangularCrossComponent_supernatural J K L M hc) N.obj

theorem probeAppendToCross_total (N : ProbeEvaluatedModules D Sc m ν) :
    (probeAppendToCross D Sc m ν i j hj hi hL hM).total N =
      probeAppendToCrossComponent D Sc m ν i j hj hi hL hM N :=
  InducedCategory.hom_ext (probeAppendToCross_native_total D Sc m ν i j hj hi hL hM N)

local notation "r₀" => List.Perm.refl ν
local notation "rj" => List.Perm.refl (j :: ν)
local notation "ri" => List.Perm.refl (i :: ν)
local notation "rL" => List.Perm.refl (i :: j :: ν)
local notation "rM" => List.Perm.swap i j ν
local notation "h₂" => List.Perm.trans (List.Perm.cons i hj) hL
local notation "Q₂inv" => oldContentReindex D Sc cut (List.Perm.symm h₂)
local notation "J₀" => oldContentAppendTo D Sc cut ν j (j :: ν) rj
local notation "K₀" => oldContentAppendTo D Sc cut ν i (i :: ν) ri
local notation "L₀" => oldContentAppendTo D Sc cut (j :: ν) i (i :: j :: ν) rL
local notation "M₀" => oldContentAppendTo D Sc cut (i :: ν) j (i :: j :: ν) rM
local notation "eS" => oldAppendPairReindexIso D Sc cut r₀ i j ri hi hi rM hM h₂
local notation "eT" => oldAppendPairReindexIso D Sc cut r₀ j i rj hj hj rL hL h₂
local notation "ES" => probeAppendPairReindexIso D Sc m r₀ i j ri hi hi rM hM h₂
local notation "ET" => probeAppendPairReindexIso D Sc m r₀ j i rj hj hj rL hL h₂
local notation "hc₀" => oldAppendToCross_supernatural D Sc cut ν i j rj ri rL rM

end OddMath.QuiverHecke
