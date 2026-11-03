import OddMath.QuiverHecke.CyclotomicAction.ELVProbeReindexPair
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeEvaluatedDistinctCrossing

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

theorem oldAppendToCrossLinear_tensor
    (N : Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k))
    (s : OldContentCategory D Sc cutoff ν) (t : OldContentCategory D Sc cutoff νi)
    (w : OldContentCategory D Sc cutoff ν₂) (a : (K).obj s ⟶ t)
    (g : (M).obj t ⟶ w) (b : N.obj s) :
    oldAppendToCrossLinear D Sc cutoff ν i j hj hi hL hM N w
        (tensor M (induced K N).toFunctor (w := w) t g
          (tensor K N.toFunctor (w := t) s a b)) =
      tensor L (induced J N).toFunctor (w := w) ((J).obj s)
        (oldAppendToCross D Sc cutoff ν i j hj hi hL hM s ≫
          twist k (D.parity i * D.parity j) ((M).map a ≫ g))
        (tensor J N.toFunctor (w := (J).obj s) s (𝟙 _) b) :=
  rectangularCrossComponent_total_tensor J K L M hc N s t w a g b

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

/-- The common canonical tensor, retaining the physical crossing and full twist. -/
def oldAppendReindexCrossTensor
    (N : Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k))
    (s : OldContentCategory D Sc cutoff ν) (t : OldContentCategory D Sc cutoff (i :: ν))
    (w : OldContentCategory D Sc cutoff ν₂) (a : (K₀).obj s ⟶ t)
    (g : (M₀).obj t ⟶ (Q₂inv).obj w) (b : N.obj s) :
    Obj L (induced J ((R₀).obj N)).toFunctor w :=
  tensor L (induced J ((R₀).obj N)).toFunctor (w := w) ((J).obj ((Q₀).obj s))
    (oldAppendToCross D Sc cutoff ν i j hj hi hL hM ((Q₀).obj s) ≫
      twist k (D.parity i * D.parity j)
        ((M).map (show (K).obj ((Q₀).obj s) ⟶ (Qi).obj t from a) ≫
          (show (M).obj ((Qi).obj t) ⟶ w from g)))
    (tensor J ((R₀).obj N).toFunctor (w := (J).obj ((Q₀).obj s)) ((Q₀).obj s) (𝟙 _) b)

attribute [local irreducible] oldAppendToCrossLinear oldAppendPairReindexLinear oldAppendReindexIso

theorem oldAppendReindexCross_left_tensor
    (N : Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k))
    (s : OldContentCategory D Sc cutoff ν) (t : OldContentCategory D Sc cutoff (i :: ν))
    (w : OldContentCategory D Sc cutoff ν₂) (a : (K₀).obj s ⟶ t)
    (g : (M₀).obj t ⟶ (Q₂inv).obj w) (b : N.obj s) :
    T N w (χ₀ N ((Q₂inv).obj w)
        (tensor M₀ (induced K₀ N).toFunctor (w := (Q₂inv).obj w) t g
          (tensor K₀ N.toFunctor (w := t) s a b))) =
      oldAppendReindexCrossTensor D Sc cutoff ν i j hj hi hL hM N s t w a g b := by
  have hcross := oldAppendToCrossLinear_tensor D Sc cutoff ν i j rj ri rL rM N s t
    ((Q₂inv).obj w) a g b
  have hp := oldAppendPairReindexIso_hom_tensor D Sc cutoff r₀ j i rj hj hj rL hL h₂ N s
    ((J₀).obj s) w (𝟙 _)
    (α₀ s ≫ twist k (D.parity i * D.parity j) ((M₀).map a ≫ g)) b
  have hv := congrArg (T N w) hcross
  exact hv.trans (hp.trans (by rfl))

end OddMath.QuiverHecke
