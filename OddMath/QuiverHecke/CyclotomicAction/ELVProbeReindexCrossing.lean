import OddMath.QuiverHecke.CyclotomicAction.ELVProbeReindexTensors
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

attribute [local irreducible] oldAppendToCrossLinear oldAppendPairReindexLinear
  oldAppendReindexIso oldAppendPairReindexIso

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

theorem oldAppendReindexCross_right_tensor
    (N : Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k))
    (s : OldContentCategory D Sc cutoff ν) (t : OldContentCategory D Sc cutoff (i :: ν))
    (w : OldContentCategory D Sc cutoff ν₂) (a : (K₀).obj s ⟶ t)
    (g : (M₀).obj t ⟶ (Q₂inv).obj w) (b : N.obj s) :
    oldAppendToCrossLinear D Sc cutoff ν i j hj hi hL hM ((R₀).obj N) w
        (S N w (tensor M₀ (induced K₀ N).toFunctor (w := (Q₂inv).obj w) t g
          (tensor K₀ N.toFunctor (w := t) s a b))) =
      oldAppendReindexCrossTensor D Sc cutoff ν i j hj hi hL hM N s t w a g b := by
  have hp := oldAppendPairReindexIso_hom_tensor D Sc cutoff r₀ i j ri hi hi rM hM h₂ N s t w a g b
  have hcross := oldAppendToCrossLinear_tensor D Sc cutoff ν i j hj hi hL hM ((R₀).obj N)
    ((Q₀).obj s) ((Qi).obj t) w
    (show (K).obj ((Q₀).obj s) ⟶ (Qi).obj t from a)
    (show (M).obj ((Qi).obj t) ⟶ w from g) b
  have hv := congrArg (oldAppendToCrossLinear D Sc cutoff ν i j hj hi hL hM ((R₀).obj N) w) hp
  exact hv.trans (hcross.trans (by rfl))

/-- The selected pair comparisons intertwine the prescribed positive crossing on all vectors. -/
theorem oldAppendReindexCrossLinear
    (N : Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k))
    (w : OldContentCategory D Sc cutoff ν₂) :
    T N w ∘ₗ χ₀ N ((Q₂inv).obj w) =
      oldAppendToCrossLinear D Sc cutoff ν i j hj hi hL hM ((R₀).obj N) w ∘ₗ S N w := by
  apply doubleHom_ext K₀ M₀ N (w := (Q₂inv).obj w)
  intro s t a g b
  simp only [LinearMap.comp_apply]
  exact (oldAppendReindexCross_left_tensor D Sc cutoff ν i j hj hi hL hM N s t w a g b).trans
    (oldAppendReindexCross_right_tensor D Sc cutoff ν i j hj hi hL hM N s t w a g b).symm

local notation "eS" => oldAppendPairReindexIso D Sc cutoff r₀ i j ri hi hi rM hM h₂
local notation "eT" => oldAppendPairReindexIso D Sc cutoff r₀ j i rj hj hj rL hL h₂
local notation "hc₀" => oldAppendToCross_supernatural D Sc cutoff ν i j rj ri rL rM

private theorem crossing_restriction_total
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (Q : C ⥤ A) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
    {P P' : Superfunctor k A (SVec k)} (f : P ⟶ P') (w : C) :
    ((restriction Q).map f).total w = f.total (Q.obj w) := rfl

/-- The whole supernatural crossing square uses the selected pair isomorphisms. -/
theorem oldAppendReindexCross
    (N : Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k)) :
    (restriction Q₂inv).map (rectangularCrossComponent J₀ K₀ L₀ M₀ hc₀ N) ≫
        (eT).hom.app N =
      (eS).hom.app N ≫ rectangularCrossComponent J K L M hc ((R₀).obj N) := by
  let V := (oldModuleReindex D Sc cutoff h₂).obj (induced M₀ (induced K₀ N))
  let W := induced L (induced J ((R₀).obj N))
  apply HomogeneousSuperfunctorIso.total_ext (F := V) (G := W)
  intro w
  rw [Superfunctor.comp_total, Superfunctor.comp_total,
    crossing_restriction_total Q₂inv (rectangularCrossComponent J₀ K₀ L₀ M₀ hc₀ N) w]
  have hraw := oldAppendReindexCrossLinear D Sc cutoff ν i j hj hi hL hM N w
  unfold oldAppendPairReindexLinear oldAppendToCrossLinear at hraw
  exact hraw

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

theorem probeAppendToCross_mem :
    probeAppendToCross D Sc m ν i j hj hi hL hM ∈ parity (R := k) _ _
      (D.parity i * D.parity j) :=
  Superfunctor.mem_parity_iff_isHomogeneous.mpr
    (fullLiftTrans_homogeneous (ProbeEvaluatesCoefficients D m Sc ν)
      (ProbeEvaluatesCoefficients D m Sc ν₂)
      (appendToCrossSource_closed D Sc m ν i j hi hM)
      (appendToCrossTarget_closed D Sc m ν i j hj hL) _
      (rectangularCrossComponent_supernatural J K L M hc).toSuperNatTrans_isHomogeneous)

theorem probeAppendToCross_native_app (p : ZMod 2) (N : ProbeEvaluatedModules D Sc m ν) :
    ((probeAppendToCross D Sc m ν i j hj hi hL hM).app p N).hom =
      (rectangularCrossComponent_supernatural J K L M hc).toSuperNatTrans.app p N.obj := rfl

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

/-- At cons representatives this is the existing selected evaluated crossing. -/
theorem probeAppendToCross_cons :
    probeAppendToCross D Sc m ν i j (List.Perm.refl _) (List.Perm.refl _)
      (List.Perm.refl _) (List.Perm.swap i j ν) = probeEvaluatedDistinctCross D Sc m ν i j := by
  apply Superfunctor.hom_ext
  intro p N
  apply InducedCategory.hom_ext
  rfl

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

/-- The selected pair square for the actual full evaluated probe crossing. -/
theorem probeAppendReindexCross (N : ProbeEvaluatedModules D Sc m ν) :
    (probeEvaluatedReindex D Sc m h₂).map
        ((probeAppendToCross D Sc m ν i j rj ri rL rM).total N) ≫ (ET).hom.app N =
      (ES).hom.app N ≫
        (probeAppendToCross D Sc m ν i j hj hi hL hM).total
          ((probeEvaluatedReindex D Sc m r₀).obj N) := by
  apply InducedCategory.hom_ext
  change (restriction Q₂inv).map (((probeAppendToCross D Sc m ν i j rj ri rL rM).total N).hom) ≫
      (eT).hom.app N.obj =
    (eS).hom.app N.obj ≫
      (((probeAppendToCross D Sc m ν i j hj hi hL hM).total
        ((probeEvaluatedReindex D Sc m r₀).obj N)).hom)
  rw [probeAppendToCross_native_total D Sc m ν i j rj ri rL rM N,
    probeAppendToCross_native_total D Sc m ν i j hj hi hL hM
      ((probeEvaluatedReindex D Sc m r₀).obj N)]
  exact oldAppendReindexCross D Sc cut ν i j hj hi hL hM N.obj

end OddMath.QuiverHecke
