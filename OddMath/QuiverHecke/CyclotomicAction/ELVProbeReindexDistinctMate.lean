import OddMath.QuiverHecke.CyclotomicAction.ELVProbeReindexCrossing
import OddMath.QuiverHecke.CyclotomicAction.ELVContentDistinctMate
import OddMath.QuiverHecke.CyclotomicAction.ELVRectangularMateIso

/-! # The prescribed distinct mate at stored OLD contents

Brundan–Ellis (1.12): transport the positive cup-crossing-cap through
the specified lower and upper append-adjunction comparisons. The
single-coend formula retains every coefficient twist.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction
universe u
attribute [local irreducible] oldAppendReindexLinear oldAppendReindexIso orderedRectangularMateLinear

private theorem rectangular_square_point {k V W V' W' : Type*} [CommRing k]
    [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
    [AddCommMonoid V'] [Module k V'] [AddCommMonoid W'] [Module k W']
    (a : V →ₗ[k] W) (b : V' →ₗ[k] W') (l : V →ₗ[k] V') (r : W →ₗ[k] W')
    (v : V) (w : W) (v' : V') (w' : W')
    (ha : a v = w) (hr : r w = w') (hl : l v = v') (hb : b v' = w') :
    (r ∘ₗ a) v = (b ∘ₗ l) v :=
  (congrArg r ha).trans (hr.trans ((congrArg b hl).trans hb).symm)

private theorem iso_total_bijective
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {F G : Superfunctor k C (SVec k)} (e : F ≅ G) (w : C) :
    Function.Bijective (e.hom.total w) := by
  have hl : Function.LeftInverse (e.inv.total w) (e.hom.total w) := by
    intro x
    have h := congrArg (fun f : End F => f.total w x) e.hom_inv_id
    rw [Superfunctor.comp_total] at h
    change e.inv.total w (e.hom.total w x) = (LinearMap.id + 0) x at h
    simpa only [add_zero, LinearMap.id_apply] using h
  have hr : Function.RightInverse (e.inv.total w) (e.hom.total w) := by
    intro x
    have h := congrArg (fun f : End G => f.total w x) e.inv_hom_id
    rw [Superfunctor.comp_total] at h
    change e.hom.total w (e.inv.total w x) = (LinearMap.id + 0) x at h
    simpa only [add_zero, LinearMap.id_apply] using h
  exact ⟨hl.injective, hr.surjective⟩

private theorem bijective_of_linear_square {k V W V' W' : Type*} [CommRing k]
    [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
    [AddCommMonoid V'] [Module k V'] [AddCommMonoid W'] [Module k W']
    (a : V →ₗ[k] W) (b : V' →ₗ[k] W') (l : V →ₗ[k] V') (r : W →ₗ[k] W')
    (hl : Function.Bijective l) (hr : Function.Bijective r) (ha : Function.Bijective a)
    (hsq : r ∘ₗ a = b ∘ₗ l) : Function.Bijective b := by
  apply (Function.Bijective.of_comp_iff (b : V' → W') hl).mp
  change Function.Bijective ((b ∘ₗ l) : V → W')
  rw [← hsq]
  exact hr.comp ha

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (ν : List I) (i j : I) {νj νi ν₂ : List I}
  (hj : (j :: ν).Perm νj) (hi : (i :: ν).Perm νi)
  (hL : (i :: νj).Perm ν₂) (hM : (j :: νi).Perm ν₂)
local notation "J₀" => oldContentAppendTo D Sc cutoff ν j (j :: ν) (List.Perm.refl _)
local notation "K₀" => oldContentAppendTo D Sc cutoff ν i (i :: ν) (List.Perm.refl _)
local notation "L₀" => oldContentAppendTo D Sc cutoff (j :: ν) i (i :: j :: ν) (List.Perm.refl _)
local notation "M₀" => oldContentAppendTo D Sc cutoff (i :: ν) j (i :: j :: ν) (List.Perm.swap i j ν)
local notation "J" => oldContentAppendTo D Sc cutoff ν j νj hj
local notation "K" => oldContentAppendTo D Sc cutoff ν i νi hi
local notation "L" => oldContentAppendTo D Sc cutoff νj i ν₂ hL
local notation "M" => oldContentAppendTo D Sc cutoff νi j ν₂ hM
local notation "Qj" => oldContentReindex D Sc cutoff hj
local notation "QiInv" => oldContentReindex D Sc cutoff hi.symm
local notation "Rj" => oldModuleReindex D Sc cutoff hj
local notation "h₂" => List.Perm.trans (List.Perm.cons i hj) hL
local notation "hc₀" => oldAppendToCross_supernatural D Sc cutoff ν i j
  (List.Perm.refl (j :: ν)) (List.Perm.refl (i :: ν))
  (List.Perm.refl (i :: j :: ν)) (List.Perm.swap i j ν)
local notation "hc" => oldAppendToCross_supernatural D Sc cutoff ν i j hj hi hL hM

/-- The lower-i comparison keeps the prescribed lower-j restriction. -/
def oldReindexDistinctSourceLinear
    (N : Superfunctor k (OldContentCategory D Sc cutoff (j :: ν)) (SVec k))
    (t : OldContentCategory D Sc cutoff νi) :
    Obj K₀ ((restriction J₀).obj N).toFunctor ((QiInv).obj t) →ₗ[k]
      Obj K ((restriction J).obj ((Rj).obj N)).toFunctor t :=
  oldAppendReindexLinear D Sc cutoff (List.Perm.refl ν) i
    (List.Perm.refl (i :: ν)) hi hi ((restriction J₀).obj N) t

/-- The upper-i comparison keeps the prescribed upper-j restriction. -/
def oldReindexDistinctTargetLinear
    (N : Superfunctor k (OldContentCategory D Sc cutoff (j :: ν)) (SVec k))
    (t : OldContentCategory D Sc cutoff νi) :
    Obj L₀ N.toFunctor ((M₀).obj ((QiInv).obj t)) →ₗ[k]
      Obj L ((Rj).obj N).toFunctor ((M).obj t) :=
  oldAppendReindexLinear D Sc cutoff hj i (List.Perm.refl (i :: j :: ν)) hL h₂ N ((M).obj t)

theorem oldReindexDistinctSourceLinear_tensor
    (N : Superfunctor k (OldContentCategory D Sc cutoff (j :: ν)) (SVec k))
    (s : OldContentCategory D Sc cutoff ν) (t : OldContentCategory D Sc cutoff νi)
    (g : (K₀).obj s ⟶ (QiInv).obj t) (v : N.obj ((J₀).obj s)) :
    oldReindexDistinctSourceLinear D Sc cutoff ν i j hj hi N t
        (tensor K₀ ((restriction J₀).obj N).toFunctor (w := (QiInv).obj t) s g v) =
      tensor K ((restriction J).obj ((Rj).obj N)).toFunctor (w := t) s g v := by
  have h := oldAppendReindexIso_hom_tensor D Sc cutoff (List.Perm.refl ν) i
    (List.Perm.refl (i :: ν)) hi hi ((restriction J₀).obj N) s t g v
  set_option backward.dsimp.instances true in
    dsimp only [oldReindexDistinctSourceLinear, oldModuleReindex] at h ⊢
  convert! h using 1

theorem oldReindexDistinctTargetLinear_tensor
    (N : Superfunctor k (OldContentCategory D Sc cutoff (j :: ν)) (SVec k))
    (s : OldContentCategory D Sc cutoff (j :: ν)) (t : OldContentCategory D Sc cutoff νi)
    (g : (L₀).obj s ⟶ (M₀).obj ((QiInv).obj t)) (v : N.obj s) :
    oldReindexDistinctTargetLinear D Sc cutoff ν i j hj hi hL hM N t
        (tensor L₀ N.toFunctor (w := (M₀).obj ((QiInv).obj t)) s g v) =
      tensor L ((Rj).obj N).toFunctor (w := (M).obj t) ((Qj).obj s) g v := by
  let g' : (L₀).obj s ⟶ (oldContentReindex D Sc cutoff (List.Perm.symm h₂)).obj ((M).obj t) := g
  have h := oldAppendReindexIso_hom_tensor D Sc cutoff hj i
    (List.Perm.refl (i :: j :: ν)) hL h₂ N s ((M).obj t) g' v
  set_option backward.dsimp.instances true in
    dsimp only [oldReindexDistinctTargetLinear, oldModuleReindex, g'] at h ⊢
  convert! h using 1

/-- The positive mate intertwines the selected source and target comparisons on all vectors. -/
theorem oldReindexDistinctLinear_mate
    (N : Superfunctor k (OldContentCategory D Sc cutoff (j :: ν)) (SVec k))
    (t : OldContentCategory D Sc cutoff νi) :
    oldReindexDistinctTargetLinear D Sc cutoff ν i j hj hi hL hM N t ∘ₗ
        orderedRectangularMateLinear J₀ K₀ L₀ M₀ hc₀ N ((QiInv).obj t) =
      orderedRectangularMateLinear J K L M hc ((Rj).obj N) t ∘ₗ
        oldReindexDistinctSourceLinear D Sc cutoff ν i j hj hi N t := by
  let N₀ := N
  let N₁ := (Rj).obj N
  let t₀ := (QiInv).obj t
  let V := Obj K₀ ((restriction J₀).obj N₀).toFunctor t₀
  let W := Obj L₀ N₀.toFunctor ((M₀).obj t₀)
  let V' := Obj K ((restriction J).obj N₁).toFunctor t
  let W' := Obj L N₁.toFunctor ((M).obj t)
  let a : V →ₗ[k] W := orderedRectangularMateLinear J₀ K₀ L₀ M₀ hc₀ N₀ t₀
  let b : V' →ₗ[k] W' := orderedRectangularMateLinear J K L M hc N₁ t
  let l : V →ₗ[k] V' := oldReindexDistinctSourceLinear D Sc cutoff ν i j hj hi N t
  let r : W →ₗ[k] W' := oldReindexDistinctTargetLinear D Sc cutoff ν i j hj hi hL hM N t
  change r ∘ₗ a = b ∘ₗ l
  apply hom_ext K₀ ((restriction J₀).obj N₀).toFunctor (w := t₀)
  intro s g v
  have h₀ := orderedRectangularMateLinear_tensor J₀ K₀ L₀ M₀ hc₀ N₀ s t₀ g v
  have h₃ := orderedRectangularMateLinear_tensor J K L M hc N₁ s t g v
  let v₀ : V := tensor K₀ ((restriction J₀).obj N₀).toFunctor (w := t₀) s g v
  let z₀ : W := tensor L₀ N₀.toFunctor (w := (M₀).obj t₀) ((J₀).obj s)
    (oldAppendToCross D Sc cutoff ν i j (List.Perm.refl _) (List.Perm.refl _)
      (List.Perm.refl _) (List.Perm.swap i j ν) s ≫
      twist k (D.parity i * D.parity j) ((M₀).map g)) v
  let v₁ : V' := tensor K ((restriction J).obj N₁).toFunctor (w := t) s g v
  let z₁ : W' := tensor L N₁.toFunctor (w := (M).obj t) ((J).obj s)
    (oldAppendToCross D Sc cutoff ν i j hj hi hL hM s ≫
      twist k (D.parity i * D.parity j) ((M).map g)) v
  have ha : a v₀ = z₀ := by convert! h₀ using 1
  have hr : r z₀ = z₁ := by
    dsimp only [r, z₀, z₁, N₀, N₁]
    rw [oldReindexDistinctTargetLinear_tensor]
    rfl
  have hl : l v₀ = v₁ := by
    dsimp only [l, v₀, v₁, N₀, N₁]
    rw [oldReindexDistinctSourceLinear_tensor]
  have hb : b v₁ = z₁ := by convert! h₃ using 1
  exact rectangular_square_point (k := k) (V := V) (W := W) (V' := V') (W' := W')
    a b l r v₀ z₀ v₁ z₁ ha hr hl hb

theorem oldReindexDistinctSourceLinear_bijective
    (N : Superfunctor k (OldContentCategory D Sc cutoff (j :: ν)) (SVec k))
    (t : OldContentCategory D Sc cutoff νi) :
    Function.Bijective (oldReindexDistinctSourceLinear D Sc cutoff ν i j hj hi N t) := by
  unfold oldReindexDistinctSourceLinear oldAppendReindexLinear
  let U := (restriction J₀).obj N
  exact iso_total_bijective
    (F := (induction K₀ ⋙ oldModuleReindex D Sc cutoff hi).obj U)
    (G := (oldModuleReindex D Sc cutoff (List.Perm.refl ν) ⋙ induction K).obj U)
    ((oldAppendReindexIso D Sc cutoff (List.Perm.refl ν) i
      (List.Perm.refl (i :: ν)) hi hi).app U) t

theorem oldReindexDistinctTargetLinear_bijective
    (N : Superfunctor k (OldContentCategory D Sc cutoff (j :: ν)) (SVec k))
    (t : OldContentCategory D Sc cutoff νi) :
    Function.Bijective (oldReindexDistinctTargetLinear D Sc cutoff ν i j hj hi hL hM N t) := by
  unfold oldReindexDistinctTargetLinear oldAppendReindexLinear
  exact iso_total_bijective
    (F := (induction L₀ ⋙ oldModuleReindex D Sc cutoff h₂).obj N)
    (G := (oldModuleReindex D Sc cutoff hj ⋙ induction L).obj N)
    ((oldAppendReindexIso D Sc cutoff hj i (List.Perm.refl (i :: j :: ν)) hL h₂).app N)
    ((M).obj t)

/-- The existing OLD PBW inverse makes the stored-target mate bijective on reindexed inputs. -/
theorem oldAppendToDistinctMateLinear_bijective_reindex (hij : i ≠ j)
    (N : Superfunctor k (OldContentCategory D Sc cutoff (j :: ν)) (SVec k))
    (t : OldContentCategory D Sc cutoff νi) :
    Function.Bijective (orderedRectangularMateLinear J K L M hc ((Rj).obj N) t) := by
  have hstd : Function.Bijective (orderedRectangularMateLinear J₀ K₀ L₀ M₀ hc₀ N ((QiInv).obj t)) :=
    oldContentDistinctMateLinear_bijective D Sc cutoff ν i j hij N ((QiInv).obj t)
  exact bijective_of_linear_square
    (orderedRectangularMateLinear J₀ K₀ L₀ M₀ hc₀ N ((QiInv).obj t))
    (orderedRectangularMateLinear J K L M hc ((Rj).obj N) t)
    (oldReindexDistinctSourceLinear D Sc cutoff ν i j hj hi N t)
    (oldReindexDistinctTargetLinear D Sc cutoff ν i j hj hi hL hM N t)
    (oldReindexDistinctSourceLinear_bijective D Sc cutoff ν i j hj hi N t)
    (oldReindexDistinctTargetLinear_bijective D Sc cutoff ν i j hj hi hL hM N t) hstd
    (oldReindexDistinctLinear_mate D Sc cutoff ν i j hj hi hL hM N t)

/-- All stored-target inputs are covered by the strict reindex equivalence. -/
theorem oldAppendToDistinctMateLinear_bijective (hij : i ≠ j)
    (N : Superfunctor k (OldContentCategory D Sc cutoff νj) (SVec k))
    (t : OldContentCategory D Sc cutoff νi) :
    Function.Bijective (orderedRectangularMateLinear J K L M hc N t) := by
  let N₀ := (oldModuleReindex D Sc cutoff hj.symm).obj N
  have hb := oldAppendToDistinctMateLinear_bijective_reindex D Sc cutoff ν i j hj hi hL hM hij N₀ t
  have hN : (Rj).obj N₀ = N := rfl
  exact Eq.mp (congrArg (fun P : Superfunctor k (OldContentCategory D Sc cutoff νj) (SVec k) =>
    Function.Bijective (orderedRectangularMateLinear J K L M hc P t)) hN) hb

/-- The actual positive stored-target mate with its constructed OLD inverse. -/
def oldAppendToDistinctMateModuleIso (hij : i ≠ j)
    (N : Superfunctor k (OldContentCategory D Sc cutoff νj) (SVec k)) :
    induced K ((restriction J).obj N) ≅ (restriction M).obj (induced L N) :=
  rectangularMateModuleIso J K L M hc N
    (fun t => oldAppendToDistinctMateLinear_bijective D Sc cutoff ν i j hj hi hL hM hij N t)

theorem oldAppendToDistinctMateModuleIso_hom (hij : i ≠ j)
    (N : Superfunctor k (OldContentCategory D Sc cutoff νj) (SVec k)) :
    (oldAppendToDistinctMateModuleIso D Sc cutoff ν i j hj hi hL hM hij N).hom =
      orderedRectangularMateComponent J K L M hc N :=
  rectangularMateModuleIso_hom J K L M hc N _

theorem oldAppendToDistinctMateModuleIso_inv_mem (hij : i ≠ j)
    (N : Superfunctor k (OldContentCategory D Sc cutoff νj) (SVec k)) :
    (oldAppendToDistinctMateModuleIso D Sc cutoff ν i j hj hi hL hM hij N).inv ∈
      parity (R := k) _ _ (D.parity i * D.parity j) :=
  rectangularMateModuleIso_inv_mem J K L M hc N _

/-- The inverse is natural in every stored-target input-module map. -/
def oldAppendToDistinctMateFunctorIso (hij : i ≠ j) :
    rectangularMateSourceFunctor (k := k) J K ≅ rectangularMateTargetFunctor (k := k) L M :=
  rectangularMateFunctorIso J K L M hc
    (fun N t => oldAppendToDistinctMateLinear_bijective D Sc cutoff ν i j hj hi hL hM hij N t)

theorem oldAppendToDistinctMateFunctorIso_hom (hij : i ≠ j) :
    (oldAppendToDistinctMateFunctorIso D Sc cutoff ν i j hj hi hL hM hij).hom =
      rectangularMateHom J K L M hc :=
  rectangularMateFunctorIso_hom J K L M hc _

theorem oldAppendToDistinctMateFunctorIso_inv_mem (hij : i ≠ j) :
    (oldAppendToDistinctMateFunctorIso D Sc cutoff ν i j hj hi hL hM hij).inv ∈
      parity (R := k) _ _ (D.parity i * D.parity j) :=
  rectangularMateFunctorIso_inv_mem J K L M hc _

end OddMath.QuiverHecke

namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction CyclotomicAction
open BicategoryStruct
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
local notation "S" => probeEvaluatedRestrictTo D Sc m ν j νj hj ⋙
  probeEvaluatedAppendTo D Sc m ν i νi hi
local notation "T" => probeEvaluatedAppendTo D Sc m νj i ν₂ hL ⋙
  probeEvaluatedRestrictTo D Sc m νi j ν₂ hM
local notation "P" => ProbeEvaluatesCoefficients D m Sc νj
local notation "Q" => ProbeEvaluatesCoefficients D m Sc νi

private theorem appendToMateSource_closed
    (N : Superfunctor k (OldContentCategory D Sc cut νj) (SVec k)) (hN : P N) :
    Q ((rectangularMateSourceFunctor (k := k) J K).obj N) :=
  ((S).obj ⟨N, hN⟩).property

private theorem appendToMateTarget_closed
    (N : Superfunctor k (OldContentCategory D Sc cut νj) (SVec k)) (hN : P N) :
    Q ((rectangularMateTargetFunctor (k := k) L M).obj N) :=
  ((T).obj ⟨N, hN⟩).property

/-- The prescribed lower restriction-induction at the stored contents. -/
abbrev probeAppendToDistinctMateSource :
    Superfunctor k (ProbeEvaluatedModules D Sc m νj) (ProbeEvaluatedModules D Sc m νi) :=
  fullLiftSuperfunctor P Q (rectangularMateSourceFunctor (k := k) J K)
    (appendToMateSource_closed D Sc m ν i j hj hi)

/-- The prescribed upper induction-restriction at the common stored target. -/
abbrev probeAppendToDistinctMateTarget :
    Superfunctor k (ProbeEvaluatedModules D Sc m νj) (ProbeEvaluatedModules D Sc m νi) :=
  fullLiftSuperfunctor P Q (rectangularMateTargetFunctor (k := k) L M)
    (appendToMateTarget_closed D Sc m i j hL hM)

theorem probeAppendToDistinctMateSource_toFunctor :
    (probeAppendToDistinctMateSource D Sc m ν i j hj hi).toFunctor = S := rfl

theorem probeAppendToDistinctMateTarget_toFunctor :
    (probeAppendToDistinctMateTarget D Sc m i j hL hM).toFunctor = T := rfl

def probeAppendToDistinctMateComponent (N : ProbeEvaluatedModules D Sc m νj) :
    (probeAppendToDistinctMateSource D Sc m ν i j hj hi).obj N ⟶
      (probeAppendToDistinctMateTarget D Sc m i j hL hM).obj N :=
  ⟨orderedRectangularMateComponent J K L M hc N.obj⟩

/-- The whole stored-target positive cup-crossing-cap, with all module maps retained. -/
def probeAppendToDistinctMate :
    probeAppendToDistinctMateSource D Sc m ν i j hj hi ⟶
      probeAppendToDistinctMateTarget D Sc m i j hL hM :=
  fullLiftTrans P Q (appendToMateSource_closed D Sc m ν i j hj hi)
    (appendToMateTarget_closed D Sc m i j hL hM) (rectangularMateHom J K L M hc)

theorem probeAppendToDistinctMate_mem :
    probeAppendToDistinctMate D Sc m ν i j hj hi hL hM ∈ parity (R := k) _ _
      (D.parity i * D.parity j) :=
  Superfunctor.mem_parity_iff_isHomogeneous.mpr
    (fullLiftTrans_homogeneous P Q (appendToMateSource_closed D Sc m ν i j hj hi)
      (appendToMateTarget_closed D Sc m i j hL hM) _
      (Superfunctor.mem_parity_iff_isHomogeneous.mp (rectangularMateHom_mem J K L M hc)))

theorem probeAppendToDistinctMate_total (N : ProbeEvaluatedModules D Sc m νj) :
    (probeAppendToDistinctMate D Sc m ν i j hj hi hL hM).total N =
      probeAppendToDistinctMateComponent D Sc m ν i j hj hi hL hM N := by
  apply InducedCategory.hom_ext
  change (rectangularMateHom J K L M hc).total N.obj = _
  exact rectangularMateHom_total J K L M hc N.obj

/-- The constructed OLD inverse is a map in the same full evaluated subcategory. -/
def probeAppendToDistinctMateModuleIso (hij : i ≠ j) (N : ProbeEvaluatedModules D Sc m νj) :
    (probeAppendToDistinctMateSource D Sc m ν i j hj hi).obj N ≅
      (probeAppendToDistinctMateTarget D Sc m i j hL hM).obj N :=
  ObjectProperty.isoMk Q
    (oldAppendToDistinctMateModuleIso D Sc cut ν i j hj hi hL hM hij N.obj)

theorem probeAppendToDistinctMateModuleIso_hom (hij : i ≠ j) (N : ProbeEvaluatedModules D Sc m νj) :
    (probeAppendToDistinctMateModuleIso D Sc m ν i j hj hi hL hM hij N).hom =
      (probeAppendToDistinctMate D Sc m ν i j hj hi hL hM).total N := by
  rw [probeAppendToDistinctMate_total]
  apply InducedCategory.hom_ext
  exact oldAppendToDistinctMateModuleIso_hom D Sc cut ν i j hj hi hL hM hij N.obj

theorem probeAppendToDistinctMateModuleIso_inv_native (hij : i ≠ j)
    (N : ProbeEvaluatedModules D Sc m νj) :
    (probeAppendToDistinctMateModuleIso D Sc m ν i j hj hi hL hM hij N).inv.hom =
      (oldAppendToDistinctMateModuleIso D Sc cut ν i j hj hi hL hM hij N.obj).inv := rfl

/-- The selected stored-target mate has its natural inverse at distinct colours. -/
def probeAppendToDistinctMateIso (hij : i ≠ j) :
    probeAppendToDistinctMateSource D Sc m ν i j hj hi ≅
      probeAppendToDistinctMateTarget D Sc m i j hL hM :=
  HomogeneousSuperfunctorIso.ofHom
    (probeAppendToDistinctMate D Sc m ν i j hj hi hL hM)
    (probeAppendToDistinctMate_mem D Sc m ν i j hj hi hL hM)
    (probeAppendToDistinctMateModuleIso D Sc m ν i j hj hi hL hM hij)
    (probeAppendToDistinctMateModuleIso_hom D Sc m ν i j hj hi hL hM hij)

theorem probeAppendToDistinctMateIso_hom (hij : i ≠ j) :
    (probeAppendToDistinctMateIso D Sc m ν i j hj hi hL hM hij).hom =
      probeAppendToDistinctMate D Sc m ν i j hj hi hL hM :=
  HomogeneousSuperfunctorIso.ofHom_hom _ _ _ _

theorem probeAppendToDistinctMateIso_inv_mem (hij : i ≠ j) :
    (probeAppendToDistinctMateIso D Sc m ν i j hj hi hL hM hij).inv ∈
      parity (R := k) _ _ (D.parity i * D.parity j) :=
  HomogeneousSuperfunctorIso.ofHom_inv_mem _ _ _ _

local notation "Ei" => probeAppendToE D Sc m ν i νi hi
local notation "V" => probeAppendToE D Sc m νj i ν₂ hL
local notation "A" => probeAppendToRightAdjunction D Sc m ν j νj hj
local notation "B" => probeAppendToRightAdjunction D Sc m νi j ν₂ hM

/-- Bending uses precisely the selected lower counit and upper unit. -/
theorem probeAppendToRectangularMate_eq :
    SKM.rectangularMate A B Ei V (probeAppendToCross D Sc m ν i j hj hi hL hM) =
      probeAppendToDistinctMate D Sc m ν i j hj hi hL hM := by
  apply Superfunctor.hom_ext
  intro q N
  rw [SKM.rectangularMate_piscat_app A B Ei V (probeAppendToCross D Sc m ν i j hj hi hL hM)
    (fun Z => Superfunctor.app_eq_zero_of_mem (B).unit_mem (by decide) Z)
    (fun Z => Superfunctor.app_eq_zero_of_mem (A).counit_mem (by decide) Z)]
  apply InducedCategory.hom_ext
  change (adjunctionUnit M).app _ ≫
      (restriction M).map
        ((rectangularCrossComponent_supernatural J K L M hc).toSuperNatTrans.app q
          ((restriction J).obj N.obj)) ≫
      (restriction M).map ((induction L).map ((adjunctionCounit J).app N.obj)) =
    (rectangularMateHom J K L M hc).app q N.obj
  by_cases hq : q = D.parity i * D.parity j
  · subst q
    rw [IsSupernatural.toSuperNatTrans_app, rectangularMateHom, IsSupernatural.toSuperNatTrans_app]
    rfl
  · simp only [rectangularMateHom, IsSupernatural.toSuperNatTrans, hq, ite_false,
      Functor.map_zero, Limits.comp_zero, Limits.zero_comp]

/-- The presentation sideways crossing is the same stored-target OLD mate. -/
theorem probeAppendToCrossMate_eq :
    SKM.crossMate (E₃ := Ei) (E₄ := V) A B (probeAppendToCross D Sc m ν i j hj hi hL hM) =
      probeAppendToDistinctMate D Sc m ν i j hj hi hL hM :=
  (SKM.crossMate_piscat_eq_rectangular A B Ei V (probeAppendToCross D Sc m ν i j hj hi hL hM)).trans
    (probeAppendToRectangularMate_eq D Sc m ν i j hj hi hL hM)

/-- The prescribed stored-target sideways crossing has its constructed inverse. -/
theorem probeAppendToCrossMate_isIso (hij : i ≠ j) :
    IsIso (SKM.crossMate (E₃ := Ei) (E₄ := V) A B (probeAppendToCross D Sc m ν i j hj hi hL hM)) := by
  rw [probeAppendToCrossMate_eq,
    ← probeAppendToDistinctMateIso_hom D Sc m ν i j hj hi hL hM hij]
  infer_instance

end OddMath.QuiverHecke
