import OddMath.QuiverHecke.CyclotomicAction.ELVProbeReindexTensors
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionGridMateTensors
import OddMath.QuiverHecke.CyclotomicAction.ELVContentMatrixEntries

/-! # The selected equal-colour mate under OLD content reindexing

Brundan–Ellis (1.13)–(1.14): compare the prescribed negative
cup-crossing-cap by its single-coend tensor formula. The append adjunction
comparisons retain the whole coefficient arrow and its super twist.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction
universe u
attribute [local irreducible] oldAppendReindexLinear oldAppendReindexIso orderedGridMateLinear
private theorem linear_square_point {k V W V' W' : Type*} [CommRing k]
    [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
    [AddCommMonoid V'] [Module k V'] [AddCommMonoid W'] [Module k W']
    (a : V →ₗ[k] W) (b : V' →ₗ[k] W') (l : V →ₗ[k] V') (r : W →ₗ[k] W')
    (v : V) (w : W) (v' : V') (w' : W')
    (ha : a v = w) (hr : r w = w') (hl : l v = v') (hb : b v' = w') :
    (r ∘ₗ a) v = (b ∘ₗ l) v :=
  (congrArg r ha).trans (hr.trans ((congrArg b hl).trans hb).symm)

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (ν : List I) (i : I) {ν₁ ν₂ : List I}
  (h₁ : (i :: ν).Perm ν₁) (h₂ : (i :: ν₁).Perm ν₂)
local notation "J₀" => oldContentAppendTo D Sc cutoff ν i (i :: ν) (List.Perm.refl _)
local notation "K₀" => oldContentAppendTo D Sc cutoff (i :: ν) i (i :: i :: ν) (List.Perm.refl _)
local notation "J" => oldContentAppendTo D Sc cutoff ν i ν₁ h₁
local notation "K" => oldContentAppendTo D Sc cutoff ν₁ i ν₂ h₂
local notation "Q⁻¹" => oldContentReindex D Sc cutoff h₁.symm
local notation "R₁" => oldModuleReindex D Sc cutoff h₁

/-- The physical equal crossing at the two prescribed stored-target appends. -/
def oldAppendToEqualCross (s : OldContentCategory D Sc cutoff ν) :
    (J ⋙ K).obj s ⟶ (J ⋙ K).obj s :=
  CyclotomicCrossingTensor.equalCrossComponent D Sc cutoff i s.obj

theorem oldAppendToEqualCross_supernatural :
    IsSupernatural k (D.parity i) (oldAppendToEqualCross D Sc cutoff ν i h₁ h₂) := by
  have h : IsSupernatural k (D.parity i * D.parity i)
      (oldAppendToEqualCross D Sc cutoff ν i h₁ h₂) := {
    mem := fun s => (CyclotomicCrossingTensor.equalCross_supernatural D Sc cutoff i).mem s.obj
    naturality := fun hf =>
      (CyclotomicCrossingTensor.equalCross_supernatural D Sc cutoff i).naturality hf }
  simpa only [SKM.zmod2_mul_self] using h
local notation "hγ₀" => oldAppendToEqualCross_supernatural D Sc cutoff ν i
  (List.Perm.refl (i :: ν)) (List.Perm.refl (i :: i :: ν))
local notation "hγ" => oldAppendToEqualCross_supernatural D Sc cutoff ν i h₁ h₂

/-- The selected lower comparison, with the local coend carriers fixed. -/
def oldReindexLowerLoopLinear
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (t : OldContentCategory D Sc cutoff ν₁) :
    Obj J₀ ((restriction J₀).obj N).toFunctor ((Q⁻¹).obj t) →ₗ[k]
      Obj J ((restriction J).obj ((R₁).obj N)).toFunctor t :=
  oldAppendReindexLinear D Sc cutoff (List.Perm.refl ν) i
    (List.Perm.refl (i :: ν)) h₁ h₁ ((restriction J₀).obj N) t

/-- The selected upper comparison, with the local coend carriers fixed. -/
def oldReindexUpperLoopLinear
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (t : OldContentCategory D Sc cutoff ν₁) :
    Obj K₀ N.toFunctor ((K₀).obj ((Q⁻¹).obj t)) →ₗ[k]
      Obj K ((R₁).obj N).toFunctor ((K).obj t) :=
  oldAppendReindexLinear D Sc cutoff h₁ i (List.Perm.refl (i :: i :: ν)) h₂
    ((h₁.cons i).trans h₂) N ((K).obj t)

/-- The upper loop comparison keeps a complete coefficient and vector. -/
theorem oldReindexUpperLoopLinear_tensor
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (t : OldContentCategory D Sc cutoff ν₁)
    (s : OldContentCategory D Sc cutoff (i :: ν))
    (g : (K₀).obj s ⟶ (K₀).obj ((Q⁻¹).obj t)) (v : N.obj s) :
    oldReindexUpperLoopLinear D Sc cutoff ν i h₁ h₂ N t (tensor K₀ N.toFunctor (w := (K₀).obj ((Q⁻¹).obj t)) s g v) =
      tensor K ((R₁).obj N).toFunctor (w := (K).obj t) ((oldContentReindex D Sc cutoff h₁).obj s) g v := by
  let g' : (K₀).obj s ⟶
      (oldContentReindex D Sc cutoff ((h₁.cons i).trans h₂).symm).obj ((K).obj t) := g
  have h := oldAppendReindexIso_hom_tensor D Sc cutoff h₁ i
    (List.Perm.refl (i :: i :: ν)) h₂ ((h₁.cons i).trans h₂) N s ((K).obj t) g' v
  set_option backward.dsimp.instances true in
    dsimp only [oldReindexUpperLoopLinear, oldModuleReindex, g'] at h ⊢
  convert! h using 1

/-- The lower loop comparison keeps a complete coefficient and vector. -/
theorem oldReindexLowerLoopLinear_tensor
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (t : OldContentCategory D Sc cutoff ν₁) (s : OldContentCategory D Sc cutoff ν)
    (g : (J₀).obj s ⟶ (Q⁻¹).obj t) (v : N.obj ((J₀).obj s)) :
    oldReindexLowerLoopLinear D Sc cutoff ν i h₁ N t
        (tensor J₀ ((restriction J₀).obj N).toFunctor (w := (Q⁻¹).obj t) s g v) =
      tensor J ((restriction J).obj ((R₁).obj N)).toFunctor (w := t) s g v := by
  have h := oldAppendReindexIso_hom_tensor D Sc cutoff (List.Perm.refl ν) i
    (List.Perm.refl (i :: ν)) h₁ h₁ ((restriction J₀).obj N) s t g v
  set_option backward.dsimp.instances true in
    dsimp only [oldReindexLowerLoopLinear, oldModuleReindex] at h ⊢
  convert! h using 1

/-- The exact negative mate intertwines the chosen lower and upper comparisons. -/
theorem oldReindexLoopLinear_mate
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (t : OldContentCategory D Sc cutoff ν₁) :
    oldReindexUpperLoopLinear D Sc cutoff ν i h₁ h₂ N t ∘ₗ
        orderedGridMateLinear J₀ K₀ hγ₀ N ((Q⁻¹).obj t) =
      orderedGridMateLinear J K hγ ((R₁).obj N) t ∘ₗ oldReindexLowerLoopLinear D Sc cutoff ν i h₁ N t := by
  let N₀ := N
  let N₁ := (R₁).obj N
  let t₀ := (Q⁻¹).obj t
  let V := Obj J₀ ((restriction J₀).obj N₀).toFunctor t₀
  let W := Obj K₀ N₀.toFunctor ((K₀).obj t₀)
  let V' := Obj J ((restriction J).obj ((R₁).obj N)).toFunctor t
  let W' := Obj K ((R₁).obj N).toFunctor ((K).obj t)
  let a : V →ₗ[k] W := orderedGridMateLinear J₀ K₀ hγ₀ N₀ t₀
  let b : V' →ₗ[k] W' := orderedGridMateLinear J K hγ N₁ t
  let l : V →ₗ[k] V' := oldReindexLowerLoopLinear D Sc cutoff ν i h₁ N t
  let r : W →ₗ[k] W' := oldReindexUpperLoopLinear D Sc cutoff ν i h₁ h₂ N t
  change r ∘ₗ a = b ∘ₗ l
  apply hom_ext J₀ ((restriction J₀).obj N₀).toFunctor (w := t₀)
  intro s g v
  have h₀ := orderedGridMateLinear_tensor J₀ K₀ hγ₀ N₀ s t₀ g v
  have h₃ := orderedGridMateLinear_tensor J K hγ N₁ s t g v
  let v₀ : V := tensor J₀ ((restriction J₀).obj N₀).toFunctor (w := t₀) s g v
  let z₀ : W := tensor K₀ N₀.toFunctor (w := (K₀).obj t₀) ((J₀).obj s)
    (-(oldAppendToEqualCross D Sc cutoff ν i (List.Perm.refl _) (List.Perm.refl _) s ≫
      twist k (D.parity i) ((K₀).map g))) v
  let v₁ : V' := tensor J ((restriction J).obj N₁).toFunctor (w := t) s g v
  let z₁ : W' := tensor K N₁.toFunctor (w := (K).obj t) ((J).obj s)
    (-(oldAppendToEqualCross D Sc cutoff ν i h₁ h₂ s ≫
      twist k (D.parity i) ((K).map g))) v
  have ha : a v₀ = z₀ := by convert! h₀ using 1
  have hr : r z₀ = z₁ := by
    dsimp only [r, z₀, z₁, N₀, N₁]
    rw [oldReindexUpperLoopLinear_tensor]
    rfl
  have hl : l v₀ = v₁ := by
    dsimp only [l, v₀, v₁, N₀, N₁]
    rw [oldReindexLowerLoopLinear_tensor]
  have hb : b v₁ = z₁ := by convert! h₃ using 1
  exact linear_square_point (k := k) (V := V) (W := W) (V' := V') (W' := W')
    a b l r v₀ z₀ v₁ z₁ ha hr hl hb
end OddMath.QuiverHecke
