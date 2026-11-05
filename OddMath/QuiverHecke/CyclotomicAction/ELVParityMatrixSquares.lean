import OddMath.QuiverHecke.CyclotomicAction.ELVParityMatrixCoordinates

/-! # Canonical parity decoration of actual finite matrix squares

DeformedMatrixComparison (4), (5) attaches the canonical source or target
parity coordinate to independently proved plain matrix entries. The linear
kernels are stated on abstract modules before a concrete coend is inserted.
Actual scalar and weighted consumers use the selected module coordinates.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u

section GenericCoordinates
variable {k A B : Type u} [CommRing k]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  (M : Superfunctor k A (SVec k)) (N : Superfunctor k B (SVec k))
  (w : A) (v : B) (e : M.obj w ≃ₗ[k] N.obj v)
local instance paritySquareSourcePi : PiSupercategory k (Superfunctor k A (SVec k)) :=
  supermodulePiSupercategory
local instance paritySquareTargetPi : PiSupercategory k (Superfunctor k B (SVec k)) :=
  supermodulePiSupercategory

theorem shiftedModuleValueLinearEquiv_source_square (q : ZMod 2) :
    SVec.toLinearMap (((SKM.homParityShiftDatum (k := k) q).iso N).hom.total v) ∘ₗ
        (shiftedModuleValueLinearEquiv M N w v e q).toLinearMap =
      e.toLinearMap ∘ₗ SVec.toLinearMap (((SKM.homParityShiftDatum (k := k) q).iso M).hom.total w) := by
  apply LinearMap.ext
  intro b
  exact shiftedModuleValueLinearEquiv_hom_coordinate M N w v e q b

theorem shiftedModuleValueLinearEquiv_target_square (q : ZMod 2) :
    (shiftedModuleValueLinearEquiv M N w v e q).toLinearMap ∘ₗ
        SVec.toLinearMap (((SKM.homParityShiftDatum (k := k) q).iso M).inv.total w) =
      SVec.toLinearMap (((SKM.homParityShiftDatum (k := k) q).iso N).inv.total v) ∘ₗ e.toLinearMap := by
  apply LinearMap.ext
  intro b
  exact shiftedModuleValueLinearEquiv_inv_coordinate M N w v e q b

end GenericCoordinates

theorem linearColumn_parity_square
    {k V W X Y A B : Type u} [CommRing k]
    [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
    [AddCommMonoid X] [Module k X] [AddCommMonoid Y] [Module k Y]
    [AddCommMonoid A] [Module k A] [AddCommMonoid B] [Module k B]
    (c : W →ₗ[k] Y) (f : V →ₗ[k] W) (g : X →ₗ[k] Y) (d : V →ₗ[k] X)
    (z : A →ₗ[k] V) (z' : B →ₗ[k] X) (s : A →ₗ[k] B)
    (o : A →ₗ[k] W) (n : B →ₗ[k] Y)
    (h : c ∘ₗ f = g ∘ₗ d) (hz : z' ∘ₗ s = d ∘ₗ z)
    (ho : o = f ∘ₗ z) (hn : n = g ∘ₗ z') : c ∘ₗ o = n ∘ₗ s := by
  rw [ho, hn]
  apply LinearMap.ext
  intro b
  exact (LinearMap.congr_fun h (z b)).trans (congrArg g (LinearMap.congr_fun hz b).symm)

theorem linearRow_parity_square
    {k V W X Y A B : Type u} [CommRing k]
    [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
    [AddCommMonoid X] [Module k X] [AddCommMonoid Y] [Module k Y]
    [AddCommMonoid A] [Module k A] [AddCommMonoid B] [Module k B]
    (c : W →ₗ[k] Y) (f : V →ₗ[k] W) (g : X →ₗ[k] Y) (d : V →ₗ[k] X)
    (z : W →ₗ[k] A) (z' : Y →ₗ[k] B) (s : A →ₗ[k] B)
    (o : V →ₗ[k] A) (n : X →ₗ[k] B)
    (h : c ∘ₗ f = g ∘ₗ d) (hz : s ∘ₗ z = z' ∘ₗ c)
    (ho : o = z ∘ₗ f) (hn : n = z' ∘ₗ g) : s ∘ₗ o = n ∘ₗ d := by
  rw [ho, hn]
  apply LinearMap.ext
  intro b
  exact (LinearMap.congr_fun hz (f b)).trans (congrArg z' (LinearMap.congr_fun h b))

theorem linearSquare_reencode
    {k V W X Y : Type u} [CommRing k]
    [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
    [AddCommMonoid X] [Module k X] [AddCommMonoid Y] [Module k Y]
    (c c₀ : W →ₗ[k] Y) (f f₀ : V →ₗ[k] W) (g g₀ : X →ₗ[k] Y) (d d₀ : V →ₗ[k] X)
    (hc : c = c₀) (hf : f = f₀) (hg : g = g₀) (hd : d = d₀)
    (h : c₀ ∘ₗ f₀ = g₀ ∘ₗ d₀) : c ∘ₗ f = g ∘ₗ d := by
  rw [hc, hf, hg, hd]
  exact h

end OddMath.QuiverHecke.ELVOld.BalancedInduction
