import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Category.ModuleCat.Basic
import OddMath.QuiverHecke.CyclotomicAction.ProbeVacuumCharts.ProbeCanonicalContent
import OddMath.QuiverHecke.CyclotomicAction.ProbeVacuumCharts.ProbeShiftedCapComparison
import OddMath.QuiverHecke.CyclotomicAction.ProbeVacuumCharts.ProbeShiftedUnitComparison

/-!
# Probe vacuum charts

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # Scalar following E/F and value charts on arbitrary output content

The missing-colour case of DeformedMatrixComparison (4) has no predecessor
content. These are the selected invertible following E/F and value charts
for any output content, with every prescribed unscaled unit/dot column.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.ELV OddMath.QuiverHecke.ELV.BalancedInduction
namespace OddMath.QuiverHecke
universe u
section Generic
variable {k C A B : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  (K : A ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
private theorem matrixUnit_endpoint_refl {p : ZMod 2}
    {β : ∀ s, K.obj s ⟶ K.obj s} (hβ : IsSupernatural k p β)
    (N : Superfunctor k A (SVec k)) (n : ℕ) (w : A) :
    endpointUnitDotLinear K hβ N n w (K.obj w) rfl = unitDotLinear K hβ N n w := by
  apply LinearMap.ext
  intro b
  exact (endpointUnitDotLinear_refl_apply K hβ N n w b).trans
    (unitDotLinear_apply K hβ N n w b).symm

end Generic
private theorem matrixUnit_plain_reencode
    {k V W Y : Type u} [CommRing k]
    [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
    [AddCommMonoid Y] [Module k Y]
    (c c₀ : W →ₗ[k] Y) (f : V →ₗ[k] W) (g g₀ : V →ₗ[k] Y) (v : V →ₗ[k] V)
    (hc : c = c₀) (hg : g₀ = g) (hv : ∀ b, v b = b) (h : c₀ ∘ₗ f = g₀) :
    c ∘ₗ f = g ∘ₗ v := by
  rw [hc]
  apply LinearMap.ext
  intro b
  exact (LinearMap.congr_fun h b).trans
    ((LinearMap.congr_fun hg b).trans (congrArg g (hv b)).symm)

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (γ : List I)
  (N : Superfunctor k (OldContentCategory D Sc (probeCutoff D m) γ) (SVec k))
  (hN : ProbeEvaluatesCoefficients D m Sc γ N)
local notation "U" => probeOldOrdinaryFunctor D Sc m γ
local notation "O" => probeOrdinaryModuleSuperfunctor D Sc m γ N hN
local notation "e" => eqToIso (probeOrdinaryModuleSuperfunctor_restrict D Sc m γ N hN)

/-- The scalar value chart on arbitrary output content. -/
def probeOutputValueLinearEquiv (w : OldContentCategory D Sc (probeCutoff D m) γ) :
    N.obj w ≃ₗ[k] (O).obj ((U).obj w) := (moduleIsoLinearEquiv e w).symm

theorem probeOutputValueLinearEquiv_symm_apply
    (w : OldContentCategory D Sc (probeCutoff D m) γ) (b : (O).obj ((U).obj w)) :
    (probeOutputValueLinearEquiv D Sc m γ N hN w).symm b = b := by
  change SVec.toLinearMap ((e).hom.total w) b = b
  simp only [SuperNatTrans.total, probeRestrictionEqToIso_hom_app,
    ↓reduceIte, one_ne_zero, add_zero, SVec.toLinearMap]
  rfl

theorem probeOutputValueLinearEquiv_apply
    (w : OldContentCategory D Sc (probeCutoff D m) γ) (b : N.obj w) :
    probeOutputValueLinearEquiv D Sc m γ N hN w b = b := by
  have h := (probeOutputValueLinearEquiv D Sc m γ N hN w).apply_symm_apply b
  have hv := probeOutputValueLinearEquiv_symm_apply D Sc m γ N hN w b
  exact (congrArg (probeOutputValueLinearEquiv D Sc m γ N hN w) hv).symm.trans h

variable (i : I)
local notation "K" => oldContentAppend D Sc (probeCutoff D m) γ i
local notation "S" => probeOrdinaryAppend D Sc m γ i

/-- The following F/E chart uses the same selected append isomorphism. -/
abbrev probeOutputFELinearEquiv (w : OldContentCategory D Sc (probeCutoff D m) γ) :=
  probeAppendLinearEquiv D Sc m γ N hN i ((K).obj w)

theorem probeOutputFELinearEquiv_hom (w : OldContentCategory D Sc (probeCutoff D m) γ) :
    (probeOutputFELinearEquiv D Sc m γ N hN i w).toLinearMap =
      probeAppendComparisonLinear D Sc m γ N hN i ((K).obj w) := rfl

/-- Every unit/dot column uses the selected scalar following and value charts,
without requiring any occurrence of i in the output content. -/
theorem probeOutputFELinearEquiv_unitDot
    (w : OldContentCategory D Sc (probeCutoff D m) γ) (n : ℕ) :
    (probeOutputFELinearEquiv D Sc m γ N hN i w).toLinearMap ∘ₗ
        unitDotLinear K (probeOldContentAppendDot_supernatural D Sc m γ i) N n w =
      unitDotLinear S (probeOrdinaryAppendDot_supernatural D Sc m γ i) O n ((U).obj w) ∘ₗ
        (probeOutputValueLinearEquiv D Sc m γ N hN w).toLinearMap := by
  have h := probeAppendComparisonLinear_unitDotColumn D Sc m γ N hN i w n
  have hEnd := matrixUnit_endpoint_refl S (probeOrdinaryAppendDot_supernatural D Sc m γ i)
    O n ((U).obj w)
  exact matrixUnit_plain_reencode _ _ _ _ _ _
    (probeOutputFELinearEquiv_hom D Sc m γ N hN i w) hEnd
    (probeOutputValueLinearEquiv_apply D Sc m γ N hN w) h

end OddMath.QuiverHecke
end

end

section

/-! # Canonical parity decoration of actual finite matrix squares

DeformedMatrixComparison (4), (5) attaches the canonical source or target
parity coordinate to independently proved plain matrix entries. The linear
kernels are stated on abstract modules before a concrete coend is inserted.
Actual scalar and weighted consumers use the selected module coordinates.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.BalancedInduction
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

end OddMath.QuiverHecke.ELV.BalancedInduction
end

end

section

/-! # Finite matrices of the prescribed shifted unit columns

The missing-colour case of Brundan--Ellis (1.13) has only the finite unit
columns. Canonical parity coordinates turn the unshifted unit-column chart
square into its actual finite column square, before specializing categories
or induced module carriers.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped BigOperators
namespace OddMath.QuiverHecke.ELV.BalancedInduction
universe u
section Families
variable {k C : Type u} [CommRing k] [Category.{u} C]
  [Preadditive C] [Linear k C] [Supercategory k C]
local instance unitColumnFamilyPi : PiSupercategory k (Superfunctor k C (SVec k)) :=
  supermodulePiSupercategory

/-- The finite canonical shifted value family, with no principal E/F slot. -/
def unitColumnSourceSpace (p : ZMod 2) (M : Superfunctor k C (SVec k))
    (m : ℕ) (w : C) : SVec k :=
  OddMath.FiniteSuperspace.product fun r : Fin m =>
    ((SKM.homParityShift (k := k) (r.val • p)).obj M).obj w
end Families

section Columns
variable {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive A] [Linear k A] [Supercategory k A]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
  (M : Superfunctor k C (SVec k))
local instance unitColumnComponentPi : PiSupercategory k (Superfunctor k C (SVec k)) :=
  supermodulePiSupercategory

/-- The literal finite assembly of the given canonically shifted unit columns. -/
def unitColumnMatrix (m : ℕ) (w : C) :
    unitColumnSourceSpace p M m w ⟶ ((restriction J).obj ((induction J).obj M)).obj w :=
  OddMath.FiniteSuperspace.assembleColumns
    (fun r : Fin m => ((SKM.homParityShift (k := k) (r.val • p)).obj M).obj w)
    (((restriction J).obj ((induction J).obj M)).obj w)
    (fun r => (shiftedUnitDotColumn J hα M r.val).total w)

private theorem unitColumn_total (n : ℕ) (w : C) :
    SVec.toLinearMap ((shiftedUnitDotColumn J hα M n).total w) =
      unitDotLinear J hα M n w ∘ₗ
        SVec.toLinearMap (((SKM.homParityShiftDatum (k := k) (n • p)).iso M).hom.total w) :=
  shiftedUnitDotColumn_total J hα M n w

end Columns

section Coordinates
variable {k C D : Type u} [CommRing k] [Category.{u} C] [Category.{u} D]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive D] [Linear k D] [Supercategory k D]
  (M : Superfunctor k C (SVec k)) (N : Superfunctor k D (SVec k))
  (w : C) (v : D) (e : M.obj w ≃ₗ[k] N.obj v)
local instance unitColumnCoordinateSourcePi : PiSupercategory k (Superfunctor k C (SVec k)) :=
  supermodulePiSupercategory
local instance unitColumnCoordinateTargetPi : PiSupercategory k (Superfunctor k D (SVec k)) :=
  supermodulePiSupercategory

/-- The whole finite family chart uses the given plain value equivalence
inside each pair of canonical source/target parity coordinates. -/
def unitColumnFamilyEquiv (p : ZMod 2) (m : ℕ) :
    unitColumnSourceSpace p M m w ≃ₗ[k] unitColumnSourceSpace p N m v :=
  LinearEquiv.piCongrRight fun r : Fin m =>
    shiftedModuleValueLinearEquiv M N w v e (r.val • p)

end Coordinates

private theorem unitColumns_square
    {k : Type u} [CommRing k] {ι : Type} [Fintype ι]
    (V W : ι → SVec k) (X Y : SVec k) (e : ∀ a, V a ≃ₗ[k] W a)
    (c : X →ₗ[k] Y) (f : ∀ a, V a ⟶ X) (g : ∀ a, W a ⟶ Y)
    (h : ∀ a, c ∘ₗ SVec.toLinearMap (f a) = SVec.toLinearMap (g a) ∘ₗ (e a).toLinearMap) :
    c ∘ₗ SVec.toLinearMap (OddMath.FiniteSuperspace.assembleColumns V X f) =
      SVec.toLinearMap (OddMath.FiniteSuperspace.assembleColumns W Y g) ∘ₗ
        (LinearEquiv.piCongrRight e).toLinearMap := by
  apply LinearMap.ext
  intro x
  change c (∑ a, f a (x a)) = ∑ a, g a (e a (x a))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro a _
  exact LinearMap.congr_fun (h a) (x a)

section Comparison
variable {k C A D B : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} D] [Preadditive D] [Linear k D] [Supercategory k D]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (T : D ⥤ B) [T.Additive] [T.Linear k] [IsSuperfunctor k T]
  {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
  {β : ∀ s, T.obj s ⟶ T.obj s} (hβ : IsSupernatural k p β)
  (M : Superfunctor k C (SVec k)) (N : Superfunctor k D (SVec k))
  (w : C) (v : D) (e : M.obj w ≃ₗ[k] N.obj v)
  (c : Obj J M.toFunctor (J.obj w) →ₗ[k] Obj T N.toFunctor (T.obj v))
local instance unitColumnSquareSourcePi : PiSupercategory k (Superfunctor k C (SVec k)) :=
  supermodulePiSupercategory
local instance unitColumnSquareTargetPi : PiSupercategory k (Superfunctor k D (SVec k)) :=
  supermodulePiSupercategory

/-- Canonical parity coordinates and finite sums transport the actual unit
matrix whenever its unshifted dotted columns commute with the given charts. -/
theorem unitColumnMatrix_square
    (h : ∀ n, c ∘ₗ unitDotLinear J hα M n w = unitDotLinear T hβ N n v ∘ₗ e.toLinearMap)
    (m : ℕ) :
    c ∘ₗ SVec.toLinearMap (unitColumnMatrix J hα M m w) =
      SVec.toLinearMap (unitColumnMatrix T hβ N m v) ∘ₗ
        (unitColumnFamilyEquiv M N w v e p m).toLinearMap := by
  apply unitColumns_square
    (fun r : Fin m => ((SKM.homParityShift (k := k) (r.val • p)).obj M).obj w)
    (fun r : Fin m => ((SKM.homParityShift (k := k) (r.val • p)).obj N).obj v)
    (((restriction J).obj ((induction J).obj M)).obj w)
    (((restriction T).obj ((induction T).obj N)).obj v)
    (fun r => shiftedModuleValueLinearEquiv M N w v e (r.val • p))
    c (fun r => (shiftedUnitDotColumn J hα M r.val).total w)
    (fun r => (shiftedUnitDotColumn T hβ N r.val).total v)
  intro r
  exact linearColumn_parity_square _ _ _ _ _ _ _ _ _ (h r.val)
    (shiftedModuleValueLinearEquiv_source_square M N w v e (r.val • p))
    (unitColumn_total J hα M r.val w) (unitColumn_total T hβ N r.val v)
end Comparison
end OddMath.QuiverHecke.ELV.BalancedInduction
end

end

section

/-! # Canonical unshifted coefficient rows of inverse unit matrices

The normalized left cap in DeformedMatrixComparison is a specified inverse
unit-matrix coordinate, followed by its original canonical source unshift.
The common-chart comparison below transports that exact row. The ordinary
right counit is a different field and is not substituted for it.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.BalancedInduction
universe u
section Rows
variable {k C : Type u} [CommRing k] [Category.{u} C]
  [Preadditive C] [Linear k C] [Supercategory k C]
  (M : Superfunctor k C (SVec k)) (w : C) (p : ZMod 2) (m : ℕ)
local instance unitInverseRowPi : PiSupercategory k (Superfunctor k C (SVec k)) :=
  supermodulePiSupercategory

/-- Project to precisely the r-th shifted value slot and remove its given shift. -/
def unitColumnUnshift (r : Fin m) : unitColumnSourceSpace p M m w ⟶ M.obj w :=
  SVec.ofHom (SVec.toLinearMap
    (((SKM.homParityShiftDatum (k := k) (r.val • p)).iso M).hom.total w) ∘ₗ LinearMap.proj r)

theorem unitColumnUnshift_apply (r : Fin m) (x : unitColumnSourceSpace p M m w) :
    unitColumnUnshift M w p m r x =
      ((SKM.homParityShiftDatum (k := k) (r.val • p)).iso M).hom.total w (x r) := rfl

/-- A specified inverse coefficient row, with exactly its canonical unshift. -/
def unitColumnInverseRow {W : SVec k} (e : unitColumnSourceSpace p M m w ≅ W) (r : Fin m) :
    W ⟶ M.obj w := e.inv ≫ unitColumnUnshift M w p m r

theorem unitColumnInverseRow_apply {W : SVec k} (e : unitColumnSourceSpace p M m w ≅ W)
    (r : Fin m) (x : W) :
    unitColumnInverseRow M w p m e r x =
      ((SKM.homParityShiftDatum (k := k) (r.val • p)).iso M).hom.total w (e.inv x r) := rfl

private theorem unitColumnInverseRow_linear {W : SVec k}
    (e : unitColumnSourceSpace p M m w ≅ W) (r : Fin m) :
    SVec.toLinearMap (unitColumnInverseRow M w p m e r) =
      SVec.toLinearMap (unitColumnUnshift M w p m r) ∘ₗ SVec.toLinearMap e.inv :=
  SVec.toLinearMap_comp e.inv (unitColumnUnshift M w p m r)
end Rows

section Coordinates
variable {k C D : Type u} [CommRing k] [Category.{u} C] [Category.{u} D]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive D] [Linear k D] [Supercategory k D]
  (M : Superfunctor k C (SVec k)) (N : Superfunctor k D (SVec k))
  (w : C) (v : D) (e : M.obj w ≃ₗ[k] N.obj v) (p : ZMod 2) (m : ℕ)

/-- The actual coordinate product intertwines the original unshifts. -/
theorem unitColumnUnshift_coordinate (r : Fin m) :
    SVec.toLinearMap (unitColumnUnshift N v p m r) ∘ₗ
        (unitColumnFamilyEquiv M N w v e p m).toLinearMap =
      e.toLinearMap ∘ₗ SVec.toLinearMap (unitColumnUnshift M w p m r) := by
  apply LinearMap.ext
  intro x
  exact shiftedModuleValueLinearEquiv_hom_coordinate M N w v e (r.val • p) (x r)
end Coordinates

section CommonComparison
variable {k C₀ C₁ C₂ : Type u} [CommRing k]
  [Category.{u} C₀] [Preadditive C₀] [Linear k C₀] [Supercategory k C₀]
  [Category.{u} C₁] [Preadditive C₁] [Linear k C₁] [Supercategory k C₁]
  [Category.{u} C₂] [Preadditive C₂] [Linear k C₂] [Supercategory k C₂]
  (M₀ : Superfunctor k C₀ (SVec k)) (M₁ : Superfunctor k C₁ (SVec k))
  (M₂ : Superfunctor k C₂ (SVec k)) (w₀ : C₀) (w₁ : C₁) (w₂ : C₂)
  (d : M₀.obj w₀ ≃ₗ[k] M₁.obj w₁) (d' : M₀.obj w₀ ≃ₗ[k] M₂.obj w₂)
  (p : ZMod 2) (m : ℕ) {B W W' : SVec k}
  (b : B ≃ₗ[k] W) (t : B ≃ₗ[k] W')
  (e : unitColumnSourceSpace p M₁ m w₁ ≅ W)
  (f : unitColumnSourceSpace p M₂ m w₂ ≅ W')
  (r : unitColumnSourceSpace p M₀ m w₀ →ₗ[k] B)

/-- Two proved forward matrix squares transport the specified inverse row
and its full canonical unshift. These hypotheses are supplied by the chosen
content and scalar matrix comparisons in the concrete left-cap application. -/
theorem unitColumnInverseRow_compare_common
    (hOld : b.toLinearMap ∘ₗ r = SVec.toLinearMap e.hom ∘ₗ
      (unitColumnFamilyEquiv M₀ M₁ w₀ w₁ d p m).toLinearMap)
    (hNew : t.toLinearMap ∘ₗ r = SVec.toLinearMap f.hom ∘ₗ
      (unitColumnFamilyEquiv M₀ M₂ w₀ w₂ d' p m).toLinearMap) (a : Fin m) :
    (d.symm.trans d').toLinearMap ∘ₗ SVec.toLinearMap (unitColumnInverseRow M₁ w₁ p m e a) =
      SVec.toLinearMap (unitColumnInverseRow M₂ w₂ p m f a) ∘ₗ (b.symm.trans t).toLinearMap := by
  have hMatrix := OddMath.FiniteSuperspace.commonChart_square
    (unitColumnFamilyEquiv M₀ M₁ w₀ w₁ d p m) b
    (unitColumnFamilyEquiv M₀ M₂ w₀ w₂ d' p m) t e f r hOld hNew
  have hCoordinate := OddMath.FiniteSuperspace.commonCoordinate_square
    (unitColumnFamilyEquiv M₀ M₁ w₀ w₁ d p m)
    (unitColumnFamilyEquiv M₀ M₂ w₀ w₂ d' p m) d d'
    (SVec.toLinearMap (unitColumnUnshift M₀ w₀ p m a))
    (SVec.toLinearMap (unitColumnUnshift M₁ w₁ p m a))
    (SVec.toLinearMap (unitColumnUnshift M₂ w₂ p m a))
    (unitColumnUnshift_coordinate M₀ M₁ w₀ w₁ d p m a)
    (unitColumnUnshift_coordinate M₀ M₂ w₀ w₂ d' p m a)
  have h := OddMath.FiniteSuperspace.inverse_row_square e f
    (unitColumnFamilyEquiv M₀ M₁ w₀ w₁ d p m |>.symm.trans
      (unitColumnFamilyEquiv M₀ M₂ w₀ w₂ d' p m)).toLinearMap
    (b.symm.trans t).toLinearMap (d.symm.trans d').toLinearMap
    (SVec.toLinearMap (unitColumnUnshift M₁ w₁ p m a))
    (SVec.toLinearMap (unitColumnUnshift M₂ w₂ p m a)) hMatrix hCoordinate
  simpa only [unitColumnInverseRow_linear] using h
end CommonComparison
end OddMath.QuiverHecke.ELV.BalancedInduction
end

end
