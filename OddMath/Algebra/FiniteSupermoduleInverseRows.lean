/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.Algebra.FiniteSupermoduleCoordinates

/-! # Homogeneous inverse rows of a specified finite module matrix

For Brundan–Ellis (1.13)–(1.14), project the inverse of the given even
finite matrix and restore each literal parity coordinate. The forward
fields and their parities remain specified; the construction proves
all inverse identities for those fields.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped BigOperators
namespace OddMath.FiniteSupermodule
universe u v
variable {k : Type u} [CommRing k]
  {C : Type v} [Category C] [Preadditive C] [Linear k C] [Supercategory k C]
  {ι : Type}
  {V T : ι → Superfunctor k C (SVec k)} {A : Superfunctor k C (SVec k)}
  (r : ∀ a, V a ≅ T a) (p : ι → ZMod 2)
  (hr : ∀ a, (r a).hom ∈ parity (R := k) _ _ (p a))
  (f : ∀ a, T a ⟶ A) (hf : ∀ a, f a ∈ parity (R := k) _ _ (p a))

/-- The specified forward field, preceded by its given parity-restoring isomorphism. -/
def restoredColumn (a : ι) : V a ⟶ A := (r a).hom ≫ f a

include p hr hf in
theorem restoredColumn_mem (a : ι) : restoredColumn r f a ∈ parity (R := k) _ _ 0 := by
  simpa only [restoredColumn, zmod2_add_self] using comp_mem (hr a) (hf a)

variable [Fintype ι]

/-- The given matrix in its canonical even finite coordinates. -/
def restoredColumns : product V ⟶ A :=
  columnsHom (restoredColumn r f) (restoredColumn_mem r p hr f hf)

theorem restoredColumns_mem : restoredColumns r p hr f hf ∈ parity (R := k) _ _ 0 := by
  unfold restoredColumns columnsHom
  exact Superfunctor.mem_parity_iff_isHomogeneous.mpr (SuperNatTrans.ofNatTrans_isHomogeneous _ _)

/-- The inverse row is the projection of the given matrix inverse, with its specified parity restored. -/
def inverseCoordinateRow (e : product V ≅ A) (a : ι) : A ⟶ T a :=
  e.inv ≫ projectionHom V a ≫ (r a).hom

variable (e : product V ≅ A) (he : e.hom = restoredColumns r p hr f hf)

include he in
theorem inverseCoordinateRow_mem (a : ι) :
    inverseCoordinateRow r e a ∈ parity (R := k) _ _ (p a) := by
  have h0 : e.hom ∈ parity (R := k) _ _ 0 := by
    rw [he]
    exact restoredColumns_mem r p hr f hf
  simpa only [inverseCoordinateRow, zero_add] using
    comp_mem (inv_mem e h0) (comp_mem (projectionHom_mem V a) (hr a))

include he in
private theorem forwardCoordinate_factor (a : ι) :
    f a = (r a).inv ≫ inclusionHom V a ≫ e.hom := by
  rw [he, restoredColumns, inclusionHom_columnsHom]
  simp only [restoredColumn, Iso.inv_hom_id_assoc]

include he in
/-- A forward field followed by its extracted inverse row is the identity. -/
theorem forward_inverseCoordinateRow (a : ι) :
    f a ≫ inverseCoordinateRow r e a = 𝟙 (T a) := by
  rw [forwardCoordinate_factor r p hr f hf e he a, inverseCoordinateRow]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc (inclusionHom V a) (projectionHom V a), inclusionHom_projectionHom]
  simp only [Category.id_comp, Iso.inv_hom_id]

include he in
/-- Different forward fields and inverse rows remain orthogonal. -/
theorem forward_inverseCoordinateRow_ne (a b : ι) (hne : a ≠ b) :
    f a ≫ inverseCoordinateRow r e b = 0 := by
  rw [forwardCoordinate_factor r p hr f hf e he a, inverseCoordinateRow]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc (inclusionHom V a) (projectionHom V b), inclusionHom_projectionHom_ne V a b hne]
  simp only [Limits.zero_comp, Limits.comp_zero]

include he in
/-- The extracted inverse rows and prescribed forward fields recover the complete target. -/
theorem sum_inverseCoordinateRow_forward :
    ∑ a, inverseCoordinateRow r e a ≫ f a = 𝟙 A := by
  have hterm (a : ι) : inverseCoordinateRow r e a ≫ f a =
      e.inv ≫ (projectionHom V a ≫ inclusionHom V a) ≫ e.hom := by
    rw [inverseCoordinateRow, forwardCoordinate_factor r p hr f hf e he a]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  calc
    _ = ∑ a, e.inv ≫ (projectionHom V a ≫ inclusionHom V a) ≫ e.hom :=
      Finset.sum_congr rfl (fun a _ => hterm a)
    _ = e.inv ≫ (∑ a, projectionHom V a ≫ inclusionHom V a) ≫ e.hom := by
      rw [Preadditive.sum_comp, Preadditive.comp_sum]
    _ = 𝟙 A := by
      simp only [sum_projectionHom_inclusionHom, Category.id_comp, Iso.inv_hom_id]

end OddMath.FiniteSupermodule
