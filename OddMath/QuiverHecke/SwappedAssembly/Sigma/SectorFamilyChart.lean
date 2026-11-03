import OddMath.QuiverHecke.SwappedAssembly.Sigma.MatrixEmbedding
import OddMath.QuiverHecke.SwappedAssembly.CentralInverse.TwoSector

/-! # Two-sector charts with absent pure summands

A finite family classified by its valid reservoir/probe side and its
window index has a canonical chart in `ProbeWindow.tObj`. Missing pure
summands are zero objects. This is the object chart for all central
sectors in Brundan–Ellis (1.13)–(1.14), including height zero.
-/
noncomputable section
namespace OddMath.QuiverHecke.SwappedAssembly
open CategoryTheory Classical
open scoped ZeroObject
variable {C : Type*} [Category C] [Preadditive C] [Limits.HasZeroObject C]

/-- Reservoir, probe, and window indices, in that order. -/
def sectorFamilyIndex {p : Bool → Prop} {ι : Type} :
    Sum {a : Bool // p a} ι → Option (Option ι)
  | .inl ⟨false, _⟩ => none
  | .inl ⟨true, _⟩ => some none
  | .inr n => some (some n)

theorem sectorFamilyIndex_injective {p : Bool → Prop} {ι : Type} :
    Function.Injective (@sectorFamilyIndex p ι) := by
  rintro (⟨a, ha⟩ | n) (⟨b, hb⟩ | m) h
  · cases a <;> cases b <;> simp_all [sectorFamilyIndex]
  · cases a <;> simp [sectorFamilyIndex] at h
  · cases b <;> simp [sectorFamilyIndex] at h
  · simpa only [sectorFamilyIndex, Option.some.injEq, Sum.inr.injEq] using h

variable {α : Type*} [Fintype α] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The pure factor object, or zero when that pure path is absent. -/
def sectorFamilyCorner (p : Bool → Prop) (V : {a : Bool // p a} → C) (a : Bool) : C :=
  if h : p a then V ⟨a, h⟩ else 0

/-- The padded two-sector object retains both named pure corners. -/
abbrev sectorFamilyObject (p : Bool → Prop) (V : {a : Bool // p a} → C) (O : C) : Mat_ C :=
  ProbeWindow.tObj (sectorFamilyCorner p V false) (sectorFamilyCorner p V true) O ι

/-- The finite path enumeration embeds into the reservoir/probe/window indices. -/
def sectorFamilyEmbedding (p : Bool → Prop) (e : α ≃ Sum {a : Bool // p a} ι) :
    Fin (Fintype.card α) ↪ Option (Option ι) where
  toFun j := sectorFamilyIndex (e ((Fintype.equivFin α).symm j))
  inj' := sectorFamilyIndex_injective.comp (e.injective.comp (Fintype.equivFin α).symm.injective)

/-- The selected factor or window chart at a classified index. -/
def sectorFamilyChartAt (p : Bool → Prop) (e : α ≃ Sum {a : Bool // p a} ι)
    (X : α → C) (V : {a : Bool // p a} → C) (O : C)
    (v : ∀ a, V a ≅ X (e.symm (.inl a))) (w : ∀ n, O ≅ X (e.symm (.inr n))) :
    ∀ z, (sectorFamilyObject (ι := ι) p V O).X (sectorFamilyIndex z) ≅ X (e.symm z)
  | .inl ⟨false, ha⟩ => eqToIso (by
      change sectorFamilyCorner p V false = V ⟨false, ha⟩
      simp only [sectorFamilyCorner, dite_eq_left ha]) ≪≫ v ⟨false, ha⟩
  | .inl ⟨true, ha⟩ => eqToIso (by
      change sectorFamilyCorner p V true = V ⟨true, ha⟩
      simp only [sectorFamilyCorner, dite_eq_left ha]) ≪≫ v ⟨true, ha⟩
  | .inr n => w n

/-- Each present corner uses its prescribed factor chart. -/
def sectorFamilyComponentIso (p : Bool → Prop) (e : α ≃ Sum {a : Bool // p a} ι)
    (X : α → C) (V : {a : Bool // p a} → C) (O : C)
    (v : ∀ a, V a ≅ X (e.symm (.inl a))) (w : ∀ n, O ≅ X (e.symm (.inr n)))
    (j : Fin (Fintype.card α)) :
    (sectorFamilyObject (ι := ι) p V O).X (sectorFamilyEmbedding p e j) ≅
      (famObj X).X j :=
  sectorFamilyChartAt p e X V O v w (e ((Fintype.equivFin α).symm j)) ≪≫
    eqToIso (congrArg X (e.symm_apply_apply _))

omit [Preadditive C] in
/-- Every unoccupied index in the two-sector model is zero. -/
theorem sectorFamily_missing_isZero (p : Bool → Prop)
    (e : α ≃ Sum {a : Bool // p a} ι) (V : {a : Bool // p a} → C) (O : C)
    (i : Option (Option ι)) (hi : ∀ j, sectorFamilyEmbedding p e j ≠ i) :
    Limits.IsZero ((sectorFamilyObject (ι := ι) p V O).X i) := by
  have hnot (z : Sum {a : Bool // p a} ι) : sectorFamilyIndex z ≠ i := by
    simpa only [sectorFamilyEmbedding, Function.Embedding.coeFn_mk,
      Equiv.symm_apply_apply, Equiv.apply_symm_apply] using
      hi ((Fintype.equivFin α) (e.symm z))
  cases i with
  | none =>
    have hp : ¬p false := fun h => hnot (.inl ⟨false, h⟩) rfl
    simpa only [sectorFamilyObject, ProbeWindow.tObj, sectorFamilyCorner, dite_eq_right hp] using
      Limits.isZero_zero C
  | some i =>
    cases i with
    | none =>
      have hp : ¬p true := fun h => hnot (.inl ⟨true, h⟩) rfl
      simpa only [sectorFamilyObject, ProbeWindow.tObj, sectorFamilyCorner, dite_eq_right hp] using
        Limits.isZero_zero C
    | some n => exact False.elim (hnot (.inr n) rfl)

/-- The canonical two-sector chart includes absent pure corners as zero,
and includes every window index. -/
def sectorFamilyIso (p : Bool → Prop) (e : α ≃ Sum {a : Bool // p a} ι)
    (X : α → C) (V : {a : Bool // p a} → C) (O : C)
    (v : ∀ a, V a ≅ X (e.symm (.inl a))) (w : ∀ n, O ≅ X (e.symm (.inr n))) :
    sectorFamilyObject (ι := ι) p V O ≅ famObj X :=
  matrixEmbeddingIso _ _ (sectorFamilyEmbedding p e)
    (sectorFamilyComponentIso p e X V O v w) (sectorFamily_missing_isZero p e V O)

end OddMath.QuiverHecke.SwappedAssembly
