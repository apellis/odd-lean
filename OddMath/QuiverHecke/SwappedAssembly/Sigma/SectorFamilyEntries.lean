import OddMath.QuiverHecke.SwappedAssembly.Sigma.SectorFamilyChart
import OddMath.QuiverHecke.SwappedAssembly.Sigma.MatrixEmbeddingEntries

/-! # Component charts at pure and window indices

These formulas normalize the finite path enumeration before substituting
factor objects. They retain the selected component charts and their
necessary endpoint equality transports.
-/
noncomputable section
namespace OddMath.QuiverHecke.SwappedAssembly
open CategoryTheory Classical
private theorem isoHomCongr {C : Type*} [Category C] {J : Type*}
    {A B : J → C} (f : ∀ j, A j ≅ B j) {j j' : J} (h : j = j') :
    (f j).hom = eqToHom (congrArg A h) ≫ (f j').hom ≫ eqToHom (congrArg B h.symm) := by
  subst j'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

variable {C : Type*} [Category C] [Preadditive C] [Limits.HasZeroObject C]
  {α : Type*} [Fintype α] {ι : Type} [Fintype ι] [DecidableEq ι]
  (p : Bool → Prop) (e : α ≃ Sum {a : Bool // p a} ι)
  (X : α → C) (V : {a : Bool // p a} → C) (O : C)
  (v : ∀ a, V a ≅ X (e.symm (.inl a))) (w : ∀ n, O ≅ X (e.symm (.inr n)))

omit [Preadditive C] in

omit [Preadditive C] in

omit [Preadditive C] in
/-- Normalize the enumeration at an arbitrary classified index before
substituting a factor object. -/
theorem sectorFamilyComponentIso_at (z : Sum {a : Bool // p a} ι) :
    sectorFamilyComponentIso p e X V O v w ((Fintype.equivFin α) (e.symm z)) =
    eqToIso (congrArg (fun z => (sectorFamilyObject (ι := ι) p V O).X (sectorFamilyIndex z))
      ((congrArg e ((Fintype.equivFin α).symm_apply_apply _)).trans
        (e.apply_symm_apply z))) ≪≫
    sectorFamilyChartAt p e X V O v w z ≪≫
    eqToIso (congrArg X ((Fintype.equivFin α).symm_apply_apply (e.symm z)).symm) := by
  apply Iso.ext
  dsimp only [sectorFamilyComponentIso]
  simp only [Iso.trans_hom, eqToIso.hom]
  rw [isoHomCongr (sectorFamilyChartAt p e X V O v w)
    ((congrArg e ((Fintype.equivFin α).symm_apply_apply _)).trans (e.apply_symm_apply z))]
  simp only [Category.assoc, eqToHom_trans]

omit [Limits.HasZeroObject C] in
private theorem matrixEntryCongr {A B : Mat_ C} (f : A ⟶ B)
    {a a' : A.ι} {b b' : B.ι} (ha : a = a') (hb : b = b') :
    f a b = eqToHom (congrArg A.X ha) ≫ f a' b' ≫ eqToHom (congrArg B.X hb.symm) := by
  subst a' b'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

omit [Preadditive C] [Limits.HasZeroObject C] in
private theorem familyEntryCongr {α β : Type*} {A : α → C} {B : β → C}
    (f : ∀ a b, A a ⟶ B b) {a a' : α} {b b' : β} (ha : a = a') (hb : b = b') :
    f a b = eqToHom (congrArg A ha) ≫ f a' b' ≫ eqToHom (congrArg B hb.symm) := by
  subst a' b'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

/-- Every present entry of the two-sector chart is exactly its selected
source component chart, the prescribed family entry, and the inverse
selected target component chart. No finite enumeration remains. -/
theorem sectorFamilyMap_entry {β : Type*} [Fintype β] {κ : Type} [Fintype κ] [DecidableEq κ]
    (q : Bool → Prop) (e' : β ≃ Sum {a : Bool // q a} κ)
    (Y : β → C) (V' : {a : Bool // q a} → C) (O' : C)
    (v' : ∀ a, V' a ≅ Y (e'.symm (.inl a))) (w' : ∀ n, O' ≅ Y (e'.symm (.inr n)))
    (f : ∀ a b, X a ⟶ Y b)
    (z : Sum {a : Bool // p a} ι) (z' : Sum {a : Bool // q a} κ) :
    (matrixEmbeddingMap (sectorFamilyIso p e X V O v w)
      (sectorFamilyIso q e' Y V' O' v' w') (famHom f))
        (sectorFamilyIndex z) (sectorFamilyIndex z') =
      (sectorFamilyChartAt p e X V O v w z).hom ≫
        f (e.symm z) (e'.symm z') ≫ (sectorFamilyChartAt q e' Y V' O' v' w' z').inv := by
  let j := (Fintype.equivFin α) (e.symm z)
  let k := (Fintype.equivFin β) (e'.symm z')
  have hj : sectorFamilyEmbedding p e j = sectorFamilyIndex z := by
    simp only [j, sectorFamilyEmbedding, Function.Embedding.coeFn_mk,
      Equiv.symm_apply_apply, Equiv.apply_symm_apply]
  have hk : sectorFamilyEmbedding q e' k = sectorFamilyIndex z' := by
    simp only [k, sectorFamilyEmbedding, Function.Embedding.coeFn_mk,
      Equiv.symm_apply_apply, Equiv.apply_symm_apply]
  have hc := matrixEntryCongr
    (A := sectorFamilyObject (ι := ι) p V O)
    (B := sectorFamilyObject (ι := κ) q V' O')
    (matrixEmbeddingMap (sectorFamilyIso p e X V O v w)
      (sectorFamilyIso q e' Y V' O' v' w') (famHom f)) hj.symm hk.symm
  rw [hc]
  change eqToHom _ ≫
    (matrixEmbeddingMap (matrixEmbeddingIso (sectorFamilyObject (ι := ι) p V O) (famObj X) (sectorFamilyEmbedding p e)
      (sectorFamilyComponentIso p e X V O v w) (sectorFamily_missing_isZero p e V O))
      (matrixEmbeddingIso (sectorFamilyObject (ι := κ) q V' O') (famObj Y) (sectorFamilyEmbedding q e')
        (sectorFamilyComponentIso q e' Y V' O' v' w')
        (sectorFamily_missing_isZero q e' V' O')) (famHom f))
      (sectorFamilyEmbedding p e j) (sectorFamilyEmbedding q e' k) ≫ eqToHom _ = _
  rw [matrixEmbeddingMap_apply]
  dsimp only [j, k]
  rw [sectorFamilyComponentIso_at, sectorFamilyComponentIso_at]
  dsimp only [famHom, famObj]
  rw [familyEntryCongr f ((Fintype.equivFin α).symm_apply_apply (e.symm z))
    ((Fintype.equivFin β).symm_apply_apply (e'.symm z'))]
  simp only [Iso.trans_hom, Iso.trans_inv, eqToIso.hom, eqToIso.inv,
    Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl,
    Category.id_comp, Category.comp_id]

end OddMath.QuiverHecke.SwappedAssembly
