import OddMath.QuiverHecke.CyclotomicAction.ELVWeightSuffixCrossing
import OddMath.QuiverHecke.CyclotomicAction.ELVContentCompositionOuterMap

/-! # The prescribed multicolour suffix in the selected triple charts

Brundan--Ellis (1.9). Retain the common first predecessor and its even
value comparison while intertwining the last pair through the two
independently selected triple charts.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVOld
universe u
private theorem suffix_cross_comparison
    {A B : Type*} [Category* A] [Category* B]
    (Qs Qt : A ⥤ B) {N N' : A} {X X' W W' : B}
    (es : X ≅ Qs.obj N) (et : X' ≅ Qt.obj N) (v : N ≅ N')
    (ws : Qs.obj N' ≅ W) (wt : Qt.obj N' ≅ W') (ts : X ≅ W) (tt : X' ≅ W')
    (y : X ⟶ X') (c : Qs.obj N ⟶ Qt.obj N) (c' : Qs.obj N' ⟶ Qt.obj N') (z : W ⟶ W')
    (hy : y = es.hom ≫ c ≫ et.inv)
    (hs : ts.hom = es.hom ≫ Qs.map v.hom ≫ ws.hom)
    (ht : tt.hom = et.hom ≫ Qt.map v.hom ≫ wt.hom)
    (hc : c ≫ Qt.map v.hom = Qs.map v.hom ≫ c')
    (hw : c' ≫ wt.hom = ws.hom ≫ z) :
    y ≫ tt.hom = ts.hom ≫ z := by
  calc
    y ≫ tt.hom = es.hom ≫ c ≫ Qt.map v.hom ≫ wt.hom := by
      simp only [hy, ht, Category.assoc, Iso.inv_hom_id_assoc]
    _ = es.hom ≫ Qs.map v.hom ≫ c' ≫ wt.hom := by
      rw [← Category.assoc c, hc]
      simp only [Category.assoc]
    _ = ts.hom ≫ z := by rw [hw, hs]; simp only [Category.assoc]

private theorem suffix_even_component_naturality
    {k : Type u} [CommRing k]
    {A B : Type*} [Category* A] [Category* B]
    [Preadditive A] [Linear k A] [Supercategory k A]
    [Preadditive B] [Linear k B] [Supercategory k B]
    (F G : A ⥤ B) (α : SuperNatTrans k F G) (p : ZMod 2)
    {N N' : A} (f : N ⟶ N') (hf : f ∈ parity (R := k) _ _ 0) :
    α.app p N ≫ G.map f = F.map f ≫ α.app p N' := by
  have h := (α.isSupernatural p).naturality hf
  simpa only [mul_zero, sign_zero, one_smul] using h.symm

private theorem suffix_eqToIso_app_mem
    {k : Type u} [CommRing k]
    {A B : Type*} [Category* A] [Category* B]
    [Preadditive B] [Linear k B] [Supercategory k B]
    {F G : A ⥤ B} (h : F = G) (M : A) :
    (eqToIso h).hom.app M ∈ parity (R := k) _ _ 0 := by
  cases h
  exact id_mem _

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i j l : I) (Λ : X) {a b c c' d : X}
  (hal : a + D.α l = b) (hbj : b + D.α j = c) (hci : c + D.α i = d)
  (hbi : b + D.α i = c') (hcj : c' + D.α j = d)
  (β : WeightBlocks D Λ a) (ε : WeightBlocks D Λ d)
  (hε : blockSucc₂ D i j Λ hbj hci (blockSucc D Λ l hal β) = ε)
local notation "β₁" => blockSucc D Λ l hal β
local notation "htε" => blockSucc₂_swap D i j Λ hbj hci hbi hcj hε
local notation "p" => D.parity i * D.parity j
local notation "hc₁" => elvBlockSucc_content_eq D l Λ hal β
local notation "hQs" => elvWeightPair_content_eq D i j Λ hbj hci β₁ ε hε
local notation "hQt" => elvWeightPair_content_eq D j i Λ hbi hcj β₁ ε htε
local notation "hTs" => elvWeightTriple_content_eq D i j l Λ hal hbj hci β ε hε
local notation "hTt" => elvWeightTriple_content_eq D j i l Λ hal hbi hcj β ε htε
local notation "Qs" => contentInductionTo D Sc cutoff bound (Subtype.val β₁) [j,i] (Subtype.val ε) hQs
local notation "Qt" => contentInductionTo D Sc cutoff bound (Subtype.val β₁) [i,j] (Subtype.val ε) hQt
local notation "α" => contentInductionTransform D Sc cutoff bound hQt hQs (contentCrossAffine_mem D Sc i j)
local notation "C₂s" => elvWeightPairComparison D Sc cutoff bound i j Λ hbj hci β₁ ε hε
local notation "C₂t" => elvWeightPairComparison D Sc cutoff bound j i Λ hbi hcj β₁ ε htε
local notation "C₃s" => elvWeightTripleComparison D Sc cutoff bound i j l Λ hal hbj hci β ε hε
local notation "C₃t" => elvWeightTripleComparison D Sc cutoff bound j i l Λ hal hbi hcj β ε htε
local notation "Ls" => contentInductionCompTo D Sc cutoff bound (Subtype.val β) [l] (Subtype.val β₁)
  hc₁ [j,i] (Subtype.val ε) hQs hTs
local notation "Lt" => contentInductionCompTo D Sc cutoff bound (Subtype.val β) [l] (Subtype.val β₁)
  hc₁ [i,j] (Subtype.val ε) hQt hTt
local notation "hv" => elvEFunctor_blockSucc_eval D Sc cutoff bound l Λ hal β
local notation "E₁" => elvEFunctor D Sc cutoff bound l Λ hal

/-- The second given multicolour crossing intertwines through both selected
triple charts, retaining the common first predecessor and its even value cast. -/
theorem elvWeightSuffixCross_comparison
    (M : ELVWeightProduct D Sc cutoff bound Λ a) :
    (elvWeightSuffixCross D Sc cutoff bound i j l Λ hal hbj hci hbi hcj).total M ε ≫ (C₃t).hom.app M =
      (C₃s).hom.app M ≫
        (contentInductionTransform D Sc cutoff bound hTt hTs
          (MonoidalSupercategory.whiskerLeft_mem (R := k) ((pres D Sc).obj (ob D [l]))
            (contentCrossAffine_mem D Sc i j))).app p (M β) := by
  apply suffix_cross_comparison Qs Qt ((C₂s).app ((E₁).obj M)) ((C₂t).app ((E₁).obj M))
    ((eqToIso hv).app M) ((Ls).app (M β)) ((Lt).app (M β)) ((C₃s).app M) ((C₃t).app M) _
    ((α).app p (((E₁).obj M) β₁))
    ((α).app p ((elvBlockInd D Sc cutoff bound l Λ hal β).obj (M β))) _
  · have hs := elvWeightSuffixCross_lastBlock D Sc cutoff bound i j l Λ hal hbj hci hbi hcj β ε hε M
    have hc := elvWeightCrossVia_component D Sc cutoff bound i j Λ hbj hci hbi hcj β₁ ε hε ((E₁).obj M)
    simpa only [Iso.app_hom, Iso.app_inv, Category.assoc] using hs.trans hc
  · simpa only [Iso.app_hom] using
      elvWeightTripleComparison_lastBlock_hom D Sc cutoff bound i j l Λ hal hbj hci β ε hε M
  · simpa only [Iso.app_hom] using
      elvWeightTripleComparison_lastBlock_hom D Sc cutoff bound j i l Λ hal hbi hcj β ε htε M
  · simp only [Iso.app_hom]
    exact suffix_even_component_naturality Qs Qt α p ((eqToIso hv).hom.app M)
      (suffix_eqToIso_app_mem hv M)
  · exact contentInductionCompTo_outer_map D Sc cutoff bound β.1 [l] [i,j] [j,i]
      β₁.1 ε.1 hc₁ hQt hQs hTt hTs (contentCrossAffine_mem D Sc i j) (M β)

end OddMath.QuiverHecke.ELVOld
