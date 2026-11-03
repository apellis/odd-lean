import OddMath.QuiverHecke.CyclotomicAction.ELVWeightPrefixCrossing
import OddMath.QuiverHecke.CyclotomicAction.ELVContentTripleWhiskering

/-! # The prescribed multicolour prefix crossing in the triple charts

Brundan--Ellis (1.9). Both weight paths use their independently selected
triple charts, the same stored second predecessor and the prescribed
normalized affine prefix. No crossing comparison is assumed.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVOld
universe u
private theorem prefix_cross_comparison
    {B C : Type*} [Category* B] [Category* C]
    (F : B ⥤ C) {A A' P P' : B} {X X' W W' : C}
    (ds : X ≅ F.obj A) (dt : X' ≅ F.obj A') (es : A ≅ P) (et : A' ≅ P')
    (ws : F.obj P ≅ W) (wt : F.obj P' ≅ W') (ts : X ≅ W) (tt : X' ≅ W')
    (x : A ⟶ A') (y : X ⟶ X') (c : P ⟶ P') (z : W ⟶ W')
    (hx : x = es.hom ≫ c ≫ et.inv) (hy : y = ds.hom ≫ F.map x ≫ dt.inv)
    (hs : ts.hom = ds.hom ≫ F.map es.hom ≫ ws.hom)
    (ht : tt.hom = dt.hom ≫ F.map et.hom ≫ wt.hom)
    (hc : F.map c ≫ wt.hom = ws.hom ≫ z) :
    y ≫ tt.hom = ts.hom ≫ z := by
  have he : F.map et.inv ≫ F.map et.hom = 𝟙 _ := by
    rw [← F.map_comp, et.inv_hom_id, F.map_id]
  calc
    y ≫ tt.hom = ds.hom ≫ F.map es.hom ≫ F.map c ≫ wt.hom := by
      simp only [hy, ht, hx, Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc]
      rw [← Category.assoc (F.map et.inv), he, Category.id_comp]
    _ = ts.hom ≫ z := by rw [hc, hs]; simp only [Category.assoc]

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i j l : I) (Λ : X) {a b b' c d : X}
  (hal : a + D.α l = b) (hlj : b + D.α j = c)
  (haj : a + D.α j = b') (hjl : b' + D.α l = c) (hci : c + D.α i = d)
  (β : WeightBlocks D Λ a) (δ : WeightBlocks D Λ c) (ε : WeightBlocks D Λ d)
  (hδ : blockSucc₂ D j l Λ hal hlj β = δ) (hε : blockSucc D Λ i hci δ = ε)
local notation "htδ" => blockSucc₂_swap D j l Λ hal hlj haj hjl hδ
local notation "p" => D.parity j * D.parity l
local notation "hc" => elvBlockSucc_content_eq_of_eq D i Λ hci δ ε hε
local notation "hPs" => elvWeightPair_content_eq D j l Λ hal hlj β δ hδ
local notation "hPt" => elvWeightPair_content_eq D l j Λ haj hjl β δ htδ
local notation "hTs" => elvWeightTriple_content_eq D i j l Λ hal hlj hci β ε
  (elvBlockSucc₃_eq_of_pair D i j l Λ hal hlj hci β δ ε hδ hε)
local notation "hTt" => elvWeightTriple_content_eq D i l j Λ haj hjl hci β ε
  (elvBlockSucc₃_eq_of_pair D i l j Λ haj hjl hci β δ ε htδ hε)
local notation "U" => contentInductionTo D Sc cutoff bound (Subtype.val δ) [i] (Subtype.val ε) hc
local notation "ds" => eqToIso (elvEFunctor_comp₃_pairBlock D Sc cutoff bound i j l Λ hal hlj hci δ ε hε)
local notation "dt" => eqToIso (elvEFunctor_comp₃_pairBlock D Sc cutoff bound i l j Λ haj hjl hci δ ε hε)
local notation "C₂s" => elvWeightPairComparison D Sc cutoff bound j l Λ hal hlj β δ hδ
local notation "C₂t" => elvWeightPairComparison D Sc cutoff bound l j Λ haj hjl β δ htδ
local notation "C₃s" => elvWeightTripleComparison D Sc cutoff bound i j l Λ hal hlj hci β ε
  (elvBlockSucc₃_eq_of_pair D i j l Λ hal hlj hci β δ ε hδ hε)
local notation "C₃t" => elvWeightTripleComparison D Sc cutoff bound i l j Λ haj hjl hci β ε
  (elvBlockSucc₃_eq_of_pair D i l j Λ haj hjl hci β δ ε htδ hε)
local notation "Ls" => contentInductionCompTo D Sc cutoff bound (Subtype.val β) [l,j] (Subtype.val δ)
  hPs [i] (Subtype.val ε) hc hTs
local notation "Lt" => contentInductionCompTo D Sc cutoff bound (Subtype.val β) [j,l] (Subtype.val δ)
  hPt [i] (Subtype.val ε) hc hTt

/-- The first given multicolour crossing intertwines through the two
selected triple charts, with their common stored second block retained. -/
theorem elvWeightPrefixCross_comparison
    (M : ELVWeightProduct D Sc cutoff bound Λ a) :
    (elvWeightPrefixCross D Sc cutoff bound i j l Λ hal hlj haj hjl hci).total M ε ≫ (C₃t).hom.app M =
      (C₃s).hom.app M ≫
        (contentInductionTransform D Sc cutoff bound hTt hTs
          (contentTriplePrefixAffine_mem D Sc j l i)).app p (M β) := by
  apply prefix_cross_comparison U ((ds).app M) ((dt).app M) ((C₂s).app M) ((C₂t).app M)
    ((Ls).app (M β)) ((Lt).app (M β)) ((C₃s).app M) ((C₃t).app M)
    ((elvWeightCrossVia D Sc cutoff bound j l Λ hal hlj haj hjl β δ hδ).app p M) _
    ((contentInductionTransform D Sc cutoff bound hPt hPs (contentCrossAffine_mem D Sc j l)).app p (M β)) _
  · simpa only [Iso.app_hom, Iso.app_inv, Category.assoc] using
      elvWeightCrossVia_component D Sc cutoff bound j l Λ hal hlj haj hjl β δ hδ M
  · simpa only [Iso.app_hom, Iso.app_inv] using
      elvWeightPrefixCross_pairBlock D Sc cutoff bound i j l Λ hal hlj haj hjl hci β δ ε hδ hε M
  · simpa only [Iso.app_hom] using
      elvWeightTripleComparison_pairBlock_hom D Sc cutoff bound i j l Λ hal hlj hci β δ ε hδ hε M
  · simpa only [Iso.app_hom] using
      elvWeightTripleComparison_pairBlock_hom D Sc cutoff bound i l j Λ haj hjl hci β δ ε htδ hε M
  · exact contentInductionCompTo_inner_map_of_eq D Sc cutoff bound β.1 [j,l] [l,j] δ.1 hPt hPs
      [i] ε.1 hc hTt hTs (contentCrossAffine_mem D Sc j l) (contentTriplePrefixAffine_mem D Sc j l i)
      (contentTriplePrefixAffine_eq_whisker D Sc j l i) (M β)

end OddMath.QuiverHecke.ELVOld
