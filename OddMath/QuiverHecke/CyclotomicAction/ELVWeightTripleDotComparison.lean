import OddMath.QuiverHecke.CyclotomicAction.ELVWeightTripleDotComponents
import OddMath.QuiverHecke.CyclotomicAction.ELVContentTripleWhiskering
import OddMath.QuiverHecke.CyclotomicAction.ELVContentCompositionOuterMap

/-! # Prescribed positioned dots through the selected weight triple chart

Brundan--Ellis (1.9), the repeated-outer correction. Induce the checked
whole pair-dot squares through the same selected triple chart used for
the given crossings; retain the literal affine contexts.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVOld
universe u
private theorem induced_dot_square
    {B C : Type*} [Category* B] [Category* C]
    (F : B ⥤ C) {A P : B} {X W : C}
    (d : X ≅ F.obj A) (e : A ≅ P) (w : F.obj P ≅ W) (t : X ≅ W)
    (x : End A) (y : End X) (c : End P) (z : End W)
    (hx : x ≫ e.hom = e.hom ≫ c)
    (hy : y = d.hom ≫ F.map x ≫ d.inv)
    (ht : t.hom = d.hom ≫ F.map e.hom ≫ w.hom)
    (hc : F.map c ≫ w.hom = w.hom ≫ z) :
    y ≫ t.hom = t.hom ≫ z := by
  have hm : F.map x ≫ F.map e.hom = F.map e.hom ≫ F.map c := by
    rw [← F.map_comp, hx, F.map_comp]
  calc
    y ≫ t.hom = d.hom ≫ F.map x ≫ F.map e.hom ≫ w.hom := by
      simp only [hy, ht, Category.assoc, Iso.inv_hom_id_assoc]
    _ = d.hom ≫ F.map e.hom ≫ F.map c ≫ w.hom := by
      rw [← Category.assoc (F.map x), hm]
      simp only [Category.assoc]
    _ = t.hom ≫ z := by rw [hc, ht]; simp only [Category.assoc]

private theorem outer_dot_square
    {A B : Type*} [Category* A] [Category* B]
    (Q : A ⥤ B) {N P : A} {X W : B}
    (e : X ≅ Q.obj N) (v : N ≅ P) (w : Q.obj P ≅ W) (t : X ≅ W)
    (y : End X) (c : End (Q.obj N)) (c' : End (Q.obj P)) (z : End W)
    (hy : y = e.hom ≫ c ≫ e.inv)
    (ht : t.hom = e.hom ≫ Q.map v.hom ≫ w.hom)
    (hc : c ≫ Q.map v.hom = Q.map v.hom ≫ c')
    (hw : c' ≫ w.hom = w.hom ≫ z) :
    y ≫ t.hom = t.hom ≫ z := by
  rw [hy, ht]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc c, hc, Category.assoc, hw]

private theorem triple_dot_even_naturality
    {k : Type u} [CommRing k]
    {A B : Type*} [Category* A] [Category* B]
    [Preadditive A] [Linear k A] [Supercategory k A]
    [Preadditive B] [Linear k B] [Supercategory k B]
    (F : A ⥤ B) (α : SuperNatTrans k F F) (p : ZMod 2)
    {N P : A} (f : N ⟶ P) (hf : f ∈ parity (R := k) _ _ 0) :
    α.app p N ≫ F.map f = F.map f ≫ α.app p P := by
  have h := (α.isSupernatural p).naturality hf
  simpa only [mul_zero, sign_zero, one_smul] using h.symm

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i j l : I) (Λ : X) {a b c d : X}
  (hal : a + D.α l = b) (hbj : b + D.α j = c) (hci : c + D.α i = d)
  (β : WeightBlocks D Λ a)
local notation "β₂" => blockSucc₂ D j l Λ hal hbj β
local notation "β₃" => elvBlockSucc₃ D i j l Λ hal hbj hci β
local notation "hP" => elvWeightPair_content_eq D j l Λ hal hbj β β₂ rfl
local notation "hT" => elvBlockTriple_content_eq D i j l Λ hal hbj hci β
local notation "hc₃" => elvBlockSucc_content_eq D i Λ hci β₂
local notation "C₂" => elvWeightPairComparison D Sc cutoff bound j l Λ hal hbj β β₂ rfl
local notation "C₃" => elvWeightTripleComparison D Sc cutoff bound i j l Λ hal hbj hci β β₃ rfl
local notation "U" => Superfunctor.toFunctor (elvBlockInd D Sc cutoff bound i Λ hci β₂)
local notation "ds" => eqToIso (elvEFunctor_comp₃_pairFirst D Sc cutoff bound i j l Λ hal hbj hci β)
local notation "L" => contentInductionCompTo D Sc cutoff bound (Subtype.val β) [l,j] (Subtype.val β₂)
  hP [i] (Subtype.val β₃) hc₃ hT
local notation "hpFirst" => MonoidalSupercategory.whiskerRight_mem (R := k) (Presentation.obj (pres D Sc) (ob D [j]))
  (firstDot_parity D Sc l [])
local notation "hpMiddle" => MonoidalSupercategory.whiskerLeft_mem (R := k) (Presentation.obj (pres D Sc) (ob D [l]))
  (firstDot_parity D Sc j [])
local notation "htFirst" => MonoidalSupercategory.whiskerRight_mem (R := k) (Presentation.obj (pres D Sc) (ob D [i])) hpFirst
local notation "htMiddle" => MonoidalSupercategory.whiskerRight_mem (R := k) (Presentation.obj (pres D Sc) (ob D [i])) hpMiddle

/-- The first prescribed weight dot intertwines through the selected triple
chart, retaining both subsequent affine right contexts. -/
theorem elvWeightTripleFirstDot_comparison
    (M : ELVWeightProduct D Sc cutoff bound Λ a) :
    (elvWeightTripleFirstDot D Sc cutoff bound i j l Λ hal hbj hci).total M β₃ ≫ (C₃).hom.app M =
      (C₃).hom.app M ≫
        (contentInductionTransform D Sc cutoff bound (σ := [l,j,i]) (τ := [l,j,i]) hT hT htFirst).app
          (D.parity l) (M β) := by
  apply induced_dot_square U ((ds).app M) ((C₂).app M) ((L).app (M β)) ((C₃).app M)
    ((elvInductionComponent D Sc cutoff bound j Λ hbj β₂).map
      ((elvWeightDot D Sc cutoff bound l Λ hal).app (D.parity l) M)) _
    ((contentInductionTransform D Sc cutoff bound hP hP hpFirst).app (D.parity l) (M β)) _
  · simpa only [Iso.app_hom] using
      elvWeightPairComparison_inner_map D Sc cutoff bound j l Λ hal hbj β M
  · simpa only [Iso.app_hom, Iso.app_inv] using
      elvWeightTripleFirstDot_blockSucc D Sc cutoff bound i j l Λ hal hbj hci β M
  · simpa only [Iso.app_hom] using
      elvWeightTripleComparison_pairFirst_hom D Sc cutoff bound i j l Λ hal hbj hci β M
  · exact contentInductionCompTo_inner_map D Sc cutoff bound β.1 [l,j] [l,j] β₂.1 hP hP
      [i] β₃.1 hc₃ hT hT hpFirst (M β)

/-- The middle prescribed weight dot uses the identical selected triple
chart, with the first affine left context and last right context retained. -/
theorem elvWeightTripleMiddleDot_comparison
    (M : ELVWeightProduct D Sc cutoff bound Λ a) :
    (elvWeightTripleMiddleDot D Sc cutoff bound i j l Λ hal hbj hci).total M β₃ ≫ (C₃).hom.app M =
      (C₃).hom.app M ≫
        (contentInductionTransform D Sc cutoff bound (σ := [l,j,i]) (τ := [l,j,i]) hT hT htMiddle).app
          (D.parity j) (M β) := by
  apply induced_dot_square U ((ds).app M) ((C₂).app M) ((L).app (M β)) ((C₃).app M)
    (elvWeightDotComponent D Sc cutoff bound j Λ hbj (D.parity j)
      ((elvEFunctor D Sc cutoff bound l Λ hal).obj M) β₂) _
    ((contentInductionTransform D Sc cutoff bound hP hP hpMiddle).app (D.parity j) (M β)) _
  · simpa only [Iso.app_hom] using
      elvWeightPairComparison_outer_map D Sc cutoff bound j l Λ hal hbj β M
  · simpa only [Iso.app_hom, Iso.app_inv] using
      elvWeightTripleMiddleDot_blockSucc D Sc cutoff bound i j l Λ hal hbj hci β M
  · simpa only [Iso.app_hom] using
      elvWeightTripleComparison_pairFirst_hom D Sc cutoff bound i j l Λ hal hbj hci β M
  · exact contentInductionCompTo_inner_map D Sc cutoff bound β.1 [l,j] [l,j] β₂.1 hP hP
      [i] β₃.1 hc₃ hT hT hpMiddle (M β)

/-- The last prescribed weight dot uses the same selected triple chart;
its input is transported by the even selected pair chart, and its affine
left context is the entire first two-letter word. -/
theorem elvWeightTripleLastDot_comparison
    (M : ELVWeightProduct D Sc cutoff bound Λ a) :
    (elvWeightTripleLastDot D Sc cutoff bound i j l Λ hal hbj hci).total M β₃ ≫ (C₃).hom.app M =
      (C₃).hom.app M ≫
        (contentInductionTransform D Sc cutoff bound (σ := [l,j,i]) (τ := [l,j,i]) hT hT
          (MonoidalSupercategory.whiskerLeft_mem (R := k)
            (Presentation.obj (pres D Sc) (ob D [l,j])) (firstDot_parity D Sc i []))).app
          (D.parity i) (M β) := by
  apply outer_dot_square U
    (eqToIso (elvInductionComponent_obj_blockSucc D Sc cutoff bound i Λ hci β₂
      ((elvE D Sc cutoff bound l Λ hal ≫ elvE D Sc cutoff bound j Λ hbj).obj M)))
    ((C₂).app M) ((L).app (M β)) ((C₃).app M) _
    ((elvBlockDot D Sc cutoff bound i Λ hci β₂).app (D.parity i)
      ((elvE D Sc cutoff bound l Λ hal ≫ elvE D Sc cutoff bound j Λ hbj).obj M β₂))
    ((elvBlockDot D Sc cutoff bound i Λ hci β₂).app (D.parity i)
      ((contentInductionTo D Sc cutoff bound β.1 [l,j] β₂.1 hP).obj (M β))) _
  · simpa only [Iso.app_hom, Iso.app_inv, eqToIso.hom, eqToIso.inv, eqToHom_app] using
      elvWeightTripleLastDot_blockSucc D Sc cutoff bound i j l Λ hal hbj hci β M
  · simpa only [Iso.app_hom, eqToIso.hom, eqToHom_app] using
      elvWeightTripleComparison_pairFirst_hom D Sc cutoff bound i j l Λ hal hbj hci β M
  · simp only [Iso.app_hom]
    exact triple_dot_even_naturality U (elvBlockDot D Sc cutoff bound i Λ hci β₂)
      (D.parity i) ((C₂).hom.app M)
      (elvWeightPairComparison_mem D Sc cutoff bound j l Λ hal hbj β β₂ rfl M).1
  · exact contentInductionCompTo_outer_map D Sc cutoff bound β.1 [l,j] [i] [i]
      β₂.1 β₃.1 hP hc₃ hc₃ hT hT (firstDot_parity D Sc i []) (M β)

end OddMath.QuiverHecke.ELVOld
