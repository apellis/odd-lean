import OddMath.QuiverHecke.CyclotomicAction.KernelEntryDegrees
import OddMath.QuiverHecke.CyclotomicAction.WeightTripleBraid.WeightAbsentCapInverse

/-!
# Weight triple comparison

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # Native distinct-colour dot slides

Brundan--Ellis (1.8), the two distinct-colour fields of
RouquierMulticolour on the prescribed original-weight generators.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELV
universe u
section Totals
variable {k : Type u} [CommRing k] {C B : Type*} [Category* C] [Category* B]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive B] [Linear k B] [Supercategory k B]
private theorem supernatural_total_smul {F G : Superfunctor k C B}
    (s : k) (c : F ⟶ G) (M : C) : (s • c).total M = s • c.total M :=
  (supernaturalTotalLinearMap F G M).map_smul s c
end Totals

section Evaluation
variable {k : Type u} [CommRing k] {C : Type*} [Category* C]
  [Preadditive C] [Linear k C] [Supercategory k C]
  {J : Type u} {A : J → Type u}
  [∀ j, Category.{u} (A j)] [∀ j, Preadditive (A j)]
  [∀ j, Linear k (A j)] [∀ j, Supercategory k (A j)]
  {F G : Superfunctor k C (∀ j, Superfunctor k (A j) (SVec k))}
private theorem moduleFamily_crossSlide_of_components
    (c : F ⟶ G) (x : F ⟶ F) (y : G ⟶ G) (s : k)
    (h : ∀ M t w, ModuleCrossSlide (c.total M t) (x.total M t) (y.total M t) w s) :
    x ≫ c = s • (c ≫ y) := by
  apply supernatural_hom_ext_total
  intro M
  rw [Superfunctor.comp_total, supernatural_total_smul, Superfunctor.comp_total]
  funext t
  change x.total M t ≫ c.total M t = s • (c.total M t ≫ y.total M t)
  apply FiniteSupermodule.hom_ext_total
  intro w
  rw [Superfunctor.comp_total, supernatural_total_smul, Superfunctor.comp_total]
  exact h M t w
end Evaluation

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i j : I) (Λ : X) {x₀ x₁ x₂ x₃ : X}
  (h₁ : x₀ + D.α j = x₁) (h₂ : x₁ + D.α i = x₃)
  (h₃ : x₀ + D.α i = x₂) (h₄ : x₂ + D.α j = x₃)

theorem elvActionCross_slideLeft_distinct (hij : i ≠ j) :
    elvE D Sc cutoff bound j Λ h₁ ◁ elvActionDot D Sc cutoff bound i Λ h₂ ≫
      elvActionCross D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ =
    SKM.zsign k (D.parity i * D.parity j) •
      (elvActionCross D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ ≫
        elvActionDot D Sc cutoff bound i Λ h₃ ▷ elvE D Sc cutoff bound j Λ h₄) := by
  rw [← sign_eq_zsign]
  apply moduleFamily_crossSlide_of_components
  intro M ε w
  rw [supernatural_total_of_mem (elvActionCross_mem D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄) M,
    supernatural_total_of_mem (TwoSupercategory.whiskerLeft_mem
      (elvE D Sc cutoff bound j Λ h₁) (elvActionDot_mem D Sc cutoff bound i Λ h₂)) M,
    supernatural_total_of_mem (TwoSupercategory.whiskerRight_mem
      (elvE D Sc cutoff bound j Λ h₄) (elvActionDot_mem D Sc cutoff bound i Λ h₃)) M]
  exact elvWeightDistinct_slideLeft_component D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ hij M ε w

theorem elvActionCross_slideRight_distinct (hij : i ≠ j) :
    elvActionCross D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ ≫
      elvE D Sc cutoff bound i Λ h₃ ◁ elvActionDot D Sc cutoff bound j Λ h₄ =
    SKM.zsign k (D.parity i * D.parity j) •
      (elvActionDot D Sc cutoff bound j Λ h₁ ▷ elvE D Sc cutoff bound i Λ h₂ ≫
        elvActionCross D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄) := by
  have h : elvActionDot D Sc cutoff bound j Λ h₁ ▷ elvE D Sc cutoff bound i Λ h₂ ≫
      elvActionCross D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ =
      sign k (D.parity i * D.parity j) •
        (elvActionCross D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ ≫
          elvE D Sc cutoff bound i Λ h₃ ◁ elvActionDot D Sc cutoff bound j Λ h₄) := by
    apply moduleFamily_crossSlide_of_components
    intro M ε w
    rw [supernatural_total_of_mem (elvActionCross_mem D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄) M,
      supernatural_total_of_mem (TwoSupercategory.whiskerRight_mem
        (elvE D Sc cutoff bound i Λ h₂) (elvActionDot_mem D Sc cutoff bound j Λ h₁)) M,
      supernatural_total_of_mem (TwoSupercategory.whiskerLeft_mem
        (elvE D Sc cutoff bound i Λ h₃) (elvActionDot_mem D Sc cutoff bound j Λ h₄)) M]
    exact elvWeightDistinct_slideRight_component D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ hij M ε w
  rw [← sign_eq_zsign]
  have hh := congrArg (fun z => sign k (D.parity i * D.parity j) • z) h
  simpa only [smul_smul, Supercategory.sign_mul_self, one_smul] using hh.symm
end OddMath.QuiverHecke.ELV
end

end

section

/-! # Triple comparisons at common stored predecessor blocks

Brundan--Ellis (1.9), multicolour triple transport. Swapped first pairs
share their actual second predecessor block while their successor
constructors have different orders. Retain that common block explicitly
in the already selected triple and pair comparisons.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i j l : I) (Λ : X) {x₀ x₁ x₂ x₃ : X}
  (h₁ : x₀ + D.α l = x₁) (h₂ : x₁ + D.α j = x₂) (h₃ : x₂ + D.α i = x₃)
  (β : WeightBlocks D Λ x₀) (δ : WeightBlocks D Λ x₂) (ε : WeightBlocks D Λ x₃)
  (hδ : blockSucc₂ D j l Λ h₁ h₂ β = δ)
  (hε : blockSucc D Λ i h₃ δ = ε)

include hδ hε in
/-- A common actual pair block supplies the selected triple predecessor witness. -/
theorem elvBlockSucc₃_eq_of_pair : elvBlockSucc₃ D i j l Λ h₁ h₂ h₃ β = ε :=
  (congrArg (blockSucc D Λ i h₃) hδ).trans hε

include hε in
/-- The literal last-content equality at the chosen common block. -/
theorem elvBlockSucc_content_eq_of_eq : δ.1 + ([i] : Multiset I) = ε.1 :=
  (elvBlockSucc_content_eq D i Λ h₃ δ).trans (congrArg Subtype.val hε)

/-- Outer dispatch uses the actual common pair coordinate before flattening. -/
theorem elvEFunctor_comp₃_pairBlock :
    (elvEFunctor D Sc cutoff bound l Λ h₁ ⋙ elvEFunctor D Sc cutoff bound j Λ h₂) ⋙
      (elvInductionComponent D Sc cutoff bound i Λ h₃ ε).toFunctor =
    (elvEFunctor D Sc cutoff bound l Λ h₁ ⋙
      (elvInductionComponent D Sc cutoff bound j Λ h₂ δ).toFunctor) ⋙
      contentInductionTo D Sc cutoff bound δ.1 [i] ε.1
        (elvBlockSucc_content_eq_of_eq D i Λ h₃ δ ε hε) := by
  cases hε
  rw [elvInductionComponent_blockSucc]
  rfl

local notation "hc" => elvBlockSucc_content_eq_of_eq D i Λ h₃ δ ε hε
local notation "hp" => elvWeightPair_content_eq D j l Λ h₁ h₂ β δ hδ
local notation "ht" => elvWeightTriple_content_eq D i j l Λ h₁ h₂ h₃ β ε
  (elvBlockSucc₃_eq_of_pair D i j l Λ h₁ h₂ h₃ β δ ε hδ hε)
local notation "C₃" => elvWeightTripleComparison D Sc cutoff bound i j l Λ h₁ h₂ h₃ β ε
  (elvBlockSucc₃_eq_of_pair D i j l Λ h₁ h₂ h₃ β δ ε hδ hε)
local notation "C₂" => elvWeightPairComparison D Sc cutoff bound j l Λ h₁ h₂ β δ hδ
local notation "R" => Superfunctor.toFunctor (elvBlockEval D Sc cutoff bound Λ β)
local notation "U" => contentInductionTo D Sc cutoff bound (Subtype.val δ) [i] (Subtype.val ε) hc
local notation "Q" => contentInductionTo D Sc cutoff bound (Subtype.val β) [l,j] (Subtype.val δ) hp
local notation "L" => contentInductionCompTo D Sc cutoff bound (Subtype.val β) [l,j] (Subtype.val δ)
  hp [i] (Subtype.val ε) hc ht

/-- The same selected factorization on native module components. -/
theorem elvWeightTripleComparison_pairBlock_hom
    (M : ELVWeightProduct D Sc cutoff bound Λ x₀) :
    (C₃).hom.app M =
      (eqToIso (elvEFunctor_comp₃_pairBlock D Sc cutoff bound i j l Λ h₁ h₂ h₃ δ ε hε)).hom.app M ≫
        (U).map ((C₂).hom.app M) ≫ (L).hom.app (M β) := by
  cases hδ
  cases hε
  exact elvWeightTripleComparison_pairFirst_hom D Sc cutoff bound i j l Λ h₁ h₂ h₃ β M

end OddMath.QuiverHecke.ELV
end

end

section

/-! # The first prescribed multicolour crossing on three inductions

Brundan--Ellis (1.9). Evaluate the first adjacent crossing with both
weight paths and their common stored second predecessor retained.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELV
universe u
private theorem prefix_total_whiskerRight
    {k : Type u} [CommRing k]
    {A B C : PiSCat.{u, u, u + 1} k} {F G : A ⟶ B}
    (f : F ⟶ G) (H : B ⟶ C) (M : A) :
    (f ▷ H).total M = H.map (f.total M) := by
  change H.map (f.app 0 M) + H.map (f.app 1 M) = H.map (f.app 0 M + f.app 1 M)
  exact H.toFunctor.map_add.symm
private theorem reassociated_cross_total
    {k : Type u} [CommRing k]
    {A B B' C E : PiSCat.{u, u, u + 1} k}
    (F : A ⟶ B) (G : B ⟶ C) (F' : A ⟶ B') (G' : B' ⟶ C) (H : C ⟶ E)
    (x : F ≫ G ⟶ F' ≫ G') (M : A) :
    ((associator F G H).inv ≫ x ▷ H ≫ (associator F' G' H).hom).total M = H.map (x.total M) := by
  erw [PiSCat.associator_inv, PiSCat.associator_hom, Category.id_comp, Category.comp_id]
  exact prefix_total_whiskerRight x H M

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i j l : I) (Λ : X) {a b b' c d : X}
  (hal : a + D.α l = b) (hlj : b + D.α j = c)
  (haj : a + D.α j = b') (hjl : b' + D.α l = c) (hci : c + D.α i = d)
local notation "E₁" => elvE D Sc cutoff bound l Λ hal
local notation "E₂" => elvE D Sc cutoff bound j Λ hlj
local notation "E₁'" => elvE D Sc cutoff bound j Λ haj
local notation "E₂'" => elvE D Sc cutoff bound l Λ hjl
local notation "E₃" => elvE D Sc cutoff bound i Λ hci
local notation "p" => D.parity j * D.parity l

/-- The first given crossing on two weight paths, reassociated through the same last induction. -/
abbrev elvWeightPrefixCross : E₁ ≫ E₂ ≫ E₃ ⟶ E₁' ≫ E₂' ≫ E₃ :=
  (associator E₁ E₂ E₃).inv ≫
    elvActionCross D Sc cutoff bound j l Λ hal hlj haj hjl ▷ E₃ ≫
      (associator E₁' E₂' E₃).hom

/-- The literal reassociated multicolour crossing is mapped by the selected outer induction. -/
theorem elvWeightPrefixCross_total
    (M : ELVWeightProduct D Sc cutoff bound Λ a) (ε : WeightBlocks D Λ d) :
    (elvWeightPrefixCross D Sc cutoff bound i j l Λ hal hlj haj hjl hci).total M ε =
      (elvInductionComponent D Sc cutoff bound i Λ hci ε).map
        ((elvActionCross D Sc cutoff bound j l Λ hal hlj haj hjl).total M) :=
  congrFun (reassociated_cross_total E₁ E₂ E₁' E₂' E₃
    (elvActionCross D Sc cutoff bound j l Λ hal hlj haj hjl) M) ε

section Supported
variable (β : WeightBlocks D Λ a) (δ : WeightBlocks D Λ c) (ε : WeightBlocks D Λ d)
  (hδ : blockSucc₂ D j l Λ hal hlj β = δ) (hε : blockSucc D Λ i hci δ = ε)
local notation "htδ" => blockSucc₂_swap D j l Λ hal hlj haj hjl hδ
local notation "U" => contentInductionTo D Sc cutoff bound (Subtype.val δ) [i] (Subtype.val ε)
  (elvBlockSucc_content_eq_of_eq D i Λ hci δ ε hε)
local notation "hs" => elvEFunctor_comp₃_pairBlock D Sc cutoff bound i j l Λ hal hlj hci δ ε hε
local notation "ht" => elvEFunctor_comp₃_pairBlock D Sc cutoff bound i l j Λ haj hjl hci δ ε hε

/-- Supported components retain the common predecessor and both literal dispatch casts. -/
theorem elvWeightPrefixCross_pairBlock
    (M : ELVWeightProduct D Sc cutoff bound Λ a) :
    (elvWeightPrefixCross D Sc cutoff bound i j l Λ hal hlj haj hjl hci).total M ε =
      (eqToIso hs).hom.app M ≫
        (U).map ((elvWeightCrossVia D Sc cutoff bound j l Λ hal hlj haj hjl β δ hδ).app p M) ≫
          (eqToIso ht).inv.app M := by
  cases hε
  have h₀ := elvWeightPrefixCross_total D Sc cutoff bound i j l Λ hal hlj haj hjl hci M (blockSucc D Λ i hci δ)
  have hm := elvInductionComponent_map_blockSucc D Sc cutoff bound i Λ hci δ
    ((elvActionCross D Sc cutoff bound j l Λ hal hlj haj hjl).total M)
  have hc := congrFun (supernatural_total_of_mem
    (elvActionCross_mem D Sc cutoff bound j l Λ hal hlj haj hjl) M) δ
  have ha : (elvActionCross D Sc cutoff bound j l Λ hal hlj haj hjl).app p M δ =
    elvWeightCrossComponent D Sc cutoff bound j l Λ hal hlj haj hjl p M δ := rfl
  have hv := elvWeightCrossComponent_of D Sc cutoff bound j l Λ hal hlj haj hjl p M β δ hδ
  have hx := hc.trans (ha.trans hv)
  have hr := congrArg
    (fun (f : (E₁ ≫ E₂).obj M δ ⟶ (E₁' ≫ E₂').obj M δ) =>
      eqToHom (elvInductionComponent_obj_blockSucc D Sc cutoff bound i Λ hci δ ((E₁ ≫ E₂).obj M)) ≫
        (elvBlockInd D Sc cutoff bound i Λ hci δ).map f ≫
          eqToHom (elvInductionComponent_obj_blockSucc D Sc cutoff bound i Λ hci δ ((E₁' ≫ E₂').obj M)).symm) hx
  simp only [eqToIso.hom, eqToIso.inv, eqToHom_app]
  exact h₀.trans (hm.trans hr)
end Supported

end OddMath.QuiverHecke.ELV
end

end

section

/-! # The prescribed multicolour prefix crossing in the triple charts

Brundan--Ellis (1.9). Both weight paths use their independently selected
triple charts, the same stored second predecessor and the prescribed
normalized affine prefix. No crossing comparison is assumed.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELV
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

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Triple comparison through a pair at a specified output block

Brundan--Ellis (1.9), multicolour suffix transport. Retain the common
first predecessor and specified final block when the last two colours
are swapped. Both paths use their already selected charts.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i j l : I) (Λ : X) {x₀ x₁ x₂ x₃ : X}
  (h₁ : x₀ + D.α l = x₁) (h₂ : x₁ + D.α j = x₂) (h₃ : x₂ + D.α i = x₃)
  (β : WeightBlocks D Λ x₀) (ε : WeightBlocks D Λ x₃)
  (hε : blockSucc₂ D i j Λ h₂ h₃ (blockSucc D Λ l h₁ β) = ε)
local notation "β₁" => blockSucc D Λ l h₁ β
local notation "E₁" => elvEFunctor D Sc cutoff bound l Λ h₁
local notation "R₁" => Superfunctor.toFunctor (elvBlockEval D Sc cutoff bound Λ β₁)
local notation "R" => Superfunctor.toFunctor (elvBlockEval D Sc cutoff bound Λ β)
local notation "J" => Superfunctor.toFunctor (elvBlockInd D Sc cutoff bound l Λ h₁ β)
local notation "hc₁" => elvBlockSucc_content_eq D l Λ h₁ β
local notation "hQ" => elvWeightPair_content_eq D i j Λ h₂ h₃ β₁ ε hε
local notation "hT" => elvWeightTriple_content_eq D i j l Λ h₁ h₂ h₃ β ε hε
local notation "Q" => contentInductionTo D Sc cutoff bound (Subtype.val β₁) [j,i] (Subtype.val ε) hQ
local notation "L" => contentInductionCompTo D Sc cutoff bound (Subtype.val β) [l] (Subtype.val β₁) hc₁
  [j,i] (Subtype.val ε) hQ hT
local notation "C₃" => elvWeightTripleComparison D Sc cutoff bound i j l Λ h₁ h₂ h₃ β ε hε
local notation "C₂" => elvWeightPairComparison D Sc cutoff bound i j Λ h₂ h₃ β₁ ε hε
local notation "hv" => elvEFunctor_blockSucc_eval D Sc cutoff bound l Λ h₁ β

/-- Native component, retaining the first-value dispatch under the chosen pair-word induction. -/
theorem elvWeightTripleComparison_lastBlock_hom
    (M : ELVWeightProduct D Sc cutoff bound Λ x₀) :
    (C₃).hom.app M = (C₂).hom.app ((E₁).obj M) ≫
      (Q).map ((eqToIso hv).hom.app M) ≫ (L).hom.app (M β) := by
  cases hε
  exact elvWeightTripleComparison_pairLast_hom D Sc cutoff bound i j l Λ h₁ h₂ h₃ β M

end OddMath.QuiverHecke.ELV
end

end

section

/-! # The second prescribed multicolour crossing on three inductions

Brundan--Ellis (1.9). The last-pair crossing is evaluated on the actual
first induced product, with its common first predecessor and both
last-pair weight paths retained.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i j l : I) (Λ : X) {a b c c' d : X}
  (hal : a + D.α l = b) (hbj : b + D.α j = c) (hci : c + D.α i = d)
  (hbi : b + D.α i = c') (hcj : c' + D.α j = d)
local notation "E₁" => elvE D Sc cutoff bound l Λ hal
local notation "E₂" => elvE D Sc cutoff bound j Λ hbj
local notation "E₃" => elvE D Sc cutoff bound i Λ hci
local notation "E₂'" => elvE D Sc cutoff bound i Λ hbi
local notation "E₃'" => elvE D Sc cutoff bound j Λ hcj
local notation "p" => D.parity i * D.parity j

/-- The second given crossing, after the literal first weight induction. -/
abbrev elvWeightSuffixCross : E₁ ≫ E₂ ≫ E₃ ⟶ E₁ ≫ E₂' ≫ E₃' :=
  E₁ ◁ elvActionCross D Sc cutoff bound i j Λ hbj hci hbi hcj

/-- The literal suffix uses the prescribed component on the actual first-induced product. -/
theorem elvWeightSuffixCross_total
    (M : ELVWeightProduct D Sc cutoff bound Λ a) (ε : WeightBlocks D Λ d) :
    (elvWeightSuffixCross D Sc cutoff bound i j l Λ hal hbj hci hbi hcj).total M ε =
      elvWeightCrossComponent D Sc cutoff bound i j Λ hbj hci hbi hcj p
        ((elvEFunctor D Sc cutoff bound l Λ hal).obj M) ε :=
  congrFun (supernatural_total_of_mem
    (elvActionCross_mem D Sc cutoff bound i j Λ hbj hci hbi hcj) ((E₁).obj M)) ε

/-- The given suffix crossing at its common first predecessor and specified output. -/
theorem elvWeightSuffixCross_lastBlock
    (β : WeightBlocks D Λ a) (ε : WeightBlocks D Λ d)
    (hε : blockSucc₂ D i j Λ hbj hci (blockSucc D Λ l hal β) = ε)
    (M : ELVWeightProduct D Sc cutoff bound Λ a) :
    (elvWeightSuffixCross D Sc cutoff bound i j l Λ hal hbj hci hbi hcj).total M ε =
      (elvWeightCrossVia D Sc cutoff bound i j Λ hbj hci hbi hcj
        (blockSucc D Λ l hal β) ε hε).app p ((elvEFunctor D Sc cutoff bound l Λ hal).obj M) := by
  rw [elvWeightSuffixCross_total]
  exact elvWeightCrossComponent_of D Sc cutoff bound i j Λ hbj hci hbi hcj p _ _ ε hε

end OddMath.QuiverHecke.ELV
end

end

section

/-! # The prescribed multicolour suffix in the selected triple charts

Brundan--Ellis (1.9). Retain the common first predecessor and its even
value comparison while intertwining the last pair through the two
independently selected triple charts.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELV
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

end OddMath.QuiverHecke.ELV
end

end

section

/-! # The six multicolour braid comparisons on the chosen weight paths

Brundan--Ellis (1.9), outside the repeated-outer correction case. All six
permutation paths keep the actual intermediate original-weight blocks.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELV
universe u
private theorem compose_square {C : Type*} [Category* C]
    {X₀ X₁ X₂ W₀ W₁ W₂ : C}
    (e₀ : X₀ ⟶ W₀) (e₁ : X₁ ⟶ W₁) (e₂ : X₂ ⟶ W₂)
    (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (a : W₀ ⟶ W₁) (b : W₁ ⟶ W₂)
    (hf : f ≫ e₁ = e₀ ≫ a) (hg : g ≫ e₂ = e₁ ≫ b) :
    (f ≫ g) ≫ e₂ = e₀ ≫ (a ≫ b) := by
  rw [Category.assoc, hg, ← Category.assoc, hf, Category.assoc]
private theorem braid_of_six_squares {C : Type*} [Category* C]
    {X₀ X₁ X₂ X₃ X₄ X₅ W₀ W₁ W₂ W₃ W₄ W₅ : C}
    (e₀ : X₀ ≅ W₀) (e₁ : X₁ ≅ W₁) (e₂ : X₂ ≅ W₂)
    (e₃ : X₃ ≅ W₃) (e₄ : X₄ ≅ W₄) (e₅ : X₅ ≅ W₅)
    (a₀ : X₀ ⟶ X₁) (a₁ : X₁ ⟶ X₂) (a₂ : X₂ ⟶ X₃)
    (b₀ : X₀ ⟶ X₄) (b₁ : X₄ ⟶ X₅) (b₂ : X₅ ⟶ X₃)
    (c₀ : W₀ ⟶ W₁) (c₁ : W₁ ⟶ W₂) (c₂ : W₂ ⟶ W₃)
    (d₀ : W₀ ⟶ W₄) (d₁ : W₄ ⟶ W₅) (d₂ : W₅ ⟶ W₃)
    (ha₀ : a₀ ≫ e₁.hom = e₀.hom ≫ c₀) (ha₁ : a₁ ≫ e₂.hom = e₁.hom ≫ c₁)
    (ha₂ : a₂ ≫ e₃.hom = e₂.hom ≫ c₂) (hb₀ : b₀ ≫ e₄.hom = e₀.hom ≫ d₀)
    (hb₁ : b₁ ≫ e₅.hom = e₄.hom ≫ d₁) (hb₂ : b₂ ≫ e₃.hom = e₅.hom ≫ d₂)
    (hh : c₀ ≫ c₁ ≫ c₂ = d₀ ≫ d₁ ≫ d₂) :
    a₀ ≫ a₁ ≫ a₂ = b₀ ≫ b₁ ≫ b₂ := by
  have hA := compose_square e₀.hom e₁.hom e₃.hom a₀ (a₁ ≫ a₂) c₀ (c₁ ≫ c₂) ha₀
    (compose_square e₁.hom e₂.hom e₃.hom a₁ a₂ c₁ c₂ ha₁ ha₂)
  have hB := compose_square e₀.hom e₄.hom e₃.hom b₀ (b₁ ≫ b₂) d₀ (d₁ ≫ d₂) hb₀
    (compose_square e₄.hom e₅.hom e₃.hom b₁ b₂ d₁ d₂ hb₁ hb₂)
  exact (cancel_mono e₃.hom).1
    (hA.trans ((congrArg (fun z => e₀.hom ≫ z) hh).trans hB.symm))

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i j l : I) (Λ : X) {a bl bj bi clj cli cji d : X}
  (hal : a + D.α l = bl) (haj : a + D.α j = bj) (hai : a + D.α i = bi)
  (hlj : bl + D.α j = clj) (hli : bl + D.α i = cli) (hjl : bj + D.α l = clj)
  (hji : bj + D.α i = cji) (hil : bi + D.α l = cli) (hij : bi + D.α j = cji)
  (hd₁ : clj + D.α i = d) (hd₂ : cli + D.α j = d) (hd₃ : cji + D.α l = d)
local notation "a₀" => elvWeightSuffixCross D Sc cutoff bound i j l Λ hal hlj hd₁ hli hd₂
local notation "a₁" => elvWeightPrefixCross D Sc cutoff bound j i l Λ hal hli hai hil hd₂
local notation "a₂" => elvWeightSuffixCross D Sc cutoff bound j l i Λ hai hil hd₂ hij hd₃
local notation "b₀" => elvWeightPrefixCross D Sc cutoff bound i j l Λ hal hlj haj hjl hd₁
local notation "b₁" => elvWeightSuffixCross D Sc cutoff bound i l j Λ haj hjl hd₁ hji hd₃
local notation "b₂" => elvWeightPrefixCross D Sc cutoff bound l i j Λ haj hji hai hij hd₃

variable (β : WeightBlocks D Λ a)
local notation "βl" => blockSucc D Λ l hal β
local notation "βi" => blockSucc D Λ i hai β
local notation "βj" => blockSucc D Λ j haj β
local notation "δ₀" => blockSucc₂ D j l Λ hal hlj β
local notation "δA" => blockSucc₂ D i l Λ hal hli β
local notation "δB" => blockSucc₂ D i j Λ haj hji β
local notation "ε" => elvBlockSucc₃ D i j l Λ hal hlj hd₁ β
local notation "hA₁" => blockSucc₂_swap D i j Λ hlj hd₁ hli hd₂ (β := βl) rfl
local notation "hA₂" => elvBlockSucc₃_eq_of_pair D j l i Λ hai hil hd₂ β δA ε
  (blockSucc₂_swap D i l Λ hal hli hai hil rfl) hA₁
local notation "hA₃" => blockSucc₂_swap D j l Λ hil hd₂ hij hd₃ (β := βi) hA₂
local notation "hB₁" => elvBlockSucc₃_eq_of_pair D i l j Λ haj hjl hd₁ β δ₀ ε
  (blockSucc₂_swap D j l Λ hal hlj haj hjl rfl) rfl
local notation "hB₂" => blockSucc₂_swap D i l Λ hjl hd₁ hji hd₃ (β := βj) hB₁
local notation "C₀" => elvWeightTripleComparison D Sc cutoff bound i j l Λ hal hlj hd₁ β ε rfl
local notation "C₁" => elvWeightTripleComparison D Sc cutoff bound j i l Λ hal hli hd₂ β ε hA₁
local notation "C₂" => elvWeightTripleComparison D Sc cutoff bound j l i Λ hai hil hd₂ β ε hA₂
local notation "C₃" => elvWeightTripleComparison D Sc cutoff bound l j i Λ hai hij hd₃ β ε hA₃
local notation "C₄" => elvWeightTripleComparison D Sc cutoff bound i l j Λ haj hjl hd₁ β ε hB₁
local notation "C₅" => elvWeightTripleComparison D Sc cutoff bound l i j Λ haj hji hd₃ β ε hB₂
local notation "h₃" => elvBlockTriple_content_eq D i j l Λ hal hlj hd₁ β
local notation "h₅" => elvWeightTriple_content_eq D j i l Λ hal hli hd₂ β ε hA₁
local notation "h₄" => elvWeightTriple_content_eq D j l i Λ hai hil hd₂ β ε hA₂
local notation "h₀" => elvWeightTriple_content_eq D l j i Λ hai hij hd₃ β ε hA₃
local notation "h₂" => elvWeightTriple_content_eq D i l j Λ haj hjl hd₁ β ε hB₁
local notation "h₁" => elvWeightTriple_content_eq D l i j Λ haj hji hd₃ β ε hB₂
local notation "c₀" => SuperNatTrans.app (contentInductionTransform D Sc cutoff bound h₅ h₃
  (contentNormalizedRight_mem D Sc l i j)) (D.parity i * D.parity j)
local notation "c₁" => SuperNatTrans.app (contentInductionTransform D Sc cutoff bound h₄ h₅
  (contentNormalizedLeft_mem D Sc i l j)) (D.parity i * D.parity l)
local notation "c₂" => SuperNatTrans.app (contentInductionTransform D Sc cutoff bound h₀ h₄
  (contentNormalizedRight_mem D Sc i j l)) (D.parity j * D.parity l)
local notation "d₀" => SuperNatTrans.app (contentInductionTransform D Sc cutoff bound h₂ h₃
  (contentNormalizedLeft_mem D Sc j l i)) (D.parity j * D.parity l)
local notation "d₁" => SuperNatTrans.app (contentInductionTransform D Sc cutoff bound h₁ h₂
  (contentNormalizedRight_mem D Sc j i l)) (D.parity i * D.parity l)
local notation "d₂" => SuperNatTrans.app (contentInductionTransform D Sc cutoff bound h₀ h₁
  (contentNormalizedLeft_mem D Sc i j l)) (D.parity i * D.parity j)

/-- The two prescribed braid paths agree at every supported output block,
outside the repeated-outer corrected case. All six charts are chosen. -/
theorem elvWeightBraid_paths (hb : ¬ (i = l ∧ i ≠ j))
    (M : ELVWeightProduct D Sc cutoff bound Λ a) :
    (a₀).total M ε ≫ (a₁).total M ε ≫ (a₂).total M ε =
      (b₀).total M ε ≫ (b₁).total M ε ≫ (b₂).total M ε := by
  apply braid_of_six_squares ((C₀).app M) ((C₁).app M) ((C₂).app M)
    ((C₃).app M) ((C₄).app M) ((C₅).app M)
    ((a₀).total M ε) ((a₁).total M ε) ((a₂).total M ε)
    ((b₀).total M ε) ((b₁).total M ε) ((b₂).total M ε)
    (c₀ (M β)) (c₁ (M β)) (c₂ (M β)) (d₀ (M β)) (d₁ (M β)) (d₂ (M β))
  · exact elvWeightSuffixCross_comparison D Sc cutoff bound i j l Λ hal hlj hd₁ hli hd₂ β ε rfl M
  · exact elvWeightPrefixCross_comparison D Sc cutoff bound j i l Λ hal hli hai hil hd₂ β δA ε rfl hA₁ M
  · exact elvWeightSuffixCross_comparison D Sc cutoff bound j l i Λ hai hil hd₂ hij hd₃ β ε hA₂ M
  · exact elvWeightPrefixCross_comparison D Sc cutoff bound i j l Λ hal hlj haj hjl hd₁ β δ₀ ε rfl rfl M
  · exact elvWeightSuffixCross_comparison D Sc cutoff bound i l j Λ haj hjl hd₁ hji hd₃ β ε hB₁ M
  · exact elvWeightPrefixCross_comparison D Sc cutoff bound l i j Λ haj hji hai hij hd₃ β δB ε rfl hB₂ M
  · exact contentInduction_uncorrected_braid D Sc cutoff bound β.1 i j l hb ε.1
      h₀ h₁ h₂ h₃ h₄ h₅ (M β)

end OddMath.QuiverHecke.ELV
end

end

section

/-! # The prescribed multicolour braid of the weight action

Brundan--Ellis (1.9) outside the repeated-outer correction case. The six
selected chart squares prove the equality for all input modules and all
output blocks, including absent predecessor sectors.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELV
universe u
private theorem total_three {k : Type u} [CommRing k]
    {A B : PiSCat.{u, u, u + 1} k} {F₀ F₁ F₂ F₃ : A ⟶ B}
    (f : F₀ ⟶ F₁) (g : F₁ ⟶ F₂) (h : F₂ ⟶ F₃) (M : A) :
    (f ≫ g ≫ h).total M = f.total M ≫ g.total M ≫ h.total M := by
  rw [Superfunctor.comp_total, Superfunctor.comp_total]

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i j l : I) (Λ : X) {a bl bj bi clj cli cji d : X}
  (hal : a + D.α l = bl) (haj : a + D.α j = bj) (hai : a + D.α i = bi)
  (hlj : bl + D.α j = clj) (hli : bl + D.α i = cli) (hjl : bj + D.α l = clj)
  (hji : bj + D.α i = cji) (hil : bi + D.α l = cli) (hij : bi + D.α j = cji)
  (hd₁ : clj + D.α i = d) (hd₂ : cli + D.α j = d) (hd₃ : cji + D.α l = d)
local notation "a₀" => elvWeightSuffixCross D Sc cutoff bound i j l Λ hal hlj hd₁ hli hd₂
local notation "a₁" => elvWeightPrefixCross D Sc cutoff bound j i l Λ hal hli hai hil hd₂
local notation "a₂" => elvWeightSuffixCross D Sc cutoff bound j l i Λ hai hil hd₂ hij hd₃
local notation "b₀" => elvWeightPrefixCross D Sc cutoff bound i j l Λ hal hlj haj hjl hd₁
local notation "b₁" => elvWeightSuffixCross D Sc cutoff bound i l j Λ haj hjl hd₁ hji hd₃
local notation "b₂" => elvWeightPrefixCross D Sc cutoff bound l i j Λ haj hji hai hij hd₃

/-- The given six multicolour crossing natural transformations satisfy
the uncorrected braid on all input modules and every output block. -/
theorem elvActionCross_multicolour_braid (hb : ¬ (i = l ∧ i ≠ j)) :
    a₀ ≫ a₁ ≫ a₂ = b₀ ≫ b₁ ≫ b₂ := by
  apply supernatural_hom_ext_total
  intro M
  funext ε
  have hL := congrFun (total_three a₀ a₁ a₂ M) ε
  have hR := congrFun (total_three b₀ b₁ b₂ M) ε
  by_cases hs : ∃ β, elvBlockSucc₃ D i j l Λ hal hlj hd₁ β = ε
  · obtain ⟨β, rfl⟩ := hs
    have h := elvWeightBraid_paths D Sc cutoff bound i j l Λ
      hal haj hai hlj hli hjl hji hil hij hd₁ hd₂ hd₃ β hb M
    exact hL.trans (h.trans hR.symm)
  · have hz := elvEFunctor_comp₃_isZero D Sc cutoff bound i j l Λ hal hlj hd₁ ε hs M
    exact hL.trans ((hz.eq_of_src _ _).trans hR.symm)

end OddMath.QuiverHecke.ELV
end

end

section

/-! # The general multicolour braid field of the chosen weight data

Brundan--Ellis (1.9), outside the repeated-outer correction case. The
field retains every prescribed crossing and associator on all weights.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i j l : I) (Λ : X) {a bl bj bi clj cli cji d : X}
  (hal : a + D.α l = bl) (haj : a + D.α j = bj) (hai : a + D.α i = bi)
  (hlj : bl + D.α j = clj) (hli : bl + D.α i = cli) (hjl : bj + D.α l = clj)
  (hji : bj + D.α i = cji) (hil : bi + D.α l = cli) (hij : bi + D.α j = cji)
  (hd₁ : clj + D.α i = d) (hd₂ : cli + D.α j = d) (hd₃ : cji + D.α l = d)

/-- Exactly the uncorrected RouquierMulticolour braid field for the
independently selected weight data, with only the source colour condition. -/
theorem elvRouquierData_multicolour_braid (hb : ¬ (i = l ∧ i ≠ j)) :
    rouquierMulticolourBraidEquation D (elvRouquierData D Sc cutoff bound Λ)
      i j l hal haj hai hlj hli hjl hji hil hij hd₁ hd₂ hd₃ := by
  apply rouquierMulticolourBraidEquation_of_paths
  have h := elvActionCross_multicolour_braid D Sc cutoff bound i j l Λ
    hal haj hai hlj hli hjl hji hil hij hd₁ hd₂ hd₃ hb
  simp only [elvRouquierData, elvWeightPrefixCross, elvWeightSuffixCross] at h ⊢
  convert h using 1

end OddMath.QuiverHecke.ELV
end

end

section

/-! # The repeated-outer braid paths in common triple charts

Brundan--Ellis (1.9). All six given crossing maps retain their actual
intermediate weight blocks and independently selected comparison isos.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELV
universe u
private theorem compose_square_2 {C : Type*} [Category* C]
    {X₀ X₁ X₂ W₀ W₁ W₂ : C}
    (e₀ : X₀ ⟶ W₀) (e₁ : X₁ ⟶ W₁) (e₂ : X₂ ⟶ W₂)
    (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (a : W₀ ⟶ W₁) (b : W₁ ⟶ W₂)
    (hf : f ≫ e₁ = e₀ ≫ a) (hg : g ≫ e₂ = e₁ ≫ b) :
    (f ≫ g) ≫ e₂ = e₀ ≫ (a ≫ b) := by
  rw [Category.assoc, hg, ← Category.assoc, hf, Category.assoc]
private theorem path_difference_square {C : Type*} [Category* C] [Preadditive C]
    {X₀ X₁ X₂ W₀ W₁ W₂ : C}
    (e₀ : X₀ ⟶ W₀) (e₁ : X₁ ⟶ W₁) (e₂ : X₂ ⟶ W₂)
    (a₀ : X₀ ⟶ X₁) (a₁ : End X₁) (a₂ : X₁ ⟶ X₀)
    (b₀ : X₀ ⟶ X₂) (b₁ : End X₂) (b₂ : X₂ ⟶ X₀)
    (c₀ : W₀ ⟶ W₁) (c₁ : End W₁) (c₂ : W₁ ⟶ W₀)
    (d₀ : W₀ ⟶ W₂) (d₁ : End W₂) (d₂ : W₂ ⟶ W₀)
    (ha₀ : a₀ ≫ e₁ = e₀ ≫ c₀) (ha₁ : a₁ ≫ e₁ = e₁ ≫ c₁)
    (ha₂ : a₂ ≫ e₀ = e₁ ≫ c₂) (hb₀ : b₀ ≫ e₂ = e₀ ≫ d₀)
    (hb₁ : b₁ ≫ e₂ = e₂ ≫ d₁) (hb₂ : b₂ ≫ e₀ = e₂ ≫ d₂) :
    (a₀ ≫ a₁ ≫ a₂ - b₀ ≫ b₁ ≫ b₂) ≫ e₀ =
      e₀ ≫ (c₀ ≫ c₁ ≫ c₂ - d₀ ≫ d₁ ≫ d₂) := by
  have ha := compose_square_2 e₀ e₁ e₀ a₀ (a₁ ≫ a₂) c₀ (c₁ ≫ c₂) ha₀
    (compose_square_2 e₁ e₁ e₀ a₁ a₂ c₁ c₂ ha₁ ha₂)
  have hb := compose_square_2 e₀ e₂ e₀ b₀ (b₁ ≫ b₂) d₀ (d₁ ≫ d₂) hb₀
    (compose_square_2 e₂ e₂ e₀ b₁ b₂ d₁ d₂ hb₁ hb₂)
  rw [Preadditive.sub_comp, ha, hb, Preadditive.comp_sub]

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i j : I) (Λ : X) {a b c d e f : X}
  (hab : a + D.α i = b) (haf : a + D.α j = f) (hbc : b + D.α j = c)
  (hbe : b + D.α i = e) (hfc : f + D.α i = c) (hcd : c + D.α i = d)
  (hed : e + D.α j = d)
local notation "a₀" => elvWeightSuffixCross D Sc cutoff bound i j i Λ hab hbc hcd hbe hed
local notation "a₁" => elvWeightPrefixCross D Sc cutoff bound j i i Λ hab hbe hab hbe hed
local notation "a₂" => elvWeightSuffixCross D Sc cutoff bound j i i Λ hab hbe hed hbc hcd
local notation "b₀" => elvWeightPrefixCross D Sc cutoff bound i j i Λ hab hbc haf hfc hcd
local notation "b₁" => elvWeightSuffixCross D Sc cutoff bound i i j Λ haf hfc hcd hfc hcd
local notation "b₂" => elvWeightPrefixCross D Sc cutoff bound i i j Λ haf hfc hab hbc hcd

variable (β : WeightBlocks D Λ a)
local notation "β₁" => blockSucc D Λ i hab β
local notation "δ" => blockSucc₂ D j i Λ hab hbc β
local notation "ε" => elvBlockSucc₃ D i j i Λ hab hbc hcd β
local notation "hA" => blockSucc₂_swap D i j Λ hbc hcd hbe hed (β := β₁) rfl
local notation "hB" => elvBlockSucc₃_eq_of_pair D i i j Λ haf hfc hcd β δ ε
  (blockSucc₂_swap D j i Λ hab hbc haf hfc rfl) rfl
local notation "h₀" => elvBlockTriple_content_eq D i j i Λ hab hbc hcd β
local notation "h₁" => elvWeightTriple_content_eq D j i i Λ hab hbe hed β ε hA
local notation "h₂" => elvWeightTriple_content_eq D i i j Λ haf hfc hcd β ε hB
local notation "C₀" => elvWeightTripleComparison D Sc cutoff bound i j i Λ hab hbc hcd β ε rfl
local notation "C₁" => elvWeightTripleComparison D Sc cutoff bound j i i Λ hab hbe hed β ε hA
local notation "C₂" => elvWeightTripleComparison D Sc cutoff bound i i j Λ haf hfc hcd β ε hB
local notation "c₀" => SuperNatTrans.app (contentInductionTransform D Sc cutoff bound h₁ h₀
  (contentNormalizedRight_mem D Sc i i j)) (D.parity i * D.parity j)
local notation "c₁" => SuperNatTrans.app (contentInductionTransform D Sc cutoff bound h₁ h₁
  (contentNormalizedLeft_mem D Sc i i j)) (D.parity i * D.parity i)
local notation "c₂" => SuperNatTrans.app (contentInductionTransform D Sc cutoff bound h₀ h₁
  (contentNormalizedRight_mem D Sc i j i)) (D.parity j * D.parity i)
local notation "d₀" => SuperNatTrans.app (contentInductionTransform D Sc cutoff bound h₂ h₀
  (contentNormalizedLeft_mem D Sc j i i)) (D.parity j * D.parity i)
local notation "d₁" => SuperNatTrans.app (contentInductionTransform D Sc cutoff bound h₂ h₂
  (contentNormalizedRight_mem D Sc j i i)) (D.parity i * D.parity i)
local notation "d₂" => SuperNatTrans.app (contentInductionTransform D Sc cutoff bound h₀ h₂
  (contentNormalizedLeft_mem D Sc i j i)) (D.parity i * D.parity j)

/-- Both paths of the prescribed weight braid intertwine through the same
source chart and the two independently chosen intermediate charts. -/
theorem elvWeightMixedPaths_comparison
    (M : ELVWeightProduct D Sc cutoff bound Λ a) :
    ((a₀).total M ε ≫ (a₁).total M ε ≫ (a₂).total M ε -
      (b₀).total M ε ≫ (b₁).total M ε ≫ (b₂).total M ε) ≫ (C₀).hom.app M =
    (C₀).hom.app M ≫
      (c₀ (M β) ≫ c₁ (M β) ≫ c₂ (M β) - d₀ (M β) ≫ d₁ (M β) ≫ d₂ (M β)) := by
  apply path_difference_square ((C₀).hom.app M) ((C₁).hom.app M) ((C₂).hom.app M)
    ((a₀).total M ε) ((a₁).total M ε) ((a₂).total M ε)
    ((b₀).total M ε) ((b₁).total M ε) ((b₂).total M ε)
    (c₀ (M β)) (c₁ (M β)) (c₂ (M β)) (d₀ (M β)) (d₁ (M β)) (d₂ (M β))
  · exact elvWeightSuffixCross_comparison D Sc cutoff bound i j i Λ hab hbc hcd hbe hed β ε rfl M
  · exact elvWeightPrefixCross_comparison D Sc cutoff bound j i i Λ hab hbe hab hbe hed
      β (blockSucc₂ D i i Λ hab hbe β) ε rfl hA M
  · exact elvWeightSuffixCross_comparison D Sc cutoff bound j i i Λ hab hbe hed hbc hcd β ε hA M
  · exact elvWeightPrefixCross_comparison D Sc cutoff bound i j i Λ hab hbc haf hfc hcd β δ ε rfl rfl M
  · exact elvWeightSuffixCross_comparison D Sc cutoff bound i i j Λ haf hfc hcd hfc hcd β ε hB M
  · exact elvWeightPrefixCross_comparison D Sc cutoff bound i i j Λ haf hfc hab hbc hcd β δ ε
      (blockSucc₂_swap D j i Λ hab hbc haf hfc rfl) rfl M

end OddMath.QuiverHecke.ELV
end

end

section

/-! # The selected pair comparison intertwines both prescribed dots

Brundan--Ellis (1.9), supporting the positioned dots in its repeated-outer
correction. The existing component-coordinate squares are retained as
whole module-map identities, so the last induction can act on them.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELV
universe u
private theorem moduleCoordinate_map
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {M N : Superfunctor k C (SVec k)} (e : M ≅ N) (x : End M) (z : End N)
    (h : ∀ w, ModuleCoordinateSquare e x w (z.total w)) :
    x ≫ e.hom = e.hom ≫ z := by
  apply FiniteSupermodule.hom_ext_total
  intro w
  rw [Superfunctor.comp_total, Superfunctor.comp_total]
  exact h w

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i j : I) (Λ : X) {x₀ x₁ x₂ : X}
  (h₁ : x₀ + D.α j = x₁) (h₂ : x₁ + D.α i = x₂)
  (β : WeightBlocks D Λ x₀)
local notation "β₂" => blockSucc₂ D i j Λ h₁ h₂ β
local notation "hP" => elvWeightPair_content_eq D i j Λ h₁ h₂ β β₂ rfl
local notation "C₂" => elvWeightPairComparison D Sc cutoff bound i j Λ h₁ h₂ β β₂ rfl

/-- The first prescribed weight dot intertwines as a whole module map
through the pair chart used by the independently given crossing. -/
theorem elvWeightPairComparison_inner_map
    (M : ELVWeightProduct D Sc cutoff bound Λ x₀) :
    (elvInductionComponent D Sc cutoff bound i Λ h₂ β₂).map
        ((elvWeightDot D Sc cutoff bound j Λ h₁).app (D.parity j) M) ≫ (C₂).hom.app M =
      (C₂).hom.app M ≫
        (contentInductionTransform D Sc cutoff bound hP hP
          (MonoidalSupercategory.whiskerRight_mem (R := k) ((pres D Sc).obj (ob D [i]))
            (firstDot_parity D Sc j []))).app (D.parity j) (M β) := by
  apply moduleCoordinate_map ((C₂).app M)
  intro w
  rw [contentInductionTransform_total]
  exact elvWeightPairComparison_inner_total D Sc cutoff bound i j Λ h₁ h₂ β M w

/-- The second prescribed weight dot uses the same selected pair chart,
with its affine left context and full coefficient twist retained. -/
theorem elvWeightPairComparison_outer_map
    (M : ELVWeightProduct D Sc cutoff bound Λ x₀) :
    elvWeightDotComponent D Sc cutoff bound i Λ h₂ (D.parity i)
        ((elvEFunctor D Sc cutoff bound j Λ h₁).obj M) β₂ ≫ (C₂).hom.app M =
      (C₂).hom.app M ≫
        (contentInductionTransform D Sc cutoff bound hP hP
          (MonoidalSupercategory.whiskerLeft_mem (R := k) ((pres D Sc).obj (ob D [j]))
            (firstDot_parity D Sc i []))).app (D.parity i) (M β) := by
  apply moduleCoordinate_map ((C₂).app M)
  intro w
  rw [contentInductionTransform_total]
  exact elvWeightPairComparison_outer_total D Sc cutoff bound i j Λ h₁ h₂ β M w

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Components of the three prescribed weight dot positions

Brundan--Ellis (1.9), the repeated-outer correction. Retain the literal
three dot whiskerings and their selected predecessor-dispatch maps,
including full coefficient parity and arbitrary input modules.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELV
universe u
private theorem dot_total_whiskerRight
    {k : Type u} [CommRing k]
    {A B C : PiSCat.{u, u, u + 1} k} {F G : A ⟶ B}
    (f : F ⟶ G) (H : B ⟶ C) (M : A) :
    (f ▷ H).total M = H.map (f.total M) := by
  change H.map (f.app 0 M) + H.map (f.app 1 M) = H.map (f.app 0 M + f.app 1 M)
  exact H.toFunctor.map_add.symm
private theorem dot_first_total
    {k : Type u} [CommRing k]
    {A B C E : PiSCat.{u, u, u + 1} k}
    (F : A ⟶ B) (G : B ⟶ C) (H : C ⟶ E) (x : End F) (M : A) :
    (x ▷ (G ≫ H)).total M = H.map ((x ▷ G).total M) := by
  rw [dot_total_whiskerRight, dot_total_whiskerRight]
  rfl
private theorem dot_middle_total
    {k : Type u} [CommRing k]
    {A B C E : PiSCat.{u, u, u + 1} k}
    (F : A ⟶ B) (G : B ⟶ C) (H : C ⟶ E) (x : End G) (M : A) :
    (F ◁ (x ▷ H)).total M = H.map ((F ◁ x).total M) := by
  change (x ▷ H).total (F.obj M) = H.map (x.total (F.obj M))
  exact dot_total_whiskerRight x H (F.obj M)

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i j l : I) (Λ : X) {a b c d : X}
  (hal : a + D.α l = b) (hbj : b + D.α j = c) (hci : c + D.α i = d)
local notation "E₁" => elvE D Sc cutoff bound l Λ hal
local notation "E₂" => elvE D Sc cutoff bound j Λ hbj
local notation "E₃" => elvE D Sc cutoff bound i Λ hci

/-- The first literal dot position, whiskered by both following inductions. -/
abbrev elvWeightTripleFirstDot : End (E₁ ≫ E₂ ≫ E₃) :=
  elvActionDot D Sc cutoff bound l Λ hal ▷ (E₂ ≫ E₃)
/-- The middle literal dot position. -/
abbrev elvWeightTripleMiddleDot : End (E₁ ≫ E₂ ≫ E₃) :=
  E₁ ◁ (elvActionDot D Sc cutoff bound j Λ hbj ▷ E₃)
/-- The last literal dot position. -/
abbrev elvWeightTripleLastDot : End (E₁ ≫ E₂ ≫ E₃) :=
  E₁ ◁ E₂ ◁ elvActionDot D Sc cutoff bound i Λ hci

/-- The first literal dot is induced from its first-pair component. -/
theorem elvWeightTripleFirstDot_total
    (M : ELVWeightProduct D Sc cutoff bound Λ a) (ε : WeightBlocks D Λ d) :
    (elvWeightTripleFirstDot D Sc cutoff bound i j l Λ hal hbj hci).total M ε =
      (elvInductionComponent D Sc cutoff bound i Λ hci ε).map
        ((elvActionDot D Sc cutoff bound l Λ hal ▷ E₂).total M) :=
  congrFun (dot_first_total E₁ E₂ E₃ (elvActionDot D Sc cutoff bound l Λ hal) M) ε

/-- The middle literal dot is induced from its last first-pair component. -/
theorem elvWeightTripleMiddleDot_total
    (M : ELVWeightProduct D Sc cutoff bound Λ a) (ε : WeightBlocks D Λ d) :
    (elvWeightTripleMiddleDot D Sc cutoff bound i j l Λ hal hbj hci).total M ε =
      (elvInductionComponent D Sc cutoff bound i Λ hci ε).map
        ((E₁ ◁ elvActionDot D Sc cutoff bound j Λ hbj).total M) :=
  congrFun (dot_middle_total E₁ E₂ E₃ (elvActionDot D Sc cutoff bound j Λ hbj) M) ε

/-- The last literal dot acts on the actual twice-induced product. -/
theorem elvWeightTripleLastDot_total
    (M : ELVWeightProduct D Sc cutoff bound Λ a) (ε : WeightBlocks D Λ d) :
    (elvWeightTripleLastDot D Sc cutoff bound i j l Λ hal hbj hci).total M ε =
      elvWeightDotComponent D Sc cutoff bound i Λ hci (D.parity i)
        ((elvEFunctor D Sc cutoff bound j Λ hbj).obj
          ((elvEFunctor D Sc cutoff bound l Λ hal).obj M)) ε :=
  congrFun (supernatural_total_of_mem
    (elvActionDot_mem D Sc cutoff bound i Λ hci) ((E₂).obj ((E₁).obj M))) ε

private theorem pairFirstDot_total
    (M : ELVWeightProduct D Sc cutoff bound Λ a) (δ : WeightBlocks D Λ c) :
    (elvActionDot D Sc cutoff bound l Λ hal ▷ E₂).total M δ =
      (elvInductionComponent D Sc cutoff bound j Λ hbj δ).map
        ((elvWeightDot D Sc cutoff bound l Λ hal).app (D.parity l) M) := by
  have h := congrFun (dot_total_whiskerRight (elvActionDot D Sc cutoff bound l Λ hal) E₂ M) δ
  rw [supernatural_total_of_mem (elvActionDot_mem D Sc cutoff bound l Λ hal) M] at h
  exact h
private theorem pairMiddleDot_total
    (M : ELVWeightProduct D Sc cutoff bound Λ a) (δ : WeightBlocks D Λ c) :
    (E₁ ◁ elvActionDot D Sc cutoff bound j Λ hbj).total M δ =
      elvWeightDotComponent D Sc cutoff bound j Λ hbj (D.parity j)
        ((elvEFunctor D Sc cutoff bound l Λ hal).obj M) δ :=
  congrFun (supernatural_total_of_mem (elvActionDot_mem D Sc cutoff bound j Λ hbj) ((E₁).obj M)) δ

section Supported
variable (β : WeightBlocks D Λ a)
local notation "β₂" => blockSucc₂ D j l Λ hal hbj β
local notation "β₃" => elvBlockSucc₃ D i j l Λ hal hbj hci β
local notation "U" => Superfunctor.toFunctor (elvBlockInd D Sc cutoff bound i Λ hci β₂)
local notation "ds" => eqToIso (elvEFunctor_comp₃_pairFirst D Sc cutoff bound i j l Λ hal hbj hci β)

/-- The supported first dot retains the outer dispatch and the independently
specified first-pair dot used by the selected pair comparison. -/
theorem elvWeightTripleFirstDot_blockSucc
    (M : ELVWeightProduct D Sc cutoff bound Λ a) :
    (elvWeightTripleFirstDot D Sc cutoff bound i j l Λ hal hbj hci).total M β₃ =
      (ds).hom.app M ≫
        (U).map ((elvInductionComponent D Sc cutoff bound j Λ hbj β₂).map
          ((elvWeightDot D Sc cutoff bound l Λ hal).app (D.parity l) M)) ≫ (ds).inv.app M := by
  have h₀ := elvWeightTripleFirstDot_total D Sc cutoff bound i j l Λ hal hbj hci M β₃
  have hm := elvInductionComponent_map_blockSucc D Sc cutoff bound i Λ hci β₂
    ((elvActionDot D Sc cutoff bound l Λ hal ▷ E₂).total M)
  have hx := pairFirstDot_total D Sc cutoff bound j l Λ hal hbj M β₂
  have hr := congrArg
    (fun (f : End ((E₁ ≫ E₂).obj M β₂)) =>
      eqToHom (elvInductionComponent_obj_blockSucc D Sc cutoff bound i Λ hci β₂ ((E₁ ≫ E₂).obj M)) ≫
        (elvBlockInd D Sc cutoff bound i Λ hci β₂).map f ≫
          eqToHom (elvInductionComponent_obj_blockSucc D Sc cutoff bound i Λ hci β₂ ((E₁ ≫ E₂).obj M)).symm) hx
  simp only [eqToIso.hom, eqToIso.inv, eqToHom_app]
  exact h₀.trans (hm.trans hr)

/-- The supported middle dot retains the same outer dispatch and the
independently specified outer dot of the first pair. -/
theorem elvWeightTripleMiddleDot_blockSucc
    (M : ELVWeightProduct D Sc cutoff bound Λ a) :
    (elvWeightTripleMiddleDot D Sc cutoff bound i j l Λ hal hbj hci).total M β₃ =
      (ds).hom.app M ≫
        (U).map (elvWeightDotComponent D Sc cutoff bound j Λ hbj (D.parity j)
          ((elvEFunctor D Sc cutoff bound l Λ hal).obj M) β₂) ≫ (ds).inv.app M := by
  have h₀ := elvWeightTripleMiddleDot_total D Sc cutoff bound i j l Λ hal hbj hci M β₃
  have hm := elvInductionComponent_map_blockSucc D Sc cutoff bound i Λ hci β₂
    ((E₁ ◁ elvActionDot D Sc cutoff bound j Λ hbj).total M)
  have hx := pairMiddleDot_total D Sc cutoff bound j l Λ hal hbj M β₂
  have hr := congrArg
    (fun (f : End ((E₁ ≫ E₂).obj M β₂)) =>
      eqToHom (elvInductionComponent_obj_blockSucc D Sc cutoff bound i Λ hci β₂ ((E₁ ≫ E₂).obj M)) ≫
        (elvBlockInd D Sc cutoff bound i Λ hci β₂).map f ≫
          eqToHom (elvInductionComponent_obj_blockSucc D Sc cutoff bound i Λ hci β₂ ((E₁ ≫ E₂).obj M)).symm) hx
  simp only [eqToIso.hom, eqToIso.inv, eqToHom_app]
  exact h₀.trans (hm.trans hr)

/-- The supported last dot retains the prescribed single-letter content dot
on the actual twice-induced input, with both dispatch directions. -/
theorem elvWeightTripleLastDot_blockSucc
    (M : ELVWeightProduct D Sc cutoff bound Λ a) :
    (elvWeightTripleLastDot D Sc cutoff bound i j l Λ hal hbj hci).total M β₃ =
      (ds).hom.app M ≫
        (elvBlockDot D Sc cutoff bound i Λ hci β₂).app (D.parity i)
          ((E₁ ≫ E₂).obj M β₂) ≫ (ds).inv.app M := by
  have h₀ := elvWeightTripleLastDot_total D Sc cutoff bound i j l Λ hal hbj hci M β₃
  have hd := elvWeightDotComponent_blockSucc D Sc cutoff bound i Λ hci (D.parity i)
    ((E₁ ≫ E₂).obj M) β₂
  simp only [eqToIso.hom, eqToIso.inv, eqToHom_app]
  exact h₀.trans hd
end Supported
end OddMath.QuiverHecke.ELV
end

end

section

/-! # Prescribed positioned dots through the selected weight triple chart

Brundan--Ellis (1.9), the repeated-outer correction. Induce the checked
whole pair-dot squares through the same selected triple chart used for
the given crossings; retain the literal affine contexts.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELV
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

end OddMath.QuiverHecke.ELV
end

end

section

/-! # The three prescribed weight dots in indexed polynomial coordinates

Brundan--Ellis (1.9), the repeated-outer correction. Evaluate the same
selected triple chart on each literal native dot and retain exactly the
indexed affine generators used by the ordered polynomial.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELV
universe u
private theorem normalized_module_square
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {A B : Superfunctor k C (SVec k)} (e : A ≅ B) (x : End A) (z z' : End B)
    (h : x ≫ e.hom = e.hom ≫ z) (hz : z = z') (w : C) :
    ModuleCoordinateSquare e x w (z'.total w) := by
  have hs := h.trans (congrArg (fun q => e.hom ≫ q) hz)
  have ht := congrArg (fun q => q.total w) hs
  rw [Superfunctor.comp_total, Superfunctor.comp_total] at ht
  exact ht

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)

private theorem indexed_dot_transform_eq {β γ : Multiset I} {σ : List I}
    (h : β + (σ : Multiset I) = γ) {p : ZMod 2}
    {a b : End ((pres D Sc).obj (ob D σ))}
    (ha : a ∈ parity (R := k) _ _ p) (hb : b ∈ parity (R := k) _ _ p)
    (hab : a = b) (M : ContentModules D Sc cutoff bound β) :
    (contentInductionTransform D Sc cutoff bound h h ha).app p M =
      (contentInductionTransform D Sc cutoff bound h h hb).app p M := by
  cases hab
  rfl

private theorem middleIndex_mem (l j i : I) :
    dotE D Sc [l,j,i] 1 ∈ parity (R := k) _ _ (D.parity j) := by
  simpa using positionedDot_parity D Sc [l] [i] j
private theorem lastIndex_mem (l j i : I) :
    dotE D Sc [l,j,i] 2 ∈ parity (R := k) _ _ (D.parity i) := by
  simpa using positionedDot_parity D Sc [l,j] [] i

variable (i j l : I) (Λ : X) {a b c d : X}
  (hal : a + D.α l = b) (hbj : b + D.α j = c) (hci : c + D.α i = d)
  (β : WeightBlocks D Λ a)
local notation "β₃" => elvBlockSucc₃ D i j l Λ hal hbj hci β
local notation "hT" => elvBlockTriple_content_eq D i j l Λ hal hbj hci β
local notation "C₃" => elvWeightTripleComparison D Sc cutoff bound i j l Λ hal hbj hci β β₃ rfl
local notation "hpFirst" => MonoidalSupercategory.whiskerRight_mem (R := k)
  (Presentation.obj (pres D Sc) (ob D [j])) (firstDot_parity D Sc l [])
local notation "hpMiddle" => MonoidalSupercategory.whiskerLeft_mem (R := k)
  (Presentation.obj (pres D Sc) (ob D [l])) (firstDot_parity D Sc j [])
local notation "htFirst" => MonoidalSupercategory.whiskerRight_mem (R := k)
  (Presentation.obj (pres D Sc) (ob D [i])) hpFirst
local notation "htMiddle" => MonoidalSupercategory.whiskerRight_mem (R := k)
  (Presentation.obj (pres D Sc) (ob D [i])) hpMiddle
local notation "htLast" => MonoidalSupercategory.whiskerLeft_mem (R := k)
  (Presentation.obj (pres D Sc) (ob D [l,j])) (firstDot_parity D Sc i [])

/-- The literal first weight dot is the indexed affine generator zero
under the selected triple chart, with full coefficient parity. -/
theorem elvWeightTripleDot_first_coordinate
    (M : ELVWeightProduct D Sc cutoff bound Λ a)
    (w : ContentCategory D Sc cutoff bound β₃.1) :
    ModuleCoordinateSquare ((C₃).app M)
      ((elvWeightTripleFirstDot D Sc cutoff bound i j l Λ hal hbj hci).total M β₃) w
      (BalancedInduction.transformLinear
        (contentAppendTo_supernatural D Sc cutoff bound hT hT (firstDot_parity D Sc l [j,i])) (M β) w) := by
  have hz := indexed_dot_transform_eq D Sc cutoff bound (σ := [l,j,i]) hT
    htFirst (firstDot_parity D Sc l [j,i]) (tripleFirstDot_affineContexts D Sc l j i) (M β)
  have h := normalized_module_square ((C₃).app M)
    ((elvWeightTripleFirstDot D Sc cutoff bound i j l Λ hal hbj hci).total M β₃) _ _
    (by simpa only [Iso.app_hom] using
      elvWeightTripleFirstDot_comparison D Sc cutoff bound i j l Λ hal hbj hci β M) hz w
  simpa only [contentInductionTransform_total] using h

/-- The literal middle weight dot is the indexed affine generator one,
using the identical selected triple chart. -/
theorem elvWeightTripleDot_middle_coordinate
    (M : ELVWeightProduct D Sc cutoff bound Λ a)
    (w : ContentCategory D Sc cutoff bound β₃.1) :
    ModuleCoordinateSquare ((C₃).app M)
      ((elvWeightTripleMiddleDot D Sc cutoff bound i j l Λ hal hbj hci).total M β₃) w
      (BalancedInduction.transformLinear
        (contentAppendTo_supernatural D Sc cutoff bound hT hT (middleIndex_mem D Sc l j i)) (M β) w) := by
  have hz := indexed_dot_transform_eq D Sc cutoff bound (σ := [l,j,i]) hT
    htMiddle (middleIndex_mem D Sc l j i) (tripleMiddleDot_affineIndex D Sc l j i) (M β)
  have h := normalized_module_square ((C₃).app M)
    ((elvWeightTripleMiddleDot D Sc cutoff bound i j l Λ hal hbj hci).total M β₃) _ _
    (by simpa only [Iso.app_hom] using
      elvWeightTripleMiddleDot_comparison D Sc cutoff bound i j l Λ hal hbj hci β M) hz w
  simpa only [contentInductionTransform_total] using h

/-- The literal last weight dot is the indexed affine generator two,
with the true native pair value and selected triple chart retained. -/
theorem elvWeightTripleDot_last_coordinate
    (M : ELVWeightProduct D Sc cutoff bound Λ a)
    (w : ContentCategory D Sc cutoff bound β₃.1) :
    ModuleCoordinateSquare ((C₃).app M)
      ((elvWeightTripleLastDot D Sc cutoff bound i j l Λ hal hbj hci).total M β₃) w
      (BalancedInduction.transformLinear
        (contentAppendTo_supernatural D Sc cutoff bound hT hT (lastIndex_mem D Sc l j i)) (M β) w) := by
  have hz := indexed_dot_transform_eq D Sc cutoff bound (σ := [l,j,i]) hT
    htLast (lastIndex_mem D Sc l j i) (tripleLastDot_affineIndex D Sc l j i) (M β)
  have h := normalized_module_square ((C₃).app M)
    ((elvWeightTripleLastDot D Sc cutoff bound i j l Λ hal hbj hci).total M β₃) _ _
    (by simpa only [Iso.app_hom] using
      elvWeightTripleLastDot_comparison D Sc cutoff bound i j l Λ hal hbj hci β M) hz w
  simpa only [contentInductionTransform_total] using h

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Exact-content components of a whole-weight supercentral map

Zero extension and naturality show that an identity transformation on the
weight product depends at each output content only on that input component.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped Classical
namespace OddMath.QuiverHecke.ELV.WeightCentreBlocks
open CyclotomicAction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (Λ : X) {x : X} (β : WeightBlocks D Λ x)

private def extensionComponent (δ : WeightBlocks D Λ x) :
    Superfunctor k (ContentModules D Sc cutoff N β.1) (ContentModules D Sc cutoff N δ.1) :=
  if h : δ = β then by subst δ; exact Superfunctor.id k _
  else ⟨elvZeroFunctor D Sc cutoff N δ.1⟩
private def extensionFunctor :
    ContentModules D Sc cutoff N β.1 ⥤ ELVWeightProduct D Sc cutoff N Λ x :=
  Functor.pi' fun δ => (extensionComponent D Sc cutoff N Λ β δ).toFunctor
private instance : (extensionFunctor D Sc cutoff N Λ β).Additive where
  map_add := funext fun δ => (extensionComponent D Sc cutoff N Λ β δ).toFunctor.map_add
private instance : (extensionFunctor D Sc cutoff N Λ β).Linear k where
  map_smul f r := funext fun δ => (extensionComponent D Sc cutoff N Λ β δ).toFunctor.map_smul r f
private instance : IsSuperfunctor k (extensionFunctor D Sc cutoff N Λ β) where
  map_mem hf δ := IsSuperfunctor.map_mem
    (F := (extensionComponent D Sc cutoff N Λ β δ).toFunctor) hf

/-- Place one exact-content module in its original-weight block and zero
modules in every other block, including root collisions. -/
def extension : Superfunctor k (ContentModules D Sc cutoff N β.1)
    (ELVWeightProduct D Sc cutoff N Λ x) := ⟨extensionFunctor D Sc cutoff N Λ β⟩

private theorem component_selected : extensionComponent D Sc cutoff N Λ β β = Superfunctor.id k _ := by
  simp [extensionComponent]

theorem extension_eval : (extension D Sc cutoff N Λ β).comp (elvBlockEval D Sc cutoff N Λ β) =
    Superfunctor.id k (ContentModules D Sc cutoff N β.1) := by
  change extensionComponent D Sc cutoff N Λ β β = _
  exact component_selected D Sc cutoff N Λ β

/-- Restrict a literal whole-weight identity transformation by zero extension
and exact output projection. -/
def restrict (η : Superfunctor.id k (ELVWeightProduct D Sc cutoff N Λ x) ⟶
    Superfunctor.id k (ELVWeightProduct D Sc cutoff N Λ x)) :
    ModuleCentre.Centre D Sc cutoff N β.1 :=
  eqToHom (extension_eval D Sc cutoff N Λ β).symm ≫
    Superfunctor.whiskerRight (Superfunctor.whiskerLeft (extension D Sc cutoff N Λ β) η)
      (elvBlockEval D Sc cutoff N Λ β) ≫
        eqToHom (extension_eval D Sc cutoff N Λ β)

/-- The selected component of zero extension is canonically the original module. -/
theorem extension_obj (M : ContentModules D Sc cutoff N β.1) :
    ((extension D Sc cutoff N Λ β).obj M) β = M :=
  congrArg (fun F => F.obj M) (extension_eval D Sc cutoff N Λ β)

private def inclusion (M : ELVWeightProduct D Sc cutoff N Λ x) :
    (extension D Sc cutoff N Λ β).obj (M β) ⟶ M := fun δ =>
  if h : δ = β then by
    subst δ
    exact eqToHom (extension_obj D Sc cutoff N Λ β (M β))
  else 0

private theorem inclusion_mem (M : ELVWeightProduct D Sc cutoff N Λ x) :
    inclusion D Sc cutoff N Λ β M ∈ parity (R := k) _ _ 0 := by
  intro δ
  by_cases h : δ = β
  · subst δ
    simp only [inclusion, ↓reduceDIte]
    exact eqToHom_mem_parity_zero (extension_obj D Sc cutoff N Λ β (M β))
  · simp only [inclusion, dite_eq_right h]
    exact Submodule.zero_mem _

private theorem transport_app {A B : Type*} [Category A] [Preadditive A] [Linear k A]
    [Supercategory k A] [Category B] [Preadditive B] [Linear k B] [Supercategory k B]
    {F G : Superfunctor k A B} (h : F = G) (t : End F) (p : ZMod 2) (M : A) :
    (eqToHom h.symm ≫ t ≫ eqToHom h).app p M =
      eqToHom (congrArg (fun K => K.obj M) h.symm) ≫ t.app p M ≫
        eqToHom (congrArg (fun K => K.obj M) h) := by
  subst G
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

private theorem conjugate_of_square {C : Type*} [Category C] {A B : C}
    (e : A ≅ B) (f : End A) (g : End B) (h : e.hom ≫ g = f ≫ e.hom) :
    e.inv ≫ f ≫ e.hom = g := by
  rw [← h, ← Category.assoc, e.inv_hom_id, Category.id_comp]

/-- The exact-content centre agrees with the original whole-weight map on
its selected component for every input family, independently of other blocks. -/
theorem restrict_app (η : Superfunctor.id k (ELVWeightProduct D Sc cutoff N Λ x) ⟶
    Superfunctor.id k (ELVWeightProduct D Sc cutoff N Λ x))
    (p : ZMod 2) (M : ELVWeightProduct D Sc cutoff N Λ x) :
    (restrict D Sc cutoff N Λ β η).app p (M β) = η.app p M β := by
  have hn := congrArg (fun f => f β)
    (η.naturality p (inclusion D Sc cutoff N Λ β M) (inclusion_mem D Sc cutoff N Λ β M))
  change inclusion D Sc cutoff N Λ β M β ≫ η.app p M β =
    koszulSign p 0 • (η.app p ((extension D Sc cutoff N Λ β).obj (M β)) β ≫
      inclusion D Sc cutoff N Λ β M β) at hn
  simp only [inclusion, ↓reduceDIte, Supercategory.koszulSign_zero_right, one_smul] at hn
  unfold restrict
  rw [transport_app]
  change eqToHom (extension_obj D Sc cutoff N Λ β (M β)).symm ≫
    η.app p ((extension D Sc cutoff N Λ β).obj (M β)) β ≫
      eqToHom (extension_obj D Sc cutoff N Λ β (M β)) = _
  exact conjugate_of_square (eqToIso (extension_obj D Sc cutoff N Λ β (M β)))
    (η.app p ((extension D Sc cutoff N Λ β).obj (M β)) β) (η.app p M β) hn

/-- Both parity pieces agree, hence so does the full underlying module map. -/
theorem restrict_total (η : Superfunctor.id k (ELVWeightProduct D Sc cutoff N Λ x) ⟶
    Superfunctor.id k (ELVWeightProduct D Sc cutoff N Λ x))
    (M : ELVWeightProduct D Sc cutoff N Λ x) :
    (restrict D Sc cutoff N Λ β η).total (M β) = η.total M β := by
  change (restrict D Sc cutoff N Λ β η).app 0 (M β) +
    (restrict D Sc cutoff N Λ β η).app 1 (M β) = _
  rw [restrict_app, restrict_app]
  rfl

end OddMath.QuiverHecke.ELV.WeightCentreBlocks
end

end
