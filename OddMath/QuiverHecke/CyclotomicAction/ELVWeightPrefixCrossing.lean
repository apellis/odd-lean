import OddMath.QuiverHecke.CyclotomicAction.ELVWeightTripleBlockComparison

/-! # The first prescribed multicolour crossing on three inductions

Brundan--Ellis (1.9). Evaluate the first adjacent crossing with both
weight paths and their common stored second predecessor retained.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVOld
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

end OddMath.QuiverHecke.ELVOld
