import OddMath.QuiverHecke.CyclotomicAction.ELVWeightBraidComparison
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightTripleLastPairComparison
import OddMath.QuiverHecke.CyclotomicAction.ELVContentCompositionOuterMap

/-! # The prescribed second weight crossing in the triple chart

Brundan--Ellis (1.9), DeformedActionAssembly §6. Compare the literal second
weight crossing through the same selected triple chart, retaining the
first-value cast and the normalized equal-colour coefficient.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVOld
universe u
private theorem braid_suffix_comparison
    {A B : Type*} [Category* A] [Category* B]
    (Q : A ⥤ B) {N N' : A} {X W : B}
    (e : X ≅ Q.obj N) (v : N ≅ N') (w : Q.obj N' ≅ W) (t : X ≅ W)
    (y : X ⟶ X) (c : Q.obj N ⟶ Q.obj N) (c' : Q.obj N' ⟶ Q.obj N') (z : W ⟶ W)
    (hy : y = e.hom ≫ c ≫ e.inv)
    (ht : t.hom = e.hom ≫ Q.map v.hom ≫ w.hom)
    (hc : c ≫ Q.map v.hom = Q.map v.hom ≫ c')
    (hw : c' ≫ w.hom = w.hom ≫ z) :
    y ≫ t.hom = t.hom ≫ z := by
  rw [hy, ht]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc c, hc, Category.assoc, hw]

private theorem braid_even_component_naturality
    {k : Type u} [CommRing k]
    {A B : Type*} [Category* A] [Category* B]
    [Preadditive A] [Linear k A] [Supercategory k A]
    [Preadditive B] [Linear k B] [Supercategory k B]
    (Q : A ⥤ B) (α : SuperNatTrans k Q Q) (p : ZMod 2)
    {N N' : A} (f : N ⟶ N') (hf : f ∈ parity (R := k) _ _ 0) :
    α.app p N ≫ Q.map f = Q.map f ≫ α.app p N' := by
  have h := (α.isSupernatural p).naturality hf
  simpa only [mul_zero, sign_zero, one_smul] using h.symm

private theorem braid_eqToIso_app_mem
    {k : Type u} [CommRing k]
    {A B : Type*} [Category* A] [Category* B]
    [Preadditive B] [Linear k B] [Supercategory k B]
    {F G : A ⥤ B} (h : F = G) (M : A) :
    (eqToIso h).hom.app M ∈ parity (R := k) _ _ 0 := by
  cases h
  exact id_mem _

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i : I) (Λ : X) {x₀ x₁ x₂ x₃ : X}
  (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂) (h₃ : x₂ + D.α i = x₃)
  (β : WeightBlocks D Λ x₀)
local notation "β₁" => blockSucc D Λ i h₁ β
local notation "β₂" => blockSucc₂ D i i Λ h₁ h₂ β
local notation "β₃" => elvBlockSucc₃ D i i i Λ h₁ h₂ h₃ β
local notation "p" => D.parity i * D.parity i
local notation "hc₁" => elvBlockSucc_content_eq D i Λ h₁ β
local notation "hQ" => elvBlockPair_content_eq D i i Λ h₂ h₃ β₁
local notation "hT" => elvBlockTriple_content_eq D i i i Λ h₁ h₂ h₃ β
local notation "E₁" => elvEFunctor D Sc cutoff bound i Λ h₁
local notation "Q" => contentInductionTo D Sc cutoff bound (Subtype.val β₁) [i,i] (Subtype.val β₃) hQ
local notation "α" => contentInductionTransform D Sc cutoff bound hQ hQ (contentCrossAffine_mem D Sc i i)
local notation "C₃" => elvWeightTripleComparison D Sc cutoff bound i i i Λ h₁ h₂ h₃ β β₃ rfl
local notation "C₂" => elvWeightPairComparison D Sc cutoff bound i i Λ h₂ h₃ β₁ β₃ rfl
local notation "L" => contentInductionCompTo D Sc cutoff bound (Subtype.val β) [i] (Subtype.val β₁) hc₁
  [i,i] (Subtype.val β₃) hQ hT
local notation "hv" => elvEFunctor_blockSucc_eval D Sc cutoff bound i Λ h₁ β

/-- The second given weight crossing intertwines with the direct affine
suffix through the very same selected triple comparison. -/
theorem elvWeightBraidSuffix_comparison
    (M : ELVWeightProduct D Sc cutoff bound Λ x₀) :
    (elvWeightBraidSuffix D Sc cutoff bound i Λ h₁ h₂ h₃).total M β₃ ≫ (C₃).hom.app M =
      (C₃).hom.app M ≫
        (contentInductionTransform D Sc cutoff bound hT hT
          (MonoidalSupercategory.whiskerLeft_mem (R := k) ((pres D Sc).obj (ob D [i]))
            (contentCrossAffine_mem D Sc i i))).app p (M β) := by
  apply braid_suffix_comparison Q ((C₂).app ((E₁).obj M)) ((eqToIso hv).app M)
    ((L).app (M β)) ((C₃).app M) _ ((α).app p (((E₁).obj M) β₁))
    ((α).app p ((elvBlockInd D Sc cutoff bound i Λ h₁ β).obj (M β))) _
  · have hs := elvWeightBraidSuffix_blockSucc D Sc cutoff bound i Λ h₁ h₂ h₃ β M
    have hc := elvWeightCrossVia_component D Sc cutoff bound i i Λ h₂ h₃ h₂ h₃ β₁ β₃ rfl ((E₁).obj M)
    simpa only [Iso.app_hom, Iso.app_inv, Category.assoc] using hs.trans hc
  · simpa only [Iso.app_hom] using
      elvWeightTripleComparison_pairLast_hom D Sc cutoff bound i i i Λ h₁ h₂ h₃ β M
  · simp only [Iso.app_hom]
    exact braid_even_component_naturality Q α p ((eqToIso hv).hom.app M)
      (braid_eqToIso_app_mem hv M)
  · exact contentInductionCompTo_outer_map D Sc cutoff bound β.1 [i] [i,i] [i,i]
      β₁.1 β₃.1 hc₁ hQ hQ hT hT (contentCrossAffine_mem D Sc i i) (M β)

end OddMath.QuiverHecke.ELVOld
