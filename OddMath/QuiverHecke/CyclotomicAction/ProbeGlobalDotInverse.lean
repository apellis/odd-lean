import OddMath.QuiverHecke.CyclotomicAction.ProbeSuperDotInverse

/-! # Invertible probe dots on content induction
This restricts the all-height dot inverse to the existing content action,
the action-level dot input of InvertibleDotProbe.md Section 5, equation (6).
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.CyclotomicAction
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) [Fintype I]
  (i : I) (m : I → ℕ)
  (ha : CyclotomicPolynomialParity D (probePolynomial (k := k) (probeDotExponent D) m))
  (n : ℕ)
local notation "a" => probePolynomial (k := k) (probeDotExponent D) m

/-- The dot inverse restricts to each existing content block. -/
def probeHeightContentDotIso (β : Multiset I) :
    heightContentInduction D Sc i a ha n β ≅ heightContentInduction D Sc i a ha n β where
  hom := heightContentDot D Sc i a ha n β
  inv := fullLiftTrans _ _ (heightContentSupported_induction D Sc i a ha n β)
    (heightContentSupported_induction D Sc i a ha n β)
    (probeHeightSuperDotIso D Sc i m ha n).inv
  hom_inv_id := by
    apply Superfunctor.hom_ext_parity
    · intro M
      apply InducedCategory.hom_ext
      exact congrArg (fun η => η.app 0 M.obj) (probeHeightSuperDotIso D Sc i m ha n).hom_inv_id
    · intro M
      apply InducedCategory.hom_ext
      exact congrArg (fun η => η.app 1 M.obj) (probeHeightSuperDotIso D Sc i m ha n).hom_inv_id
  inv_hom_id := by
    apply Superfunctor.hom_ext_parity
    · intro M
      apply InducedCategory.hom_ext
      exact congrArg (fun η => η.app 0 M.obj) (probeHeightSuperDotIso D Sc i m ha n).inv_hom_id
    · intro M
      apply InducedCategory.hom_ext
      exact congrArg (fun η => η.app 1 M.obj) (probeHeightSuperDotIso D Sc i m ha n).inv_hom_id

/-- Transport the dot isomorphism through the existing content identification. -/
private def probeContentCastIso {C : Type*} [Category C] [Preadditive C] [Linear k C]
    [Supercategory k C] {r s : ℕ} {γ δ : Multiset I} (hr : r = s) (hγ : γ = δ)
    (F : Superfunctor k C (ObjectProperty.FullSubcategory (heightContentSupported D Sc a ha r γ)))
    (E : F ≅ F) :
    F.comp (heightContentCast D Sc a ha hr hγ) ≅
      F.comp (heightContentCast D Sc a ha hr hγ) where
  hom := heightContentCastTrans D Sc a ha hr hγ E.hom
  inv := heightContentCastTrans D Sc a ha hr hγ E.inv
  hom_inv_id := by
    subst hr
    subst hγ
    exact E.hom_inv_id
  inv_hom_id := by
    subst hr
    subst hγ
    exact E.inv_hom_id

/-- The prescribed probe dot is invertible on global content induction,
including the vacuum boundary. -/
def probeGlobalContentDotIso {β δ : Multiset I} (h : {i} + β = δ) :
    globalContentInduction D Sc i a ha h ≅ globalContentInduction D Sc i a ha h :=
  probeContentCastIso D Sc m ha (card_of_add i h) h
    (heightContentInduction D Sc i a ha β.card β)
    (probeHeightContentDotIso D Sc i m ha β.card β)

/-- The isomorphism uses the existing global dot as its forward map. -/
theorem probeGlobalContentDotIso_hom {β δ : Multiset I} (h : {i} + β = δ) :
    (probeGlobalContentDotIso D Sc i m ha h).hom = globalContentDot D Sc i a ha h := rfl

end OddMath.QuiverHecke.CyclotomicAction
