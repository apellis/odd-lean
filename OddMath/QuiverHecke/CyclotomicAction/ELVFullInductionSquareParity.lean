import OddMath.QuiverHecke.CyclotomicAction.ELVFullInductionSquareSource

/-! # Evenness of the selected full-inclusion charts

The canonical parity-coordinate comparison for Brundan–Ellis
(1.13)–(1.14) uses the selected extension and restriction isomorphisms,
whose forward and inverse module maps are even.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
private theorem natIso_app_hom {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (e : F ≅ G) (x : C) : (e.app x).hom = e.hom.app x := rfl

private theorem functorEq_mem
    {k C D : Type u} [CommRing k] [Category.{u} C] [Category.{u} D]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive D] [Linear k D] [Supercategory k D]
    (J K : C ⥤ D) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    [K.Additive] [K.Linear k] [IsSuperfunctor k K] (h : J = K)
    (M : Superfunctor k C (SVec k)) :
    (inductionFunctorIsoOfEq J K h).hom.app M ∈ parity (R := k) _ _ 0 := by
  subst K
  exact id_mem _

variable {k C A B E : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (U : A ⥤ E) [U.Additive] [U.Linear k] [IsSuperfunctor k U] [U.Full] [U.Faithful]
  (Q : C ⥤ B) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
  (T : B ⥤ E) [T.Additive] [T.Linear k] [IsSuperfunctor k T]
  (h : J ⋙ U = Q ⋙ T) (M : Superfunctor k C (SVec k))

omit [U.Full] [U.Faithful] in
/-- All three legs of the chosen induction extension comparison are even. -/
theorem fullSquareExtensionIso_hom_mem :
    (fullSquareExtensionIso J U Q T h).hom.app M ∈ parity (R := k) _ _ 0 := by
  have h0 := comp_mem (inductionComp_hom_mem J U M)
    (comp_mem (functorEq_mem (J ⋙ U) (Q ⋙ T) h M) (inductionComp_inv_mem Q T M))
  simpa only [fullSquareExtensionIso, Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
    Category.assoc, zero_add] using h0

/-- The selected full-inclusion unit and extension comparison are even. -/
theorem fullSquareRestrictionIso_hom_mem :
    (fullSquareRestrictionIso J U Q T h M).hom ∈ parity (R := k) _ _ 0 := by
  have hU : (fullyFaithfulUnitIso U (induced J M)).hom ∈ parity (R := k) _ _ 0 := by
    rw [fullyFaithfulUnitIso_hom]
    exact adjunctionUnit_mem U (induced J M)
  have hE := map_mem (restriction U) (fullSquareExtensionIso_hom_mem J U Q T h M)
  have h0 := comp_mem hU hE
  simp only [fullSquareRestrictionIso, Iso.trans_hom, Functor.mapIso_hom, natIso_app_hom]
  set_option backward.dsimp.instances true in
    dsimp only [induction, Functor.comp_obj] at h0 ⊢
  simpa only [zero_add] using h0

theorem fullSquareRestrictionIso_inv_mem :
    (fullSquareRestrictionIso J U Q T h M).inv ∈ parity (R := k) _ _ 0 :=
  inv_mem _ (fullSquareRestrictionIso_hom_mem J U Q T h M)

/-- An even chosen input isomorphism retains evenness of the full source chart. -/
theorem fullSquareSourceIso_hom_mem (P : Superfunctor k B (SVec k)) (e : induced Q M ≅ P)
    (he : e.hom ∈ parity (R := k) _ _ 0) :
    (fullSquareSourceIso J U Q T h M P e).hom ∈ parity (R := k) _ _ 0 := by
  have hE := map_mem (restriction U) (map_mem (induction T) he)
  have h0 := comp_mem (fullSquareRestrictionIso_hom_mem J U Q T h M) hE
  simp only [fullSquareSourceIso, Iso.trans_hom, Functor.mapIso_hom]
  set_option backward.dsimp.instances true in
    dsimp only [induction, Functor.comp_obj] at h0 ⊢
  simpa only [zero_add] using h0

theorem fullSquareSourceIso_inv_mem (P : Superfunctor k B (SVec k)) (e : induced Q M ≅ P)
    (he : e.hom ∈ parity (R := k) _ _ 0) :
    (fullSquareSourceIso J U Q T h M P e).inv ∈ parity (R := k) _ _ 0 :=
  inv_mem _ (fullSquareSourceIso_hom_mem J U Q T h M P e he)

/-- The source chart is the total component of the specified module isomorphism. -/
theorem fullSquareSourceIso_total_apply (P : Superfunctor k B (SVec k)) (e : induced Q M ≅ P)
    (w : A) (x : Obj J M.toFunctor w) :
    (fullSquareSourceIso J U Q T h M P e).hom.total w x =
      fullSquareSourceLinear J U Q T h M P e w x := rfl

end OddMath.QuiverHecke.ELVOld.BalancedInduction
