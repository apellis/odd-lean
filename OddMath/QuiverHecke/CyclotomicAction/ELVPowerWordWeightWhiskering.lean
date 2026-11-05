import OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordContentWhiskering
import OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordWeightCross

/-! # Arbitrary-arrow append transport on the weight word family

SwappedVacuumCoordinates §§4–6: preserve the existing whole append chart
while transporting arbitrary full old-Hom maps through the chosen E functor.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.PowerWordWeightWhiskering
open CyclotomicAction CyclotomicCrossingTensor
universe u
private theorem square_paste {C : Type*} [Category* C] {A B E F S T : C}
    (ha : A = B) (hb : E = F) (s : B ≅ S) (t : F ≅ T)
    (c : B ⟶ F) (w : S ⟶ T) (h : c ≫ t.hom = s.hom ≫ w) :
    (eqToHom ha ≫ c ≫ eqToHom hb.symm) ≫ (eqToHom hb ≫ t.hom) =
      (eqToHom ha ≫ s.hom) ≫ w := by
  cases ha
  cases hb
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using h

variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (L : I × ℕ → ℕ)

/-- The existing whole append chart at its given supported block. -/
theorem append_component (Λ : X) (ν : List I) (i : I) (x y : X)
    (hx : x = PowerWordWeight.wordWeight D Λ ν)
    (hy : y = PowerWordWeight.wordWeight D Λ (ν ++ [i])) (h : x + D.α i = y)
    (β : WeightBlocks D Λ x) (hν : (ν : Multiset I) = β.1) :
    (PowerWordWeightCross.appendIsoAtWeights D Sc cutoff L Λ ν i x y hx hy h).hom
      (blockSucc D Λ i h β) =
    eqToHom (elvInductionComponent_obj_blockSucc D Sc cutoff (PowerWordContent.powerBound D cutoff L)
      i Λ h β (PowerWordWeight.wordFamily D Sc cutoff L Λ x ν)) ≫
      (PowerWordWeight.contentAppendIsoTo D Sc cutoff L ν i β.1 (blockSucc D Λ i h β).1 hν
        (elvBlockSucc_content_eq D i Λ h β)).hom := by
  cases hx
  cases hy
  have hβ : β = PowerWordWeight.wordBlock D Λ ν := Subtype.ext hν.symm
  subst β
  change (PowerWordWeight.weightAppendAtIso D Sc cutoff L Λ ν i
    (blockSucc D Λ i h (PowerWordWeight.wordBlock D Λ ν))).hom = _
  unfold PowerWordWeight.weightAppendAtIso
  simp only
  rfl

/-- The full signed old-Hom map on every unchanged content component. -/
def wordFamilyArrow (Λ x : X) (s t : List I)
    (g : (OldCategory.mk t : OldCategory D Sc cutoff) ⟶ OldCategory.mk s) :
    PowerWordWeight.wordFamily D Sc cutoff L Λ x s ⟶ PowerWordWeight.wordFamily D Sc cutoff L Λ x t :=
  fun β => PowerWordContentCross.contentWordArrow D Sc cutoff L β.1 s t g

/-- The single-E source vanishes outside the content of the appended word. -/
theorem append_source_isZero (Λ : X) (ν : List I) (i : I) (x y : X)
    (hx : x = PowerWordWeight.wordWeight D Λ ν)
    (hy : y = PowerWordWeight.wordWeight D Λ (ν ++ [i])) (h : x + D.α i = y)
    (δ : WeightBlocks D Λ y) (hδ : δ.1 ≠ (((ν ++ [i]) : List I) : Multiset I)) :
    Limits.IsZero (((elvE D Sc cutoff (PowerWordContent.powerBound D cutoff L) i Λ h).obj
      (PowerWordWeight.wordFamily D Sc cutoff L Λ x ν)) δ) :=
  (PowerWordWeight.wordAt_isZero D Sc cutoff L (ν ++ [i]) δ.1 hδ).of_iso
    (Pi.isoApp (PowerWordWeightCross.appendIsoAtWeights D Sc cutoff L Λ ν i x y hx hy h) δ)

/-- The given E functor intertwines arbitrary full old-Hom maps through the
existing whole single-append charts, on every content component. -/
theorem append_family_arrow (Λ : X) (s t : List I) (i : I) (x y : X)
    (hxs : x = PowerWordWeight.wordWeight D Λ s)
    (hys : y = PowerWordWeight.wordWeight D Λ (s ++ [i]))
    (hxt : x = PowerWordWeight.wordWeight D Λ t)
    (hyt : y = PowerWordWeight.wordWeight D Λ (t ++ [i]))
    (h : x + D.α i = y) (hst : (s : Multiset I) = (t : Multiset I))
    (g : (OldCategory.mk t : OldCategory D Sc cutoff) ⟶ OldCategory.mk s) :
    (elvE D Sc cutoff (PowerWordContent.powerBound D cutoff L) i Λ h).map
      (wordFamilyArrow D Sc cutoff L Λ x s t g) ≫
        (PowerWordWeightCross.appendIsoAtWeights D Sc cutoff L Λ t i x y hxt hyt h).hom =
    (PowerWordWeightCross.appendIsoAtWeights D Sc cutoff L Λ s i x y hxs hys h).hom ≫
      wordFamilyArrow D Sc cutoff L Λ y (s ++ [i]) (t ++ [i]) ((append D Sc cutoff i).map g) := by
  funext δ
  let β : WeightBlocks D Λ x := ⟨s, hxs.symm⟩
  classical
  by_cases he : δ = blockSucc D Λ i h β
  · subst δ
    change (elvInductionComponent D Sc cutoff (PowerWordContent.powerBound D cutoff L) i Λ h
      (blockSucc D Λ i h β)).map (wordFamilyArrow D Sc cutoff L Λ x s t g) ≫
        (PowerWordWeightCross.appendIsoAtWeights D Sc cutoff L Λ t i x y hxt hyt h).hom
          (blockSucc D Λ i h β) =
      (PowerWordWeightCross.appendIsoAtWeights D Sc cutoff L Λ s i x y hxs hys h).hom
          (blockSucc D Λ i h β) ≫
        PowerWordContentCross.contentWordArrow D Sc cutoff L (blockSucc D Λ i h β).1
          (s ++ [i]) (t ++ [i]) ((append D Sc cutoff i).map g)
    rw [append_component D Sc cutoff L Λ t i x y hxt hyt h β hst.symm,
      append_component D Sc cutoff L Λ s i x y hxs hys h β rfl,
      elvInductionComponent_map_blockSucc]
    have hc := PowerWordContentWhiskering.append_word_arrow D Sc cutoff L s t i β.1
      (blockSucc D Λ i h β).1 rfl hst.symm (elvBlockSucc_content_eq D i Λ h β) g
    have hp := square_paste
      (elvInductionComponent_obj_blockSucc D Sc cutoff (PowerWordContent.powerBound D cutoff L)
        i Λ h β (PowerWordWeight.wordFamily D Sc cutoff L Λ x s))
      (elvInductionComponent_obj_blockSucc D Sc cutoff (PowerWordContent.powerBound D cutoff L)
        i Λ h β (PowerWordWeight.wordFamily D Sc cutoff L Λ x t))
      (PowerWordWeight.contentAppendIsoTo D Sc cutoff L s i β.1 (blockSucc D Λ i h β).1 rfl
        (elvBlockSucc_content_eq D i Λ h β))
      (PowerWordWeight.contentAppendIsoTo D Sc cutoff L t i β.1 (blockSucc D Λ i h β).1 hst.symm
        (elvBlockSucc_content_eq D i Λ h β)) _ _ hc
    dsimp only [elvBlockInd, elvBlockAppend, wordFamilyArrow, Superfunctor.map]
    simpa only [Category.assoc] using hp
  · have hd : δ.1 ≠ (((s ++ [i]) : List I) : Multiset I) := by
      intro hd
      apply he
      apply Subtype.ext
      change δ.1 = {i} + (s : Multiset I)
      rw [hd, ← Multiset.coe_add]
      exact add_comm _ _
    exact (append_source_isZero D Sc cutoff L Λ s i x y hxs hys h δ hd).eq_of_src _ _

end OddMath.QuiverHecke.ELVOld.PowerWordWeightWhiskering
