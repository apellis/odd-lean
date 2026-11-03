import OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordWeight
import OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordContentDot
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightDot

/-! # The chosen original-weight dot in regular-power word coordinates

SwappedVacuumCoordinates §§4–6: identify the existing original-weight dot
on every actual word-family E component through its selected comparison.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.PowerWordWeightDot
open CyclotomicAction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (L : I × ℕ → ℕ)

/-- The same descended old-Hom dot on any exact-content component. -/
def wordDotAt (ν : List I) (i : I) (β : Multiset I) : End (PowerWordWeight.wordAt D Sc cutoff L (ν ++ [i]) β) :=
  (BalancedInduction.restriction
    (contentInclusion D Sc cutoff (PowerWordContent.powerBound D cutoff L) β)).map
      (PowerWordContentDot.weightedWordDot D Sc cutoff L ν i)

private theorem contentDotTo_square (ν : List I) (i : I) (β γ : Multiset I)
    (hν : (ν : Multiset I) = β) (hγ : β + ([i] : Multiset I) = γ) :
    (contentInductionTransform D Sc cutoff (PowerWordContent.powerBound D cutoff L) hγ hγ (by
      simpa only [pow_one, one_nsmul] using firstDot_pow_parity D Sc i [] 1)).app (D.parity i)
        (PowerWordWeight.wordAt D Sc cutoff L ν β) ≫
      (PowerWordWeight.contentAppendIsoTo D Sc cutoff L ν i β γ hν hγ).hom =
    (PowerWordWeight.contentAppendIsoTo D Sc cutoff L ν i β γ hν hγ).hom ≫ wordDotAt D Sc cutoff L ν i γ := by
  subst β
  have he : γ = ((ν ++ [i] : List I) : Multiset I) := hγ.symm.trans (Multiset.coe_add ν [i])
  subst γ
  have hc := PowerWordContentDot.content_append_dot D Sc cutoff L ν i
  rw [PowerWordContentDot.chosenContentDot_eq] at hc
  exact hc

private theorem conjugate_from_eq {C : Type*} [Category* C] {A B E : C}
    (e : A ≅ B) (f : B ≅ E) (s : A ⟶ A) (x : B ⟶ B) (y : E ⟶ E)
    (hs : s = e.hom ≫ x ≫ e.inv) (h : x ≫ f.hom = f.hom ≫ y) :
    s ≫ (e ≪≫ f).hom = (e ≪≫ f).hom ≫ y := by
  rw [hs]
  simp only [Iso.trans_hom, Category.assoc, Iso.inv_hom_id_assoc]
  rw [h]

/-- The actual weight dot at the occupied successor block is the literal
old-Hom word dot under the prescribed original-weight comparison. -/
theorem weight_dot_component (Λ : X) (ν : List I) (i : I) :
    elvWeightDotComponent D Sc cutoff (PowerWordContent.powerBound D cutoff L) i Λ
      (PowerWordWeight.wordWeight_append D Λ ν i) (D.parity i)
      (PowerWordWeight.wordFamily D Sc cutoff L Λ (PowerWordWeight.wordWeight D Λ ν) ν)
      (blockSucc D Λ i (PowerWordWeight.wordWeight_append D Λ ν i) (PowerWordWeight.wordBlock D Λ ν)) ≫
        (PowerWordWeight.weightAppendComponentIso D Sc cutoff L Λ ν i).hom =
    (PowerWordWeight.weightAppendComponentIso D Sc cutoff L Λ ν i).hom ≫
      wordDotAt D Sc cutoff L ν i
        (blockSucc D Λ i (PowerWordWeight.wordWeight_append D Λ ν i) (PowerWordWeight.wordBlock D Λ ν)).1 :=
  conjugate_from_eq
    (eqToIso (elvInductionComponent_obj_blockSucc D Sc cutoff (PowerWordContent.powerBound D cutoff L)
      i Λ (PowerWordWeight.wordWeight_append D Λ ν i) (PowerWordWeight.wordBlock D Λ ν)
      (PowerWordWeight.wordFamily D Sc cutoff L Λ (PowerWordWeight.wordWeight D Λ ν) ν)))
    (PowerWordWeight.contentAppendIsoTo D Sc cutoff L ν i _ _ rfl (by rw [blockSucc_val, add_comm]; rfl))
    _ _ _
    (elvWeightDotComponent_blockSucc D Sc cutoff (PowerWordContent.powerBound D cutoff L) i Λ
      (PowerWordWeight.wordWeight_append D Λ ν i) (D.parity i)
      (PowerWordWeight.wordFamily D Sc cutoff L Λ (PowerWordWeight.wordWeight D Λ ν) ν)
      (PowerWordWeight.wordBlock D Λ ν))
    (contentDotTo_square D Sc cutoff L ν i _ _ rfl (by rw [blockSucc_val, add_comm]; rfl))

/-- The full old-Hom dot on every block of the next word family. -/
def wordFamilyDot (Λ : X) (ν : List I) (i : I) :
    End (PowerWordWeight.wordFamily D Sc cutoff L Λ (PowerWordWeight.wordWeight D Λ (ν ++ [i])) (ν ++ [i])) :=
  fun δ => wordDotAt D Sc cutoff L ν i δ.1

private theorem selected_hom (Λ : X) (ν : List I) (i : I) :
    (PowerWordWeight.weightAppendIso D Sc cutoff L Λ ν i).hom
      (blockSucc D Λ i (PowerWordWeight.wordWeight_append D Λ ν i) (PowerWordWeight.wordBlock D Λ ν)) =
      (PowerWordWeight.weightAppendComponentIso D Sc cutoff L Λ ν i).hom := by
  change (PowerWordWeight.weightAppendAtIso D Sc cutoff L Λ ν i _).hom = _
  unfold PowerWordWeight.weightAppendAtIso
  simp

/-- The independently chosen original-weight dot is the full old-Hom word
dot under the selected whole-family comparison. Every present and absent
content component is included, and no operator-comparison premise is used. -/
theorem weight_append_dot (Λ : X) (ν : List I) (i : I) :
    (elvActionDot D Sc cutoff (PowerWordContent.powerBound D cutoff L) i Λ
      (PowerWordWeight.wordWeight_append D Λ ν i)).app (D.parity i)
      (PowerWordWeight.wordFamily D Sc cutoff L Λ (PowerWordWeight.wordWeight D Λ ν) ν) ≫
        (PowerWordWeight.weightAppendIso D Sc cutoff L Λ ν i).hom =
    (PowerWordWeight.weightAppendIso D Sc cutoff L Λ ν i).hom ≫ wordFamilyDot D Sc cutoff L Λ ν i := by
  funext δ
  change elvWeightDotComponent D Sc cutoff (PowerWordContent.powerBound D cutoff L) i Λ
      (PowerWordWeight.wordWeight_append D Λ ν i) (D.parity i)
      (PowerWordWeight.wordFamily D Sc cutoff L Λ (PowerWordWeight.wordWeight D Λ ν) ν) δ ≫
        (PowerWordWeight.weightAppendIso D Sc cutoff L Λ ν i).hom δ =
      (PowerWordWeight.weightAppendIso D Sc cutoff L Λ ν i).hom δ ≫ wordDotAt D Sc cutoff L ν i δ.1
  classical
  by_cases hδ : δ = blockSucc D Λ i (PowerWordWeight.wordWeight_append D Λ ν i) (PowerWordWeight.wordBlock D Λ ν)
  · subst δ
    rw [selected_hom]
    exact weight_dot_component D Sc cutoff L Λ ν i
  · exact (PowerWordWeight.weightAppend_isZero D Sc cutoff L Λ ν i δ hδ).eq_of_src _ _

end OddMath.QuiverHecke.ELVOld.PowerWordWeightDot
