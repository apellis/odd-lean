import OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordContent
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightModules

/-! # Scheduled word modules under the chosen weight induction

SwappedVacuumCoordinates §§4–6: attach the bounded regular-power word model
to the original weight product and its independently chosen E functor.
All content components are retained. This is an object comparison; transport
of chosen dot/crossing maps remains a separate step.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.PowerWordWeight
open CyclotomicAction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (L : I × ℕ → ℕ)

/-- Every content component of the same actual descended word module. -/
def wordAt (ν : List I) (β : Multiset I) :
    ContentModules D Sc cutoff (PowerWordContent.powerBound D cutoff L) β :=
  (BalancedInduction.restriction (contentInclusion D Sc cutoff
    (PowerWordContent.powerBound D cutoff L) β)).obj (PowerWordContent.weightedWord D Sc cutoff L ν)

/-- The original weight product, retaining every content block. -/
def wordFamily (Λ x : X) (ν : List I) :
    ELVWeightProduct D Sc cutoff (PowerWordContent.powerBound D cutoff L) Λ x :=
  fun β => wordAt D Sc cutoff L ν β.1

/-- The source and target content labels are arbitrary equal presentations
of the same literal word contents. -/
def contentAppendIsoTo (ν : List I) (i : I) (β γ : Multiset I)
    (hν : (ν : Multiset I) = β) (hγ : β + ([i] : Multiset I) = γ) :
    BalancedInduction.induced
      (contentAppendTo D Sc cutoff (PowerWordContent.powerBound D cutoff L) β [i] γ hγ)
      (wordAt D Sc cutoff L ν β) ≅ wordAt D Sc cutoff L (ν ++ [i]) γ := by
  subst β
  have he : γ = ((ν ++ [i] : List I) : Multiset I) := hγ.symm.trans (Multiset.coe_add ν [i])
  subst γ
  exact PowerWordContent.contentAppendIso D Sc cutoff L ν i

/-- The unchanged original weight associated with the word content. -/
abbrev wordWeight (Λ : X) (ν : List I) : X := blockWeight D Λ (ν : Multiset I)

omit [Fintype I] in
theorem wordWeight_append (Λ : X) (ν : List I) (i : I) :
    wordWeight D Λ ν + D.α i = wordWeight D Λ (ν ++ [i]) := by
  unfold wordWeight
  rw [← Multiset.coe_add, add_comm (ν : Multiset I) ([i] : Multiset I)]
  exact (blockWeight_cons D Λ i (ν : Multiset I)).symm

/-- The occupied block of the original weight product. -/
def wordBlock (Λ : X) (ν : List I) : WeightBlocks D Λ (wordWeight D Λ ν) := ⟨ν, rfl⟩

/-- The actual E component at its actual successor block is the next
regular-power word component, via the given content append comparison. -/
def weightAppendComponentIso (Λ : X) (ν : List I) (i : I) :
    ((elvE D Sc cutoff (PowerWordContent.powerBound D cutoff L) i Λ (wordWeight_append D Λ ν i)).obj
      (wordFamily D Sc cutoff L Λ (wordWeight D Λ ν) ν))
        (blockSucc D Λ i (wordWeight_append D Λ ν i) (wordBlock D Λ ν)) ≅
    wordAt D Sc cutoff L (ν ++ [i])
      (blockSucc D Λ i (wordWeight_append D Λ ν i) (wordBlock D Λ ν)).1 :=
  eqToIso (elvInductionComponent_obj_blockSucc D Sc cutoff (PowerWordContent.powerBound D cutoff L)
    i Λ (wordWeight_append D Λ ν i) (wordBlock D Λ ν)
    (wordFamily D Sc cutoff L Λ (wordWeight D Λ ν) ν)) ≪≫
      contentAppendIsoTo D Sc cutoff L ν i _ _ rfl (by rw [blockSucc_val, add_comm]; rfl)

/-- Other content components are literally zero because the underlying
actual word module has the proved exact support. -/
theorem wordAt_isZero (ν : List I) (β : Multiset I) (hβ : β ≠ (ν : Multiset I)) :
    Limits.IsZero (wordAt D Sc cutoff L ν β) := by
  apply (Limits.IsZero.iff_id_eq_zero _).mpr
  apply Superfunctor.hom_ext
  intro p w
  have hs : Subsingleton ((wordAt D Sc cutoff L ν β).obj w) :=
    PowerWordContent.weightedWord_supported D Sc cutoff L ν w.obj
      (fun he => hβ (w.content.symm.trans he))
  apply SVec.hom_ext
  intro x
  exact hs.elim _ _

private theorem induction_isZero {C B : Type*} [Category* C] [Category* B]
    [Preadditive C] [Preadditive B] (F : C ⥤ B) [F.Additive] (x : C) (hx : Limits.IsZero x) :
    Limits.IsZero (F.obj x) := by
  apply (Limits.IsZero.iff_id_eq_zero _).mpr
  have he : 𝟙 x = 0 := (Limits.IsZero.iff_id_eq_zero _).mp hx
  rw [← F.map_id, he, F.map_zero]

/-- Every nonselected output block of the actual E object is zero. This
includes both absent predecessors and present predecessors outside support. -/
theorem weightAppend_isZero (Λ : X) (ν : List I) (i : I)
    (δ : WeightBlocks D Λ (wordWeight D Λ (ν ++ [i])))
    (hδ : δ ≠ blockSucc D Λ i (wordWeight_append D Λ ν i) (wordBlock D Λ ν)) :
    Limits.IsZero (((elvE D Sc cutoff (PowerWordContent.powerBound D cutoff L) i Λ
      (wordWeight_append D Λ ν i)).obj (wordFamily D Sc cutoff L Λ (wordWeight D Λ ν) ν)) δ) := by
  classical
  change Limits.IsZero ((elvInductionComponent D Sc cutoff (PowerWordContent.powerBound D cutoff L)
    i Λ (wordWeight_append D Λ ν i) δ).obj (wordFamily D Sc cutoff L Λ (wordWeight D Λ ν) ν))
  by_cases hc : ∃ β, blockSucc D Λ i (wordWeight_append D Λ ν i) β = δ
  · obtain ⟨β, rfl⟩ := hc
    have hβ : β.1 ≠ (ν : Multiset I) := by
      intro he
      apply hδ
      exact congrArg (blockSucc D Λ i (wordWeight_append D Λ ν i)) (show β = wordBlock D Λ ν from Subtype.ext he)
    rw [elvInductionComponent_obj_blockSucc]
    exact induction_isZero (elvBlockInd D Sc cutoff (PowerWordContent.powerBound D cutoff L)
      i Λ (wordWeight_append D Λ ν i) β).toFunctor _ (wordAt_isZero D Sc cutoff L ν β.1 hβ)
  · exact elvInductionComponent_isZero D Sc cutoff (PowerWordContent.powerBound D cutoff L)
      i Λ (wordWeight_append D Λ ν i) δ hc _

/-- Component isomorphisms use the given selected comparison on the occupied
block and uniqueness of zero objects on every other block. -/
def weightAppendAtIso (Λ : X) (ν : List I) (i : I)
    (δ : WeightBlocks D Λ (wordWeight D Λ (ν ++ [i]))) :
    (((elvE D Sc cutoff (PowerWordContent.powerBound D cutoff L) i Λ
      (wordWeight_append D Λ ν i)).obj (wordFamily D Sc cutoff L Λ (wordWeight D Λ ν) ν)) δ) ≅
      wordAt D Sc cutoff L (ν ++ [i]) δ.1 := by
  classical
  by_cases hδ : δ = blockSucc D Λ i (wordWeight_append D Λ ν i) (wordBlock D Λ ν)
  · subst δ
    exact weightAppendComponentIso D Sc cutoff L Λ ν i
  · have hβ : δ.1 ≠ ((ν ++ [i] : List I) : Multiset I) := by
      intro he
      apply hδ
      apply Subtype.ext
      change δ.1 = {i} + (ν : Multiset I)
      rw [he, ← Multiset.coe_add]
      exact add_comm _ _
    exact (weightAppend_isZero D Sc cutoff L Λ ν i δ hδ).iso
      (wordAt_isZero D Sc cutoff L (ν ++ [i]) δ.1 hβ)

/-- The whole independently chosen original-weight E object is the next
word family, including all present and absent content blocks. -/
def weightAppendIso (Λ : X) (ν : List I) (i : I) :
    (elvE D Sc cutoff (PowerWordContent.powerBound D cutoff L) i Λ
      (wordWeight_append D Λ ν i)).obj (wordFamily D Sc cutoff L Λ (wordWeight D Λ ν) ν) ≅
    wordFamily D Sc cutoff L Λ (wordWeight D Λ (ν ++ [i])) (ν ++ [i]) :=
  Pi.isoMk (fun δ => weightAppendAtIso D Sc cutoff L Λ ν i δ)

end OddMath.QuiverHecke.ELVOld.PowerWordWeight
