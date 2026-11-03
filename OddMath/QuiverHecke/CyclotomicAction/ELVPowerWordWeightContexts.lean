import OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordEvaluation
import OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordContexts

/-! # Chosen right contexts on the full-coefficient weight word family

SwappedVacuumCoordinates §§4–6: iterate the given E functors and existing
single-append charts on arbitrary full old-Hom arrows.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.PowerWordWeightContexts
open CyclotomicAction CyclotomicCrossingTensor
universe u
section Weight
variable {I X : Type u} [AddCommGroup X] (D : SKM.Datum I X)
/-- The literal successive target weights along a right context. -/
def contextWeight (x : X) : List I → X
  | [] => x
  | i :: η => contextWeight (x + D.α i) η
end Weight

private theorem comparison_step {C B E : Type*} [Category* C] [Category* B] [Category* E]
    (K : C ⥤ B) (H : B ⥤ E) {P Q : C} {V W : B} {S T : E}
    (e : K.obj P ≅ V) (f : K.obj Q ≅ W) (c : H.obj V ≅ S) (d : H.obj W ≅ T)
    (x : P ⟶ Q) (y : V ⟶ W) (z : S ⟶ T)
    (h₀ : K.map x ≫ f.hom = e.hom ≫ y) (h₁ : H.map y ≫ d.hom = c.hom ≫ z) :
    (K ⋙ H).map x ≫ (H.mapIso f ≪≫ d).hom = (H.mapIso e ≪≫ c).hom ≫ z := by
  simp only [Functor.comp_map, Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [← Category.assoc, ← H.map_comp, h₀, H.map_comp, Category.assoc, h₁]

variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (L : I × ℕ → ℕ)
  (Λ : X)
local notation "N" => PowerWordContent.powerBound D cutoff L

/-- Actual successive E functors, at their actual successive weights. -/
def contextFunctor (x : X) : (η : List I) → ELVWeightProduct D Sc cutoff N Λ x ⥤
    ELVWeightProduct D Sc cutoff N Λ (contextWeight D x η)
  | [] => 𝟭 _
  | i :: η => elvEFunctor D Sc cutoff N i Λ (rfl : x + D.α i = x + D.α i) ⋙
      contextFunctor (x + D.α i) η

omit [Fintype I] in
private theorem append_weight (ν : List I) (i : I) (x : X)
    (hx : x = PowerWordWeight.wordWeight D Λ ν) :
    x + D.α i = PowerWordWeight.wordWeight D Λ (ν ++ [i]) :=
  (congrArg (fun y => y + D.α i) hx).trans (PowerWordWeight.wordWeight_append D Λ ν i)

omit [Fintype I] in
/-- The resulting weight is the weight of the literal extended word. -/
theorem context_weight_word (ν η : List I) (x : X)
    (hx : x = PowerWordWeight.wordWeight D Λ ν) :
    contextWeight D x η = PowerWordWeight.wordWeight D Λ (PowerWordContexts.extendedWord ν η) := by
  induction η generalizing ν x with
  | nil => exact hx
  | cons i η ih => exact ih (ν ++ [i]) (x + D.α i) (append_weight D Λ ν i x hx)

/-- Only the existing whole append comparisons are composed. -/
def contextIso (ν : List I) (x : X) (hx : x = PowerWordWeight.wordWeight D Λ ν) :
    (η : List I) → (contextFunctor D Sc cutoff L Λ x η).obj (PowerWordWeight.wordFamily D Sc cutoff L Λ x ν) ≅
      PowerWordWeight.wordFamily D Sc cutoff L Λ (contextWeight D x η) (PowerWordContexts.extendedWord ν η)
  | [] => Iso.refl _
  | i :: η => (contextFunctor D Sc cutoff L Λ (x + D.α i) η).mapIso
      (PowerWordWeightCross.appendIsoAtWeights D Sc cutoff L Λ ν i x (x + D.α i) hx
        (append_weight D Λ ν i x hx) rfl) ≪≫
      contextIso (ν ++ [i]) (x + D.α i) (append_weight D Λ ν i x hx) η

private def contextEquation (s t η : List I) (x : X)
    (hs : x = PowerWordWeight.wordWeight D Λ s) (ht : x = PowerWordWeight.wordWeight D Λ t)
    (g : (OldCategory.mk t : OldCategory D Sc cutoff) ⟶ OldCategory.mk s) : Prop :=
  (contextFunctor D Sc cutoff L Λ x η).map (PowerWordWeightWhiskering.wordFamilyArrow D Sc cutoff L Λ x s t g) ≫
      (contextIso D Sc cutoff L Λ t x ht η).hom =
    (contextIso D Sc cutoff L Λ s x hs η).hom ≫
      PowerWordWeightWhiskering.wordFamilyArrow D Sc cutoff L Λ (contextWeight D x η)
        (PowerWordContexts.extendedWord s η) (PowerWordContexts.extendedWord t η)
        (PowerWordContexts.extendedArrow D Sc cutoff s t η g)

/-- Every chosen right context has the prescribed full old-Hom operator on
all content blocks and coefficient vectors. The weight equalities only
express the unchanged weights of the same-content words. -/
theorem context_family_arrow (s t η : List I) (x : X)
    (hs : x = PowerWordWeight.wordWeight D Λ s) (ht : x = PowerWordWeight.wordWeight D Λ t)
    (hst : (s : Multiset I) = (t : Multiset I))
    (g : (OldCategory.mk t : OldCategory D Sc cutoff) ⟶ OldCategory.mk s) :
    contextEquation D Sc cutoff L Λ s t η x hs ht g := by
  induction η generalizing s t x with
  | nil =>
      change (𝟭 _).map _ ≫ (Iso.refl _).hom = (Iso.refl _).hom ≫ _
      simp only [Functor.id_map, Iso.refl_hom, Category.comp_id, Category.id_comp]
      rfl
  | cons i η ih =>
      have hst' : ((s ++ [i] : List I) : Multiset I) = ((t ++ [i] : List I) : Multiset I) := by
        rw [← Multiset.coe_add, ← Multiset.coe_add, hst]
      exact comparison_step
        (elvEFunctor D Sc cutoff N i Λ (rfl : x + D.α i = x + D.α i))
        (contextFunctor D Sc cutoff L Λ (x + D.α i) η)
        (PowerWordWeightCross.appendIsoAtWeights D Sc cutoff L Λ s i x (x + D.α i) hs
          (append_weight D Λ s i x hs) rfl)
        (PowerWordWeightCross.appendIsoAtWeights D Sc cutoff L Λ t i x (x + D.α i) ht
          (append_weight D Λ t i x ht) rfl)
        (contextIso D Sc cutoff L Λ (s ++ [i]) (x + D.α i) (append_weight D Λ s i x hs) η)
        (contextIso D Sc cutoff L Λ (t ++ [i]) (x + D.α i) (append_weight D Λ t i x ht) η)
        (PowerWordWeightWhiskering.wordFamilyArrow D Sc cutoff L Λ x s t g)
        (PowerWordWeightWhiskering.wordFamilyArrow D Sc cutoff L Λ (x + D.α i) (s ++ [i]) (t ++ [i])
          ((append D Sc cutoff i).map g))
        (PowerWordWeightWhiskering.wordFamilyArrow D Sc cutoff L Λ (contextWeight D (x + D.α i) η)
          (PowerWordContexts.extendedWord (s ++ [i]) η) (PowerWordContexts.extendedWord (t ++ [i]) η)
          (PowerWordContexts.extendedArrow D Sc cutoff (s ++ [i]) (t ++ [i]) η ((append D Sc cutoff i).map g)))
        (PowerWordWeightWhiskering.append_family_arrow D Sc cutoff L Λ s t i x (x + D.α i)
          hs (append_weight D Λ s i x hs) ht (append_weight D Λ t i x ht) rfl hst g)
        (ih (s ++ [i]) (t ++ [i]) (x + D.α i) (append_weight D Λ s i x hs)
          (append_weight D Λ t i x ht) hst' ((append D Sc cutoff i).map g))

/-- Apply the given context to a selected chart, then use only the existing
recursive whole append comparisons. -/
def contextChart (ν η : List I) (x : X) (hx : x = PowerWordWeight.wordWeight D Λ ν)
    {A : ELVWeightProduct D Sc cutoff N Λ x}
    (e : A ≅ PowerWordWeight.wordFamily D Sc cutoff L Λ x ν) :
    (contextFunctor D Sc cutoff L Λ x η).obj A ≅
      PowerWordWeight.wordFamily D Sc cutoff L Λ (contextWeight D x η) (PowerWordContexts.extendedWord ν η) :=
  (contextFunctor D Sc cutoff L Λ x η).mapIso e ≪≫ contextIso D Sc cutoff L Λ ν x hx η

private theorem contextualize_arrow (s t η : List I) (x : X)
    (hs : x = PowerWordWeight.wordWeight D Λ s) (ht : x = PowerWordWeight.wordWeight D Λ t)
    (hst : (s : Multiset I) = (t : Multiset I))
    (g : (OldCategory.mk t : OldCategory D Sc cutoff) ⟶ OldCategory.mk s)
    {A B : ELVWeightProduct D Sc cutoff N Λ x}
    (e : A ≅ PowerWordWeight.wordFamily D Sc cutoff L Λ x s)
    (f : B ≅ PowerWordWeight.wordFamily D Sc cutoff L Λ x t) (a : A ⟶ B)
    (ha : a ≫ f.hom = e.hom ≫ PowerWordWeightWhiskering.wordFamilyArrow D Sc cutoff L Λ x s t g) :
    (contextFunctor D Sc cutoff L Λ x η).map a ≫ (contextChart D Sc cutoff L Λ t η x ht f).hom =
      (contextChart D Sc cutoff L Λ s η x hs e).hom ≫
        PowerWordWeightWhiskering.wordFamilyArrow D Sc cutoff L Λ (contextWeight D x η)
          (PowerWordContexts.extendedWord s η) (PowerWordContexts.extendedWord t η)
          (PowerWordContexts.extendedArrow D Sc cutoff s t η g) :=
  comparison_step (𝟭 _) (contextFunctor D Sc cutoff L Λ x η) e f
    (contextIso D Sc cutoff L Λ s x hs η) (contextIso D Sc cutoff L Λ t x ht η) a _ _ ha
    (context_family_arrow D Sc cutoff L Λ s t η x hs ht hst g)

/-- The given dot, inside an arbitrary chosen right E-context, has the
literal appended old-Hom coordinate on every coefficient vector. -/
theorem dot_in_context (ν η : List I) (i : I) :
    (contextFunctor D Sc cutoff L Λ (PowerWordWeight.wordWeight D Λ (ν ++ [i])) η).map
      ((elvActionDot D Sc cutoff N i Λ (PowerWordWeight.wordWeight_append D Λ ν i)).app (D.parity i)
        (PowerWordEvaluation.value D Sc cutoff L Λ ν)) ≫
      (contextChart D Sc cutoff L Λ (ν ++ [i]) η _ rfl (PowerWordEvaluation.appendChart D Sc cutoff L Λ ν i)).hom =
    (contextChart D Sc cutoff L Λ (ν ++ [i]) η _ rfl (PowerWordEvaluation.appendChart D Sc cutoff L Λ ν i)).hom ≫
      PowerWordWeightWhiskering.wordFamilyArrow D Sc cutoff L Λ
        (contextWeight D (PowerWordWeight.wordWeight D Λ (ν ++ [i])) η)
        (PowerWordContexts.extendedWord (ν ++ [i]) η) (PowerWordContexts.extendedWord (ν ++ [i]) η)
        (PowerWordContexts.extendedArrow D Sc cutoff (ν ++ [i]) (ν ++ [i]) η
          (oldAppendDotComponent D Sc cutoff i (OldCategory.mk ν))) :=
  contextualize_arrow D Sc cutoff L Λ (ν ++ [i]) (ν ++ [i]) η _ rfl rfl rfl
    (oldAppendDotComponent D Sc cutoff i (OldCategory.mk ν))
    (PowerWordEvaluation.appendChart D Sc cutoff L Λ ν i) (PowerWordEvaluation.appendChart D Sc cutoff L Λ ν i) _
    (PowerWordEvaluation.dot_append_value D Sc cutoff L Λ ν i)

omit [Fintype I] in
private theorem pair_weight (ν : List I) (i j : I) {xj xu : X}
    (h₁ : PowerWordWeight.wordWeight D Λ ν + D.α j = xj) (h₂ : xj + D.α i = xu) :
    xu = PowerWordWeight.wordWeight D Λ ((ν ++ [j]) ++ [i]) :=
  h₂.symm.trans ((congrArg (fun x => x + D.α i)
    (h₁.symm.trans (PowerWordWeight.wordWeight_append D Λ ν j))).trans
      (PowerWordWeight.wordWeight_append D Λ (ν ++ [j]) i))

/-- The given signed crossing inside an arbitrary chosen right E-context,
for both colour cases, retains every old-arrow coefficient and actual weight. -/
theorem cross_in_context (ν η : List I) (i j : I) {xj xu xi : X}
    (h₁ : PowerWordWeight.wordWeight D Λ ν + D.α j = xj) (h₂ : xj + D.α i = xu)
    (h₃ : PowerWordWeight.wordWeight D Λ ν + D.α i = xi) (h₄ : xi + D.α j = xu) :
    (contextFunctor D Sc cutoff L Λ xu η).map
      ((elvActionCross D Sc cutoff N i j Λ h₁ h₂ h₃ h₄).app (D.parity i * D.parity j)
        (PowerWordEvaluation.value D Sc cutoff L Λ ν)) ≫
      (contextChart D Sc cutoff L Λ ((ν ++ [i]) ++ [j]) η xu (pair_weight D Λ ν j i h₃ h₄)
        (PowerWordEvaluation.pairChart D Sc cutoff L Λ ν j i h₃ h₄)).hom =
    (contextChart D Sc cutoff L Λ ((ν ++ [j]) ++ [i]) η xu (pair_weight D Λ ν i j h₁ h₂)
      (PowerWordEvaluation.pairChart D Sc cutoff L Λ ν i j h₁ h₂)).hom ≫
      PowerWordWeightWhiskering.wordFamilyArrow D Sc cutoff L Λ (contextWeight D xu η)
        (PowerWordContexts.extendedWord ((ν ++ [j]) ++ [i]) η)
        (PowerWordContexts.extendedWord ((ν ++ [i]) ++ [j]) η)
        (PowerWordContexts.extendedArrow D Sc cutoff ((ν ++ [j]) ++ [i]) ((ν ++ [i]) ++ [j]) η
          (PowerWordContentCross.normalizedOldCross D Sc cutoff ν i j)) := by
  have hst : (((ν ++ [j]) ++ [i] : List I) : Multiset I) = (((ν ++ [i]) ++ [j] : List I) : Multiset I) := by
    rw [← Multiset.coe_add, ← Multiset.coe_add, ← Multiset.coe_add, ← Multiset.coe_add]
    ac_rfl
  exact contextualize_arrow D Sc cutoff L Λ ((ν ++ [j]) ++ [i]) ((ν ++ [i]) ++ [j]) η xu
    (pair_weight D Λ ν i j h₁ h₂) (pair_weight D Λ ν j i h₃ h₄) hst
    (PowerWordContentCross.normalizedOldCross D Sc cutoff ν i j)
    (PowerWordEvaluation.pairChart D Sc cutoff L Λ ν i j h₁ h₂)
    (PowerWordEvaluation.pairChart D Sc cutoff L Λ ν j i h₃ h₄) _
    (PowerWordEvaluation.cross_pair_value D Sc cutoff L Λ ν i j h₁ h₂ h₃ h₄)
end OddMath.QuiverHecke.ELVOld.PowerWordWeightContexts
