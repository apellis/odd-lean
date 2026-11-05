import OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordWhiskering

/-! # Right contexts for the chosen regular-power word action

SwappedVacuumCoordinates §§4–5: iterate the independently chosen append
functors and their selected comparisons, retaining both parity components
of every old arrow and the full coefficient-power quotient.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.PowerWordContexts
open CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (L : I × ℕ → ℕ)

/-- Successive literal right appends, with endpoints fixed recursively. -/
def extendedWord (s : List I) : List I → List I
  | [] => s
  | i :: η => extendedWord (s ++ [i]) η

theorem extendedWord_eq (s η : List I) : extendedWord s η = s ++ η := by
  induction η generalizing s with
  | nil => simp [extendedWord]
  | cons i η ih => simpa only [extendedWord, List.append_assoc, List.singleton_append] using ih (s ++ [i])

/-- The literal composite of the existing append induction functors. -/
def contextInduction : List I →
    Superfunctor k (OldCategory D Sc cutoff) (SVec k) ⥤
      Superfunctor k (OldCategory D Sc cutoff) (SVec k)
  | [] => 𝟭 _
  | i :: η => BalancedInduction.induction (append D Sc cutoff i) ⋙ contextInduction η

/-- The old arrow is extended by those same append functors. -/
def extendedArrow (s t : List I) : (η : List I) →
    ((OldCategory.mk t : OldCategory D Sc cutoff) ⟶ OldCategory.mk s) →
    ((OldCategory.mk (extendedWord t η) : OldCategory D Sc cutoff) ⟶ OldCategory.mk (extendedWord s η))
  | [], g => g
  | i :: η, g => extendedArrow (s ++ [i]) (t ++ [i]) η ((append D Sc cutoff i).map g)

/-- Only the existing selected single append isomorphisms are composed. -/
def contextIso (s : List I) : (η : List I) →
    (contextInduction D Sc cutoff η).obj (powerWordModule D Sc cutoff L s) ≅
      powerWordModule D Sc cutoff L (extendedWord s η)
  | [] => Iso.refl _
  | i :: η => (contextInduction D Sc cutoff η).mapIso (powerWordAppendIso D Sc cutoff L s i) ≪≫
      contextIso (s ++ [i]) η

private def contextEquation (s t η : List I)
    (g : (OldCategory.mk t : OldCategory D Sc cutoff) ⟶ OldCategory.mk s) : Prop :=
  (contextInduction D Sc cutoff η).map (PowerWordMorphisms.fromArrow D Sc cutoff L s t g) ≫
      (contextIso D Sc cutoff L t η).hom =
    (contextIso D Sc cutoff L s η).hom ≫
      PowerWordMorphisms.fromArrow D Sc cutoff L (extendedWord s η) (extendedWord t η)
        (extendedArrow D Sc cutoff s t η g)

private theorem comparison_step {C B E : Type*} [Category* C] [Category* B] [Category* E]
    (K : C ⥤ B) (H : B ⥤ E) {P Q : C} {V W : B} {S T : E}
    (e : K.obj P ≅ V) (f : K.obj Q ≅ W) (c : H.obj V ≅ S) (d : H.obj W ≅ T)
    (x : P ⟶ Q) (y : V ⟶ W) (z : S ⟶ T)
    (h₀ : K.map x ≫ f.hom = e.hom ≫ y) (h₁ : H.map y ≫ d.hom = c.hom ≫ z) :
    (K ⋙ H).map x ≫ (H.mapIso f ≪≫ d).hom = (H.mapIso e ≪≫ c).hom ≫ z := by
  simp only [Functor.comp_map, Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [← Category.assoc, ← H.map_comp, h₀, H.map_comp, Category.assoc, h₁]

end OddMath.QuiverHecke.ELVOld.PowerWordContexts
