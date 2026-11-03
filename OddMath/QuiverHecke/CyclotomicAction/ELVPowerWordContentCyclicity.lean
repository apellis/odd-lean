import OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordWeight
import OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordYoneda

/-! # Cyclicity of the full regular-power word module on exact content

SwappedVacuumCoordinates §4 uses the word identity as cyclic vector in the
signed Hom model. Equality on this unit determines whole supernatural module
maps: all full coefficient vectors are covered by the proved generator
surjectivity, not an assumed faithful evaluation.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.PowerWordContentCyclicity
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (L : I × ℕ → ℕ)
  (ν : List I) (β : Multiset I) (hν : (ν : Multiset I) = β)

/-- The literal word object in its own exact content category. -/
def wordObject : ContentCategory D Sc cutoff (PowerWordContent.powerBound D cutoff L) β :=
  ⟨⟨ν⟩, hν⟩

/-- The actual old-Hom identity tensor the regular coefficient unit. -/
def wordUnit : (PowerWordWeight.wordAt D Sc cutoff L ν β).obj (wordObject D Sc cutoff L ν β hν) :=
  PowerWordYoneda.unitVector D Sc cutoff L ν

theorem wordUnit_even : wordUnit D Sc cutoff L ν β hν ∈
    ((PowerWordWeight.wordAt D Sc cutoff L ν β).obj (wordObject D Sc cutoff L ν β hν)).part 0 :=
  PowerWordYoneda.unitVector_even D Sc cutoff L ν

/-- Each entire old arrow, including its coefficients, maps to this literal
quotient arrow inside the chosen content category. -/
def arrowFromOld (w : ContentCategory D Sc cutoff (PowerWordContent.powerBound D cutoff L) β)
    (g : (OldCategory.mk ν : OldCategory D Sc cutoff) ⟶ OldCategory.mk w.obj.word) :
    wordObject D Sc cutoff L ν β hν ⟶ w :=
  truncateOld D Sc cutoff (PowerWordContent.powerBound D cutoff L) ν w.obj.word g

/-- The full old coefficient/Hom generator on the unchanged model carrier. -/
def generator (w : ContentCategory D Sc cutoff (PowerWordContent.powerBound D cutoff L) β) :
    ((OldCategory.mk ν : OldCategory D Sc cutoff) ⟶ OldCategory.mk w.obj.word) →ₗ[k]
      (PowerWordWeight.wordAt D Sc cutoff L ν β).obj w :=
  powerWordGenerator D Sc cutoff L ν (OldCategory.mk w.obj.word)

theorem generator_surjective
    (w : ContentCategory D Sc cutoff (PowerWordContent.powerBound D cutoff L) β) :
    Function.Surjective (generator D Sc cutoff L ν β w) :=
  powerWordGenerator_surjective D Sc cutoff L ν (OldCategory.mk w.obj.word)

/-- Every vector is obtained from the unit by a full old arrow in the
actual descended content action. -/
theorem generator_as_map_unit
    (w : ContentCategory D Sc cutoff (PowerWordContent.powerBound D cutoff L) β)
    (g : (OldCategory.mk ν : OldCategory D Sc cutoff) ⟶ OldCategory.mk w.obj.word) :
    (PowerWordWeight.wordAt D Sc cutoff L ν β).map (arrowFromOld D Sc cutoff L ν β hν w g)
      (wordUnit D Sc cutoff L ν β hν) = generator D Sc cutoff L ν β w g := by
  have hm := weightedRestrictionModule_map D Sc cutoff (PowerWordContent.powerBound D cutoff L)
    (powerWordModule D Sc cutoff L ν) (PowerWordContent.word_killsWeighted D Sc cutoff L ν)
    (OldCategory.mk ν) (OldCategory.mk w.obj.word) g
  change (PowerWordContent.weightedWord D Sc cutoff L ν).map
    ((oldTruncateFunctor D Sc cutoff (PowerWordContent.powerBound D cutoff L)).map g) =
      (powerWordModule D Sc cutoff L ν).map g at hm
  change (PowerWordContent.weightedWord D Sc cutoff L ν).map
    ((oldTruncateFunctor D Sc cutoff (PowerWordContent.powerBound D cutoff L)).map g)
      (PowerWordYoneda.unitVector D Sc cutoff L ν) = _
  rw [hm]
  change (powerWordModule D Sc cutoff L ν).map g
    (powerWordGenerator D Sc cutoff L ν (OldCategory.mk ν) (𝟙 _)) =
      powerWordGenerator D Sc cutoff L ν (OldCategory.mk w.obj.word) g
  simpa only [Category.id_comp] using PowerWordYoneda.generator_naturality D Sc cutoff L ν g (𝟙 _)

variable (M : ContentModules D Sc cutoff (PowerWordContent.powerBound D cutoff L) β)

/-- The entire coefficient arrow remains inside the total parity twist. -/
theorem app_generator
    (f : PowerWordWeight.wordAt D Sc cutoff L ν β ⟶ M) (p : ZMod 2)
    (w : ContentCategory D Sc cutoff (PowerWordContent.powerBound D cutoff L) β)
    (g : (OldCategory.mk ν : OldCategory D Sc cutoff) ⟶ OldCategory.mk w.obj.word) :
    f.app p w (generator D Sc cutoff L ν β w g) =
      M.map (twist k p (arrowFromOld D Sc cutoff L ν β hν w g))
        (f.app p (wordObject D Sc cutoff L ν β hν) (wordUnit D Sc cutoff L ν β hν)) := by
  have hn := congrArg (fun a => a (wordUnit D Sc cutoff L ν β hν))
    ((f.isSupernatural p).naturality_twist (arrowFromOld D Sc cutoff L ν β hν w g))
  change f.app p w ((PowerWordWeight.wordAt D Sc cutoff L ν β).map
      (arrowFromOld D Sc cutoff L ν β hν w g) (wordUnit D Sc cutoff L ν β hν)) = _ at hn
  rw [generator_as_map_unit] at hn
  exact hn

/-- Unit evaluation retains both homogeneous components. -/
def evaluate (f : PowerWordWeight.wordAt D Sc cutoff L ν β ⟶ M) :
    M.obj (wordObject D Sc cutoff L ν β hν) := f.total (wordObject D Sc cutoff L ν β hν) (wordUnit D Sc cutoff L ν β hν)

private theorem evaluate_part (f : PowerWordWeight.wordAt D Sc cutoff L ν β ⟶ M) (p : ZMod 2) :
    f.app p (wordObject D Sc cutoff L ν β hν) (wordUnit D Sc cutoff L ν β hν) ∈
      (M.obj (wordObject D Sc cutoff L ν β hν)).part p := by
  have hp := SVec.apply_mem_part (f.app_mem p _) (wordUnit_even D Sc cutoff L ν β hν)
  rw [zero_add] at hp
  exact hp

theorem evaluate_component (f : PowerWordWeight.wordAt D Sc cutoff L ν β ⟶ M) (p : ZMod 2) :
    (M.obj (wordObject D Sc cutoff L ν β hν)).proj p (evaluate D Sc cutoff L ν β hν M f) =
      f.app p (wordObject D Sc cutoff L ν β hν) (wordUnit D Sc cutoff L ν β hν) := by
  change (M.obj (wordObject D Sc cutoff L ν β hν)).proj p (_ + _) = _
  rw [map_add, SVec.proj_apply_of_mem_part _ (evaluate_part D Sc cutoff L ν β hν M f 0),
    SVec.proj_apply_of_mem_part _ (evaluate_part D Sc cutoff L ν β hν M f 1)]
  rcases parity_eq_zero_or_one p with rfl | rfl <;> simp

/-- Equality on the unit implies equality on every vector of every content
component, including all exterior coefficient classes. -/
theorem hom_ext (f g : PowerWordWeight.wordAt D Sc cutoff L ν β ⟶ M)
    (h : evaluate D Sc cutoff L ν β hν M f = evaluate D Sc cutoff L ν β hν M g) : f = g := by
  apply Superfunctor.hom_ext
  intro p w
  apply LinearMap.ext
  intro x
  obtain ⟨a, rfl⟩ := generator_surjective D Sc cutoff L ν β w x
  rw [app_generator, app_generator]
  rw [← evaluate_component, ← evaluate_component, h]

end OddMath.QuiverHecke.ELVOld.PowerWordContentCyclicity
