import OddMath.QuiverHecke.CyclotomicAction.ELVContentTripleWhiskering

/-! # Affine contexts of the three positioned dots

Brundan--Ellis (1.9), the repeated-outer polynomial. Normalize the literal
contexts obtained from the selected triple-dot comparison to the three
source positions, before any module or coefficient evaluation.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k)

/-- The first dot retains both right contexts as the first position of the whole word. -/
theorem tripleFirstDot_affineContexts (l j i : I) :
    (dotE D Sc [l] 0 ▷ (pres D Sc).obj (ob D [j])) ▷ (pres D Sc).obj (ob D [i]) =
      dotE D Sc [l,j,i] 0 := by
  erw [dotE_whiskerRight D Sc [l] [j] 0 (by simp),
    dotE_whiskerRight D Sc [l,j] [i] 0 (by simp)]
  rfl

/-- The middle dot has the first-letter left context and final-letter right context. -/
theorem tripleMiddleDot_affineContexts (l j i : I) :
    ((pres D Sc).obj (ob D [l]) ◁ dotE D Sc [j] 0) ▷ (pres D Sc).obj (ob D [i]) =
      (pres D Sc).obj (ob D [l]) ◁ dotE D Sc [j,i] 0 := by
  have h := MonoidalSupercategory.associator_naturality (R := k)
    (𝟙 ((pres D Sc).obj (ob D [l]))) (dotE D Sc [j] 0)
    (𝟙 ((pres D Sc).obj (ob D [i])))
  simp only [MonoidalSupercategory.tensorHom_def (R := k),
    MonoidalSupercategory.id_whiskerRight (R := k), MonoidalSupercategory.whiskerLeft_id (R := k),
    Category.id_comp, Category.comp_id, Presentation.associator_eq, eqToIso.hom, eqToHom_refl] at h
  rw [dotE_whiskerRight D Sc [j] [i] 0 (by simp)] at h
  exact h

/-- The last dot sees the two-letter left context as the nested first and middle contexts. -/
theorem tripleLastDot_affineContexts (l j i : I) :
    (pres D Sc).obj (ob D [l,j]) ◁ dotE D Sc [i] 0 =
      (pres D Sc).obj (ob D [l]) ◁ (pres D Sc).obj (ob D [j]) ◁ dotE D Sc [i] 0 := by
  have h := MonoidalSupercategory.associator_naturality (R := k)
    (𝟙 ((pres D Sc).obj (ob D [l]))) (𝟙 ((pres D Sc).obj (ob D [j]))) (dotE D Sc [i] 0)
  simp only [MonoidalSupercategory.tensorHom_def (R := k),
    MonoidalSupercategory.id_whiskerRight (R := k), MonoidalSupercategory.whiskerLeft_id (R := k),
    Category.id_comp, Category.comp_id, Presentation.associator_eq, eqToIso.hom, eqToHom_refl] at h
  exact h

/-- The middle literal context is exactly the indexed polynomial generator. -/
theorem tripleMiddleDot_affineIndex (l j i : I) :
    ((pres D Sc).obj (ob D [l]) ◁ dotE D Sc [j] 0) ▷ (pres D Sc).obj (ob D [i]) =
      dotE D Sc [l,j,i] 1 := by
  erw [tripleMiddleDot_affineContexts D Sc l j i, whiskerLeft_letter_dotE]

/-- The last literal context is exactly the indexed polynomial generator. -/
theorem tripleLastDot_affineIndex (l j i : I) :
    (pres D Sc).obj (ob D [l,j]) ◁ dotE D Sc [i] 0 = dotE D Sc [l,j,i] 2 := by
  erw [tripleLastDot_affineContexts D Sc l j i, whiskerLeft_letter_dotE, whiskerLeft_letter_dotE]

end OddMath.QuiverHecke.ELVOld
