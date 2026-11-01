import OddMath.QuiverHecke.CyclotomicAction.ELVOldSupermodules
import OddMath.QuiverHecke.CyclotomicAction.ELVTruncatedAppend

/-! # The existing old append functor preserves the full super grading

Right extension is the tensor of the identity on full ELV coefficients with
even affine right-whiskering. Its parity preservation passes to the actual
old cyclotomic quotient, including exterior coefficients. This equips the
independently defined append functor for actual supermodule induction.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

namespace CyclotomicCrossingTensor

instance append_additive (i : I) : (append D Sc cutoff i).Additive where
  map_add {v w} f g :=
    ((ideal D Sc cutoff v.word w.word).mapQ
      (ideal D Sc cutoff (v.word ++ [i]) (w.word ++ [i]))
      (rightContext D Sc cutoff [i] v.word w.word)
      (fun _ hr => ideal_rightContext D Sc cutoff [i] hr)).map_add f g

instance append_linear (i : I) : (append D Sc cutoff i).Linear k where
  map_smul {v w} f r :=
    ((ideal D Sc cutoff v.word w.word).mapQ
      (ideal D Sc cutoff (v.word ++ [i]) (w.word ++ [i]))
      (rightContext D Sc cutoff [i] v.word w.word)
      (fun _ hr => ideal_rightContext D Sc cutoff [i] hr)).map_smul r f

instance append_super (i : I) : IsSuperfunctor k (append D Sc cutoff i) where
  map_mem := by
    rintro v w p f ⟨a, ha, rfl⟩
    exact Submodule.mem_map_of_mem (rightContext_mem_parity D Sc cutoff [i] ha)

end CyclotomicCrossingTensor
end OddMath.QuiverHecke.ELVOld
