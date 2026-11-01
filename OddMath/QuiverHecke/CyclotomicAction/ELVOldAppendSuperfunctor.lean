import OddMath.QuiverHecke.CyclotomicAction.ELVOldSupermodules

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

theorem rightContext_mem_parity (σ : List I) {v w : List I} {p : ZMod 2}
    {a : hom D Sc cutoff v w}
    (ha : a ∈ parity (R := k) (obj D Sc cutoff v) (obj D Sc cutoff w) p) :
    rightContext D Sc cutoff σ v w a ∈
      parity (R := k) (obj D Sc cutoff (v ++ σ)) (obj D Sc cutoff (w ++ σ)) p := by
  let K := Supercategory.homSVec k _ (obj D Sc cutoff v).fst (obj D Sc cutoff w).fst
  let U := Supercategory.homSVec k _ (obj D Sc cutoff v).snd (obj D Sc cutoff w).snd
  let U' := Supercategory.homSVec k _ (obj D Sc cutoff (v ++ σ)).snd
    (obj D Sc cutoff (w ++ σ)).snd
  let g : U ⟶ U' := affineRightContext D Sc σ v w
  have hg : g ∈ SVec.parityHom U U' 0 := by
    apply SVec.mem_parityHom_of_apply_mem
    intro q f hf
    change affineRightContext D Sc σ v w f ∈ U'.part (q + 0)
    simpa only [add_zero] using
      (Supercategory.mem_homSVec_part_iff k).2
        (MonoidalSupercategory.whiskerRight_mem ((pres D Sc).obj (ob D σ))
          ((Supercategory.mem_homSVec_part_iff k).1 hf))
  change a ∈ (SVec.tensorObj K U).part p at ha
  change rightContext D Sc cutoff σ v w a ∈ (SVec.tensorObj K U').part p
  have hp := SVec.apply_mem_part (SVec.whiskerLeft_mem K hg) ha
  rw [SVec.whiskerLeft_even K hg] at hp
  simpa only [add_zero] using hp

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
