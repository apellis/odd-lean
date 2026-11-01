import OddMath.QuiverHecke.CyclotomicAction.ELVProbeOrdinaryCategory

/-! # The literal commuting append square for scalar probe specialization
Ordinary right append acts on the existing cycHom quotients. The full scalar
functors commute with canonical old append exactly, providing the concrete
square for the induction-composition comparison.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
namespace OddMath.QuiverHecke
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (ν : List I)
local notation "cut" => probeCutoff D m
local notation "a" => probePolynomial (k := k) (probeDotExponent D) m
local notation "C" => OrdinaryContentCategory D Sc a ν

/-- Right append on the literal ordinary quotient content category. -/
def probeOrdinaryAppend (i : I) : C ⥤ OrdinaryContentCategory D Sc a (i :: ν) where
  obj v := ⟨v.word ++ [i], (v.wordPerm.append (List.Perm.refl [i])).trans
    (List.perm_append_comm : (ν ++ [i]).Perm ([i] ++ ν))⟩
  map {v w} := probeCycHomRightContext D m Sc [i] v.word w.word
  map_id v := by
    change (cycHom D Sc a (v.word ++ [i]) (v.word ++ [i])).mkQ
      ((𝟙 ((pres D Sc).obj (ob D v.word))) ▷ ((pres D Sc).obj (ob D [i]))) = _
    exact congrArg (cycHom D Sc a (v.word ++ [i]) (v.word ++ [i])).mkQ
      (MonoidalSupercategory.id_whiskerRight (R := k) _ _)
  map_comp {v t w} f g := by
    obtain ⟨f,rfl⟩ := (cycHom D Sc a v.word t.word).mkQ_surjective f
    obtain ⟨g,rfl⟩ := (cycHom D Sc a t.word w.word).mkQ_surjective g
    change (cycHom D Sc a (v.word ++ [i]) (w.word ++ [i])).mkQ
      ((f ≫ g) ▷ ((pres D Sc).obj (ob D [i]))) =
      (cycHom D Sc a (v.word ++ [i]) (w.word ++ [i])).mkQ
        ((f ▷ ((pres D Sc).obj (ob D [i]))) ≫ (g ▷ ((pres D Sc).obj (ob D [i]))))
    exact congrArg (cycHom D Sc a (v.word ++ [i]) (w.word ++ [i])).mkQ
      (MonoidalSupercategory.comp_whiskerRight (R := k) f g _)

instance (i : I) : (probeOrdinaryAppend D Sc m ν i).Additive where
  map_add {v w} f g := (probeCycHomRightContext D m Sc [i] v.word w.word).map_add f g
instance (i : I) : (probeOrdinaryAppend D Sc m ν i).Linear k where
  map_smul {v w} f r := (probeCycHomRightContext D m Sc [i] v.word w.word).map_smul r f

/-- The square uses the actual old append, actual full scalar functors and
actual ordinary quotient append, with no assumed natural comparison. -/
theorem probeOldOrdinaryFunctor_append (i : I) :
    ELVOld.oldContentAppend D Sc cut ν i ⋙ probeOldOrdinaryFunctor D Sc m (i :: ν) =
      probeOldOrdinaryFunctor D Sc m ν ⋙ probeOrdinaryAppend D Sc m ν i := by
  apply CategoryTheory.Functor.ext
  case h_obj =>
    intro v
    rfl
  case h_map =>
    intro v w f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    exact elvProbeOldHom_rightContext D m Sc [i] v.obj.word w.obj.word f

end OddMath.QuiverHecke

