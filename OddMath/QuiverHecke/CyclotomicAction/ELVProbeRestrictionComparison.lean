import OddMath.QuiverHecke.CyclotomicAction.ELVProbeAppendTensors

/-! # Scalar descent and restriction along append

The ordinary-probe comparison in STATUS critical-chain item 3 must retain the
chosen induction–restriction adjunction of DeformedActionAssembly §5. Scalar
coefficient evaluation is preserved by restriction, and the descended old
restriction equals literal ordinary restriction on the same vectors.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory

namespace OddMath.QuiverHecke
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (ν : List I) (i : I)
local notation "cut" => probeCutoff D m
local notation "a" => probePolynomial (k := k) (probeDotExponent D) m
local notation "J" => ELVOld.oldContentAppend D Sc cut ν i
local notation "T" => probeOrdinaryAppend D Sc m ν i
local notation "Q" => probeOldOrdinaryFunctor D Sc m ν
local notation "U" => probeOldOrdinaryFunctor D Sc m (i :: ν)

/-- Restriction preserves the full scalar coefficient evaluation condition,
including the odd coefficient kernel. -/
theorem probeOldRestriction_evaluatesCoefficients
    (N : Superfunctor k (ELVOld.OldContentCategory D Sc cut (i :: ν)) (SVec k))
    (hN : ProbeEvaluatesCoefficients D m Sc (i :: ν) N) :
    ProbeEvaluatesCoefficients D m Sc ν
      ((ELVOld.BalancedInduction.restriction J).obj N) := by
  intro v c
  change N.toFunctor.map ((J).map (probeOldCoefficient D m Sc ν v c)) = _
  rw [probeOldCoefficient_append]
  exact hN ((J).obj v) c

/-- Scalar descent commutes with the specified old and ordinary append
restrictions, as an equality of supermodules on the original vector values. -/
theorem probeOrdinaryRestrictionModule_eq
    (N : Superfunctor k (ELVOld.OldContentCategory D Sc cut (i :: ν)) (SVec k))
    (hN : ProbeEvaluatesCoefficients D m Sc (i :: ν) N) :
    probeOrdinaryModuleSuperfunctor D Sc m ν
      ((ELVOld.BalancedInduction.restriction J).obj N)
      (probeOldRestriction_evaluatesCoefficients D Sc m ν i N hN) =
        (ELVOld.BalancedInduction.restriction T).obj
          (probeOrdinaryModuleSuperfunctor D Sc m (i :: ν) N hN) := by
  let R := (ELVOld.BalancedInduction.restriction J).obj N
  let hR := probeOldRestriction_evaluatesCoefficients D Sc m ν i N hN
  apply Superfunctor.ext
  apply CategoryTheory.Functor.ext
  case h_obj =>
    intro v
    rfl
  case h_map =>
    intro v w f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    let sv := probeOrdinaryOldObject D Sc m ν v
    let sw := probeOrdinaryOldObject D Sc m ν w
    obtain ⟨g, hg⟩ := elvProbeOldHom_surjective D m Sc v.word w.word f
    let g₀ : sv ⟶ sw := g
    have hq : (Q).map (X := sv) (Y := sw) g₀ = f := hg
    rw [← hq]
    have hs : (U).map (X := (J).obj sv) (Y := (J).obj sw)
        ((J).map (X := sv) (Y := sw) g₀) =
        (T).map (X := (Q).obj sv) (Y := (Q).obj sw)
          ((Q).map (X := sv) (Y := sw) g₀) :=
      elvProbeOldHom_rightContext D m Sc [i] sv.obj.word sw.obj.word g₀
    change probeOrdinaryModuleHom D m Sc ν R hR sv sw ((Q).map g₀) =
      probeOrdinaryModuleHom D m Sc (i :: ν) N hN ((J).obj sv) ((J).obj sw)
        ((T).map ((Q).map g₀))
    calc
      _ = R.toFunctor.map g₀ :=
        probeOrdinaryModuleHom_old D m Sc ν R hR sv sw g₀
      _ = N.toFunctor.map ((J).map g₀) := rfl
      _ = probeOrdinaryModuleHom D m Sc (i :: ν) N hN ((J).obj sv) ((J).obj sw)
          ((U).map ((J).map g₀)) :=
        (probeOrdinaryModuleHom_old D m Sc (i :: ν) N hN
          ((J).obj sv) ((J).obj sw) ((J).map g₀)).symm
      _ = _ := congrArg
        (probeOrdinaryModuleHom D m Sc (i :: ν) N hN ((J).obj sv) ((J).obj sw)) hs

end OddMath.QuiverHecke
