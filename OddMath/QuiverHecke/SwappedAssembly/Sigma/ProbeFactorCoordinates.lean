import OddMath.QuiverHecke.SwappedAssembly.Sigma.ProbeToReservoirBend

/-! # Probe cup coordinates for the central matrix -/
noncomputable section
namespace OddMath.QuiverHecke.SwappedAssembly
open CategoryTheory StringDiagrams OddMath.SKM BicategoryStruct Supercategory
universe u uB v w
variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type uB} [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}
namespace ProbeReservoir
variable {P : ProbeReservoir k B D Sc}

/-- The probe cup path in its canonical precomposition adjunction chart. -/
def probeCupFactorIso (i : I) (ν : X) {t : Sector I}
    (hv : StepValid (false, i) true t)
    (hw : StepValid (true, i) true (nextSector (false, i) true t))
    (e : nextSector (true, i) true (nextSector (false, i) true t) = t) (Z : P.H t) :
    (P.pathFunctor (SPath.two (c₁ := ⟨dn i, SKM.wt D ν [up i]⟩)
      (c₂ := ⟨up i, ν⟩) true true hv hw e)).obj Z ≅
    (homContentPreF P.T P.W.obj i (P.muM t) (P.muP_preF i hv)).obj
      ((homContentPreE P.T P.W.obj i (P.muM t) (P.muP_preF i hv)).obj Z) :=
  twoPathEndpointIso true true hv hw e Z ≪≫
    (homContentPreF P.T P.W.obj i (P.muM t) (P.muP_preF i hv)).mapIso
      (eqToIso (eq_of_heq (P.preE_obj_heq i e.symm (P.muP_preF i hv)
        (P.muP_preE i (nextSector (false, i) true t)) (e.symm ▸ Z))).symm) ≪≫
    (homContentPreF P.T P.W.obj i (P.muM t) (P.muP_preF i hv)).mapIso
      ((homContentPreE P.T P.W.obj i (P.muM t) (P.muP_preF i hv)).mapIso
        (twoPathReturnIso true true e Z))

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
