import OddMath.QuiverHecke.SwappedAssembly.Sigma.ReservoirPrincipal

/-! # The actual central probe-to-reservoir bend -/
noncomputable section
namespace OddMath.QuiverHecke.SwappedAssembly
open CategoryTheory StringDiagrams OddMath.SKM BicategoryStruct Supercategory
universe u uB v w

private theorem counit_transport {A B : Type*} [Category A] [Category B]
    (E : A ⥤ B) (F : B ⥤ A) (adj : E ⊣ F)
    {Y : A} {Z₀ Z : B} (q : Y = F.obj Z₀) (r : Z₀ = Z) :
    E.map (eqToHom q) ≫ adj.counit.app Z₀ ≫ eqToHom r =
      E.map (eqToHom q) ≫ E.map (F.map (eqToHom r)) ≫ adj.counit.app Z := by
  subst q r
  simp only [eqToHom_refl]
  rw [E.map_id, F.map_id, E.map_id]
  simp only [Category.id_comp, Category.comp_id]

variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type uB} [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}
omit [∀ a b : B, PiSupercategory k (a ⟶ b)] in
private theorem preE_obj_heq_reservoir
    (T : RouquierFamily (k := k) (B := B) D) (W : X → B) (i : I)
    {a b r r' : X} (h : -b + D.α i = -a) (er : r = r')
    (U : homWeightSector T.obj W a r) (U' : homWeightSector T.obj W a r')
    (hU : HEq U U') :
    HEq ((homContentPreE T W i r h).obj U) ((homContentPreE T W i r' h).obj U') := by
  subst er
  obtain rfl := eq_of_heq hU
  rfl

private theorem postE_obj_heq_weights (T : X → B)
    (W : RouquierFamily (k := k) (B := B) D) (i : I) (β : I →₀ ℕ) (μ : X)
    {m m' n n' : X} (em : m = m') (en : n = n')
    (h : m + D.α i = n) (h' : m' + D.α i = n')
    (U : homWeightSector T W.obj μ m) (U' : homWeightSector T W.obj μ m')
    (hU : HEq U U') :
    HEq ((homContentPostE T W i β μ h).obj U) ((homContentPostE T W i β μ h').obj U') := by
  subst em en
  obtain rfl := eq_of_heq hU
  rfl

namespace ProbeReservoir
variable {P : ProbeReservoir k B D Sc}

/-- The computed probe cap-path chart uses the canonical inverse-defined
left adjunction of the given probe family. -/
def probeCapFactorIso (i : I) (ν : X) {t : Sector I}
    (hw : StepValid (false, i) true (nextSector (true, i) true t))
    (e : nextSector (false, i) true (nextSector (true, i) true t) = t) (Z : P.H t) :
    (P.pathFunctor (SPath.two (c₁ := ⟨up i, SKM.wt D ν [dn i]⟩)
      (c₂ := ⟨dn i, ν⟩) true true (by trivial) hw e)).obj Z ≅
    (homContentPreE P.T P.W.obj i (P.muM t) (P.muP_preE i t)).obj
      ((homContentPreF P.T P.W.obj i (P.muM t) (P.muP_preE i t)).obj Z) :=
  twoPathEndpointIso true true (by trivial) hw e Z ≪≫
    (homContentPreE P.T P.W.obj i (P.muM t) (P.muP_preE i t)).mapIso
      (eqToIso (eq_of_heq (P.preF_obj_heq i e.symm (P.muP_preE i t)
        (P.muP_preF i hw) (e.symm ▸ Z)).symm)) ≪≫
    (homContentPreE P.T P.W.obj i (P.muM t) (P.muP_preE i t)).mapIso
      ((homContentPreF P.T P.W.obj i (P.muM t) (P.muP_preE i t)).mapIso
        (twoPathReturnIso true true e Z))

private theorem capImage_probe_endpoint (i : I) (ν : X) {t : Sector I}
    (hw : StepValid (false, i) true (nextSector (true, i) true t))
    (e : nextSector (false, i) true (nextSector (true, i) true t) = t) (Z : P.H t) :
    P.capImage i ν (SPath.two true true (by trivial) hw e) (.nil t) Z =
      (twoPathEndpointIso (c₁ := ⟨up i, SKM.wt D ν [dn i]⟩) (c₂ := ⟨dn i, ν⟩)
        true true (by trivial) hw e Z).hom ≫
      P.preCap i t (by trivial) hw e.symm (e.symm ▸ Z) ≫
      (twoPathReturnIso true true e Z).hom := by
  unfold capImage
  rw [P.twoZero_two (Z' := e.symm ▸ Z) (hZ := eqRec_heq _ _)]
  rfl

/-- The actual probe cap is the canonical shifted precomposition
counit in its computed endpoint chart. -/
theorem capImage_probe_factor (i : I) (ν : X) {t : Sector I}
    (hw : StepValid (false, i) true (nextSector (true, i) true t))
    (e : nextSector (false, i) true (nextSector (true, i) true t) = t) (Z : P.H t) :
    P.capImage i ν (SPath.two true true (by trivial) hw e) (.nil t) Z =
      (probeCapFactorIso i ν hw e Z).hom ≫
        (homContentPreAdjunction P.T P.W.obj P.T.leftAdjoints i (P.muM t)
          (P.muP_preE i t)).counit.app Z := by
  rw [capImage_probe_endpoint]
  let q := eq_of_heq (P.preF_obj_heq i e.symm (P.muP_preE i t)
    (P.muP_preF i hw) (e.symm ▸ Z)).symm
  let r : (e.symm ▸ (e.symm ▸ Z) : P.H t) = Z :=
    eq_of_heq ((eqRec_heq _ _).trans (eqRec_heq _ _))
  have h := counit_transport
    (homContentPreE P.T P.W.obj i (P.muM t) (P.muP_preE i t))
    (homContentPreF P.T P.W.obj i (P.muM t) (P.muP_preE i t))
    (homContentPreAdjunction P.T P.W.obj P.T.leftAdjoints i (P.muM t) (P.muP_preE i t)) q r
  simpa only [probeCapFactorIso, Iso.trans_hom, Functor.mapIso_hom, eqToIso.hom,
    twoPathReturnIso, capEntry, preCap, Category.assoc,
    step, nextSector, muM, q, r, pathFunctor_nil, Functor.id_obj] using congrArg (fun f =>
      (twoPathEndpointIso (c₁ := ⟨up i, SKM.wt D ν [dn i]⟩) (c₂ := ⟨dn i, ν⟩)
        true true (by trivial) hw e Z).hom ≫ f) h

/-- The RP coefficient object after a reservoir cup, compared to its
native post/pre composite. The full formal right sector is transported. -/
def probeToReservoirCoefficientIso (i : I) (t : Sector I)
    (U : P.H (nextSector (true, i) true t)) :
    P.rpObj i i (nextSector (false, i) false t) (by simp [StepValid, nextSector])
      ((congrArg (nextSector (true, i) true) (SPath.next_dnUp_false_false (i := i) t)).symm ▸ U) ≅
    (homContentPostE P.T.obj P.W i t.1 (P.muP t) (P.muM_postF i t)).obj
      ((homContentPreE P.T P.W.obj i (P.muM t) (P.muP_preE i t)).obj U) := by
  let tR := nextSector (true, i) false (nextSector (false, i) false t)
  let er := congrArg (nextSector (true, i) true) (SPath.next_dnUp_false_false (i := i) t)
  have en : P.muM tR = P.muM t := congrArg P.muM (SPath.next_dnUp_false_false (i := i) t)
  have hpre := preE_obj_heq_reservoir P.T P.W.obj i (P.muP_preE i t) en
    (er.symm ▸ U : P.H (nextSector (true, i) true tR)) U (eqRec_heq _ _)
  have hpost := postE_obj_heq_weights P.T.obj P.W i t.1 (P.muP t) en rfl
    (P.muM_postE i (by simp [StepValid, nextSector] :
      StepValid (true, i) false (nextSector (false, i) false t))) (P.muM_postF i t)
    _ _ hpre
  apply eqToIso
  apply eq_of_heq
  simpa only [rpObj, step, tR, er, nextSector, muP] using hpost

/-- The native coefficient used by the XP-to-YR bend. This transports
actual coefficient data; it imposes no inverse or bend identity. -/
def probeToReservoirCoefficient (c : P.CrossCoeff) (i : I) (t : Sector I)
    (U : P.H (nextSector (true, i) true t)) :
    End ((homContentPostE P.T.obj P.W i t.1 (P.muP t) (P.muM_postF i t)).obj
      ((homContentPreE P.T P.W.obj i (P.muM t) (P.muP_preE i t)).obj U)) :=
  (probeToReservoirCoefficientIso i t U).inv ≫
    c.a i (nextSector (false, i) false t) (by simp [StepValid, nextSector])
      ((congrArg (nextSector (true, i) true) (SPath.next_dnUp_false_false (i := i) t)).symm ▸ U) ≫
    (probeToReservoirCoefficientIso i t U).hom

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
