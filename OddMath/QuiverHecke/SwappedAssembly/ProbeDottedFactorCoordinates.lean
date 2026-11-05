import OddMath.QuiverHecke.SwappedAssembly.Sigma.ProbeFactorCoordinates
import OddMath.SKM.RouquierHomPreCoordinates

/-! # Probe dotted cap rows and cup columns

The actual augmented-matrix entries, before imposing any mixed-block
inverse condition. All dot exponents, including zero, are retained.
This supplies the probe rows of the Brundan–Ellis inversion relation
(Definition 1.5), in the normalized coordinates of
`SwappedHomInversion.md`, §2.
-/
noncomputable section
namespace OddMath.QuiverHecke.SwappedAssembly
open CategoryTheory StringDiagrams OddMath.SKM BicategoryStruct Supercategory
universe u uB v w
private theorem compPow_eq_pow {C : Type*} [Category C] {A : C} (f : End A) (n : ℕ) :
    ProbeReservoir.compPow f n = f ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [ProbeReservoir.compPow, pow_succ, ih]; rfl

private theorem dottedCounit_transport {A B : Type*} [Category A] [Category B]
    (E : A ⥤ B) (F : B ⥤ A) (adj : E ⊣ F) (x : ∀ Y : A, End (E.obj Y))
    (n : ℕ) {Y : A} {Z₀ Z : B} (q : Y = F.obj Z₀) (r : Z₀ = Z) :
    ProbeReservoir.compPow (x Y) n ≫ E.map (eqToHom q) ≫ adj.counit.app Z₀ ≫ eqToHom r =
      (E.map (eqToHom q) ≫ E.map (F.map (eqToHom r))) ≫
        (ProbeReservoir.compPow (x (F.obj Z)) n ≫ adj.counit.app Z) := by
  subst q r
  simp only [eqToHom_refl]
  rw [E.map_id, F.map_id, E.map_id]
  simp only [Category.id_comp, Category.comp_id]

private theorem map_end_pow {C C' : Type*} [Category C] [Category C']
    (F : C ⥤ C') {Z : C} (d : End Z) (n : ℕ) :
    (show End (F.obj Z) from F.map d) ^ n = F.map (d ^ n) := by
  induction n with
  | zero => exact (F.map_id Z).symm
  | succ n ih => rw [pow_succ', pow_succ', End.mul_def, End.mul_def, ih, F.map_comp]

private theorem dottedUnit_transport {L : Type*} {C : L → Type*}
    [∀ l, Category (C l)] {B : Type*} [Category B] {Pr : L → Prop}
    (E : ∀ l, Pr l → C l ⥤ B) (F : ∀ l, Pr l → B ⥤ C l)
    (adj : ∀ l h, E l h ⊣ F l h) (x : ∀ l h (Y : C l), End ((E l h).obj Y))
    {l l' : L} (el : l = l') (h : Pr l) (h' : Pr l')
    {Z₀ Z : C l} {Z' : C l'} (hZ : HEq Z₀ Z')
    (q : (E l h).obj Z₀ = (E l' h').obj Z') (r : Z₀ = Z) (n : ℕ) :
    eqToHom r.symm ≫ (adj l h).unit.app Z₀ ≫ (F l h).map (eqToHom q) ≫
        ProbeReservoir.compPow ((F l h).map (x l' h' Z')) n =
      ((adj l h).unit.app Z ≫ ProbeReservoir.compPow ((F l h).map (x l h Z)) n) ≫
        (F l h).map ((E l h).map (eqToHom r.symm)) ≫ (F l h).map (eqToHom q) := by
  subst el
  have hh : h' = h := Subsingleton.elim _ _
  subst h'
  obtain rfl := eq_of_heq hZ
  subst r
  simp only [eqToHom_refl]
  rw [(E l h).map_id, (F l h).map_id]
  let f : Z₀ ⟶ (F l h).obj ((E l h).obj Z₀) := (adj l h).unit.app Z₀
  let g : End ((F l h).obj ((E l h).obj Z₀)) :=
    ProbeReservoir.compPow ((F l h).map (x l h Z₀)) n
  change (𝟙 Z₀) ≫ f ≫ (𝟙 _) ≫ g = (f ≫ g) ≫ (𝟙 _) ≫ (𝟙 _)
  simp only [Category.id_comp, Category.comp_id]

variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type uB} [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}
namespace ProbeReservoir
variable {P : ProbeReservoir k B D Sc}

/-- The dot on the first strand, including the identity comparison for
the empty outer path. -/
private theorem compLayer_dot_first (c : P.CrossCoeff) (i : I) (ν : X)
    {s t : Sector I} (hv : StepValid (true, i) true s)
    (pv : SPath (wd D ν [dn i]) (nextSector (true, i) true s) t) (Z : P.H t) :
    compLayer (P.upwardGens c) (SKM.lay D ν [] (SKM.Shape.dot i) [dn i])
      (.cons _ true s hv pv) (.cons _ true s hv pv) Z =
      homReservoirDot P.T P.W.obj i (P.muM s) (P.muP_preE i s) ((P.pathFunctor pv).obj Z) := by
  rw [compLayer_eq_of_path (P.upwardGens c) (SKM.lay D ν [] (SKM.Shape.dot i) [dn i]) (.nil s)
    (.cons _ true s hv (.nil _)) (.cons _ true s hv (.nil _)) pv
    (.cons _ true s hv pv) (.cons _ true s hv pv) rfl rfl Z]
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  change P.dotImage i (SKM.wt D ν [dn i])
    (.cons _ true s hv (.nil _)) (.cons _ true s hv (.nil _))
      ((P.pathFunctor pv).obj Z) = _
  exact P.dotImage_probe i _ s hv hv _

/-- The diagonal cap-row dot, in the selected endpoint chart, is the
prescribed shifted precomposition dot. -/
theorem capRow_dot_probe (c : P.CrossCoeff) (i : I) (ν : X)
    {t t' : Sector I} (hv : StepValid (true, i) true t)
    (hw : StepValid (false, i) true (nextSector (true, i) true t))
    (e : nextSector (false, i) true (nextSector (true, i) true t) = t') (Z : P.H t') :
    let p : SPath (wd D ν [up i, dn i]) t t' := SPath.two true true hv hw e
    compLayer (P.upwardGens c) (SKM.lay D ν [] (SKM.Shape.dot i) [dn i]) p p Z =
      (twoPathEndpointIso (c₁ := ⟨up i, SKM.wt D ν [dn i]⟩) (c₂ := ⟨dn i, ν⟩) true true hv hw e Z).hom ≫
        homReservoirDot P.T P.W.obj i (P.muM t) (P.muP_preE i t)
          ((P.step (false, i) true _ hw).obj (e.symm ▸ Z)) ≫
        (twoPathEndpointIso (c₁ := ⟨up i, SKM.wt D ν [dn i]⟩) (c₂ := ⟨dn i, ν⟩) true true hv hw e Z).inv := by
  subst e
  dsimp only [twoPathEndpointIso, SPath.two, pathFunctor_cons, pathFunctor_nil,
    Functor.comp_obj, Functor.id_obj]
  simp only [eqToIso_refl, Iso.refl_hom, Iso.refl_inv, Category.id_comp]
  erw [Category.comp_id]
  convert! compLayer_dot_first c i ν hv (.cons _ true _ hw (.nil _)) Z using 1

/-- The actual probe cap entry in its fixed endpoint charts, with
its given shifted adjunction retained. -/
private theorem capImage_probe_endpoint (i : I) (ν : X) {t : Sector I}
    (hv : StepValid (true, i) true t)
    (hw : StepValid (false, i) true (nextSector (true, i) true t))
    (e : nextSector (false, i) true (nextSector (true, i) true t) = t) (Z : P.H t) :
    P.capImage i ν (SPath.two true true hv hw e) (.nil t) Z =
      (twoPathEndpointIso (c₁ := ⟨up i, SKM.wt D ν [dn i]⟩) (c₂ := ⟨dn i, ν⟩) true true hv hw e Z).hom ≫
        P.preCap i t hv hw e.symm (e.symm ▸ Z) ≫
        (twoPathReturnIso true true e Z).hom := by
  unfold capImage
  rw [P.twoZero_two (Z' := e.symm ▸ Z) (hZ := eqRec_heq _ _)]
  rfl

private theorem compPow_iso {C : Type*} [Category C] {A B : C} (e : A ≅ B)
    (f : End B) (n : ℕ) :
    compPow (e.hom ≫ f ≫ e.inv) n = e.hom ≫ compPow f n ≫ e.inv := by
  induction n with
  | zero => simp [compPow]
  | succ n ih => simp [compPow, ih, Category.assoc]

/-- Every actual probe cap row is the inherited probe-dot power and
specified factor counit, in the selected equality charts. -/
theorem epsEntry_probe (c : P.CrossCoeff) (i : I) (n : ℕ) (ν : X) {t : Sector I}
    (hv : StepValid (true, i) true t)
    (hw : StepValid (false, i) true (nextSector (true, i) true t))
    (e : nextSector (false, i) true (nextSector (true, i) true t) = t) (Z : P.H t) :
    P.epsEntry c i n ν (SPath.two true true hv hw e) (.nil t) Z =
      (twoPathEndpointIso (c₁ := ⟨up i, SKM.wt D ν [dn i]⟩) (c₂ := ⟨dn i, ν⟩)
        true true hv hw e Z).hom ≫
      compPow (homReservoirDot P.T P.W.obj i (P.muM t) (P.muP_preE i t)
        ((P.step (false, i) true _ hw).obj (e.symm ▸ Z))) n ≫
      P.preCap i t hv hw e.symm (e.symm ▸ Z) ≫
      (twoPathReturnIso true true e Z).hom := by
  rw [epsEntry_eq_dot_cap, capRow_dot_probe, capImage_probe_endpoint, compPow_iso]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- The diagonal cup-column dot, in the fixed endpoint chart, is the
lowering functor applied to the prescribed shifted dot. -/
theorem cupColumn_dot_probe (c : P.CrossCoeff) (i : I) (ν : X)
    {t t' : Sector I} (hv : StepValid (false, i) true t)
    (hw : StepValid (true, i) true (nextSector (false, i) true t))
    (e : nextSector (true, i) true (nextSector (false, i) true t) = t') (Z : P.H t') :
    let p : SPath (wd D ν [dn i, up i]) t t' := SPath.two true true hv hw e
    compLayer (P.upwardGens c) (SKM.lay D ν [dn i] (SKM.Shape.dot i) []) p p Z =
      (twoPathEndpointIso (c₁ := ⟨dn i, SKM.wt D ν [up i]⟩) (c₂ := ⟨up i, ν⟩)
        true true hv hw e Z).hom ≫
        (P.step (false, i) true t hv).map
          (homReservoirDot P.T P.W.obj i (P.muM (nextSector (false, i) true t))
            (P.muP_preE i (nextSector (false, i) true t))
            (e.symm ▸ Z : P.H (nextSector (true, i) true (nextSector (false, i) true t)))) ≫
        (twoPathEndpointIso (c₁ := ⟨dn i, SKM.wt D ν [up i]⟩) (c₂ := ⟨up i, ν⟩)
          true true hv hw e Z).inv := by
  subst e
  dsimp only [twoPathEndpointIso, SPath.two, pathFunctor_cons, pathFunctor_nil,
    Functor.comp_obj, Functor.id_obj]
  simp only [eqToIso_refl, Iso.refl_hom, Iso.refl_inv, Category.id_comp]
  erw [Category.comp_id]
  erw [compLayer_eq_of_path (P.upwardGens c) (SKM.lay D ν [dn i] (SKM.Shape.dot i) [])
    (.cons _ true t hv (.nil _)) (.cons _ true _ hw (.nil _))
    (.cons _ true _ hw (.nil _)) (.nil _)
    (.cons _ true t hv (.cons _ true _ hw (.nil _)))
    (.cons _ true t hv (.cons _ true _ hw (.nil _))) rfl rfl Z]
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  change (P.step (false, i) true t hv).map
    (P.dotImage i ν (.cons _ true _ hw (.nil _)) (.cons _ true _ hw (.nil _)) Z) = _
  rw [P.dotImage_probe]
  rfl

/-- The actual probe cup entry in its fixed endpoint charts. -/
theorem cupImage_probe_endpoint (i : I) (ν : X) {t : Sector I}
    (hv : StepValid (false, i) true t)
    (hw : StepValid (true, i) true (nextSector (false, i) true t))
    (e : nextSector (true, i) true (nextSector (false, i) true t) = t) (Z : P.H t) :
    P.cupImage i ν (.nil t) (SPath.two true true hv hw e) Z =
      (twoPathReturnIso true true e Z).inv ≫
        P.preCup i t hv hw e.symm (e.symm ▸ Z) ≫
        (twoPathEndpointIso (c₁ := ⟨dn i, SKM.wt D ν [up i]⟩) (c₂ := ⟨up i, ν⟩)
          true true hv hw e Z).inv := by
  unfold cupImage
  rw [P.zeroTwo_two (Z' := e.symm ▸ Z) (hZ := eqRec_heq _ _)]
  rfl

/-- Every actual probe cup column is the specified shifted unit
followed by the lowering image of the shifted dot power. -/
theorem etaEntry_probe (c : P.CrossCoeff) (i : I) (n : ℕ) (ν : X) {t : Sector I}
    (hv : StepValid (false, i) true t)
    (hw : StepValid (true, i) true (nextSector (false, i) true t))
    (e : nextSector (true, i) true (nextSector (false, i) true t) = t) (Z : P.H t) :
    P.etaEntry c i n ν (.nil t) (SPath.two true true hv hw e) Z =
      (twoPathReturnIso true true e Z).inv ≫
      P.preCup i t hv hw e.symm (e.symm ▸ Z) ≫
      compPow ((P.step (false, i) true t hv).map
        (homReservoirDot P.T P.W.obj i (P.muM (nextSector (false, i) true t))
          (P.muP_preE i (nextSector (false, i) true t))
            (e.symm ▸ Z : P.H (nextSector (true, i) true (nextSector (false, i) true t))))) n ≫
      (twoPathEndpointIso (c₁ := ⟨dn i, SKM.wt D ν [up i]⟩) (c₂ := ⟨up i, ν⟩)
        true true hv hw e Z).inv := by
  rw [etaEntry_eq_cup_dot, cupColumn_dot_probe, cupImage_probe_endpoint, compPow_iso]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- Every probe cap row is the inherited dot power followed by the
canonical inverse-defined precomposition counit. -/
theorem epsEntry_probe_factor (c : P.CrossCoeff) (i : I) (n : ℕ) (ν : X) {t : Sector I}
    (hw : StepValid (false, i) true (nextSector (true, i) true t))
    (e : nextSector (false, i) true (nextSector (true, i) true t) = t) (Z : P.H t) :
    P.epsEntry c i n ν (SPath.two true true (by trivial) hw e) (.nil t) Z =
      (probeCapFactorIso i ν hw e Z).hom ≫
        homReservoirCap P.T P.W.obj i (P.muM t) (P.muP_preE i t) n Z := by
  rw [epsEntry_probe]
  let q : (P.step (false, i) true (nextSector (true, i) true t) hw).obj (e.symm ▸ Z) =
      (homContentPreF P.T P.W.obj i (P.muM t) (P.muP_preE i t)).obj
        (e.symm ▸ (e.symm ▸ Z) : P.H t) :=
    eq_of_heq (P.preF_obj_heq i e.symm (P.muP_preE i t)
      (P.muP_preF i hw) (e.symm ▸ Z)).symm
  let r : (e.symm ▸ (e.symm ▸ Z) : P.H t) = Z :=
    eq_of_heq ((eqRec_heq _ _).trans (eqRec_heq _ _))
  have h := dottedCounit_transport
    (homContentPreE P.T P.W.obj i (P.muM t) (P.muP_preE i t))
    (homContentPreF P.T P.W.obj i (P.muM t) (P.muP_preE i t))
    (homContentPreAdjunction P.T P.W.obj P.T.leftAdjoints i (P.muM t) (P.muP_preE i t))
    (homReservoirDot P.T P.W.obj i (P.muM t) (P.muP_preE i t)) n
    (Y := (P.step (false, i) true (nextSector (true, i) true t) hw).obj (e.symm ▸ Z))
    (Z₀ := (e.symm ▸ (e.symm ▸ Z) : P.H t)) (Z := Z) q r

  have hh := congrArg (fun f =>
      (twoPathEndpointIso (c₁ := ⟨up i, SKM.wt D ν [dn i]⟩) (c₂ := ⟨dn i, ν⟩)
        true true (by trivial) hw e Z).hom ≫ f) h
  rw [homReservoirCap, ← compPow_eq_pow]
  simpa only [probeCapFactorIso, Iso.trans_hom, Functor.mapIso_hom,
    eqToIso.hom, twoPathReturnIso, preCap, Category.assoc, step, nextSector, muM,
    pathFunctor_nil, Functor.id_obj] using hh

/-- Every probe cup column is the canonical precomposition unit followed
by the lowering image of the inherited dot power, including exponent zero. -/
theorem etaEntry_probe_factor (c : P.CrossCoeff) (i : I) (n : ℕ) (ν : X) {t : Sector I}
    (hv : StepValid (false, i) true t)
    (hw : StepValid (true, i) true (nextSector (false, i) true t))
    (e : nextSector (true, i) true (nextSector (false, i) true t) = t) (Z : P.H t) :
    P.etaEntry c i n ν (.nil t) (SPath.two true true hv hw e) Z =
      homReservoirCup P.T P.W.obj i (P.muM t) (P.muP_preF i hv) n Z ≫
        (probeCupFactorIso i ν hv hw e Z).inv := by
  rw [etaEntry_probe]
  let q := eq_of_heq (P.preE_obj_heq i e.symm (P.muP_preF i hv)
    (P.muP_preE i (nextSector (false, i) true t)) (e.symm ▸ Z))
  let r : (e.symm ▸ (e.symm ▸ Z) : P.H t) = Z :=
    eq_of_heq ((eqRec_heq _ _).trans (eqRec_heq _ _))
  have h := dottedUnit_transport
    (C := fun a => homWeightSector P.T.obj P.W.obj a (P.muM t))
    (Pr := fun a => -P.muP (nextSector (false, i) true t) + D.α i = -a)
    (fun a h => homContentPreE P.T P.W.obj i (P.muM t) h)
    (fun a h => homContentPreF P.T P.W.obj i (P.muM t) h)
    (fun a h => homContentPreAdjunction P.T P.W.obj P.T.leftAdjoints i (P.muM t) h)
    (fun a h => homReservoirDot P.T P.W.obj i (P.muM t) h)
    (congrArg P.muP e.symm) (P.muP_preF i hv) (P.muP_preE i (nextSector (false, i) true t))
    (by exact eqRec_heq _ _) q r n
  simpa only [probeCupFactorIso, Iso.trans_inv, Functor.mapIso_inv,
    eqToIso.inv, eqToIso.hom, twoPathReturnIso, preCup, preAdjAt, homReservoirCup,
    compPow_eq_pow, map_end_pow, Category.assoc, step, nextSector, muM, q, r,
    pathFunctor_nil, Functor.id_obj] using congrArg (fun f => f ≫
      (twoPathEndpointIso (c₁ := ⟨dn i, SKM.wt D ν [up i]⟩) (c₂ := ⟨up i, ν⟩)
        true true hv hw e Z).inv) h

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
