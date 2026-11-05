import OddMath.QuiverHecke.SwappedAssembly.ReservoirDottedAdjunctionRows

/-! # The actual reservoir rows in native dotted adjunction coordinates -/
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

/-- The actual two-reservoir cap path compared to the single prescribed
shifted postcomposition adjunction. The inner and return charts are
computed equality transports. -/
def reservoirCapFactorIso (i : I) (ν : X) {t : Sector I}
    (hv : StepValid (true, i) false t)
    (hw : StepValid (false, i) false (nextSector (true, i) false t))
    (e : nextSector (false, i) false (nextSector (true, i) false t) = t) (Z : P.H t) :
    (P.pathFunctor (SPath.two (c₁ := ⟨up i, SKM.wt D ν [dn i]⟩)
      (c₂ := ⟨dn i, ν⟩) false false hv hw e)).obj Z ≅
    (homContentPostE P.T.obj P.W i t.1 (P.muP t) (P.muM_postE i hv)).obj
      ((homContentPostF P.T.obj P.W i t.1 (P.muP t) (P.muM_postE i hv)).obj Z) :=
  twoPathEndpointIso false false hv hw e Z ≪≫
    (homContentPostE P.T.obj P.W i t.1 (P.muP t) (P.muM_postE i hv)).mapIso
      (eqToIso (eq_of_heq (P.postF_obj_heq i t.1 e.symm (P.muM_postE i hv)
        (P.muM_postF i (nextSector (true, i) false t)) (e.symm ▸ Z)).symm)) ≪≫
    (homContentPostE P.T.obj P.W i t.1 (P.muP t) (P.muM_postE i hv)).mapIso
      ((homContentPostF P.T.obj P.W i t.1 (P.muP t) (P.muM_postE i hv)).mapIso
        (twoPathReturnIso false false e Z))

/-- The actual reservoir entry of the augmented positive matrix is the
native dotted counit, for every exponent and every Hom object. -/
theorem epsEntry_reservoir_factor (c : P.CrossCoeff) (i : I) (n : ℕ) (ν : X) {t : Sector I}
    (hv : StepValid (true, i) false t)
    (hw : StepValid (false, i) false (nextSector (true, i) false t))
    (e : nextSector (false, i) false (nextSector (true, i) false t) = t) (Z : P.H t) :
    P.epsEntry c i n ν (SPath.two false false hv hw e) (.nil t) Z =
      (reservoirCapFactorIso i ν hv hw e Z).hom ≫
        homContentPostCap P.T.obj P.W i t.1 (P.muP t) (P.muM_postE i hv) n Z := by
  rw [epsEntry_reservoir]
  let q := eq_of_heq (P.postF_obj_heq i t.1 e.symm (P.muM_postE i hv)
    (P.muM_postF i (nextSector (true, i) false t)) (e.symm ▸ Z)).symm
  let r : (e.symm ▸ (e.symm ▸ Z) : P.H t) = Z :=
    eq_of_heq ((eqRec_heq _ _).trans (eqRec_heq _ _))
  have h := dottedCounit_transport
    (homContentPostE P.T.obj P.W i t.1 (P.muP t) (P.muM_postE i hv))
    (homContentPostF P.T.obj P.W i t.1 (P.muP t) (P.muM_postE i hv))
    (homContentPostAdjunction P.T.obj P.W i t.1 (P.muP t) (P.muM_postE i hv))
    (homContentPostDot P.T.obj P.W i t.1 (P.muP t) (P.muM_postE i hv)) n q r
  simpa only [reservoirCapFactorIso, Iso.trans_hom, Functor.mapIso_hom,
    eqToIso.hom, twoPathReturnIso, postCap, homContentPostCap, compPow_eq_pow,
    Category.assoc, step, nextSector, muP, q, r, pathFunctor_nil, Functor.id_obj] using congrArg (fun f =>
      (twoPathEndpointIso (c₁ := ⟨up i, SKM.wt D ν [dn i]⟩) (c₂ := ⟨dn i, ν⟩)
        false false hv hw e Z).hom ≫ f) h

/-- The actual two-reservoir cup path in the single prescribed shifted
postcomposition adjunction, including its inner and return transports. -/
def reservoirCupFactorIso (i : I) (ν : X) {t : Sector I}
    (hv : StepValid (false, i) false t)
    (hw : StepValid (true, i) false (nextSector (false, i) false t))
    (e : nextSector (true, i) false (nextSector (false, i) false t) = t) (Z : P.H t) :
    (P.pathFunctor (SPath.two (c₁ := ⟨dn i, SKM.wt D ν [up i]⟩)
      (c₂ := ⟨up i, ν⟩) false false hv hw e)).obj Z ≅
    (homContentPostF P.T.obj P.W i t.1 (P.muP t) (P.muM_postF i t)).obj
      ((homContentPostE P.T.obj P.W i t.1 (P.muP t) (P.muM_postF i t)).obj Z) :=
  twoPathEndpointIso false false hv hw e Z ≪≫
    (homContentPostF P.T.obj P.W i t.1 (P.muP t) (P.muM_postF i t)).mapIso
      (eqToIso (eq_of_heq (P.postE_obj_heq i t.1 e.symm (P.muM_postF i t)
        (P.muM_postE i hw) (e.symm ▸ Z))).symm) ≪≫
    (homContentPostF P.T.obj P.W i t.1 (P.muP t) (P.muM_postF i t)).mapIso
      ((homContentPostE P.T.obj P.W i t.1 (P.muP t) (P.muM_postF i t)).mapIso
        (twoPathReturnIso false false e Z))

/-- The actual reservoir entry of the augmented negative matrix is the
native dotted unit, for every exponent and every full Hom object. -/
theorem etaEntry_reservoir_factor (c : P.CrossCoeff) (i : I) (n : ℕ) (ν : X) {t : Sector I}
    (hv : StepValid (false, i) false t)
    (hw : StepValid (true, i) false (nextSector (false, i) false t))
    (e : nextSector (true, i) false (nextSector (false, i) false t) = t) (Z : P.H t) :
    P.etaEntry c i n ν (.nil t) (SPath.two false false hv hw e) Z =
      homContentPostCup P.T.obj P.W i t.1 (P.muP t) (P.muM_postF i t) n Z ≫
        (reservoirCupFactorIso i ν hv hw e Z).inv := by
  rw [etaEntry_reservoir]
  let q := eq_of_heq (P.postE_obj_heq i t.1 e.symm (P.muM_postF i t)
    (P.muM_postE i hw) (e.symm ▸ Z))
  let r : (e.symm ▸ (e.symm ▸ Z) : P.H t) = Z :=
    eq_of_heq ((eqRec_heq _ _).trans (eqRec_heq _ _))
  have h := dottedUnit_transport
    (C := fun m => homWeightSector P.T.obj P.W.obj (P.muP t) m)
    (Pr := fun m => m + D.α i = P.muM (nextSector (false, i) false t))
    (fun m h => homContentPostE P.T.obj P.W i t.1 (P.muP t) h)
    (fun m h => homContentPostF P.T.obj P.W i t.1 (P.muP t) h)
    (fun m h => homContentPostAdjunction P.T.obj P.W i t.1 (P.muP t) h)
    (fun m h => homContentPostDot P.T.obj P.W i t.1 (P.muP t) h)
    (congrArg P.muM e.symm) (P.muM_postF i t) (P.muM_postE i hw)
    (by exact eqRec_heq _ _) q r n
  simpa only [reservoirCupFactorIso, Iso.trans_inv, Functor.mapIso_inv,
    eqToIso.inv, eqToIso.hom, twoPathReturnIso, postCup, homContentPostCup,
    compPow_eq_pow, map_end_pow, Category.assoc, step, nextSector, muP, q, r,
    pathFunctor_nil, Functor.id_obj] using congrArg (fun f => f ≫
      (twoPathEndpointIso (c₁ := ⟨dn i, SKM.wt D ν [up i]⟩) (c₂ := ⟨up i, ν⟩)
        false false hv hw e Z).inv) h

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
