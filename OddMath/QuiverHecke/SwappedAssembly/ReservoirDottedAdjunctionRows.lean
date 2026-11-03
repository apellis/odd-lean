import OddMath.QuiverHecke.SwappedAssembly.LeftwardInverse
import OddMath.QuiverHecke.SwappedAssembly.CupCapZigzag

/-! # Literal dotted cap rows and cup columns

The actual augmented-matrix entries, before imposing any mixed-block
inverse condition. All dot exponents, including zero, are retained.
-/
noncomputable section
namespace OddMath.QuiverHecke.SwappedAssembly
open CategoryTheory StringDiagrams OddMath.SKM
universe u uB v w
variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type uB} [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}
namespace ProbeReservoir
variable {P : ProbeReservoir k B D Sc}

/-- A bare cap layer has exactly the given cap image. -/
theorem compLayer_cap (gens : P.Generators) (i : I) (ν : X) {s t : Sector I}
    (p : SPath (wd D ν [up i, dn i]) s t) (r : SPath (wd D ν []) s t) (Z : P.H t) :
    compLayer gens (SKM.lay D ν [] (SKM.Shape.cap i) []) p r Z = gens.cap i ν p r Z := by
  cases r
  rw [compLayer_eq_of_path gens (SKM.lay D ν [] (SKM.Shape.cap i) []) (.nil s) p
    (.nil s) (.nil s) p (.nil s) (SPath.append_nil_pair p) rfl Z]
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

/-- A bare cup layer has exactly the given cup image. -/
theorem compLayer_cup (gens : P.Generators) (i : I) (ν : X) {s t : Sector I}
    (r : SPath (wd D ν []) s t) (q : SPath (wd D ν [dn i, up i]) s t) (Z : P.H t) :
    compLayer gens (SKM.lay D ν [] (SKM.Shape.cup i) []) r q Z = gens.cup i ν r q Z := by
  cases r
  rw [compLayer_eq_of_path gens (SKM.lay D ν [] (SKM.Shape.cup i) []) (.nil s) (.nil s)
    q (.nil s) (.nil s) q rfl (SPath.append_nil_pair q) Z]
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

/-- The full cap row is the diagonal dot power followed by the actual cap.
No crossing coefficient occurs on the right-hand side. -/
theorem epsEntry_eq_dot_cap (c : P.CrossCoeff) (i : I) (n : ℕ) (ν : X)
    {s t : Sector I} (p : SPath (wd D ν [up i, dn i]) s t)
    (r : SPath (wd D ν []) s t) (Z : P.H t) :
    P.epsEntry c i n ν p r Z =
      compPow (compLayer (P.upwardGens c) (SKM.lay D ν [] (SKM.Shape.dot i) [dn i]) p p Z) n ≫
        P.capImage i ν p r Z := by
  classical
  unfold epsEntry
  simp only [SKM.epsL, SKM.layList, List.map_append]
  erw [compList_append _ _ _ ((SKM.sChain_dotsL [] i [dn i] n).chain D ν)
    ((by simp [SKM.Shape.dom, SKM.Shape.cod] : SKM.SChain [up i, dn i] [([], SKM.Shape.cap i, [])] []).chain D ν)]
  simp only [SKM.layList, List.map_cons, List.map_nil, compList_one,
    SPath.cast_self, eqToHom_refl, Category.id_comp, Category.comp_id]
  erw [Finset.sum_eq_single p]
  · erw [compList_dotsL (P.upwardGens c) ν [] i [dn i] n _ p p Z]
    simp only [dite_eq_ite, ↓reduceIte, eqToHom_refl, Category.comp_id]
    rw [compLayer_cap]
    rfl
  · intro b _ hb
    erw [compList_dotsL (P.upwardGens c) ν [] i [dn i] n _ p b Z]
    simp only [dite_eq_right (Ne.symm hb), Limits.zero_comp]
  · simp

/-- The full cup column is the actual cup followed by its diagonal dot
power. The expression includes the zero-th power. -/
theorem etaEntry_eq_cup_dot (c : P.CrossCoeff) (i : I) (n : ℕ) (ν : X)
    {s t : Sector I} (r : SPath (wd D ν []) s t)
    (q : SPath (wd D ν [dn i, up i]) s t) (Z : P.H t) :
    P.etaEntry c i n ν r q Z = P.cupImage i ν r q Z ≫
      compPow (compLayer (P.upwardGens c) (SKM.lay D ν [dn i] (SKM.Shape.dot i) []) q q Z) n := by
  classical
  unfold etaEntry
  simp only [SKM.etaL, SKM.layList, List.map_append]
  erw [compList_append _ _ _
    ((by simp [SKM.Shape.dom, SKM.Shape.cod] : SKM.SChain [] [([], SKM.Shape.cup i, [])] [dn i, up i]).chain D ν)
    ((SKM.sChain_dotsL [dn i] i [] n).chain D ν)]
  simp only [SKM.layList, List.map_cons, List.map_nil, compList_one,
    SPath.cast_self, eqToHom_refl, Category.id_comp, Category.comp_id]
  erw [Finset.sum_eq_single q]
  · erw [compList_dotsL (P.upwardGens c) ν [dn i] i [] n _ q q Z]
    simp only [dite_eq_ite, ↓reduceIte, eqToHom_refl, Category.comp_id]
    rw [compLayer_cup]
    rfl
  · intro b _ hb
    erw [compList_dotsL (P.upwardGens c) ν [dn i] i [] n _ b q Z]
    simp only [dite_eq_right hb, Limits.comp_zero]
  · simp

/-- The endpoint equality chart for a two-strand path. It is fixed by
transport, rather than chosen from a possible isomorphism. -/
def twoPathEndpointIso {c₁ c₂ : Col I X} {t t' : Sector I}
    (a b : Bool) (hv : StepValid c₁.l a t)
    (hw : StepValid c₂.l b (nextSector c₁.l a t))
    (e : nextSector c₂.l b (nextSector c₁.l a t) = t') (Z : P.H t') :
    (P.pathFunctor (SPath.two a b hv hw e)).obj Z ≅
      (P.step c₁.l a t hv).obj ((P.step c₂.l b _ hw).obj (e.symm ▸ Z)) :=
  eqToIso (by subst e; rfl)

/-- Returning a Hom object around a closed sector path changes only its
equality transport. -/
def twoPathReturnIso {l₁ l₂ : Letter I} {t : Sector I} (a b : Bool)
    (e : nextSector l₂ b (nextSector l₁ a t) = t) (Z : P.H t) :
    (e.symm ▸ (e.symm ▸ Z) : P.H t) ≅ Z :=
  eqToIso (eq_of_heq ((eqRec_heq _ _).trans (eqRec_heq _ _)))

/-- The dot on the first strand, including the identity comparison for
the empty outer path. -/
private theorem compLayer_dot_first (c : P.CrossCoeff) (i : I) (ν : X)
    {s t : Sector I} (hv : StepValid (true, i) false s)
    (pv : SPath (wd D ν [dn i]) (nextSector (true, i) false s) t) (Z : P.H t) :
    compLayer (P.upwardGens c) (SKM.lay D ν [] (SKM.Shape.dot i) [dn i])
      (.cons _ false s hv pv) (.cons _ false s hv pv) Z =
      homContentPostDot P.T.obj P.W i s.1 (P.muP s) _ ((P.pathFunctor pv).obj Z) := by
  rw [compLayer_eq_of_path (P.upwardGens c) (SKM.lay D ν [] (SKM.Shape.dot i) [dn i]) (.nil s)
    (.cons _ false s hv (.nil _)) (.cons _ false s hv (.nil _)) pv
    (.cons _ false s hv pv) (.cons _ false s hv pv) rfl rfl Z]
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  change P.dotImage i (SKM.wt D ν [dn i])
    (.cons _ false s hv (.nil _)) (.cons _ false s hv (.nil _))
      ((P.pathFunctor pv).obj Z) = _
  exact P.dotImage_reservoir i _ s hv hv _

/-- The diagonal cap-row dot, in the selected endpoint chart, is the
prescribed shifted postcomposition dot. -/
theorem capRow_dot_reservoir (c : P.CrossCoeff) (i : I) (ν : X)
    {t t' : Sector I} (hv : StepValid (true, i) false t)
    (hw : StepValid (false, i) false (nextSector (true, i) false t))
    (e : nextSector (false, i) false (nextSector (true, i) false t) = t') (Z : P.H t') :
    let p : SPath (wd D ν [up i, dn i]) t t' := SPath.two false false hv hw e
    compLayer (P.upwardGens c) (SKM.lay D ν [] (SKM.Shape.dot i) [dn i]) p p Z =
      (twoPathEndpointIso (c₁ := ⟨up i, SKM.wt D ν [dn i]⟩) (c₂ := ⟨dn i, ν⟩) false false hv hw e Z).hom ≫
        homContentPostDot P.T.obj P.W i t.1 (P.muP t) _
          ((P.step (false, i) false _ hw).obj (e.symm ▸ Z)) ≫
        (twoPathEndpointIso (c₁ := ⟨up i, SKM.wt D ν [dn i]⟩) (c₂ := ⟨dn i, ν⟩) false false hv hw e Z).inv := by
  subst e
  dsimp only [twoPathEndpointIso, SPath.two, pathFunctor_cons, pathFunctor_nil,
    Functor.comp_obj, Functor.id_obj]
  simp only [eqToIso_refl, Iso.refl_hom, Iso.refl_inv, Category.id_comp]
  erw [Category.comp_id]
  convert! compLayer_dot_first c i ν hv (.cons _ false _ hw (.nil _)) Z using 1

/-- The actual reservoir cap entry in its fixed endpoint charts, with
its given shifted adjunction retained. -/
theorem capImage_reservoir_endpoint (i : I) (ν : X) {t : Sector I}
    (hv : StepValid (true, i) false t)
    (hw : StepValid (false, i) false (nextSector (true, i) false t))
    (e : nextSector (false, i) false (nextSector (true, i) false t) = t) (Z : P.H t) :
    P.capImage i ν (SPath.two false false hv hw e) (.nil t) Z =
      (twoPathEndpointIso (c₁ := ⟨up i, SKM.wt D ν [dn i]⟩) (c₂ := ⟨dn i, ν⟩) false false hv hw e Z).hom ≫
        P.postCap i t hv hw e.symm (e.symm ▸ Z) ≫
        (twoPathReturnIso false false e Z).hom := by
  unfold capImage
  rw [P.twoZero_two (Z' := e.symm ▸ Z) (hZ := eqRec_heq _ _)]
  rfl

private theorem compPow_iso {C : Type*} [Category C] {A B : C} (e : A ≅ B)
    (f : End B) (n : ℕ) :
    compPow (e.hom ≫ f ≫ e.inv) n = e.hom ≫ compPow f n ≫ e.inv := by
  induction n with
  | zero => simp [compPow]
  | succ n ih => simp [compPow, ih, Category.assoc]

/-- Every actual reservoir cap row is the shifted post-dot power and
specified factor counit, in the selected equality charts. -/
theorem epsEntry_reservoir (c : P.CrossCoeff) (i : I) (n : ℕ) (ν : X) {t : Sector I}
    (hv : StepValid (true, i) false t)
    (hw : StepValid (false, i) false (nextSector (true, i) false t))
    (e : nextSector (false, i) false (nextSector (true, i) false t) = t) (Z : P.H t) :
    P.epsEntry c i n ν (SPath.two false false hv hw e) (.nil t) Z =
      (twoPathEndpointIso (c₁ := ⟨up i, SKM.wt D ν [dn i]⟩) (c₂ := ⟨dn i, ν⟩)
        false false hv hw e Z).hom ≫
      compPow (homContentPostDot P.T.obj P.W i t.1 (P.muP t) _
        ((P.step (false, i) false _ hw).obj (e.symm ▸ Z))) n ≫
      P.postCap i t hv hw e.symm (e.symm ▸ Z) ≫
      (twoPathReturnIso false false e Z).hom := by
  rw [epsEntry_eq_dot_cap, capRow_dot_reservoir, capImage_reservoir_endpoint, compPow_iso]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- The diagonal cup-column dot, in the fixed endpoint chart, is the
lowering functor applied to the prescribed shifted dot. -/
theorem cupColumn_dot_reservoir (c : P.CrossCoeff) (i : I) (ν : X)
    {t t' : Sector I} (hv : StepValid (false, i) false t)
    (hw : StepValid (true, i) false (nextSector (false, i) false t))
    (e : nextSector (true, i) false (nextSector (false, i) false t) = t') (Z : P.H t') :
    let p : SPath (wd D ν [dn i, up i]) t t' := SPath.two false false hv hw e
    compLayer (P.upwardGens c) (SKM.lay D ν [dn i] (SKM.Shape.dot i) []) p p Z =
      (twoPathEndpointIso (c₁ := ⟨dn i, SKM.wt D ν [up i]⟩) (c₂ := ⟨up i, ν⟩)
        false false hv hw e Z).hom ≫
        (P.step (false, i) false t hv).map
          (homContentPostDot P.T.obj P.W i (nextSector (false, i) false t).1
            (P.muP (nextSector (false, i) false t)) (P.muM_postE i hw)
            (e.symm ▸ Z : P.H (nextSector (true, i) false (nextSector (false, i) false t)))) ≫
        (twoPathEndpointIso (c₁ := ⟨dn i, SKM.wt D ν [up i]⟩) (c₂ := ⟨up i, ν⟩)
          false false hv hw e Z).inv := by
  subst e
  dsimp only [twoPathEndpointIso, SPath.two, pathFunctor_cons, pathFunctor_nil,
    Functor.comp_obj, Functor.id_obj]
  simp only [eqToIso_refl, Iso.refl_hom, Iso.refl_inv, Category.id_comp]
  erw [Category.comp_id]
  erw [compLayer_eq_of_path (P.upwardGens c) (SKM.lay D ν [dn i] (SKM.Shape.dot i) [])
    (.cons _ false t hv (.nil _)) (.cons _ false _ hw (.nil _))
    (.cons _ false _ hw (.nil _)) (.nil _)
    (.cons _ false t hv (.cons _ false _ hw (.nil _)))
    (.cons _ false t hv (.cons _ false _ hw (.nil _))) rfl rfl Z]
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  change (P.step (false, i) false t hv).map
    (P.dotImage i ν (.cons _ false _ hw (.nil _)) (.cons _ false _ hw (.nil _)) Z) = _
  rw [P.dotImage_reservoir]

/-- The actual reservoir cup entry in its fixed endpoint charts. -/
theorem cupImage_reservoir_endpoint (i : I) (ν : X) {t : Sector I}
    (hv : StepValid (false, i) false t)
    (hw : StepValid (true, i) false (nextSector (false, i) false t))
    (e : nextSector (true, i) false (nextSector (false, i) false t) = t) (Z : P.H t) :
    P.cupImage i ν (.nil t) (SPath.two false false hv hw e) Z =
      (twoPathReturnIso false false e Z).inv ≫
        P.postCup i t hv hw e.symm (e.symm ▸ Z) ≫
        (twoPathEndpointIso (c₁ := ⟨dn i, SKM.wt D ν [up i]⟩) (c₂ := ⟨up i, ν⟩)
          false false hv hw e Z).inv := by
  unfold cupImage
  rw [P.zeroTwo_two (Z' := e.symm ▸ Z) (hZ := eqRec_heq _ _)]
  rfl

/-- Every actual reservoir cup column is the specified shifted unit
followed by the lowering image of the shifted dot power. -/
theorem etaEntry_reservoir (c : P.CrossCoeff) (i : I) (n : ℕ) (ν : X) {t : Sector I}
    (hv : StepValid (false, i) false t)
    (hw : StepValid (true, i) false (nextSector (false, i) false t))
    (e : nextSector (true, i) false (nextSector (false, i) false t) = t) (Z : P.H t) :
    P.etaEntry c i n ν (.nil t) (SPath.two false false hv hw e) Z =
      (twoPathReturnIso false false e Z).inv ≫
      P.postCup i t hv hw e.symm (e.symm ▸ Z) ≫
      compPow ((P.step (false, i) false t hv).map
        (homContentPostDot P.T.obj P.W i (nextSector (false, i) false t).1
          (P.muP (nextSector (false, i) false t)) (P.muM_postE i hw)
            (e.symm ▸ Z : P.H (nextSector (true, i) false (nextSector (false, i) false t))))) n ≫
      (twoPathEndpointIso (c₁ := ⟨dn i, SKM.wt D ν [up i]⟩) (c₂ := ⟨up i, ν⟩)
        false false hv hw e Z).inv := by
  rw [etaEntry_eq_cup_dot, cupColumn_dot_reservoir, cupImage_reservoir_endpoint, compPow_iso]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
