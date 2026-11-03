import OddMath.QuiverHecke.SwappedAssembly.ReservoirWordFunctor
import OddMath.QuiverHecke.SwappedAssembly.ReservoirLayerGenerators
import OddMath.QuiverHecke.SwappedAssembly.ReservoirLayerCrossings

/-! # Word coordinates on both reservoir path contexts

SwappedVacuumCoordinates §§2–6: transport both actual outer path
contexts to their reversed reservoir induction words. The right chart is
even, so its interchange with any generator map introduces no extra sign.
-/
noncomputable section
namespace OddMath.QuiverHecke.SwappedAssembly
open CategoryTheory StringDiagrams OddMath.SKM BicategoryStruct Supercategory
universe u uB v w
variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type uB} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}
omit [∀ a b : B, PiSupercategory k (a ⟶ b)] in
private theorem context_square {a b c d : B}
    (F : (a ⟶ c) ⥤ (a ⟶ d)) (K : c ⟶ d) (e : F ≅ homPost (k := k) K)
    {Z Z' : a ⟶ b} (r : Z ≅ Z') (hr : r.hom ∈ parity (R := k) _ _ 0)
    {A B₁ : b ⟶ c} (g : A ⟶ B₁) :
    F.map (Z ◁ g) ≫ (F.map (r.hom ▷ B₁) ≫ e.hom.app (Z' ≫ B₁)) =
      (F.map (r.hom ▷ A) ≫ e.hom.app (Z' ≫ A)) ≫ (Z' ◁ g) ▷ K := by
  have hright := (TwoSupercategory.whisker_exchange_of_even_left hr g).symm
  have hleft := e.hom.naturality (Z' ◁ g)
  change F.map (Z' ◁ g) ≫ e.hom.app (Z' ≫ B₁) =
    e.hom.app (Z' ≫ A) ≫ (Z' ◁ g) ▷ K at hleft
  rw [← Category.assoc, ← F.map_comp, hright, F.map_comp, Category.assoc, hleft]
  simp only [Category.assoc]

private theorem refine_entry_square {C : Type*} [Category* C] {G X X' S T S' T' : C}
    (x : G ⟶ X) (m : G ⟶ X') (e : X ≅ S) (d : X' ≅ T) (f : S ≅ S') (g : T ≅ T')
    (a : S ⟶ T) (b : S' ⟶ T') (hm : m ≫ d.hom = x ≫ e.hom ≫ a)
    (ha : a ≫ g.hom = f.hom ≫ b) :
    m ≫ (d ≪≫ g).hom = x ≫ (e ≪≫ f).hom ≫ b := by
  calc
    m ≫ (d ≪≫ g).hom = (m ≫ d.hom) ≫ g.hom := by simp only [Iso.trans_hom, Category.assoc]
    _ = (x ≫ e.hom ≫ a) ≫ g.hom := congrArg (fun z => z ≫ g.hom) hm
    _ = x ≫ (e ≪≫ f).hom ≫ b := by
      simp only [Iso.trans_hom, Category.assoc]
      rw [ha]

namespace ProbeReservoir
variable (P : ProbeReservoir k B D Sc)

/-- Both reservoir context functors become their prescribed words.
The intervening factor 1-morphism is left unchanged. -/
def reservoirContextIso {l r : List (Col I X)} {cL cM cR d : I →₀ ℕ}
    (pu : SPath l (0,cL) (0,cM)) (hu : ∀ a ∈ l, a.l.1 = true)
    (pv : SPath r (0,cR) (0,d)) (hv : ∀ a ∈ r, a.l.1 = true)
    (Y : P.H (0,d)) (A : P.W.obj (P.muM (0,cR)) ⟶ P.W.obj (P.muM (0,cM))) :
    (P.pathFunctor pu).obj ((P.pathFunctor pv).obj Y ≫ A) ≅
      ((Y ≫ ReservoirWord.word P.W.toRouquierData P.ΛR pv hv) ≫ A) ≫
        ReservoirWord.word P.W.toRouquierData P.ΛR pu hu :=
  (P.pathFunctor pu).mapIso (TwoSupercategory.whiskerRightIso (R := k)
    ((P.reservoirWordFunctorIso pv hv).app Y) A) ≪≫
    (P.reservoirWordFunctorIso pu hu).app ((Y ≫
      ReservoirWord.word P.W.toRouquierData P.ΛR pv hv) ≫ A)

/-- Both-context coordinates are even, including for odd reservoir data. -/
theorem reservoirContextIso_hom_mem {l r : List (Col I X)} {cL cM cR d : I →₀ ℕ}
    (pu : SPath l (0,cL) (0,cM)) (hu : ∀ a ∈ l, a.l.1 = true)
    (pv : SPath r (0,cR) (0,d)) (hv : ∀ a ∈ r, a.l.1 = true)
    (Y : P.H (0,d)) (A : P.W.obj (P.muM (0,cR)) ⟶ P.W.obj (P.muM (0,cM))) :
    (P.reservoirContextIso pu hu pv hv Y A).hom ∈ parity (R := k) _ _ 0 := by
  simpa only [reservoirContextIso, Iso.trans_hom, Functor.mapIso_hom,
    TwoSupercategory.whiskerRightIso_hom, Iso.app_hom, homPost, zero_add] using
    comp_mem (P.pathFunctor_map_mem pu (TwoSupercategory.whiskerRight_mem A
      (P.reservoirWordFunctorIso_hom_mem pv hv Y)))
      (P.reservoirWordFunctorIso_hom_mem pu hu _)

/-- The prescribed factor map in both actual path contexts becomes its
literal two-whiskered word map. The map may have arbitrary parity
components; evenness of the right chart is the only interchange input. -/
theorem reservoirContext_square {l r : List (Col I X)} {cL cM cR d : I →₀ ℕ}
    (pu : SPath l (0,cL) (0,cM)) (hu : ∀ a ∈ l, a.l.1 = true)
    (pv : SPath r (0,cR) (0,d)) (hv : ∀ a ∈ r, a.l.1 = true)
    (Y : P.H (0,d)) {A B₁ : P.W.obj (P.muM (0,cR)) ⟶ P.W.obj (P.muM (0,cM))}
    (a : A ⟶ B₁) :
    (P.pathFunctor pu).map (((P.pathFunctor pv).obj Y) ◁ a) ≫
        (P.reservoirContextIso pu hu pv hv Y B₁).hom =
      (P.reservoirContextIso pu hu pv hv Y A).hom ≫
        ((Y ≫ ReservoirWord.word P.W.toRouquierData P.ΛR pv hv) ◁ a) ▷
          ReservoirWord.word P.W.toRouquierData P.ΛR pu hu := by
  exact context_square (a := P.T.obj (-P.muP (0,cM)))
    (b := P.W.obj (P.muM (0,cR))) (c := P.W.obj (P.muM (0,cM)))
    (d := P.W.obj (P.muM (0,cL))) (A := A) (B₁ := B₁) (P.pathFunctor pu) (ReservoirWord.word P.W.toRouquierData P.ΛR pu hu)
    (P.reservoirWordFunctorIso pu hu) ((P.reservoirWordFunctorIso pv hv).app Y)
    (P.reservoirWordFunctorIso_hom_mem pv hv Y) a


/-- The literal dot path in its two reservoir word contexts. -/
def reservoirLayerDotWordIso (ν : X) (u v : List (Letter I)) (i : I)
    {cL c d : I →₀ ℕ} (hv : StepValid (true,i) false (0,c))
    (pu : SPath (SKM.lay D ν u (.dot i) v).left (0,cL) (0,c))
    (hu : ∀ a ∈ (SKM.lay D ν u (.dot i) v).left, a.l.1 = true)
    (pv : SPath (SKM.lay D ν u (.dot i) v).right (0,c - Finsupp.single i 1) (0,d))
    (hr : ∀ a ∈ (SKM.lay D ν u (.dot i) v).right, a.l.1 = true)
    (Y : P.H (0,d)) :
    (P.pathFunctor ((pu.append (.cons ⟨up i,SKM.wt D ν v⟩ false (0,c) hv (.nil _))).append pv)).obj Y ≅
      ((Y ≫ ReservoirWord.word P.W.toRouquierData P.ΛR pv hr) ≫
        P.W.E i (P.reservoirVacuumEdge i c hv)) ≫
        ReservoirWord.word P.W.toRouquierData P.ΛR pu hu :=
  P.reservoirLayerDotIso ν u v i hv pu pv Y ≪≫
    P.reservoirContextIso pu hu pv hr Y (P.W.E i (P.reservoirVacuumEdge i c hv))

/-- The literal dot matrix, through both reversed reservoir word charts,
acts by the unchanged two-whiskered factor dot on every Hom input. -/
theorem layerMap_reservoir_dot_word (a : P.CrossCoeff) {Gs Ys : ∀ s, P.H s}
    (ν : X) (u v : List (Letter I)) (i : I)
    (x : P.Mod Gs Ys (SKM.lay D ν u (.dot i) v).dom)
    {cL c d : I →₀ ℕ} (hv : StepValid (true,i) false (0,c))
    (pu : SPath (SKM.lay D ν u (.dot i) v).left (0,cL) (0,c))
    (hu : ∀ b ∈ (SKM.lay D ν u (.dot i) v).left, b.l.1 = true)
    (pv : SPath (SKM.lay D ν u (.dot i) v).right (0,c - Finsupp.single i 1) (0,d))
    (hr : ∀ b ∈ (SKM.lay D ν u (.dot i) v).right, b.l.1 = true)
    (hq : P.wt (0,d) = (SKM.lay D ν u (.dot i) v).cod.endR) :
    P.layerMap (P.upwardGens a) (SKM.lay D ν u (.dot i) v) x (0,cL) ⟨(0,d),hq⟩
        ((pu.append (.cons ⟨up i,SKM.wt D ν v⟩ false (0,c) hv (.nil _))).append pv) ≫
        (P.reservoirLayerDotWordIso ν u v i hv pu hu pv hr (Ys (0,d))).hom =
      x (0,cL) ⟨(0,d),hq.trans (SKM.lay_valid D ν u (.dot i) v).endR_eq⟩
        ((pu.append (.cons ⟨up i,SKM.wt D ν v⟩ false (0,c) hv (.nil _))).append pv) ≫
        (P.reservoirLayerDotWordIso ν u v i hv pu hu pv hr (Ys (0,d))).hom ≫
        (((Ys (0,d) ≫ ReservoirWord.word P.W.toRouquierData P.ΛR pv hr) ◁
          P.W.dot i (P.reservoirVacuumEdge i c hv)) ▷
          ReservoirWord.word P.W.toRouquierData P.ΛR pu hu) := by
  exact refine_entry_square _ _ (P.reservoirLayerDotIso ν u v i hv pu pv (Ys (0,d)))
    (P.reservoirLayerDotIso ν u v i hv pu pv (Ys (0,d)))
    (P.reservoirContextIso pu hu pv hr (Ys (0,d)) (P.W.E i (P.reservoirVacuumEdge i c hv)))
    (P.reservoirContextIso pu hu pv hr (Ys (0,d)) (P.W.E i (P.reservoirVacuumEdge i c hv))) _ _
    (P.layerMap_reservoir_dot a ν u v i hr x hv pu pv hq)
    (P.reservoirContext_square pu hu pv hr (Ys (0,d)) (P.W.dot i (P.reservoirVacuumEdge i c hv)))

/-- The equal-colour crossing path in its two reservoir word contexts. -/
def reservoirLayerSameCrossWordIso (ν : X) (u v : List (Letter I)) (i : I)
    {cL c d : I →₀ ℕ} (hv : StepValid (true,i) false (0,c))
    (hw : StepValid (true,i) false (nextSector (true,i) false (0,c)))
    (pu : SPath (SKM.lay D ν u (.cross i i) v).left (0,cL) (0,c))
    (hu : ∀ a ∈ (SKM.lay D ν u (.cross i i) v).left, a.l.1 = true)
    (pv : SPath (SKM.lay D ν u (.cross i i) v).right
      (0,c - Finsupp.single i 1 - Finsupp.single i 1) (0,d))
    (hr : ∀ a ∈ (SKM.lay D ν u (.cross i i) v).right, a.l.1 = true)
    (Y : P.H (0,d)) :
    (P.pathFunctor ((pu.append
      (.cons ⟨up i,SKM.wt D (SKM.wt D ν v) [up i]⟩ false (0,c) hv
        (.cons ⟨up i,SKM.wt D ν v⟩ false _ hw (.nil _)))).append pv)).obj Y ≅
      ((Y ≫ ReservoirWord.word P.W.toRouquierData P.ΛR pv hr) ≫
        P.W.E i (P.reservoirVacuumEdge i (c - Finsupp.single i 1) hw) ≫ P.W.E i (P.reservoirVacuumEdge i c hv)) ≫
        ReservoirWord.word P.W.toRouquierData P.ΛR pu hu :=
  P.reservoirLayerSameCrossIso ν u v i hv hw pu pv Y ≪≫
    P.reservoirContextIso pu hu pv hr Y (P.W.E i (P.reservoirVacuumEdge i (c - Finsupp.single i 1) hw) ≫ P.W.E i (P.reservoirVacuumEdge i c hv))

/-- The literal equal-colour crossing matrix in its two reversed word
contexts. The factor crossing and its sign are unchanged. -/
theorem layerMap_reservoir_cross_same_word (a : P.CrossCoeff) {Gs Ys : ∀ s, P.H s}
    (ν : X) (u v : List (Letter I)) (i : I)
    (x : P.Mod Gs Ys (SKM.lay D ν u (.cross i i) v).dom)
    {cL c d : I →₀ ℕ} (hv : StepValid (true,i) false (0,c))
    (hw : StepValid (true,i) false (nextSector (true,i) false (0,c)))
    (pu : SPath (SKM.lay D ν u (.cross i i) v).left (0,cL) (0,c))
    (hu : ∀ b ∈ (SKM.lay D ν u (.cross i i) v).left, b.l.1 = true)
    (pv : SPath (SKM.lay D ν u (.cross i i) v).right
      (0,c - Finsupp.single i 1 - Finsupp.single i 1) (0,d))
    (hr : ∀ b ∈ (SKM.lay D ν u (.cross i i) v).right, b.l.1 = true)
    (hq : P.wt (0,d) = (SKM.lay D ν u (.cross i i) v).cod.endR) :
    P.layerMap (P.upwardGens a) (SKM.lay D ν u (.cross i i) v) x (0,cL) ⟨(0,d),hq⟩
        ((pu.append (.cons ⟨up i,SKM.wt D (SKM.wt D ν v) [up i]⟩ false (0,c) hv
          (.cons ⟨up i,SKM.wt D ν v⟩ false _ hw (.nil _)))).append pv) ≫
        (P.reservoirLayerSameCrossWordIso ν u v i hv hw pu hu pv hr (Ys (0,d))).hom =
      x (0,cL) ⟨(0,d),hq.trans (SKM.lay_valid D ν u (.cross i i) v).endR_eq⟩
        ((pu.append (.cons ⟨up i,SKM.wt D (SKM.wt D ν v) [up i]⟩ false (0,c) hv
          (.cons ⟨up i,SKM.wt D ν v⟩ false _ hw (.nil _)))).append pv) ≫
        (P.reservoirLayerSameCrossWordIso ν u v i hv hw pu hu pv hr (Ys (0,d))).hom ≫
        (((Ys (0,d) ≫ ReservoirWord.word P.W.toRouquierData P.ΛR pv hr) ◁
          P.W.cross i i (P.reservoirVacuumEdge i (c - Finsupp.single i 1) hw) (P.reservoirVacuumEdge i c hv)
            (P.reservoirVacuumEdge i (c - Finsupp.single i 1) hw) (P.reservoirVacuumEdge i c hv)) ▷
          ReservoirWord.word P.W.toRouquierData P.ΛR pu hu) := by
  exact refine_entry_square _ _ (P.reservoirLayerSameCrossIso ν u v i hv hw pu pv (Ys (0,d)))
    (P.reservoirLayerSameCrossIso ν u v i hv hw pu pv (Ys (0,d)))
    (P.reservoirContextIso pu hu pv hr (Ys (0,d))
      (P.W.E i (P.reservoirVacuumEdge i (c - Finsupp.single i 1) hw) ≫ P.W.E i (P.reservoirVacuumEdge i c hv)))
    (P.reservoirContextIso pu hu pv hr (Ys (0,d))
      (P.W.E i (P.reservoirVacuumEdge i (c - Finsupp.single i 1) hw) ≫ P.W.E i (P.reservoirVacuumEdge i c hv))) _ _
    (P.layerMap_reservoir_cross_same a ν u v i hr x hv hw pu pv hq)
    (P.reservoirContext_square pu hu pv hr (Ys (0,d))
      (P.W.cross i i (P.reservoirVacuumEdge i (c - Finsupp.single i 1) hw) (P.reservoirVacuumEdge i c hv) (P.reservoirVacuumEdge i (c - Finsupp.single i 1) hw) (P.reservoirVacuumEdge i c hv)))

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
