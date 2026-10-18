import OddMath.SKM.Rho.Normalize

/-!
# Layer Formula for ρ

Supporting calculations for Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, Proposition 9.8 with the corrected crossing sign.
These calculations use a purely even commutative coefficient ring and the
existing super Kac–Moody presentation.
-/
noncomputable section
namespace OddMath.SKM.RhoInversionKernel
open CategoryTheory StringDiagrams Supercategory BicategoryStruct RhoWords RhoEvaluator
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D} {hc : Sc.Homogeneous}
theorem eq_underlying {ν μ : X}
    {a b : rhoObj (D := D) (Sc := Sc) (sy := sy) (hc := hc) ν ⟶ rhoObj μ} (h : a = b) :
    eqToHom h = eqToHom (congrArg (fun x => (pres D Sc).obj x.obj.obj.obj) h) := by
  cases h
  rfl

theorem rev_wL {Ω ν μ : X}
    (a : rhoObj (D := D) (Sc := Sc) (sy := sy) (hc := hc) Ω ⟶ rhoObj ν)
    {b c : rhoObj (D := D) (Sc := Sc) (sy := sy) (hc := hc) ν ⟶ rhoObj μ}
    (f : b ⟶ c) (ha : a.par = 0) :
    a ◁ f = (pres D Sc).wRAt μ f a.obj.obj.obj b.obj.obj.start_eq c.obj.obj.start_eq := by
  change QEnvelope.toHom (Envelope.toHom
    (BicategoryStruct.whiskerRight (B := Uqπ D Sc sy hc) f a)) = _
  rw [TwoEnvelope.toHom_whiskerRight_of_par_zero _ _ ha]
  rfl

theorem rev_wR {Ω ν μ : X}
    {a b : rhoObj (D := D) (Sc := Sc) (sy := sy) (hc := hc) Ω ⟶ rhoObj ν}
    (f : a ⟶ b)
    (c : rhoObj (D := D) (Sc := Sc) (sy := sy) (hc := hc) ν ⟶ rhoObj μ)
    (hc0 : c.par = 0) :
    f ▷ c = (pres D Sc).wL c.obj.obj.obj f := by
  change QEnvelope.toHom (Envelope.toHom
    (BicategoryStruct.whiskerLeft (B := Uqπ D Sc sy hc) c f)) = _
  rw [TwoEnvelope.toHom_whiskerLeft_of_par_zero _ hc0]
  rfl

theorem at_obj (ν μ : X) (s : List (Letter I)) (h : wt D μ s = ν) :
    (rhoAt (Sc := Sc) (sy := sy) (hc := hc) ν μ s h).obj.obj.obj = ob D ν (rhoWord s) := by
  change ob D ν (rhoWord ((wd D μ s).map Col.l)) = _
  rw [wd_map_l]

private theorem transport_heq {C : Type*} [Category C] {a b a' b' : C}
    (ha : a = a') (hb : b' = b) (f : a' ⟶ b') :
    HEq (eqToHom ha ≫ f ≫ eqToHom hb) f := by
  subst a' b'
  exact heq_of_eq (by simp)

theorem smul_cl_heq (a : k) (μ : X) {s r s' r' : List (Letter I)}
    {A B : List (LayerData I)} (hs : s = s') (hr : r = r') (hA : A = B) :
    HEq (a • cl D Sc μ s r A) (a • cl D Sc μ s' r' B) := by
  cases hs; cases hr; cases hA
  rfl

theorem layer_formula (t : k) (Ω μ : X) (u : List (Letter I)) (g : Shape I)
    (v : List (Letter I)) (h : wt D μ (u ++ g.dom ++ v) = Ω) :
    HEq (rhoLayer (sy := sy) (hc := hc) t Ω μ u g v h)
      (RhoGenerators.coeff (D := D) t g •
        cl D Sc Ω (rhoWord (u ++ g.dom ++ v)) (rhoWord (u ++ g.cod ++ v))
          ((RhoGenerators.layers g).map (whL (rhoWord v) (rhoWord u)))) := by
  simp only [rhoLayer, place, RhoGenerators.generator,
    TwoSupercategory.whiskerLeft_comp (R := k) (B := TwoSRev k (Uqπ D Sc sy hc)),
    TwoSupercategory.comp_whiskerRight (R := k) (B := TwoSRev k (Uqπ D Sc sy hc)),
    TwoSupercategory.whiskerLeft_eqToHom k, TwoSupercategory.eqToHom_whiskerRight k,
    Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
  simp only [rev_wL, rev_wR, rhoMap_par, eq_underlying]
  generalize_proofs ht hu hdom hv0 ha hcod hs0 hr0 hb
  refine (transport_heq ha hb _).trans ?_
  change HEq ((pres D Sc).wRAt μ
    ((pres D Sc).wL (ob D (wt D μ v) (rhoWord ((wd D μ v).map Col.l)))
      (RhoGenerators.coeff (D := D) t g • cl D Sc (wt D (wt D μ v) g.dom)
        (rhoWord g.dom) (rhoWord g.cod) (RhoGenerators.layers g)))
    (ob D Ω (rhoWord ((wd D (wt D (wt D μ v) g.dom) u).map Col.l))) _ _) _
  have hv : wt D Ω (rhoWord ((wd D (wt D (wt D μ v) g.dom) u).map Col.l)) =
      wt D (wt D μ v) g.dom := by
    rw [wd_map_l, ← h]
    simpa only [wt_append] using rhoWord_wt (wt D (wt D μ v) g.dom) u
  have hs : wt D (wt D (wt D μ v) g.dom) (rhoWord g.dom) = wt D μ v :=
    rhoWord_wt _ _
  have hr : wt D (wt D (wt D μ v) g.dom) (rhoWord g.cod) = wt D μ v := by
    rw [g.wt_dom_eq_wt_cod]
    exact rhoWord_wt _ _
  have hω : wt D (wt D μ v) (rhoWord ((wd D μ v).map Col.l)) = μ := by
    rw [wd_map_l]
    exact rhoWord_wt _ _
  have H := raw_context (Sc := Sc) (RhoGenerators.coeff (D := D) t g)
    (wt D μ v) (wt D (wt D μ v) g.dom) Ω μ
    (rhoWord ((wd D μ v).map Col.l)) (rhoWord g.dom) (rhoWord g.cod)
    (rhoWord ((wd D (wt D (wt D μ v) g.dom) u).map Col.l)) hs hr hv hω
    (RhoGenerators.layers g) (RhoGenerators.layers_chain g)
  exact H.trans (smul_cl_heq _ _
    (by simp only [wd_map_l, rhoWord_append, List.append_assoc])
    (by simp only [wd_map_l, rhoWord_append, List.append_assoc])
    (by rw [wd_map_l, wd_map_l]))
end OddMath.SKM.RhoInversionKernel
