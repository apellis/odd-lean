import OddMath.SKM.Rho.Words
import OddMath.SKM.Rho.Upward
import OddMath.SKM.Rho.Matrix

/-!
# Generators for ρ

Supporting calculations for Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, Proposition 9.8 with the corrected crossing sign.
These calculations use a purely even commutative coefficient ring and the
existing super Kac–Moody presentation.
-/
noncomputable section
namespace OddMath.SKM.RhoGenerators
open CategoryTheory StringDiagrams Supercategory BicategoryStruct RhoWords
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D} {hc : Sc.Homogeneous}

def atWord (ν μ : X) (s : List (Letter I)) (h : wt D μ s = ν) :
    rhoObj (Sc := Sc) (sy := sy) (hc := hc) ν ⟶ rhoObj μ :=
  Envelope.mk 0 (QEnvelope.mk (rhoShift sy μ s)
    (psiWordAt μ ν (rhoWord s) (h ▸ rhoWord_wt μ s)))

theorem map_word (ν μ : X) (s : List (Letter I)) (h : wt D μ s = ν) :
    rhoMap (sy := sy) (hc := hc) (psiWordAt (Sc := Sc) ν μ s h) = atWord ν μ s h :=
  rhoMap_wordAt ν μ s h

def layers : Shape I → List (LayerData I)
  | .dot i => ddotL i
  | .cross i j => dcrossL j i
  | .cup i => [([], .cup i, [])]
  | .cap i => [([], .cap i, [])]
  | .lcross i j => lcrossL j i
  | .dcup i n => dcupL i n
  | .dcap i n => dcapL i n

def coeff (t : k) : Shape I → k
  | .dot i => psiCoeff t (D.parity i)
  | .cross i j => psiCoeff t (D.parity i * D.parity j)
  | .cup _ | .cap _ => 1
  | .lcross i j => psiCoeff (-t) (D.parity i * D.parity j)
  | .dcup i n | .dcap i n => RhoMixed.entryCoeff (-t) (D.parity i) n

theorem layers_chain (g : Shape I) : SChain (rhoWord g.dom) (layers g) (rhoWord g.cod) := by
  cases g with
  | dot i => exact sChain_ddotL i
  | cross i j => exact sChain_dcrossL j i
  | cup i => exact ⟨rfl, rfl⟩
  | cap i => exact ⟨rfl, rfl⟩
  | lcross i j => exact sChain_lcrossL j i
  | dcup i n => exact sChain_dcupL i n
  | dcap i n => exact sChain_dcapL i n

def normal (t : k) (ν μ : X) (g : Shape I) (h : wt D μ g.dom = ν) :
    atWord (Sc := Sc) (sy := sy) (hc := hc) ν μ g.dom h ⟶
      atWord ν μ g.cod ((g.wt_dom_eq_wt_cod D μ).symm.trans h) :=
  coeff (D := D) t g • cl D Sc ν (rhoWord g.dom) (rhoWord g.cod) (layers g)

def generator (t : k) (ν μ : X) (g : Shape I) (h : wt D μ g.dom = ν) :
    rhoMap (sy := sy) (hc := hc) (psiWordAt (Sc := Sc) ν μ g.dom h) ⟶
      rhoMap (psiWordAt ν μ g.cod ((g.wt_dom_eq_wt_cod D μ).symm.trans h)) :=
  eqToHom (map_word ν μ g.dom h) ≫ normal t ν μ g h ≫
    eqToHom (map_word ν μ g.cod ((g.wt_dom_eq_wt_cod D μ).symm.trans h)).symm

theorem layers_parity (g : Shape I) : parsum (D := D) (layers g) = g.parity D := by
  cases g with
  | cross i j => simpa only [layers, Shape.parity, mul_comm] using parsum_dcrossL (D := D) j i
  | dot i | cup i | cap i | lcross i j | dcup i n | dcap i n =>
    simp [layers, ddotL, mateL, dotsL, whL, parsum, Shape.parity,
      dcupL, dcapL, lcrossL, mul_comm]

theorem normal_parity (t : k) (ν μ : X) (g : Shape I) (h : wt D μ g.dom = ν) :
    normal (Sc := Sc) (sy := sy) (hc := hc) t ν μ g h ∈ parity (R := k) _ _ (g.parity D) := by
  change coeff t g • cl D Sc ν _ _ _ ∈
    (pres D Sc).homDeg (Presentation.parityDeg (sig D)) _ _ (g.parity D + (0 + 0))
  simp only [add_zero]
  apply Submodule.smul_mem
  rw [cl_of (layers_chain g)]
  apply Presentation.diag_mem_homDeg'
  rw [degree_parity_mkD]
  exact layers_parity g

theorem shift_dom_cod (μ : X) (g : Shape I) : rhoShift sy μ g.dom = rhoShift sy μ g.cod := by
  cases g with
  | dot i => rfl
  | cross i j => exact rhoUpShift_swap μ i j
  | cup i | cap i | dcup i n | dcap i n =>
    simp [Shape.dom, Shape.cod, rhoShift, rhoLetterShift, wt, sh, D.cd.coroot_root_self]
    ring
  | lcross i j =>
    simp [Shape.dom, Shape.cod, rhoShift, rhoLetterShift, wt, sh, Datum.h]
    have hh := sy.symm i j
    simp only [Datum.d] at hh
    nlinarith

theorem layers_degree (ν μ : X) (g : Shape I) (h : wt D μ g.dom = ν) :
    gsum D sy ν (layers g) = gdeg D sy (g, μ) := by
  cases g with
  | dot i =>
    simp [layers, gsum, ddotL, mateL, dotsL, whL, gdeg, Datum.d_self]
    ring
  | cross i j =>
    simp [layers, gsum, dcrossL, sigmaL, whL, gdeg, Datum.d_self]
    ring
  | lcross i j => simp [layers, gdeg]
  | cup i | cap i | dcup i n | dcap i n =>
    have hn : ν = μ := by simpa [Shape.dom, wt, sh] using h.symm
    rw [hn]
    simp [layers, gsum, gdeg, dcupL, dcapL]

theorem normal_degree (t : k) (ν μ : X) (g : Shape I) (h : wt D μ g.dom = ν) :
    normal (Sc := Sc) (sy := sy) (hc := hc) t ν μ g h ∈
      GradedSupercategory.degree (R := k) _ _ (gdeg D sy (g, μ)) := by
  change coeff t g • cl D Sc ν _ _ _ ∈ (pres D Sc).homDeg (gdeg D sy) _ _
    (gdeg D sy (g, μ) + (rhoShift sy μ g.dom - rhoShift sy μ g.cod))
  rw [shift_dom_cod μ g, sub_self, add_zero]
  apply Submodule.smul_mem
  rw [← layers_degree ν μ g h]
  exact cl_mem_gdeg sy ν _ _ _

private theorem transport_parity {C : Type*} [Category C] [Preadditive C] [Linear k C]
    [Supercategory k C] {a b a' b' : C} (ha : a = a') (hb : b' = b) {p : ZMod 2}
    {η : a' ⟶ b'} (hη : η ∈ parity (R := k) _ _ p) :
    eqToHom ha ≫ η ≫ eqToHom hb ∈ parity (R := k) _ _ p := by
  subst a' b'
  simpa using hη

private theorem transport_degree {C : Type*} [Category C] [Preadditive C] [Linear k C]
    [Supercategory k C] [GradedSupercategory k C]
    {a b a' b' : C} (ha : a = a') (hb : b' = b) {n : ℤ}
    {η : a' ⟶ b'} (hη : η ∈ GradedSupercategory.degree (R := k) _ _ n) :
    eqToHom ha ≫ η ≫ eqToHom hb ∈ GradedSupercategory.degree (R := k) _ _ n := by
  subst a' b'
  simpa using hη

theorem generator_parity (t : k) (ν μ : X) (g : Shape I) (h : wt D μ g.dom = ν) :
    generator (Sc := Sc) (sy := sy) (hc := hc) t ν μ g h ∈ parity (R := k) _ _ (g.parity D) :=
  transport_parity _ _ (normal_parity t ν μ g h)

theorem generator_degree (t : k) (ν μ : X) (g : Shape I) (h : wt D μ g.dom = ν) :
    generator (Sc := Sc) (sy := sy) (hc := hc) t ν μ g h ∈
      GradedSupercategory.degree (R := k) _ _ (gdeg D sy (g, μ)) :=
  transport_degree _ _ (normal_degree t ν μ g h)

end OddMath.SKM.RhoGenerators
