import OddMath.SKM.Rho.LayerFormula

/-!
# Raw Formula for ρ

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

def imageLayers : List (LayerData I) → List (LayerData I)
  | [] => []
  | (u,g,v) :: L => (RhoGenerators.layers g).map (whL (rhoWord v) (rhoWord u)) ++ imageLayers L

def imageCoeff (t : k) : List (LayerData I) → k
  | [] => 1
  | (_,g,_) :: L => RhoGenerators.coeff (D := D) t g * imageCoeff t L

theorem image_chain {s r : List (Letter I)} {L : List (LayerData I)} (h : SChain s L r) :
    SChain (rhoWord s) (imageLayers L) (rhoWord r) := by
  induction L generalizing s with
  | nil => cases h; rfl
  | cons x L ih =>
    obtain ⟨rfl, h⟩ := h
    apply SChain.append (t' := rhoWord (x.1 ++ x.2.1.cod ++ x.2.2))
    · simpa only [rhoWord_append, List.append_assoc] using
        (RhoGenerators.layers_chain x.2.1).whisk (rhoWord x.2.2) (rhoWord x.1)
    · exact ih h

theorem comp_heq {C : Type*} [Category C] {a b c a' b' c' : C}
    (ha : a = a') (hb : b = b') (hc : c = c')
    {f : a ⟶ b} {g : b ⟶ c} {f' : a' ⟶ b'} {g' : b' ⟶ c'}
    (hf : HEq f f') (hg : HEq g g') : HEq (f ≫ g) (f' ≫ g') := by
  subst a' b' c'
  cases hf; cases hg
  rfl

theorem id_heq {C : Type*} [Category C] {a b : C} (h : a = b) : HEq (𝟙 a) (𝟙 b) := by
  cases h
  rfl

theorem raw_formula (t : k) (ν μ : X) (L : List (LayerData I))
    {s r : List (Letter I)} (hs : wt D μ s = ν) (hr : wt D μ r = ν) (h : SChain s L r) :
    HEq (rhoRaw (sy := sy) (hc := hc) t ν μ L hs hr h)
      (imageCoeff (D := D) t L • cl D Sc ν (rhoWord s) (rhoWord r) (imageLayers L)) := by
  induction L generalizing s with
  | nil =>
    cases h
    simp only [rhoRaw, eqToHom_refl, imageCoeff, imageLayers, one_smul, cl_nil]
    exact id_heq (congrArg (pres D Sc).obj (at_obj ν μ r hr))
  | cons x L ih =>
    obtain ⟨rfl, h⟩ := h
    simp only [rhoRaw, eqToHom_refl, Category.id_comp]
    have H := comp_heq
      (congrArg (pres D Sc).obj (at_obj (Sc := Sc) (sy := sy) (hc := hc) ν μ _ hs))
      (congrArg (pres D Sc).obj (at_obj (Sc := Sc) (sy := sy) (hc := hc) ν μ _ _))
      (congrArg (pres D Sc).obj (at_obj (Sc := Sc) (sy := sy) (hc := hc) ν μ _ hr))
      (layer_formula t ν μ x.1 x.2.1 x.2.2 hs) (ih _ h)
    refine H.trans (heq_of_eq ?_)
    rw [Linear.smul_comp, Linear.comp_smul, cl_comp]
    · exact smul_smul _ _ _
    · simpa only [rhoWord_append, List.append_assoc] using
        (RhoGenerators.layers_chain x.2.1).whisk (rhoWord x.2.2) (rhoWord x.1)
    · exact image_chain h

end OddMath.SKM.RhoInversionKernel
