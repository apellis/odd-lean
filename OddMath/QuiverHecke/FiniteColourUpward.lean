/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.FiniteColourBubbles
import OddMath.QuiverHecke.UpwardCoefficientDetection
import OddMath.QuiverHecke.WeightedCoefficientSeparation
import OddMath.QuiverHecke.AlphaPositional
import OddMath.QuiverHecke.HomDimension

/-!
# Finite-colour detection of upward coefficient independence

Brundan–Ellis, *Super Kac–Moody 2-categories*, Definition 1.5 and the Nondegeneracy
Conjecture (§11). The upward evaluation `upwardCoefficientMap` of the coefficient-extended
quiver Hecke category is injective for a Cartan datum as soon as it is injective for every
restriction of the datum to a finite set of colours.

The upward image of `a ⊗ x^l ψ_w`, with `a` a product of a word of coefficient generators,
is the value of an explicit formal sum of normal-form layer lists (`termS`); colour inclusion
carries the formal sums of a restriction onto those of the full datum. A vanishing upward
image therefore vanishes in a sufficiently large finite restriction (`evS_eq_zero_restrict`),
and the inclusion of coefficient-extended Hom spaces (`coefficientInclude`) carries the
restricted element back to the original one.
-/

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams Categorification.TypeA SKM.FiniteColour
open scoped Classical TensorProduct

/-! ## Positioned generators under a map of colours -/

section Map
variable {I I' : Type*} (f : I → I')

/-- A map of colours on generating shapes. -/
def Shape.map : Shape I → Shape I'
  | .dot i => .dot (f i)
  | .cross i j => .cross (f i) (f j)

/-- A map of colours on layers. -/
def layerMap (x : LayerData I) : LayerData I' := (x.1.map f, Shape.map f x.2.1, x.2.2.map f)

theorem PG.act_map (g : PG) (t : List I) : g.act (t.map f) = (g.act t).map f := by
  cases g with
  | dot p => rfl
  | cross a =>
    simp only [PG.act, ← List.map_drop]
    rcases h : t.drop a with _ | ⟨x, _ | ⟨y, r⟩⟩ <;> simp [List.map_take]

theorem PG.ld_map (g : PG) (t : List I) : g.ld (t.map f) = (g.ld t).map (layerMap f) := by
  cases g with
  | dot p =>
    simp only [PG.ld, ← List.map_drop]
    rcases h : t.drop p with _ | ⟨x, r⟩ <;> simp [layerMap, Shape.map, List.map_take]
  | cross a =>
    simp only [PG.ld, ← List.map_drop]
    rcases h : t.drop a with _ | ⟨x, _ | ⟨y, r⟩⟩ <;> simp [layerMap, Shape.map, List.map_take]

theorem pl_map (t : List I) (gs : List PG) : pl (t.map f) gs = (pl t gs).map (layerMap f) := by
  induction gs generalizing t with
  | nil => rfl
  | cons g gs ih => rw [pl_cons, pl_cons, PG.ld_map, PG.act_map, ih, List.map_append]

theorem tgt_map (t : List I) (gs : List PG) : tgt (t.map f) gs = (tgt t gs).map f := by
  induction gs generalizing t with
  | nil => rfl
  | cons g gs ih => rw [tgt_cons, tgt_cons, PG.act_map, ih]

end Map

/-! ## Normal-form indices of a restriction -/

section Restrict
universe u
variable {I : Type u} (J : Finset I)

theorem upWord_map (t : List J) : (upWord t).map (letter J) = upWord (t.map Subtype.val) := by
  simp [upWord, letter, Function.comp_def]

theorem upLayers_layerMap (ls : List (LayerData J)) :
    upLayers (ls.map (layerMap Subtype.val)) = (upLayers ls).map (layerData J) := by
  simp only [upLayers, List.map_map]
  refine List.map_congr_left fun x _ => ?_
  obtain ⟨a, g, b⟩ := x
  cases g <;> simp [layerMap, layerData, Shape.map, Shape.toSKM, shape, upWord, letter,
    Function.comp_def]

theorem canWord_congr {n m : ℕ} (h : n = m) (w : Equiv.Perm (Fin n)) :
    canWord n w = canWord m ((finCongr h).permCongr w) := by
  subst h
  congr 1

theorem exists_map_val_eq (t : List I) (h : ∀ i ∈ t, i ∈ J) :
    ∃ t' : List J, t'.map Subtype.val = t :=
  ⟨t.attach.map fun x => ⟨x.1, h x.1 x.2⟩, by simp⟩

variable {J}

theorem length_map_val (t : List J) : t.length = (t.map Subtype.val).length :=
  (List.length_map _).symm

/-- A normal-form index of a restriction, as an index of the full datum. -/
def NFIdx.push {t t' : List J} (i : NFIdx t t') :
    NFIdx (t.map Subtype.val) (t'.map Subtype.val) :=
  ⟨(i.1.1, (finCongr (length_map_val t)).permCongr i.1.2), i.2.1,
    fun x hx => length_map_val t ▸ i.2.2.1 x hx, by
      have e := tgt_eq i.2.2.2
      have hc := sChain_pl (t.map Subtype.val) (i.1.1.map PG.dot ++ cw (canWord t.length i.1.2))
      rw [tgt_map, e, canWord_congr (length_map_val t)] at hc
      exact hc⟩

/-- A normal-form index of the full datum on restricted words, as an index of the
restriction. -/
def NFIdx.lift {t t' : List J} (i : NFIdx (t.map Subtype.val) (t'.map Subtype.val)) :
    NFIdx t t' :=
  ⟨(i.1.1, (finCongr (length_map_val t).symm).permCongr i.1.2), i.2.1,
    fun x hx => (length_map_val t).symm ▸ i.2.2.1 x hx, by
      have e := tgt_eq i.2.2.2
      rw [canWord_congr (length_map_val t).symm, tgt_map] at e
      have hc := sChain_pl t (i.1.1.map PG.dot ++
        cw (canWord t.length ((finCongr (length_map_val t).symm).permCongr i.1.2)))
      rwa [List.map_injective_iff.mpr Subtype.val_injective e] at hc⟩

theorem NFIdx.push_lift {t t' : List J} (i : NFIdx (t.map Subtype.val) (t'.map Subtype.val)) :
    i.lift.push = i := by
  apply Subtype.ext
  refine Prod.ext rfl ?_
  ext x
  simp [NFIdx.push, NFIdx.lift]

theorem NFIdx.gens_lift {t t' : List J} (i : NFIdx (t.map Subtype.val) (t'.map Subtype.val)) :
    i.lift.gens = i.gens := by
  simp only [NFIdx.gens, NFIdx.lift]
  rw [← canWord_congr]

end Restrict

/-! ## Upward images as formal sums -/

universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cs : SKM.CScalars Sc)

variable {D Sc} in
/-- The upward image of `a ⊗ ψ`, for `a` the product of the word `w` and `ψ` the class of
the positioned generators `gs`, as a formal sum. -/
def termS (μ : X) (t : List I) (w : List (SKM.SYMGen D)) (gs : List PG) :
    List (k × List (SKM.LayerData I)) :=
  compS (upWord t) (upWord t) (whS (upWord t) (wordS cs μ w)) [(1, upLayers (pl t gs))]

theorem evS_termS (μ : X) {t t' : List I} (w : List (SKM.SYMGen D)) (gs : List PG)
    (h : SChain t (pl t gs) t') :
    evS D Sc μ (upWord t) (upWord t') (termS cs μ t w gs) =
      SKM.bubAt D Sc μ (upWord t) (SKM.betaSYM cs μ ((w.map (SKM.SYM.ι D k)).prod)) ≫
        (alpha D Sc μ).map (cl D Sc t t' gs h) := by
  rw [termS, evS_compS, evS_whS, evS_wordS, evS_single, one_smul, alpha_cl]

theorem evS_termS_nf (μ : X) {t t' : List I} (w : List (SKM.SYMGen D)) (i : NFIdx t t') :
    evS D Sc μ (upWord t) (upWord t') (termS cs μ t w i.gens) =
      SKM.bubAt D Sc μ (upWord t) (SKM.betaSYM cs μ ((w.map (SKM.SYM.ι D k)).prod)) ≫
        (alpha D Sc μ).map i.nf :=
  evS_termS D Sc cs μ w i.gens i.2.2.2

theorem pushS_termS (J : Finset I) (μ : X) (t : List J)
    (w : List (SKM.SYMGen (D.restrictColours J))) (gs : List PG) :
    pushS J (termS (cs.restrictColours D J Sc) μ t w gs) =
      termS cs μ (t.map Subtype.val) (w.map (genMap J)) gs := by
  simp only [termS, pushS_compS, pushS_whS, pushS_wordS, upWord_map]
  congr 1
  rw [pl_map, upLayers_layerMap]
  rfl

/-- The upward image of a finite combination of products of generator words and normal
forms is the value of an explicit formal sum. -/
theorem upwardCoefficientMap_list (μ : X) (t t' : List I)
    (L : List (k × List (SKM.SYMGen D) × NFIdx t t')) :
    upwardCoefficientMap D Sc cs μ t t'
        ((L.map fun q => q.1 • sourceCoefficientHom D Sc
          ((q.2.1.map (SKM.SYM.ι D k)).prod) q.2.2.nf).sum) =
      evS D Sc μ (upWord t) (upWord t')
        (L.flatMap fun q => smulS q.1 (termS cs μ t q.2.1 q.2.2.gens)) := by
  induction L with
  | nil => simp
  | cons q L ih =>
    rw [List.map_cons, List.sum_cons, map_add, map_smul, upwardCoefficientMap_source, ih,
      List.flatMap_cons, evS_append, evS_smulS, evS_termS_nf]

/-- Every coefficient-extended morphism is a finite combination of products of generator
words and normal forms. -/
theorem exists_list_eq (t t' : List I) (x : coefficientObj D Sc t ⟶ coefficientObj D Sc t') :
    ∃ L : List (k × List (SKM.SYMGen D) × NFIdx t t'),
      x = (L.map fun q => q.1 • sourceCoefficientHom D Sc
        ((q.2.1.map (SKM.SYM.ι D k)).prod) q.2.2.nf).sum := by
  let v : List (SKM.SYMGen D) × NFIdx t t' → (coefficientObj D Sc t ⟶ coefficientObj D Sc t') :=
    fun q => sourceCoefficientHom D Sc ((q.1.map (SKM.SYM.ι D k)).prod) q.2.nf
  have hspan : Submodule.span k (Set.range v) = ⊤ := by
    rw [eq_top_iff, ← (extensionBasis D Sc t t').span_eq, Submodule.span_le]
    rintro _ ⟨⟨a, i⟩, rfl⟩
    rw [extensionBasis_apply]
    let φ : SKM.SYM D k →ₗ[k] (coefficientObj D Sc t ⟶ coefficientObj D Sc t') :=
      (sourceTensorEquiv D Sc t t').toLinearMap ∘ₗ (TensorProduct.mk k _ _).flip i.nf
    have hφ : ∀ s, φ s = sourceCoefficientHom D Sc s i.nf := fun _ => rfl
    have ha : SKM.SYM.coefficientBasis D k a ∈
        Submodule.span k (Set.range fun w : List (SKM.SYMGen D) =>
          (w.map (SKM.SYM.ι D k)).prod) := by
      rw [span_wordProd]; trivial
    have hm := Submodule.mem_map_of_mem (f := φ) ha
    rw [Submodule.map_span, hφ] at hm
    refine Submodule.span_mono ?_ hm
    rintro _ ⟨_, ⟨w, rfl⟩, rfl⟩
    exact ⟨(w, i), rfl⟩
  have hx : x ∈ Submodule.span k (Set.range v) := by rw [hspan]; trivial
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hx
  refine ⟨c.support.toList.map fun q => (c q, q.1, q.2), ?_⟩
  rw [← hc, Finsupp.sum, List.map_map, Finset.sum_map_toList]
  rfl

/-! ## Inclusion of coefficient-extended Hom spaces -/

section Include
variable (J : Finset I) (t t' : List J)

/-- Inclusion of quiver Hecke Hom spaces of a restriction, on the normal-form basis. -/
def homInclude :
    ((pres (D.restrictColours J) (Sc.restrictColours D J)).obj (ob _ t) ⟶
        (pres (D.restrictColours J) (Sc.restrictColours D J)).obj (ob _ t')) →ₗ[k]
      ((pres D Sc).obj (ob D (t.map Subtype.val)) ⟶
        (pres D Sc).obj (ob D (t'.map Subtype.val))) :=
  (basisNF (D.restrictColours J) (Sc.restrictColours D J) t t').constr k fun i => i.push.nf

theorem homInclude_nf (i : NFIdx (t.map Subtype.val) (t'.map Subtype.val)) :
    homInclude D Sc J t t' i.lift.nf = i.nf := by
  rw [homInclude, ← basisNF_apply, Module.Basis.constr_basis, NFIdx.push_lift]

/-- Inclusion of coefficient-extended Hom spaces of a restriction. -/
def coefficientInclude :
    (coefficientObj (D.restrictColours J) (Sc.restrictColours D J) t ⟶
        coefficientObj (D.restrictColours J) (Sc.restrictColours D J) t') →ₗ[k]
      (coefficientObj D Sc (t.map Subtype.val) ⟶ coefficientObj D Sc (t'.map Subtype.val)) :=
  (sourceTensorEquiv D Sc _ _).toLinearMap ∘ₗ
    TensorProduct.map (symRestrict D J k).toLinearMap (homInclude D Sc J t t') ∘ₗ
      (sourceTensorEquiv (D.restrictColours J) (Sc.restrictColours D J) t t').symm.toLinearMap

theorem coefficientInclude_source (a : SKM.SYM (D.restrictColours J) k)
    (f : (pres (D.restrictColours J) (Sc.restrictColours D J)).obj (ob _ t) ⟶
      (pres (D.restrictColours J) (Sc.restrictColours D J)).obj (ob _ t')) :
    coefficientInclude D Sc J t t' (sourceCoefficientHom _ _ a f) =
      sourceCoefficientHom D Sc (symRestrict D J k a) (homInclude D Sc J t t' f) := by
  have e : (sourceTensorEquiv (D.restrictColours J) (Sc.restrictColours D J) t t').symm
      (sourceCoefficientHom _ _ a f) = a ⊗ₜ f :=
    (LinearEquiv.symm_apply_eq _).mpr rfl
  simp only [coefficientInclude, LinearMap.comp_apply, LinearEquiv.coe_coe, e,
    TensorProduct.map_tmul, sourceTensorEquiv_tmul, AlgHom.toLinearMap_apply]

end Include

/-! ## Detection -/

/-- **Finite-colour detection of upward coefficient independence.** If the upward
evaluation is injective on every finite-colour restriction of the words `t`, `t'`, it is
injective for the full datum. -/
theorem upwardCoefficientMap_injective_of_restrictColours (μ : X) (t t' : List I)
    (h : ∀ (J : Finset I) (tJ t'J : List J), tJ.map Subtype.val = t →
      t'J.map Subtype.val = t' →
      Function.Injective (upwardCoefficientMap (D.restrictColours J) (Sc.restrictColours D J)
        (cs.restrictColours D J Sc) μ tJ t'J)) :
    Function.Injective (upwardCoefficientMap D Sc cs μ t t') := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨L, rfl⟩ := exists_list_eq D Sc t t' x
  rw [upwardCoefficientMap_list] at hx
  obtain ⟨J₁, hJ₁⟩ := evS_eq_zero_restrict D Sc μ _ _ _ hx
  obtain ⟨J, hJ₁J, htJ, ht'J, hw⟩ : ∃ J : Finset I, J₁ ⊆ J ∧ (∀ i ∈ t, i ∈ J) ∧
      (∀ i ∈ t', i ∈ J) ∧ ∀ q ∈ L, ∀ g ∈ q.2.1, genColour g ∈ J := by
    refine ⟨J₁ ∪ t.toFinset ∪ t'.toFinset ∪ (L.flatMap fun q => q.2.1.map genColour).toFinset,
      fun i hi => by simp [hi], fun i hi => by simp [hi], fun i hi => by simp [hi], ?_⟩
    intro q hq g hg
    simp only [Finset.mem_union, List.mem_toFinset, List.mem_flatMap, List.mem_map]
    exact Or.inr ⟨q, hq, g, hg, rfl⟩
  obtain ⟨tJ, rfl⟩ := exists_map_val_eq J t htJ
  obtain ⟨t'J, rfl⟩ := exists_map_val_eq J t' ht'J
  let lw : List (SKM.SYMGen D) → List (SKM.SYMGen (D.restrictColours J)) := fun w =>
    if hw : ∀ g ∈ w, genColour g ∈ J then Classical.choose (exists_map_genMap_eq J w hw)
    else []
  have hlw : ∀ q ∈ L, (lw q.2.1).map (genMap J) = q.2.1 := by
    intro q hq
    simp only [lw]
    split_ifs with h'
    · exact Classical.choose_spec (exists_map_genMap_eq J q.2.1 h')
    · exact absurd (hw q hq) h'
  let LJ := L.map fun q => (q.1, lw q.2.1, q.2.2.lift)
  have hup : upwardCoefficientMap (D.restrictColours J) (Sc.restrictColours D J)
      (cs.restrictColours D J Sc) μ tJ t'J
        ((LJ.map fun q => q.1 • sourceCoefficientHom _ _
          ((q.2.1.map (SKM.SYM.ι _ k)).prod) q.2.2.nf).sum) = 0 := by
    rw [upwardCoefficientMap_list]
    refine hJ₁ J hJ₁J _ _ _ (upWord_map J tJ) (upWord_map J t'J) ?_
    simp only [pushS, LJ, List.map_flatMap, List.flatMap_map]
    refine List.flatMap_congr fun q hq => ?_
    rw [← pushS, pushS_smulS, pushS_termS, hlw q hq, NFIdx.gens_lift]
  have h0 := h J tJ t'J rfl rfl (hup.trans (map_zero _).symm)
  have hx' : coefficientInclude D Sc J tJ t'J
      ((LJ.map fun q => q.1 • sourceCoefficientHom _ _
          ((q.2.1.map (SKM.SYM.ι _ k)).prod) q.2.2.nf).sum) =
      (L.map fun q => q.1 • sourceCoefficientHom D Sc
          ((q.2.1.map (SKM.SYM.ι D k)).prod) q.2.2.nf).sum := by
    rw [map_list_sum, List.map_map, List.map_map]
    congr 1
    refine List.map_congr_left fun q hq => ?_
    simp only [Function.comp_apply, map_smul, coefficientInclude_source, symRestrict_prod,
      hlw q hq, homInclude_nf]
  rw [← hx', h0, map_zero]

end OddMath.QuiverHecke
