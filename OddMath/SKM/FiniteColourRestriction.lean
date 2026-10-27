/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.FiniteColourRelations
import OddMath.SKM.MoreGenerators
import StringDiagrams.LayerMap.Generators

/-!
# Restriction to a finite colour subtype

The finite-witness step of `SwappedActionAssembly`, §8, for the presentation
of Brundan–Ellis, Definition 1.5. Only the colour type is restricted: the
weight group, all region labels, roots, coroots and coefficient ring are
unchanged. No independence of the roots or nontriviality of the ring is used.
-/

noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : Datum I X)
variable (J : Finset I)

/-- The induced datum on a finite colour subtype, with the original weight group. -/
def Datum.restrictColours : Datum J X where
  cd :=
    { root := fun i => D.α i.val
      coroot := fun i => D.cd.coroot i.val
      coroot_root_self := fun i => D.cd.coroot_root_self i.val }
  isGCM :=
    { diag := fun i => D.isGCM.diag i.val
      offDiag_nonpos := fun i j hij =>
        D.isGCM.offDiag_nonpos i.val j.val (fun h => hij (Subtype.ext h))
      zero_comm := fun i j => D.isGCM.zero_comm i.val j.val }
  parity := fun i => D.parity i.val
  even_of_odd := fun i j hi => D.even_of_odd i.val j.val hi

variable {k : Type w} [CommRing k] (Sc : Scalars D k)

/-- Restrict the parameters, without changing the ground ring. -/
def Scalars.restrictColours : Scalars (D.restrictColours J) k where
  t i j := Sc.t i.val j.val
  t_self i := Sc.t_self i.val
  t_symm_of_d_eq_zero i j h := Sc.t_symm_of_d_eq_zero i.val j.val h
  s i j := Sc.s i.val j.val
  s_symm i j := Sc.s_symm i.val j.val
  s_eq_zero i j := Sc.s_eq_zero i.val j.val
  two_isUnit h := Sc.two_isUnit (by obtain ⟨i, hi⟩ := h; exact ⟨i.val, hi⟩)

/-- Restriction of the normalized bubble parameters (1.17). -/
def CScalars.restrictColours (cs : CScalars Sc) : CScalars (Sc.restrictColours D J) where
  c μ i := cs.c μ i.val
  shift μ i j := cs.shift μ i.val j.val

namespace FiniteColour

/-- Inclusion of signed letters. -/
def letter (l : Letter J) : Letter I := (l.1, l.2.val)

/-- Inclusion of generating shapes. -/
def shape : Shape J → Shape I
  | .dot i => .dot i.val
  | .cross i j => .cross i.val j.val
  | .cup i => .cup i.val
  | .cap i => .cap i.val
  | .lcross i j => .lcross i.val j.val
  | .dcup i n => .dcup i.val n
  | .dcap i n => .dcap i.val n

@[simp] theorem shape_dom (g : Shape J) : (shape J g).dom = g.dom.map (letter J) := by
  cases g <;> rfl

@[simp] theorem shape_cod (g : Shape J) : (shape J g).cod = g.cod.map (letter J) := by
  cases g <;> rfl

@[simp] theorem shape_parity (g : Shape J) :
    (shape J g).parity D = g.parity (D.restrictColours J) := by
  cases g <;> rfl

@[simp] theorem sh_letter (l : Letter J) : sh D (letter J l) = sh (D.restrictColours J) l := rfl

@[simp] theorem wt_letters (μ : X) (t : List (Letter J)) :
    wt D μ (t.map (letter J)) = wt (D.restrictColours J) μ t := by
  induction t with
  | nil => rfl
  | cons l t ih => simp only [List.map_cons, wt_cons, sh_letter, ih]

/-- Inclusion of region-labelled strands; the region is not reindexed. -/
def colour (c : Col J X) : Col I X := ⟨letter J c.l, c.r⟩

@[simp] theorem wd_letters (μ : X) (t : List (Letter J)) :
    wd D μ (t.map (letter J)) = (wd (D.restrictColours J) μ t).map (colour J) := by
  induction t with
  | nil => rfl
  | cons l t ih => simp only [List.map_cons, wd_cons, wt_letters, ih]; rfl

/-- The inclusion of the finite-colour signature, hence of all free diagrams. -/
def inclusion : SigMap (sig (D.restrictColours J)) (sig D) where
  region := id
  colour := colour J
  colourSrc _ := rfl
  colourTgt _ := rfl
  gen g := (shape J g.1, g.2)
  dom g := by
    change wd D g.2 (shape J g.1).dom = _
    rw [shape_dom, wd_letters]; rfl
  cod g := by
    change wd D g.2 (shape J g.1).cod = _
    rw [shape_cod, wd_letters]; rfl
  left g := by
    change wt D g.2 (shape J g.1).dom = _
    rw [shape_dom, wt_letters]; rfl
  right _ := rfl

/-- Inclusion preserves precisely the parity used in superinterchange. -/
theorem inclusion_odd (g : (sig (D.restrictColours J)).Gen) :
    (sig D).odd ((inclusion D J).gen g) = (sig (D.restrictColours J)).odd g := by
  change decide ((shape J g.1).parity D = 1) = decide (g.1.parity _ = 1)
  rw [shape_parity]

/-- Inclusion of every defining relation label, retaining its original region,
integer windows and all scalar parameters. -/
def relationLabel : Rel (D.restrictColours J) → Rel D
  | .quadEq i ν => .quadEq i.val ν
  | .quadZero i j ν hij hd => .quadZero i.val j.val ν (fun h => hij (Subtype.ext h)) hd
  | .quadNe i j ν hij hd => .quadNe i.val j.val ν (fun h => hij (Subtype.ext h)) hd
  | .slideL i j ν hij => .slideL i.val j.val ν (fun h => hij (Subtype.ext h))
  | .slideLEq i ν => .slideLEq i.val ν
  | .slideR i j ν hij => .slideR i.val j.val ν (fun h => hij (Subtype.ext h))
  | .slideREq i ν => .slideREq i.val ν
  | .braid i j l ν h => .braid i.val j.val l.val ν (fun ⟨hil, hij⟩ => h ⟨Subtype.ext hil, fun e => hij (congrArg Subtype.val e)⟩)
  | .braidEq i j ν hij => .braidEq i.val j.val ν (fun h => hij (Subtype.ext h))
  | .zigE i ν => .zigE i.val ν
  | .zigF i ν => .zigF i.val ν
  | .invNe₁ i j ν hij => .invNe₁ i.val j.val ν (fun h => hij (Subtype.ext h))
  | .invNe₂ i j ν hij => .invNe₂ i.val j.val ν (fun h => hij (Subtype.ext h))
  | .invP₁ i ν hh => .invP₁ i.val ν hh
  | .invP₂ i ν hh => .invP₂ i.val ν hh
  | .invP₃ i ν m hm => .invP₃ i.val ν m hm
  | .invP₄ i ν n hn => .invP₄ i.val ν n hn
  | .invP₅ i ν m n hm hn => .invP₅ i.val ν m n hm hn
  | .invM₁ i ν hh => .invM₁ i.val ν hh
  | .invM₂ i ν hh => .invM₂ i.val ν hh
  | .invM₃ i ν m hm => .invM₃ i.val ν m hm
  | .invM₄ i ν n hn => .invM₄ i.val ν n hn
  | .invM₅ i ν m n hm hn => .invM₅ i.val ν m n hm hn
  | .dcupZero i ν n hn => .dcupZero i.val ν n hn
  | .dcapZero i ν n hn => .dcapZero i.val ν n hn

/-- Restrict a raw relation label whose complete parameter support lies in `J`.
The proof uses the label support, never the support of its linear expansion. -/
def restrictLabel (r : Rel D) (hr : ∀ i ∈ r.colours, i ∈ J) :
    Rel (D.restrictColours J) := by
  cases r with
  | quadEq i ν =>
    let i' : J := ⟨i, hr i (by simp [Rel.colours])⟩
    exact .quadEq i' ν
  | quadZero i j ν hij hd =>
    let i' : J := ⟨i, hr i (by simp [Rel.colours])⟩
    let j' : J := ⟨j, hr j (by simp [Rel.colours])⟩
    exact .quadZero i' j' ν (fun e => hij (congrArg Subtype.val e)) hd
  | quadNe i j ν hij hd =>
    let i' : J := ⟨i, hr i (by simp [Rel.colours])⟩
    let j' : J := ⟨j, hr j (by simp [Rel.colours])⟩
    exact .quadNe i' j' ν (fun e => hij (congrArg Subtype.val e)) hd
  | slideL i j ν hij =>
    let i' : J := ⟨i, hr i (by simp [Rel.colours])⟩
    let j' : J := ⟨j, hr j (by simp [Rel.colours])⟩
    exact .slideL i' j' ν (fun e => hij (congrArg Subtype.val e))
  | slideLEq i ν =>
    let i' : J := ⟨i, hr i (by simp [Rel.colours])⟩
    exact .slideLEq i' ν
  | slideR i j ν hij =>
    let i' : J := ⟨i, hr i (by simp [Rel.colours])⟩
    let j' : J := ⟨j, hr j (by simp [Rel.colours])⟩
    exact .slideR i' j' ν (fun e => hij (congrArg Subtype.val e))
  | slideREq i ν =>
    let i' : J := ⟨i, hr i (by simp [Rel.colours])⟩
    exact .slideREq i' ν
  | braid i j l ν h =>
    let i' : J := ⟨i, hr i (by simp [Rel.colours])⟩
    let j' : J := ⟨j, hr j (by simp [Rel.colours])⟩
    let l' : J := ⟨l, hr l (by simp [Rel.colours])⟩
    exact .braid i' j' l' ν (fun ⟨hil, hij⟩ => h ⟨congrArg Subtype.val hil, fun e => hij (Subtype.ext e)⟩)
  | braidEq i j ν hij =>
    let i' : J := ⟨i, hr i (by simp [Rel.colours])⟩
    let j' : J := ⟨j, hr j (by simp [Rel.colours])⟩
    exact .braidEq i' j' ν (fun e => hij (congrArg Subtype.val e))
  | zigE i ν =>
    let i' : J := ⟨i, hr i (by simp [Rel.colours])⟩
    exact .zigE i' ν
  | zigF i ν =>
    let i' : J := ⟨i, hr i (by simp [Rel.colours])⟩
    exact .zigF i' ν
  | invNe₁ i j ν hij =>
    let i' : J := ⟨i, hr i (by simp [Rel.colours])⟩
    let j' : J := ⟨j, hr j (by simp [Rel.colours])⟩
    exact .invNe₁ i' j' ν (fun e => hij (congrArg Subtype.val e))
  | invNe₂ i j ν hij =>
    let i' : J := ⟨i, hr i (by simp [Rel.colours])⟩
    let j' : J := ⟨j, hr j (by simp [Rel.colours])⟩
    exact .invNe₂ i' j' ν (fun e => hij (congrArg Subtype.val e))
  | invP₁ i ν hh =>
    let i' : J := ⟨i, hr i (by simp [Rel.colours])⟩
    exact .invP₁ i' ν hh
  | invP₂ i ν hh =>
    let i' : J := ⟨i, hr i (by simp [Rel.colours])⟩
    exact .invP₂ i' ν hh
  | invP₃ i ν m hm =>
    let i' : J := ⟨i, hr i (by simp [Rel.colours])⟩
    exact .invP₃ i' ν m hm
  | invP₄ i ν n hn =>
    let i' : J := ⟨i, hr i (by simp [Rel.colours])⟩
    exact .invP₄ i' ν n hn
  | invP₅ i ν m n hm hn =>
    let i' : J := ⟨i, hr i (by simp [Rel.colours])⟩
    exact .invP₅ i' ν m n hm hn
  | invM₁ i ν hh =>
    let i' : J := ⟨i, hr i (by simp [Rel.colours])⟩
    exact .invM₁ i' ν hh
  | invM₂ i ν hh =>
    let i' : J := ⟨i, hr i (by simp [Rel.colours])⟩
    exact .invM₂ i' ν hh
  | invM₃ i ν m hm =>
    let i' : J := ⟨i, hr i (by simp [Rel.colours])⟩
    exact .invM₃ i' ν m hm
  | invM₄ i ν n hn =>
    let i' : J := ⟨i, hr i (by simp [Rel.colours])⟩
    exact .invM₄ i' ν n hn
  | invM₅ i ν m n hm hn =>
    let i' : J := ⟨i, hr i (by simp [Rel.colours])⟩
    exact .invM₅ i' ν m n hm hn
  | dcupZero i ν n hn =>
    let i' : J := ⟨i, hr i (by simp [Rel.colours])⟩
    exact .dcupZero i' ν n hn
  | dcapZero i ν n hn =>
    let i' : J := ⟨i, hr i (by simp [Rel.colours])⟩
    exact .dcapZero i' ν n hn

/-- Restriction followed by inclusion returns the original raw relation. -/
@[simp] theorem relationLabel_restrictLabel (r : Rel D)
    (hr : ∀ i ∈ r.colours, i ∈ J) :
    relationLabel D J (restrictLabel D J r hr) = r := by
  cases r <;> rfl

@[simp] theorem relationLabel_dom (r : Rel (D.restrictColours J)) :
    (relationLabel D J r).dom = r.dom.map (letter J) := by
  cases r <;> rfl

@[simp] theorem relationLabel_cod (r : Rel (D.restrictColours J)) :
    (relationLabel D J r).cod = r.cod.map (letter J) := by
  cases r <;> rfl

@[simp] theorem relationLabel_region (r : Rel (D.restrictColours J)) :
    (relationLabel D J r).ν = r.ν := by
  cases r <;> rfl

/-- Inclusion on objects in normal form. -/
@[simp] theorem inclusion_ob (μ : X) (t : List (Letter J)) :
    (inclusion D J).obj (ob (D.restrictColours J) μ t) = ob D μ (t.map (letter J)) := by
  apply Obj.ext
  · exact (wt_letters D J μ t).symm
  · exact (wd_letters D J μ t).symm

/-- Inclusion of normal-form layer data. -/
def layerData (x : LayerData J) : LayerData I :=
  (x.1.map (letter J), shape J x.2.1, x.2.2.map (letter J))

/-- A well-formed normal-form chain remains well formed under inclusion. -/
theorem chain_map {t t' : List (Letter J)} {ls : List (LayerData J)}
    (h : SChain t ls t') :
    SChain (t.map (letter J)) (ls.map (layerData J)) (t'.map (letter J)) := by
  induction ls generalizing t with
  | nil => exact congrArg (List.map (letter J)) h
  | cons x ls ih =>
    obtain ⟨rfl, h⟩ := h
    refine ⟨?_, ?_⟩
    · simp [layerData]
    · simpa [layerData] using ih h

@[simp] theorem inclusion_lay (μ : X) (u : List (Letter J)) (g : Shape J)
    (v : List (Letter J)) :
    (inclusion D J).layer (lay (D.restrictColours J) μ u g v) =
      lay D μ (u.map (letter J)) (shape J g) (v.map (letter J)) := by
  simp [SigMap.layer, inclusion, lay, shape_dom, ← List.map_append,
    wt_letters, wd_letters]

/-- Inclusion of a free diagram, expressed at its normal-form boundary words. -/
def diagram {μ : X} {t t' : List (Letter J)}
    (d : ob (D.restrictColours J) μ t ⟶ ob (D.restrictColours J) μ t') :
    ob D μ (t.map (letter J)) ⟶ ob D μ (t'.map (letter J)) :=
  Diagram.cast ((inclusion D J).toLayerMap.map d)
    (inclusion_ob D J μ t) (inclusion_ob D J μ t')

/-- Inclusion preserves the full layer list, including interior cup/cap vertices. -/
@[simp] theorem diagram_mkD (μ : X) {t t' : List (Letter J)}
    (ls : List (LayerData J)) (h : SChain t ls t') :
    diagram D J (mkD (D.restrictColours J) μ ls h) =
      mkD D μ (ls.map (layerData J)) (chain_map J h) := by
  apply Diagram.ext
  change ((layList (D.restrictColours J) μ ls).map (inclusion D J).layer) = _
  simp only [layers_mkD, layList, List.map_map]
  apply List.map_congr_left
  intro x _
  exact inclusion_lay D J μ x.1 x.2.1 x.2.2

/-- The induced linear map on normal-form free Hom spaces. -/
def linear (μ : X) (t t' : List (Letter J)) :
    LinDiagram k (ob (D.restrictColours J) μ t) (ob (D.restrictColours J) μ t') →ₗ[k]
      LinDiagram k (ob D μ (t.map (letter J))) (ob D μ (t'.map (letter J))) :=
  Finsupp.lmapDomain k k (diagram D J)

@[simp] theorem linear_of (μ : X) {t t' : List (Letter J)}
    (d : ob (D.restrictColours J) μ t ⟶ ob (D.restrictColours J) μ t') :
    linear D J μ t t' (LinDiagram.of d : LinDiagram k _ _) =
      LinDiagram.of (diagram D J d) := Finsupp.mapDomain_single

@[simp] theorem diagram_id (μ : X) (t : List (Letter J)) :
    diagram D J (𝟙 (ob (D.restrictColours J) μ t)) = 𝟙 _ := rfl

@[simp] theorem linear_sub (μ : X) (t t' : List (Letter J))
    (f g : LinDiagram k (ob (D.restrictColours J) μ t) (ob (D.restrictColours J) μ t')) :
    linear D J μ t t' (f - g) = linear D J μ t t' f - linear D J μ t t' g :=
  (linear D J μ t t').map_sub f g

@[simp] theorem linear_add (μ : X) (t t' : List (Letter J))
    (f g : LinDiagram k (ob (D.restrictColours J) μ t) (ob (D.restrictColours J) μ t')) :
    linear D J μ t t' (f + g) = linear D J μ t t' f + linear D J μ t t' g :=
  (linear D J μ t t').map_add f g

@[simp] theorem linear_neg (μ : X) (t t' : List (Letter J))
    (f : LinDiagram k (ob (D.restrictColours J) μ t) (ob (D.restrictColours J) μ t')) :
    linear D J μ t t' (-f) = -linear D J μ t t' f :=
  (linear D J μ t t').map_neg f

@[simp] theorem linear_smul (μ : X) (t t' : List (Letter J)) (a : k)
    (f : LinDiagram k (ob (D.restrictColours J) μ t) (ob (D.restrictColours J) μ t')) :
    linear D J μ t t' (a • f) = a • linear D J μ t t' f :=
  (linear D J μ t t').map_smul a f

@[simp] theorem linear_sum (μ : X) (t t' : List (Letter J)) {ι : Type*} (s : Finset ι)
    (f : ι → LinDiagram k (ob (D.restrictColours J) μ t) (ob (D.restrictColours J) μ t')) :
    linear D J μ t t' (∑ i ∈ s, f i) = ∑ i ∈ s, linear D J μ t t' (f i) :=
  map_sum (linear D J μ t t') f s

@[simp] theorem linear_zero (μ : X) (t t' : List (Letter J)) :
    linear (k := k) D J μ t t' 0 = 0 := (linear D J μ t t').map_zero

@[simp] theorem linear_ite (μ : X) (t t' : List (Letter J)) (p : Prop) [Decidable p]
    (f g : LinDiagram k (ob (D.restrictColours J) μ t) (ob (D.restrictColours J) μ t')) :
    linear D J μ t t' (if p then f else g) =
      if p then linear D J μ t t' f else linear D J μ t t' g := by
  split_ifs <;> rfl

/-- Inclusion carries every defining linear relation to its original-colour
relation. The heterogeneous equality accounts only for the boundary-word
identities `relationLabel_dom` and `relationLabel_cod`. -/
theorem linear_relation (r : Rel (D.restrictColours J)) :
    HEq (linear D J r.ν r.dom r.cod (relation (D.restrictColours J)
      (Sc.restrictColours D J) r)) (relation D Sc (relationLabel D J r)) := by
  cases r <;> apply heq_of_eq <;>
    dsimp only [Rel.ν, Rel.dom, Rel.cod, relationLabel]
  all_goals
    simp only [relation, linear_sub, linear_add, linear_neg, linear_smul, linear_sum,
      linear_ite, linear_zero, dg, idg, linear_of, diagram_mkD, diagram_id]
    simp [layerData, shape, letter, crossL, dotsL, sigmaL, lcrossL, epsL, etaL,
      dcupL, dcapL, Scalars.restrictColours, Datum.restrictColours, Datum.dn, Datum.d]
  all_goals rfl

/-- Restricting a supported relation and then including its linear expansion
recovers that same defining relation, not merely its label or boundary. -/
theorem linear_restrictLabel (r : Rel D) (hr : ∀ i ∈ r.colours, i ∈ J) :
    let s := restrictLabel D J r hr
    HEq (linear D J s.ν s.dom s.cod
      (relation (D.restrictColours J) (Sc.restrictColours D J) s)) (relation D Sc r) := by
  have congrRelation (a b : Rel D) (h : a = b) :
      HEq (relation D Sc a) (relation D Sc b) := by
    cases h
    rfl
  exact (linear_relation D J Sc (restrictLabel D J r hr)).trans
    (congrRelation _ _ (relationLabel_restrictLabel D J r hr))

/-- Every user-defined relation has a lift to a finite-colour presentation
whose inclusion recovers its full linear expansion. -/
theorem relation_finite_lift (r : Rel D) :
    ∃ (J : Finset I) (s : Rel (D.restrictColours J)),
      relationLabel D J s = r ∧
      HEq (linear D J s.ν s.dom s.cod
        (relation (D.restrictColours J) (Sc.restrictColours D J) s)) (relation D Sc r) := by
  classical
  let J := r.colours.toFinset
  have hr : ∀ i ∈ r.colours, i ∈ J := fun i hi => List.mem_toFinset.mpr hi
  exact ⟨J, restrictLabel D J r hr, relationLabel_restrictLabel D J r hr,
    linear_restrictLabel D J Sc r hr⟩

end FiniteColour
end OddMath.SKM
