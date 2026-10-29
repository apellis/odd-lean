/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.HalfTurn.Mirror
import OddMath.QuiverHecke.CyclotomicAction.ParameterTransport
import StringDiagrams.Super.SOpPresented

/-!
# The reflection of the quiver Hecke supercategory in a horizontal axis

The second factor of the half-turn `U` of `docs/Nondegeneracy/SwappedVacuumCoordinates.md` §4.
Reflection in a horizontal axis keeps words and positions, reverses vertical composition with the
Koszul sign of the super-opposite, fixes dots and sends the crossing `τ : Eᵢ Eⱼ → Eⱼ Eᵢ` to
`-(-1)^{|i||j|} ε_{ij}` times the crossing `Eⱼ Eᵢ → Eᵢ Eⱼ`, where `ε_{ii} = -1` and `ε_{ij} = 1`
for `i ≠ j`. It is a contravariant superfunctor from the quiver Hecke supercategory with
parameters `Sc` to the one with parameters `parameterTwist D Sc`. Composed with the reflection
`mirrorFunctor` in a vertical axis, the crossing weights multiply to `ε_{ij}`, the weight of §4.

## Main declarations

* `flip_mkD`: the image of a normal-form diagram, with its sign.
* `flip_rel`: the images of the defining relations (BE2, arXiv:1701.04133v2, Definition 1.5,
  upward part) vanish in the target, with twisted parameters.
* `flipFunctor D Sc`: the induced contravariant superfunctor.
-/
noncomputable section
open scoped Classical
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams Supercategory
open SKM (zsign)
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
variable {k : Type w} [CommRing k] (Sc : SKM.Scalars D k)

/-- The reflection of a generator in a horizontal axis. -/
def Shape.flip : Shape I → Shape I
  | .dot i => .dot i
  | .cross i j => .cross j i

@[simp] theorem Shape.dom_flip (g : Shape I) : g.flip.dom = g.cod := by
  cases g <;> rfl

@[simp] theorem Shape.cod_flip (g : Shape I) : g.flip.cod = g.dom := by
  cases g <;> rfl

theorem Shape.parity_flip (g : Shape I) : g.flip.parity D = g.parity D := by
  cases g <;> simp [Shape.flip, Shape.parity, mul_comm]

/-- The weight of the horizontal reflection: `1` on dots and `-(-1)^{|i||j|} ε_{ij}` on the
crossing of `i` and `j`. -/
def flipWeight : Shape I → k
  | .dot _ => 1
  | .cross i j => -zsign k (D.parity i * D.parity j) * (if i = j then -1 else 1)

/-- The horizontal reflection of a contextual generator. -/
def flipLD (x : LayerData I) : LayerData I := (x.1, x.2.1.flip, x.2.2)

/-- The layers of the reflected diagram, in reverse order. -/
def flipL (ls : List (LayerData I)) : List (LayerData I) := (ls.map flipLD).reverse

/-- The parity of a list of contextual generators. -/
def psum (ls : List (LayerData I)) : ZMod 2 := (ls.map fun x => x.2.1.parity D).sum

/-- The scalar of the reflected diagram: the weights and the Koszul signs of the reversal. -/
def flipC : List (LayerData I) → k
  | [] => 1
  | x :: ls => zsign k (x.2.1.parity D * psum D ls) * flipWeight D x.2.1 * flipC ls

theorem sChain_flipL {t t' : List I} {ls : List (LayerData I)} (h : SChain t ls t') :
    SChain t' (flipL ls) t := by
  induction ls generalizing t with
  | nil => exact (show t = t' from h).symm
  | cons x ls ih =>
    obtain ⟨rfl, h2⟩ := h
    have h1 : SChain (x.1 ++ x.2.1.cod ++ x.2.2) [flipLD x] (x.1 ++ x.2.1.dom ++ x.2.2) :=
      ⟨by simp [flipLD], by simp [flipLD]⟩
    simpa [flipL] using (ih h2).append h1

/-! ## The functor on generators -/

/-- The relabelling of the horizontal reflection: the identity on regions and strands. -/
abbrev flipMap : ColourMap (sig D) (sig D) := ColourMap.id (sig D)

/-- The image of a generator, a morphism from its bottom boundary to its top boundary. -/
def flipImg (g : (sig D).Gen) :
    (pres D Sc).obj (LocalMap.genCod (flipMap D) g) ⟶
      (pres D Sc).obj (LocalMap.genDom (flipMap D) g) :=
  flipWeight (k := k) D g • (pres D Sc).diag (mkD D [([], Shape.flip g, [])]
    (t := g.cod) (t' := g.dom) ⟨by simp, by simp⟩)

theorem flipPar (a b : Obj (sig D)) (p : ZMod 2) :
    parity (R := k) ((pres D Sc).obj a) ((pres D Sc).obj b) p =
      (pres D Sc).homDeg (Presentation.parityDeg (sig D)) a b p := rfl

theorem flipImg_mem (g : (sig D).Gen) :
    flipImg D Sc g ∈ (pres D Sc).homDeg (Presentation.parityDeg (sig D))
      (LocalMap.genCod (flipMap D) g) (LocalMap.genDom (flipMap D) g)
      (Presentation.parityDeg (sig D) g) := by
  refine Submodule.smul_mem _ _ (Presentation.diag_mem_homDeg' ?_)
  rw [degree_parity_mkD, parityDeg_sig]
  simp [Shape.parity_flip]

set_option backward.isDefEq.respectTransparency false in
/-- The image of a layer `u ⊗ g ⊗ v`: the reflected generator in the same context. -/
theorem layerImg_flip (u : List I) (g : Shape I) (v : List I) :
    SOpMap.layerImg (flipMap D) (flipImg D Sc) (lay D u g v) =
      flipWeight (k := k) D g • (pres D Sc).diag (mkD D [(u, g.flip, v)]
        (t := u ++ g.cod ++ v) (t' := u ++ g.dom ++ v) ⟨by simp, by simp⟩) := by
  unfold SOpMap.layerImg flipImg
  rw [Presentation.whisk_smul, Presentation.whisk_diag _ _ _ _
    (Obj.whiskerOK_of_subsingleton _ _ _)]
  simp only [Linear.comp_smul, eqToHom_refl, Category.id_comp, Category.comp_id]
  congr 1
  apply Presentation.diag_eq_of_layers_eq
  simp [layList, lay, Layer.whisker]

theorem sign_eq_zsign' (p : ZMod 2) : sign k p = zsign k p := by
  fin_cases p <;> rfl

theorem mkD_cons {t t' : List I} (x : LayerData I) (ls : List (LayerData I))
    (h : SChain t (x :: ls) t') :
    mkD D (x :: ls) h =
      mkD D [x] (t' := x.1 ++ x.2.1.cod ++ x.2.2) ⟨h.1, rfl⟩ ≫ mkD D ls h.2 := by
  apply Diagram.ext
  simp [layList]

set_option backward.isDefEq.respectTransparency false in
theorem flip_mkD_one (u : List I) (g : Shape I) (v : List I) :
    SOp.unsop ((SOpMap.functor (flipMap D) (flipImg D Sc)).map
      (mkD D [(u, g, v)] (t := u ++ g.dom ++ v) (t' := u ++ g.cod ++ v) ⟨rfl, rfl⟩)) =
      flipWeight (k := k) D g • (pres D Sc).diag (mkD D [(u, g.flip, v)]
        (t := u ++ g.cod ++ v) (t' := u ++ g.dom ++ v) ⟨by simp, by simp⟩) := by
  show SOp.unsop ((SOpMap.interp (flipMap D) (flipImg D Sc)).functor.map
    (Diagram.mk [lay D u g v] _)) = _
  rw [Interpretation.functor_map_mk_cons, Interpretation.functor_map_mk_nil,
    SOpMap.unsop_eqToHom_comp, SOpMap.unsop_comp_eqToHom]
  erw [SOp.unsop_mk']
  rw [layerImg_flip]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- **The image of a normal-form diagram**: the reflected layers in reverse order, with the
weights and the Koszul signs of the super-opposite. -/
theorem flip_mkD {t t' : List I} (ls : List (LayerData I)) (h : SChain t ls t') :
    SOp.unsop ((SOpMap.functor (flipMap D) (flipImg D Sc)).map (mkD D ls h)) =
      flipC (k := k) D ls • (pres D Sc).diag (mkD D (flipL ls) (sChain_flipL h)) := by
  induction ls generalizing t with
  | nil =>
    obtain rfl : t = t' := h
    show SOp.unsop ((SOpMap.interp (flipMap D) (flipImg D Sc)).functor.map
      (Diagram.mk [] _)) = _
    rw [Interpretation.functor_map_mk_nil, flipC, one_smul,
      show mkD D (flipL []) (sChain_flipL (t := t) (t' := t) rfl) = 𝟙 _ from Diagram.ext rfl,
      Presentation.diag_id]
    rfl
  | cons x ls ih =>
    obtain ⟨u, g, v⟩ := x
    obtain ⟨rfl, h2⟩ := h
    rw [mkD_cons, Functor.map_comp,
      SOp.comp_of_mem (SOp.mem_parity_iff.mp
          (SOpMap.functor_map_mem (flipPar D Sc) (flipImg_mem D Sc) _))
        (SOp.mem_parity_iff.mp (SOpMap.functor_map_mem (flipPar D Sc) (flipImg_mem D Sc) _)),
      flip_mkD_one, ih h2, degree_parity_mkD, degree_parity_mkD, sign_eq_zsign']
    simp only [Linear.smul_comp, Linear.comp_smul, smul_smul]
    have h1 : SChain (u ++ g.cod ++ v) [(u, g.flip, v)] (u ++ g.dom ++ v) :=
      ⟨by simp, by simp⟩
    rw [diag_mkD_congr D Sc _ ((sChain_flipL h2).append h1) (by simp [flipL, flipLD]),
      diag_mkD_append D Sc _ _ _ (sChain_flipL h2) h1]
    congr 1
    simp only [flipC, psum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    ring

/-! ## Reflected scalars of concrete layer lists -/

@[simp] theorem flipLD_mk (u : List I) (g : Shape I) (v : List I) :
    flipLD (u, g, v) = (u, g.flip, v) := rfl

@[simp] theorem Shape.flip_dot (i : I) : (Shape.dot i).flip = Shape.dot i := rfl

@[simp] theorem Shape.flip_cross (i j : I) : (Shape.cross i j).flip = Shape.cross j i := rfl

@[simp] theorem flipL_nil : flipL ([] : List (LayerData I)) = [] := rfl

@[simp] theorem flipL_append (A B : List (LayerData I)) :
    flipL (A ++ B) = flipL B ++ flipL A := by
  simp [flipL]

@[simp] theorem flipL_cons (x : LayerData I) (A : List (LayerData I)) :
    flipL (x :: A) = flipL A ++ [flipLD x] := by
  simp [flipL]

@[simp] theorem flipL_replicate (n : ℕ) (x : LayerData I) :
    flipL (List.replicate n x) = List.replicate n (flipLD x) := by
  simp [flipL]

@[simp] theorem psum_nil : psum D ([] : List (LayerData I)) = 0 := rfl

@[simp] theorem psum_cons (x : LayerData I) (A : List (LayerData I)) :
    psum D (x :: A) = x.2.1.parity D + psum D A := by
  simp [psum]

@[simp] theorem psum_append (A B : List (LayerData I)) :
    psum D (A ++ B) = psum D A + psum D B := by
  simp [psum]

@[simp] theorem psum_replicate (n : ℕ) (x : LayerData I) :
    psum D (List.replicate n x) = (n : ZMod 2) * x.2.1.parity D := by
  simp [psum, List.sum_replicate, nsmul_eq_mul]

@[simp] theorem flipC_nil : flipC (k := k) D [] = 1 := rfl

theorem flipC_cons (x : LayerData I) (A : List (LayerData I)) :
    flipC (k := k) D (x :: A) = zsign k (x.2.1.parity D * psum D A) * flipWeight D x.2.1 *
      flipC D A := rfl

@[simp] theorem flipC_singleton (x : LayerData I) :
    flipC (k := k) D [x] = flipWeight D x.2.1 := by
  simp [flipC, psum, SKM.zsign]

@[simp] theorem flipC_append (A B : List (LayerData I)) :
    flipC (k := k) D (A ++ B) =
      zsign k (psum D A * psum D B) * flipC D A * flipC D B := by
  induction A with
  | nil => simp [SKM.zsign]
  | cons x A ih =>
    simp only [List.cons_append, flipC, ih, psum_append, psum_cons]
    rw [show x.2.1.parity D * (psum D A + psum D B) =
        x.2.1.parity D * psum D A + x.2.1.parity D * psum D B by ring,
      show (x.2.1.parity D + psum D A) * psum D B =
        x.2.1.parity D * psum D B + psum D A * psum D B by ring,
      SKM.zsign_add, SKM.zsign_add]
    ring

theorem flipC_replicate_dot_add_two (n : ℕ) (u : List I) (i : I) (v : List I) :
    flipC (k := k) D (List.replicate (n + 2) (u, Shape.dot i, v)) =
      zsign k (D.parity i) * flipC D (List.replicate n (u, Shape.dot i, v)) := by
  simp only [List.replicate_succ, flipC, psum_cons, psum_replicate, flipWeight, Shape.parity,
    mul_one, ← mul_assoc]
  congr 1
  rw [← SKM.zsign_add]
  congr 1
  generalize D.parity i = a
  generalize (n : ZMod 2) = b
  fin_cases a <;> fin_cases b <;> decide

/-- `n` dots on one strand reflect with the sign `(-1)^{|i| ⌊n/2⌋}`. -/
@[simp] theorem flipC_replicate_dot (n : ℕ) (u : List I) (i : I) (v : List I) :
    flipC (k := k) D (List.replicate n (u, Shape.dot i, v)) =
      zsign k (D.parity i * ((n / 2 : ℕ) : ZMod 2)) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [SKM.zsign]
  | one => simp [flipWeight, SKM.zsign]
  | more n ih _ =>
    rw [flipC_replicate_dot_add_two, ih, ← SKM.zsign_add,
      show (n + 2) / 2 = n / 2 + 1 by omega]
    push_cast
    ring_nf

/-! ## The functor on linear combinations of diagrams -/

/-- The horizontal reflection on linear combinations of diagrams, with values in the target
presentation. -/
abbrev flipLin {a b : Obj (sig D)} (f : LinDiagram k a b) :
    (pres D Sc).obj b ⟶ (pres D Sc).obj a :=
  SOp.unsop ((freeLift k (SOpMap.functor (flipMap D) (flipImg D Sc))).map f)

theorem flipLin_dg {t t' : List I} (ls : List (LayerData I)) (h : SChain t ls t') :
    flipLin D Sc (dg (k := k) D ls h) =
      flipC (k := k) D ls • (pres D Sc).diag (mkD D (flipL ls) (sChain_flipL h)) := by
  rw [flipLin, dg, freeLift_map_of, flip_mkD]

theorem flipLin_idg (t : List I) : flipLin D Sc (idg (k := k) D t) = 𝟙 _ := by
  rw [flipLin, idg, freeLift_map_of, CategoryTheory.Functor.map_id]
  rfl

theorem flipLin_sub {a b : Obj (sig D)} (f g : LinDiagram k a b) :
    flipLin D Sc (f - g) = flipLin D Sc f - flipLin D Sc g := by
  rw [flipLin, Functor.map_sub, SOp.unsop_sub]

theorem flipLin_smul {a b : Obj (sig D)} (c : k) (f : LinDiagram k a b) :
    flipLin D Sc (c • f) = c • flipLin D Sc f := by
  rw [flipLin, Functor.map_smul, SOp.unsop_smul]

theorem flipLin_sum {a b : Obj (sig D)} {ι : Type*} (s : Finset ι) (f : ι → LinDiagram k a b) :
    flipLin D Sc (∑ x ∈ s, f x) = ∑ x ∈ s, flipLin D Sc (f x) := by
  rw [flipLin, Functor.map_sum]
  exact map_sum (SOp.unsopₗ _ _) _ _

end OddMath.QuiverHecke

/-! ## The defining relations

The target has the twisted parameters `parameterTwist D Sc`; this requires the coefficients to
live in the universe of the colours, as in `OddMath.QuiverHecke.parameterTwist`. -/

namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams Supercategory
open SKM (zsign)
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X) [CommRing k]
  (Sc : SKM.Scalars D k)

theorem parameterSignUnit_coe (p : ZMod 2) : ((parameterSignUnit (k := k) p : kˣ) : k) = zsign k p := by
  unfold parameterSignUnit SKM.zsign
  split_ifs <;> simp

theorem parameterTwist_t_ne {i j : I} (hij : i ≠ j) :
    ((parameterTwist D Sc).t i j : k) =
      zsign k (parameterSignExponent D i j (D.dn i j) 0) * Sc.t i j := by
  simp [parameterTwist, hij, parameterSignUnit_coe]

theorem parameterTwist_s (i j : I) (p q : ℕ) :
    (parameterTwist D Sc).s i j p q = zsign k (parameterSignExponent D i j p q) * Sc.s i j p q :=
  rfl

/-- The horizontal reflection on linear combinations, into the super-opposite of the target. -/
abbrev flipFree : Free k (Obj (sig D)) ⥤ SOp k (pres D (parameterTwist D Sc)).Presented :=
  freeLift k (SOpMap.functor (flipMap D) (flipImg D (parameterTwist D Sc)))

/-- A relation whose reflection is a multiple of a relation of the target is killed. -/
theorem flip_rel_of {r : Rel D} (r' : Rel D) (hd : r'.dom = r.cod) (hc : r'.cod = r.dom) (c : k)
    (h : flipLin D (parameterTwist D Sc) (relation D Sc r) =
      c • (eqToHom (congrArg (pres D (parameterTwist D Sc)).obj (congrArg (ob D) hd.symm)) ≫
        (pres D (parameterTwist D Sc)).lin (relation D (parameterTwist D Sc) r') ≫
          eqToHom (congrArg (pres D (parameterTwist D Sc)).obj (congrArg (ob D) hc)))) :
    (flipFree D Sc).map ((pres D Sc).rel r) = 0 := by
  apply SOp.unsop_injective
  have h' := (pres D (parameterTwist D Sc)).lin_rel_self r'
  change (pres D _).lin (relation D _ r') = 0 at h'
  change flipLin D (parameterTwist D Sc) (relation D Sc r) = 0
  rw [h, h']
  simp

/-- Expand the reflection of a relation and a relation of the target into diagrams. -/
macro "flip_expand" : tactic => `(tactic|
  simp only [relation, flipLin_sub, flipLin_smul, flipLin_sum, flipLin_dg, flipLin_idg,
    eqToHom_refl, Category.id_comp, Category.comp_id, dotsL, crossL, flipL_append,
    flipL_replicate, flipL_cons, flipL_nil, flipLD_mk, Shape.flip_dot, Shape.flip_cross,
    List.nil_append, List.cons_append, List.append_nil, List.singleton_append, flipC_append,
    flipC_singleton, flipC_cons, flipC_nil, flipC_replicate_dot, psum_append, psum_replicate, psum_cons, psum_nil,
    Shape.parity, Presentation.lin_sub, Presentation.lin_smul, Presentation.lin_of, smul_sub,
    add_zero, mul_one, one_mul])

theorem flip_rel_quadEq (i : I) :
    (flipFree D Sc).map ((pres D Sc).rel (Rel.quadEq i)) = 0 := by
  refine flip_rel_of D Sc (.quadEq i) rfl rfl (zsign k (D.parity i)) ?_
  flip_expand
  congr 1
  simp only [flipWeight]
  generalize D.parity i = a
  fin_cases a <;> simp [zsign]


theorem flip_rel_quadZero (i j : I) (hij : i ≠ j) (hd : D.d i j = 0) :
    (flipFree D Sc).map ((pres D Sc).rel (Rel.quadZero i j hij hd)) = 0 := by
  refine flip_rel_of D Sc (.quadZero i j hij hd) rfl rfl (zsign k (D.parity i * D.parity j)) ?_
  flip_expand
  rw [parameterTwist_t_ne D Sc hij, show D.dn i j = 0 by simp [SKM.Datum.dn, hd]]
  simp only [flipWeight, hij, Ne.symm hij, ↓reduceIte, parameterSignExponent]
  generalize D.parity i = a
  generalize D.parity j = b
  fin_cases a <;> fin_cases b <;> simp [zsign]

theorem flip_rel_slideL (i j : I) (hij : i ≠ j) :
    (flipFree D Sc).map ((pres D Sc).rel (Rel.slideL i j hij)) = 0 := by
  refine flip_rel_of D Sc (.slideR j i hij.symm) rfl rfl
    (zsign k (D.parity i * D.parity j) * flipWeight D (Shape.cross i j)) ?_
  flip_expand
  simp only [flipWeight, hij, ↓reduceIte]
  generalize D.parity i = a
  generalize D.parity j = b
  fin_cases a <;> fin_cases b <;> simp [zsign]

theorem flip_rel_slideR (i j : I) (hij : i ≠ j) :
    (flipFree D Sc).map ((pres D Sc).rel (Rel.slideR i j hij)) = 0 := by
  refine flip_rel_of D Sc (.slideL j i hij.symm) rfl rfl
    (zsign k (D.parity i * D.parity j) * flipWeight D (Shape.cross i j)) ?_
  flip_expand
  simp only [flipWeight, hij, ↓reduceIte]
  generalize D.parity i = a
  generalize D.parity j = b
  fin_cases a <;> fin_cases b <;> simp [zsign]

theorem flip_rel_slideLEq (i : I) :
    (flipFree D Sc).map ((pres D Sc).rel (Rel.slideLEq i)) = 0 := by
  refine flip_rel_of D Sc (.slideREq i) rfl rfl 1 ?_
  flip_expand
  simp only [flipWeight]
  generalize D.parity i = a
  fin_cases a <;> simp [zsign]

theorem flip_rel_slideREq (i : I) :
    (flipFree D Sc).map ((pres D Sc).rel (Rel.slideREq i)) = 0 := by
  refine flip_rel_of D Sc (.slideLEq i) rfl rfl 1 ?_
  flip_expand
  simp only [flipWeight]
  generalize D.parity i = a
  fin_cases a <;> simp [zsign]

theorem flip_rel_braid (i j m : I) (h : ¬(i = m ∧ i ≠ j)) :
    (flipFree D Sc).map ((pres D Sc).rel (Rel.braid i j m h)) = 0 := by
  refine flip_rel_of D Sc (.braid m j i fun ⟨e, hne⟩ => h ⟨e.symm, e ▸ hne⟩) rfl rfl
    (flipC D (crossL [] i j [m] ++ crossL [j] i m [] ++ crossL [] j m [i])) ?_
  flip_expand
  congr 2
  generalize D.parity i = a
  generalize D.parity j = b
  generalize D.parity m = c
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp [zsign] <;> ring

theorem flip_rel_quadNe (i j : I) (hij : i ≠ j) (hd : D.d i j ≠ 0) :
    (flipFree D Sc).map ((pres D Sc).rel (Rel.quadNe i j hij hd)) = 0 := by
  refine flip_rel_of D Sc (.quadNe i j hij hd) rfl rfl (zsign k (D.parity i * D.parity j)) ?_
  flip_expand
  rw [parameterTwist_t_ne D Sc hij, parameterTwist_t_ne D Sc (Ne.symm hij),
    lin_sum D (parameterTwist D Sc), Finset.smul_sum]
  simp only [lin_sum D (parameterTwist D Sc), Presentation.lin_smul, Presentation.lin_of,
    Finset.smul_sum, smul_smul, parameterTwist_s, parameterSignExponent, Nat.zero_div,
    Nat.cast_zero, mul_zero, add_zero]
  congr 1
  · congr 1
    · congr 1
      · congr 1
        simp only [flipWeight, hij, Ne.symm hij, ↓reduceIte]
        generalize D.parity i = a
        generalize D.parity j = b
        fin_cases a <;> fin_cases b <;> simp [zsign]
      · congr 1
        rw [SKM.zsign_add]
        generalize D.parity i = a
        generalize D.parity j = b
        generalize ((D.dn i j / 2 : ℕ) : ZMod 2) = e
        fin_cases a <;> fin_cases b <;> fin_cases e <;> simp [zsign]
    · congr 1
      rw [SKM.zsign_add]
      generalize D.parity i = a
      generalize D.parity j = b
      generalize ((D.dn j i / 2 : ℕ) : ZMod 2) = e
      fin_cases a <;> fin_cases b <;> fin_cases e <;> simp [zsign]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [diag_dots_swap D (parameterTwist D Sc) (t := [i, j]) [] [] [] i j x y
    ([], Shape.dot i, [j]) ([i], Shape.dot j, []) rfl rfl rfl, smul_smul]
  congr 1
  rw [SKM.zsign_add, SKM.zsign_add]
  generalize D.parity i = a
  generalize D.parity j = b
  generalize (x : ZMod 2) = c
  generalize (y : ZMod 2) = d
  generalize ((x / 2 : ℕ) : ZMod 2) = e
  generalize ((y / 2 : ℕ) : ZMod 2) = f
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> fin_cases e <;> fin_cases f <;>
    simp [zsign]
  exact (sChain_dotsL [i] j [] y).append (sChain_dotsL [] i [j] x)



/-- Halving the two parts of `n - 1 = x + r` loses one, modulo `2`, when `n` is even. -/
theorem parity_half_add {P : ZMod 2} {x r n : ℕ} (h : x + r + 1 = n) (hn : P * (n : ZMod 2) = 0) :
    P * (((x / 2 : ℕ) : ZMod 2) + ((r / 2 : ℕ) : ZMod 2)) = P * (1 + ((n / 2 : ℕ) : ZMod 2)) := by
  fin_cases P
  · simp
  · simp only [Fin.mk_one, one_mul] at hn ⊢
    obtain ⟨m, rfl⟩ := (ZMod.natCast_eq_zero_iff n 2).mp hn
    have e : x / 2 + r / 2 + 1 = m := by omega
    rw [Nat.mul_div_cancel_left m two_pos, ← e]
    push_cast
    generalize ((x / 2 : ℕ) : ZMod 2) = a
    generalize ((r / 2 : ℕ) : ZMod 2) = b
    fin_cases a <;> fin_cases b <;> decide

/-- Membership in a concatenation of blocks of repeated layers. -/
local macro "dots_mem" : tactic => `(tactic|
  (intro x hx; simp only [List.mem_append, List.mem_replicate] at hx; tauto))

/-- **Reversal of three dot blocks** on the strands of `i j i`, with the Koszul sign of each
exchanged pair. -/
theorem diag_dots_reverse_three (i j : I) (a q b : ℕ)
    (h : SChain [i, j, i] (List.replicate a ([], Shape.dot i, [j, i]) ++
      List.replicate q ([i], Shape.dot j, [i]) ++
      List.replicate b ([i, j], Shape.dot i, [])) [i, j, i])
    (h' : SChain [i, j, i] (List.replicate b ([i, j], Shape.dot i, []) ++
      List.replicate q ([i], Shape.dot j, [i]) ++
      List.replicate a ([], Shape.dot i, [j, i])) [i, j, i]) :
    (pres D Sc).diag (mkD D _ h) =
      (zsign k ((a : ZMod 2) * D.parity i * ((q : ZMod 2) * D.parity j)) *
        zsign k ((a : ZMod 2) * D.parity i * ((b : ZMod 2) * D.parity i)) *
        zsign k ((q : ZMod 2) * D.parity j * ((b : ZMod 2) * D.parity i))) •
        (pres D Sc).diag (mkD D _ h') := by
  set A : LayerData I := ([], Shape.dot i, [j, i]) with hA
  set C : LayerData I := ([i], Shape.dot j, [i]) with hC
  set B : LayerData I := ([i, j], Shape.dot i, []) with hB
  have sc : ∀ L : List (LayerData I), (∀ x ∈ L, x = A ∨ x = C ∨ x = B) →
      SChain [i, j, i] L [i, j, i] := fun L hL => sChain_of_dots _ L fun x hx => by
    rcases hL x hx with rfl | rfl | rfl
    exacts [⟨i, rfl, rfl⟩, ⟨j, rfl, rfl⟩, ⟨i, rfl, rfl⟩]
  rw [diag_mkD_append D Sc (List.replicate a A ++ List.replicate q C) (List.replicate b B) h _ _,
    diag_dots_swap D Sc (t := [i, j, i]) [] [] [i] i j a q A C rfl rfl rfl _ _,
    Linear.smul_comp,
    ← diag_mkD_append D Sc (List.replicate q C ++ List.replicate a A) (List.replicate b B) _,
    diag_mkD_congr D Sc (A := List.replicate q C ++ List.replicate a A ++ List.replicate b B)
      (B := List.replicate q C ++ (List.replicate a A ++ List.replicate b B)) _ _
      (List.append_assoc _ _ _),
    diag_mkD_append D Sc (List.replicate q C) (List.replicate a A ++ List.replicate b B) _ _ _,
    diag_dots_swap D Sc (t := [i, j, i]) [] [j] [] i i a b A B rfl rfl rfl _ _,
    Linear.comp_smul,
    ← diag_mkD_append D Sc (List.replicate q C) (List.replicate b B ++ List.replicate a A) _,
    diag_mkD_congr D Sc (A := List.replicate q C ++ (List.replicate b B ++ List.replicate a A))
      (B := List.replicate q C ++ List.replicate b B ++ List.replicate a A) _ _
      (List.append_assoc _ _ _).symm,
    diag_mkD_append D Sc (List.replicate q C ++ List.replicate b B) (List.replicate a A) _ _ _,
    diag_dots_swap D Sc (t := [i, j, i]) [i] [] [] j i q b C B rfl rfl rfl _ _,
    Linear.smul_comp,
    ← diag_mkD_append D Sc (List.replicate b B ++ List.replicate q C) (List.replicate a A) h']
  all_goals try exact sc _ (by dots_mem)
  rw [smul_smul, smul_smul, mul_assoc]

theorem flip_rel_braidEq (i j : I) (hij : i ≠ j) :
    (flipFree D Sc).map ((pres D Sc).rel (Rel.braidEq i j hij)) = 0 := by
  refine flip_rel_of D Sc (.braidEq i j hij) rfl rfl
    (zsign k (D.parity i * (D.parity j + 1))) ?_
  flip_expand
  rw [parameterTwist_t_ne D Sc hij]
  simp only [lin_sum D (parameterTwist D Sc), Presentation.lin_smul, Presentation.lin_of,
    Finset.smul_sum, smul_smul, parameterTwist_s, parameterSignExponent, Nat.zero_div,
    Nat.cast_zero, mul_zero, add_zero]
  refine congrArg₂ (· - ·) (congrArg₂ (· - ·) (congrArg₂ (· - ·)
    (congrArg (· • _) ?_) (congrArg (· • _) ?_)) ?_) ?_
  · simp only [flipWeight, hij, Ne.symm hij, ↓reduceIte]
    generalize D.parity i = a
    generalize D.parity j = b
    fin_cases a <;> fin_cases b <;> simp [zsign]
  · simp only [flipWeight, hij, Ne.symm hij, ↓reduceIte]
    generalize D.parity i = a
    generalize D.parity j = b
    fin_cases a <;> fin_cases b <;> simp [zsign]
  · refine Finset.sum_congr rfl fun x hx => ?_
    have hx' := Finset.mem_range.mp hx
    rw [diag_dots_swap D (parameterTwist D Sc) (t := [i, j, i]) [] [j] [] i i (D.dn i j - 1 - x) x
      ([], Shape.dot i, [j, i]) ([i, j], Shape.dot i, []) rfl rfl rfl _
      ((sChain_dotsL [i, j] i [] x).append (sChain_dotsL [] i [j, i] _)), smul_smul]
    congr 1
    have key := parity_half_add (P := D.parity i) (x := x) (r := D.dn i j - 1 - x) (by omega)
      (SKM.parity_mul_dn D i j)
    generalize ((x / 2 : ℕ) : ZMod 2) = e at key ⊢
    generalize (((D.dn i j - 1 - x) / 2 : ℕ) : ZMod 2) = e' at key ⊢
    generalize ((D.dn i j / 2 : ℕ) : ZMod 2) = e'' at key ⊢
    generalize ((D.dn i j - 1 - x : ℕ) : ZMod 2) = c
    generalize (x : ZMod 2) = c'
    generalize D.parity i = a at key ⊢
    generalize D.parity j = b
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases c' <;> fin_cases e <;>
      fin_cases e' <;> fin_cases e'' <;> simp [zsign] at key ⊢
  · refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
      Finset.sum_congr rfl fun z hz => ?_
    have hz' := Finset.mem_range.mp hz
    by_cases hs : Sc.s i j x y = 0
    · simp [hs]
    have hxP : D.parity i * (x : ZMod 2) = 0 := by
      rw [mul_comm]; exact zmod2_eq_zero_of_ne_one fun h => hs (Sc.s_eq_zero i j x y h)
    rw [diag_mkD_congr D (parameterTwist D Sc)
        (A := List.replicate (x - 1 - z) ([], Shape.dot i, [j, i]) ++
          (List.replicate y ([i], Shape.dot j, [i]) ++ List.replicate z ([i, j], Shape.dot i, [])))
        (B := List.replicate (x - 1 - z) ([], Shape.dot i, [j, i]) ++
          List.replicate y ([i], Shape.dot j, [i]) ++ List.replicate z ([i, j], Shape.dot i, []))
        _ (((sChain_dotsL [] i [j, i] (x - 1 - z)).append (sChain_dotsL [i] j [i] y)).append
          (sChain_dotsL [i, j] i [] z)) (List.append_assoc _ _ _).symm,
      diag_dots_reverse_three D (parameterTwist D Sc) i j (x - 1 - z) y z _
        (((sChain_dotsL [i, j] i [] z).append (sChain_dotsL [i] j [i] y)).append
          (sChain_dotsL [] i [j, i] _)), smul_smul]
    congr 1
    have key := parity_half_add (P := D.parity i) (x := z) (r := x - 1 - z) (by omega) hxP
    generalize Sc.s i j x y = S
    generalize SKM.zsign k (D.parity i * (D.parity j + (z : ZMod 2))) = Z
    generalize ((z / 2 : ℕ) : ZMod 2) = hz at key ⊢
    generalize (((x - 1 - z) / 2 : ℕ) : ZMod 2) = hr at key ⊢
    generalize ((x / 2 : ℕ) : ZMod 2) = hx at key ⊢
    generalize ((y / 2 : ℕ) : ZMod 2) = hy
    generalize ((x - 1 - z : ℕ) : ZMod 2) = cr
    generalize (z : ZMod 2) = cz
    generalize (y : ZMod 2) = cy
    generalize D.parity i = a at key ⊢
    generalize D.parity j = b
    calc _ = Z * S * zsign k ((cz * a + cy * b) * (cr * a) + cz * a * (cy * b) + a * hz +
          b * hy + a * hr + cr * a * (cy * b) + cr * a * (cz * a) + cy * b * (cz * a)) := by
          simp only [SKM.zsign_add]; ring
      _ = Z * S * zsign k (a * (b + 1) + (a * b + a * hx + b * hy)) := by
          congr 2
          revert key
          revert a b cz cy cr hz hr hx hy
          decide
      _ = _ := by simp only [SKM.zsign_add]; ring

/-- The images of all defining relations vanish, with the twisted parameters. -/
theorem flip_rel (r : Rel D) : (flipFree D Sc).map ((pres D Sc).rel r) = 0 := by
  cases r with
  | quadEq i => exact flip_rel_quadEq D Sc i
  | quadZero i j hij hd => exact flip_rel_quadZero D Sc i j hij hd
  | quadNe i j hij hd => exact flip_rel_quadNe D Sc i j hij hd
  | slideL i j hij => exact flip_rel_slideL D Sc i j hij
  | slideLEq i => exact flip_rel_slideLEq D Sc i
  | slideR i j hij => exact flip_rel_slideR D Sc i j hij
  | slideREq i => exact flip_rel_slideREq D Sc i
  | braid i j m h => exact flip_rel_braid D Sc i j m h
  | braidEq i j hij => exact flip_rel_braidEq D Sc i j hij

/-- **The reflection in a horizontal axis**, a contravariant superfunctor from the quiver Hecke
supercategory with parameters `Sc` to the one with parameters `parameterTwist D Sc`: words are
kept, dots are fixed and the crossing `Eᵢ Eⱼ → Eⱼ Eᵢ` goes to `flipWeight` times the crossing
`Eⱼ Eᵢ → Eᵢ Eⱼ`. -/
def flipFunctor : (pres D Sc).Presented ⥤ SOp k (pres D (parameterTwist D Sc)).Presented :=
  SOpMap.liftGen (flipPar D (parameterTwist D Sc)) (flipMap D) (flipImg D (parameterTwist D Sc))
    (pres D Sc) (flipImg_mem D _) (flip_rel D Sc)


end OddMath.QuiverHecke
