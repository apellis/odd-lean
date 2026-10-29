/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.PositionalRelations
import OddMath.SKM.Calculus
import StringDiagrams.Biadjunction.Zigzag
import StringDiagrams.LayerMap.Generators

/-!
# The reflection of the quiver Hecke supercategory in a vertical axis

The first factor of the half-turn `U` of `docs/Nondegeneracy/SwappedVacuumCoordinates.md` §4.
The reflection in a vertical axis reverses words, fixes dots and sends the crossing
`τ : Eᵢ Eⱼ → Eⱼ Eᵢ` to `-(-1)^{|i||j|} τ : Eⱼ Eᵢ → Eᵢ Eⱼ`. It respects the relations (1.7)–(1.9)
of BE2 (arXiv:1701.04133v2, Definition 1.5, upward part) with the same parameters, so it is a
functor of the quiver Hecke supercategory `pres D Sc` to itself.

## Main declarations

* `mirrorSig D`: the reflection of the quiver Hecke signature.
* `mirror_map_mkD`: the reflection of a normal-form diagram.
* `mirror_rel`: the images of the defining relations vanish.
* `mirrorFunctor D Sc`: the induced functor.
-/
noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams
open SKM (zsign)
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
variable {k : Type w} [CommRing k] (Sc : SKM.Scalars D k)

/-- The reflection of a generator. -/
def Shape.mirror : Shape I → Shape I
  | .dot i => .dot i
  | .cross i j => .cross j i

@[simp] theorem Shape.dom_mirror (g : Shape I) : g.mirror.dom = g.dom.reverse := by
  cases g <;> rfl

@[simp] theorem Shape.cod_mirror (g : Shape I) : g.mirror.cod = g.cod.reverse := by
  cases g <;> rfl

theorem Shape.parity_mirror (g : Shape I) : g.mirror.parity D = g.parity D := by
  cases g <;> simp [Shape.mirror, Shape.parity, mul_comm]

/-- The reflection of the quiver Hecke signature in a vertical axis. -/
def mirrorSig : SigMirror (sig D) (sig D) where
  region := id
  colour := id
  colourSrc _ := rfl
  colourTgt _ := rfl
  gen := Shape.mirror
  dom g := by simp [sig]
  cod g := by simp [sig]
  left _ := rfl
  right _ := rfl

theorem mirrorSig_odd (g : (sig D).Gen) : (sig D).odd ((mirrorSig D).gen g) = (sig D).odd g := by
  show decide (Shape.parity D (Shape.mirror g) = 1) = decide (g.parity D = 1)
  rw [Shape.parity_mirror]

/-- The weight of the reflection: `1` on dots, `-(-1)^{|i||j|}` on the crossing of `i` and `j`. -/
def mirrorWeight : Shape I → k
  | .dot _ => 1
  | .cross i j => -zsign k (D.parity i * D.parity j)

/-- The reflection of a contextual generator. -/
def mirrorLD (x : LayerData I) : LayerData I := (x.2.2.reverse, x.2.1.mirror, x.1.reverse)

theorem sChain_mirror {t t' : List I} {ls : List (LayerData I)} (h : SChain t ls t') :
    SChain t.reverse (ls.map mirrorLD) t'.reverse := by
  induction ls generalizing t with
  | nil => cases h; rfl
  | cons x ls ih =>
    obtain ⟨rfl, h⟩ := h
    refine ⟨by simp [mirrorLD], ?_⟩
    have := ih h
    simpa [mirrorLD] using this

theorem mirrorSig_obj (t : List I) :
    (mirrorSig D).toLayerMap.obj (ob D t) = ob D t.reverse := by
  show (⟨(), (t.map id).reverse⟩ : Obj (sig D)) = ⟨(), t.reverse⟩
  rw [List.map_id]

/-- The reflection of a normal-form diagram is the normal-form diagram of the reflected layers. -/
theorem mirror_map_mkD {t t' : List I} (ls : List (LayerData I)) (h : SChain t ls t') :
    (mirrorSig D).toLayerMap.map (mkD D ls h) =
      Diagram.cast (mkD D (ls.map mirrorLD) (sChain_mirror h)) (mirrorSig_obj D t).symm
        (mirrorSig_obj D t').symm := by
  apply Diagram.ext
  simp only [LayerMap.layers_map, layers_mkD, Diagram.layers_cast, layList, List.map_map]
  refine List.map_congr_left fun x _ => ?_
  show (⟨(), (x.2.2.map id).reverse, x.2.1.mirror, (x.1.map id).reverse⟩ : Layer (sig D)) = _
  simp [lay, mirrorLD]

theorem weight_mkD (χ : Shape I → k) {t t' : List I} (ls : List (LayerData I))
    (h : SChain t ls t') :
    Diagram.weight (S := sig D) χ (mkD D ls h) = (ls.map fun x => χ x.2.1).prod := by
  simp [Diagram.weight, Diagram.weightList, layList, lay, Function.comp_def]

/-- The image of a normal-form diagram under the weighted reflection. -/
theorem mirror_dg {t t' : List I} (ls : List (LayerData I)) (h : SChain t ls t') :
    (freeLift k ((mirrorSig D).toLayerMap.toPresented (pres D Sc) (mirrorWeight D))).map
        (dg (k := k) D ls h) =
      (ls.map fun x => mirrorWeight (k := k) D x.2.1).prod •
        (eqToHom (congrArg (pres D Sc).obj (mirrorSig_obj D t)) ≫
          (pres D Sc).diag (mkD D (ls.map mirrorLD) (sChain_mirror h)) ≫
            eqToHom (congrArg (pres D Sc).obj (mirrorSig_obj D t').symm)) := by
  rw [dg, LayerMap.freeLift_toPresented_of, weight_mkD, mirror_map_mkD, Presentation.diag_cast]

theorem mirror_idg (t : List I) :
    (freeLift k ((mirrorSig D).toLayerMap.toPresented (pres D Sc) (mirrorWeight D))).map
        (idg (k := k) D t) =
      eqToHom (congrArg (pres D Sc).obj (mirrorSig_obj D t)) ≫
          eqToHom (congrArg (pres D Sc).obj (mirrorSig_obj D t).symm) := by
  rw [idg, LayerMap.freeLift_toPresented_of, Diagram.weight_id, one_smul, LayerMap.map_id,
    Presentation.diag_id]
  simp

/-! ## Interchange of dot blocks -/

theorem diag_mkD_append {t t' t'' : List I} (A B : List (LayerData I))
    (h : SChain t (A ++ B) t'') (hA : SChain t A t') (hB : SChain t' B t'') :
    (pres D Sc).diag (mkD D (A ++ B) h) =
      (pres D Sc).diag (mkD D A hA) ≫ (pres D Sc).diag (mkD D B hB) := by
  rw [← Presentation.diag_comp]
  apply Presentation.diag_eq_of_layers_eq
  simp [layList]

theorem diag_mkD_congr {t t' : List I} {A B : List (LayerData I)} (h : SChain t A t')
    (h' : SChain t B t') (e : A = B) :
    (pres D Sc).diag (mkD D A h) = (pres D Sc).diag (mkD D B h') := by
  subst e; rfl

theorem zsign_odd_sig (g g' : Shape I) :
    ((if (sig D).odd g && (sig D).odd g' then -1 else 1 : ℤ) : k) =
      zsign k (g.parity D * g'.parity D) := by
  show ((if decide (g.parity D = 1) && decide (g'.parity D = 1) then -1 else 1 : ℤ) : k) = _
  generalize g.parity D = a; generalize g'.parity D = b
  fin_cases a <;> fin_cases b <;> simp [zsign]

section DotSwap

variable (l m v : List I) (i j : I)

/-- The word under two dot blocks. -/
abbrev swapWord : List I := l ++ [i] ++ m ++ [j] ++ v

/-- A dot on the strand `i`. -/
abbrev dotI : LayerData I := (l, Shape.dot i, m ++ [j] ++ v)

/-- A dot on the strand `j`. -/
abbrev dotJ : LayerData I := (l ++ [i] ++ m, Shape.dot j, v)

/-- The lists of dots on the two strands. -/
def IsDotList (A : List (LayerData I)) : Prop :=
  ∀ x ∈ A, x = dotI l m v i j ∨ x = dotJ l m v i j

theorem sChain_of_isDotList (A : List (LayerData I)) (hA : IsDotList l m v i j A) :
    SChain (swapWord l m v i j) A (swapWord l m v i j) := by
  induction A with
  | nil => rfl
  | cons x A ih =>
    have hx := hA x (by simp)
    have hA' : IsDotList l m v i j A := fun y hy => hA y (by simp [hy])
    rcases hx with rfl | rfl
    · refine ⟨by simp [swapWord, Shape.dom], ?_⟩
      have e : (dotI l m v i j).1 ++ (dotI l m v i j).2.1.cod ++ (dotI l m v i j).2.2 =
          swapWord l m v i j := by simp [swapWord, Shape.cod]
      rw [e]; exact ih hA'
    · refine ⟨by simp [swapWord, Shape.dom], ?_⟩
      have e : (dotJ l m v i j).1 ++ (dotJ l m v i j).2.1.cod ++ (dotJ l m v i j).2.2 =
          swapWord l m v i j := by simp [swapWord, Shape.cod]
      rw [e]; exact ih hA'

/-- The class of a list of dots on the two strands. -/
def dotDiag (A : List (LayerData I)) (hA : IsDotList l m v i j A) :
    (pres D Sc).obj (ob D (swapWord l m v i j)) ⟶ (pres D Sc).obj (ob D (swapWord l m v i j)) :=
  (pres D Sc).diag (mkD D A (sChain_of_isDotList l m v i j A hA))

theorem isDotList_append {A B : List (LayerData I)} (hA : IsDotList l m v i j A)
    (hB : IsDotList l m v i j B) : IsDotList l m v i j (A ++ B) := by
  intro x hx
  rcases List.mem_append.mp hx with h | h
  exacts [hA x h, hB x h]

theorem isDotList_I (n : ℕ) : IsDotList l m v i j (List.replicate n (dotI l m v i j)) := by
  intro x hx; exact Or.inl (List.eq_of_mem_replicate hx)

theorem isDotList_J (n : ℕ) : IsDotList l m v i j (List.replicate n (dotJ l m v i j)) := by
  intro x hx; exact Or.inr (List.eq_of_mem_replicate hx)

theorem dotDiag_append (A B : List (LayerData I)) (hA : IsDotList l m v i j A)
    (hB : IsDotList l m v i j B) :
    dotDiag D Sc l m v i j (A ++ B) (isDotList_append l m v i j hA hB) =
      dotDiag D Sc l m v i j A hA ≫ dotDiag D Sc l m v i j B hB :=
  diag_mkD_append D Sc A B _ _ _

theorem dotDiag_congr {A : List (LayerData I)} (hA : IsDotList l m v i j A)
    (B : List (LayerData I)) (e : A = B) :
    dotDiag D Sc l m v i j A hA = dotDiag D Sc l m v i j B (e ▸ hA) := by
  subst e; rfl

theorem dotDiag_IJ :
    dotDiag D Sc l m v i j [dotI l m v i j, dotJ l m v i j]
        (isDotList_append l m v i j (isDotList_I l m v i j 1) (isDotList_J l m v i j 1)) =
      zsign k (D.parity i * D.parity j) •
        dotDiag D Sc l m v i j [dotJ l m v i j, dotI l m v i j]
          (isDotList_append l m v i j (isDotList_J l m v i j 1) (isDotList_I l m v i j 1)) := by
  rw [dotDiag, dotDiag, (pres D Sc).diag_interchange_of_layers () l m v (Shape.dot i)
    (Shape.dot j) (mkD D [dotI l m v i j, dotJ l m v i j] _)
    (mkD D [dotJ l m v i j, dotI l m v i j] _) rfl rfl, zsign_odd_sig]
  rfl

/-- One dot on `i` passes a block of `b` dots on `j`. -/
theorem dotDiag_I_J (b : ℕ) :
    dotDiag D Sc l m v i j ([dotI l m v i j] ++ List.replicate b (dotJ l m v i j))
        (isDotList_append l m v i j (isDotList_I l m v i j 1) (isDotList_J l m v i j b)) =
      zsign k (D.parity i * ((b : ZMod 2) * D.parity j)) •
        dotDiag D Sc l m v i j (List.replicate b (dotJ l m v i j) ++ [dotI l m v i j])
          (isDotList_append l m v i j (isDotList_J l m v i j b) (isDotList_I l m v i j 1)) := by
  induction b with
  | zero =>
    simp only [List.replicate_zero, List.append_nil, List.nil_append, Nat.cast_zero, zero_mul,
      mul_zero, SKM.zsign_zero, one_smul]
  | succ b ih =>
    have hI := isDotList_I l m v i j
    have hJ := isDotList_J l m v i j
    have hc : ∀ {A B : List (LayerData I)}, IsDotList l m v i j A → IsDotList l m v i j B →
        IsDotList l m v i j (A ++ B) := isDotList_append l m v i j
    set x := dotI l m v i j
    set y := dotJ l m v i j
    set Y := List.replicate b y
    rw [dotDiag_congr D Sc l m v i j _ ([x, y] ++ Y)
        (by simp [x, y, Y, List.replicate_succ]),
      dotDiag_append D Sc l m v i j [x, y] Y (hc (hI 1) (hJ 1)) (hJ b), dotDiag_IJ,
      Linear.smul_comp,
      ← dotDiag_append D Sc l m v i j [y, x] Y (hc (hJ 1) (hI 1)) (hJ b),
      dotDiag_congr D Sc l m v i j _ ([y] ++ ([x] ++ Y))
        (by simp),
      dotDiag_append D Sc l m v i j [y] ([x] ++ Y) (hJ 1) (hc (hI 1) (hJ b)), ih,
      Linear.comp_smul,
      ← dotDiag_append D Sc l m v i j [y] (Y ++ [x]) (hJ 1) (hc (hJ b) (hI 1)), smul_smul,
      dotDiag_congr D Sc l m v i j _ (List.replicate (b + 1) y ++ [x])
        (by
          simp only [Y]
          rw [← List.append_assoc, List.singleton_append, ← List.replicate_succ])]
    congr 1
    rw [← SKM.zsign_add]
    congr 1
    push_cast
    ring

/-- **Interchange of dot blocks**: `a` dots on `i` and `b` dots on `j` commute up to
`(-1)^{a|i| b|j|}`. -/
theorem dotDiag_swap (a b : ℕ) :
    dotDiag D Sc l m v i j (List.replicate a (dotI l m v i j) ++ List.replicate b (dotJ l m v i j))
        (isDotList_append l m v i j (isDotList_I l m v i j a) (isDotList_J l m v i j b)) =
      zsign k ((a : ZMod 2) * D.parity i * ((b : ZMod 2) * D.parity j)) •
        dotDiag D Sc l m v i j
          (List.replicate b (dotJ l m v i j) ++ List.replicate a (dotI l m v i j))
          (isDotList_append l m v i j (isDotList_J l m v i j b) (isDotList_I l m v i j a)) := by
  have hI := isDotList_I l m v i j
  have hJ := isDotList_J l m v i j
  have hc : ∀ {A B : List (LayerData I)}, IsDotList l m v i j A → IsDotList l m v i j B →
      IsDotList l m v i j (A ++ B) := isDotList_append l m v i j
  induction a with
  | zero =>
    simp only [List.replicate_zero, List.append_nil, List.nil_append, Nat.cast_zero, zero_mul,
      SKM.zsign_zero, one_smul]
  | succ a ih =>
    set x := dotI l m v i j
    set y := dotJ l m v i j
    set Xa := List.replicate a x
    set Y := List.replicate b y
    rw [dotDiag_congr D Sc l m v i j _ ([x] ++ (Xa ++ Y))
        (by simp [x, y, Xa, Y, List.replicate_succ]),
      dotDiag_append D Sc l m v i j [x] (Xa ++ Y) (hI 1) (hc (hI a) (hJ b)), ih,
      Linear.comp_smul,
      ← dotDiag_append D Sc l m v i j [x] (Y ++ Xa) (hI 1) (hc (hJ b) (hI a)),
      dotDiag_congr D Sc l m v i j _ (([x] ++ Y) ++ Xa)
        (by simp),
      dotDiag_append D Sc l m v i j ([x] ++ Y) Xa (hc (hI 1) (hJ b)) (hI a), dotDiag_I_J,
      Linear.smul_comp,
      ← dotDiag_append D Sc l m v i j (Y ++ [x]) Xa (hc (hJ b) (hI 1)) (hI a), smul_smul,
      dotDiag_congr D Sc l m v i j _ (Y ++ List.replicate (a + 1) x)
        (by simp [Xa, List.replicate_succ])]
    congr 1
    rw [← SKM.zsign_add]
    congr 1
    push_cast
    ring

end DotSwap

end OddMath.QuiverHecke

namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams
open SKM (zsign)
variable {I : Type*} {X : Type*} [AddCommGroup X] (D : SKM.Datum I X)
variable {k : Type*} [CommRing k] (Sc : SKM.Scalars D k)

/-- The weighted reflection, as a functor on linear combinations of diagrams. -/
abbrev mirrorLin : (Free k (Obj (sig D))) ⥤ (pres D Sc).Presented :=
  freeLift k ((mirrorSig D).toLayerMap.toPresented (pres D Sc) (mirrorWeight D))

/-- Expand the image of a relation and a relation of the target into classes of diagrams. -/
macro "mirror_expand" : tactic => `(tactic|
  simp only [relation, Functor.map_sub, Functor.map_smul, mirror_dg, mirror_idg,
    eqToHom_refl, Category.id_comp, Category.comp_id, dotsL, crossL, List.map_replicate,
    List.map_cons, List.map_nil, List.map_append, List.replicate_one, mirrorLD, Shape.mirror,
    List.reverse_nil, List.reverse_cons, List.nil_append, List.cons_append, List.prod_cons,
    List.prod_nil, List.singleton_append, mirrorWeight, mul_one, one_mul,
    Presentation.lin_sub, Presentation.lin_smul, Presentation.lin_of, smul_sub])

theorem mirror_rel_of {r : Rel D} (r' : Rel D) (hd : r'.dom = r.dom.reverse)
    (hc : r'.cod = r.cod.reverse) (c : k)
    (h : (mirrorLin D Sc).map (relation D Sc r) =
      c • (eqToHom (congrArg (pres D Sc).obj ((mirrorSig_obj D r.dom).trans (by rw [hd]))) ≫
        (pres D Sc).lin (relation D Sc r') ≫
          eqToHom (congrArg (pres D Sc).obj ((mirrorSig_obj D r.cod).trans (by rw [hc])).symm))) :
    (mirrorLin D Sc).map ((pres D Sc).rel r) = 0 := by
  have h' := (pres D Sc).lin_rel_self r'
  change (pres D Sc).lin (relation D Sc r') = 0 at h'
  change (mirrorLin D Sc).map (relation D Sc r) = 0
  rw [h, h']
  simp

theorem mirror_rel_quadEq (i : I) :
    (mirrorLin D Sc).map ((pres D Sc).rel (Rel.quadEq i)) = 0 := by
  refine mirror_rel_of D Sc (.quadEq i) rfl rfl 1 ?_
  mirror_expand
  generalize D.parity i = a
  fin_cases a <;> simp [zsign]

theorem mirror_rel_quadZero (i j : I) (hij : i ≠ j) (hd : D.d i j = 0) :
    (mirrorLin D Sc).map ((pres D Sc).rel (Rel.quadZero i j hij hd)) = 0 := by
  refine mirror_rel_of D Sc (.quadZero j i hij.symm ((D.d_eq_zero_iff i j).mp hd)) rfl rfl 1 ?_
  mirror_expand
  rw [Sc.t_symm_of_d_eq_zero i j hd]
  generalize D.parity i = a
  generalize D.parity j = b
  fin_cases a <;> fin_cases b <;> simp [zsign] <;> rfl

theorem mirror_rel_slideL (i j : I) (hij : i ≠ j) :
    (mirrorLin D Sc).map ((pres D Sc).rel (Rel.slideL i j hij)) = 0 := by
  refine mirror_rel_of D Sc (.slideR j i hij.symm) rfl rfl 1 ?_
  mirror_expand
  generalize D.parity i = a
  generalize D.parity j = b
  fin_cases a <;> fin_cases b <;> simp [zsign] <;> module

theorem mirror_rel_slideR (i j : I) (hij : i ≠ j) :
    (mirrorLin D Sc).map ((pres D Sc).rel (Rel.slideR i j hij)) = 0 := by
  refine mirror_rel_of D Sc (.slideL j i hij.symm) rfl rfl 1 ?_
  mirror_expand
  generalize D.parity i = a
  generalize D.parity j = b
  fin_cases a <;> fin_cases b <;> simp [zsign] <;> module

theorem mirror_rel_slideLEq (i : I) :
    (mirrorLin D Sc).map ((pres D Sc).rel (Rel.slideLEq i)) = 0 := by
  refine mirror_rel_of D Sc (.slideREq i) rfl rfl 1 ?_
  mirror_expand
  generalize D.parity i = a
  fin_cases a <;> simp [zsign] <;> module

theorem mirror_rel_slideREq (i : I) :
    (mirrorLin D Sc).map ((pres D Sc).rel (Rel.slideREq i)) = 0 := by
  refine mirror_rel_of D Sc (.slideLEq i) rfl rfl 1 ?_
  mirror_expand
  generalize D.parity i = a
  fin_cases a <;> simp [zsign] <;> module

theorem mirror_rel_braid (i j m : I) (h : ¬(i = m ∧ i ≠ j)) :
    (mirrorLin D Sc).map ((pres D Sc).rel (Rel.braid i j m h)) = 0 := by
  refine mirror_rel_of D Sc (.braid m j i fun ⟨e, hne⟩ => h ⟨e.symm, e ▸ hne⟩) rfl rfl
    (zsign k (D.parity i * D.parity j) * zsign k (D.parity i * D.parity m) *
      zsign k (D.parity j * D.parity m)) ?_
  mirror_expand
  generalize D.parity i = a
  generalize D.parity j = b
  generalize D.parity m = c
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp [zsign] <;> module

theorem lin_sum {a b : Obj (sig D)} {ι : Type*} (s : Finset ι) (f : ι → LinDiagram k a b) :
    (pres D Sc).lin (∑ x ∈ s, f x) = ∑ x ∈ s, (pres D Sc).lin (f x) := by
  simp only [Presentation.lin, Functor.map_sum]

/-- Two dot blocks on distinct strands commute up to the Koszul sign, for normal-form diagrams
on any word equal to the underlying word. -/
theorem diag_dots_swap {t : List I} (l m v : List I) (i j : I) (a b : ℕ) (x y : LayerData I)
    (ht : t = swapWord l m v i j) (hx : x = dotI l m v i j) (hy : y = dotJ l m v i j)
    (h : SChain t (List.replicate a x ++ List.replicate b y) t)
    (h' : SChain t (List.replicate b y ++ List.replicate a x) t) :
    (pres D Sc).diag (mkD D _ h) =
      zsign k ((a : ZMod 2) * D.parity i * ((b : ZMod 2) * D.parity j)) •
        (pres D Sc).diag (mkD D _ h') := by
  subst ht hx hy
  exact dotDiag_swap D Sc l m v i j a b

theorem zmod2_eq_zero_of_ne_one {a : ZMod 2} (h : a ≠ 1) : a = 0 := by
  fin_cases a
  · rfl
  · exact absurd rfl h

theorem mirror_rel_quadNe (i j : I) (hij : i ≠ j) (hd : D.d i j ≠ 0) :
    (mirrorLin D Sc).map ((pres D Sc).rel (Rel.quadNe i j hij hd)) = 0 := by
  refine mirror_rel_of D Sc (.quadNe j i hij.symm (fun h => hd ((D.d_eq_zero_iff j i).mp h)))
    rfl rfl 1 ?_
  mirror_expand
  simp only [List.prod_replicate, one_pow, one_smul, Functor.map_sum, Functor.map_smul,
    mirror_dg, lin_sum, Presentation.lin_smul, Presentation.lin_of, List.map_append,
    List.map_replicate, mirrorLD, Shape.mirror, mirrorWeight, List.reverse_nil,
    List.reverse_cons, List.nil_append, List.prod_append, mul_one, eqToHom_refl,
    Category.id_comp, Category.comp_id]
  have hc : -zsign k (D.parity i * D.parity j) * -zsign k (D.parity j * D.parity i) = 1 := by
    rw [mul_comm (D.parity j)]
    generalize D.parity i * D.parity j = a
    fin_cases a <;> simp [zsign]
  rw [hc, one_smul]
  congr 1
  · exact sub_right_comm _ _ _
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
  rw [Sc.s_symm i j x y]
  by_cases hs : Sc.s j i y x = 0
  · simp [hs]
  rw [diag_dots_swap D Sc (t := [j, i]) [] [] [] j i y x ([], Shape.dot j, [i])
    ([j], Shape.dot i, []) rfl rfl rfl,
    zmod2_eq_zero_of_ne_one (a := (y : ZMod 2) * D.parity j)
      (fun h => hs (Sc.s_eq_zero j i y x h)), zero_mul, SKM.zsign_zero, one_smul]

/-- A list of dot layers, each on a strand of the word `t`, is a normal-form chain on `t`. -/
theorem sChain_of_dots (t : List I) (L : List (LayerData I))
    (hL : ∀ x ∈ L, ∃ c, x.2.1 = Shape.dot c ∧ x.1 ++ [c] ++ x.2.2 = t) : SChain t L t := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    obtain ⟨c, hc, he⟩ := hL x (by simp)
    obtain ⟨u, g, w⟩ := x
    simp only at hc he
    subst hc
    refine ⟨by simpa [Shape.dom] using he.symm, ?_⟩
    have e : u ++ (Shape.dot c).cod ++ w = t := by simpa [Shape.cod] using he
    rw [e]
    exact ih fun y hy => hL y (by simp [hy])

/-- Dots on the outer strands of `i j i` pass each other, up to the Koszul sign. -/
theorem braidEq_dots_two (i j : I) (a b : ℕ) (c : k)
    (hab : ((a + b + 1 : ℕ) : ZMod 2) * D.parity i = 0)
    (h : SChain [i, j, i] (List.replicate a ([], Shape.dot i, [j, i]) ++
      List.replicate b ([i, j], Shape.dot i, [])) [i, j, i])
    (h' : SChain [i, j, i] (List.replicate b ([i, j], Shape.dot i, []) ++
      List.replicate a ([], Shape.dot i, [j, i])) [i, j, i]) :
    (zsign k (D.parity i * (D.parity j + a)) * c) • (pres D Sc).diag (mkD D _ h) =
      zsign k (D.parity i * D.parity i) •
        ((zsign k (D.parity i * (D.parity j + b)) * c) • (pres D Sc).diag (mkD D _ h')) := by
  rw [diag_dots_swap D Sc (t := [i, j, i]) [] [j] [] i i a b ([], Shape.dot i, [j, i])
    ([i, j], Shape.dot i, []) rfl rfl rfl h h', smul_smul, smul_smul]
  congr 1
  have key : zsign k (D.parity i * (D.parity j + a)) *
      zsign k ((a : ZMod 2) * D.parity i * ((b : ZMod 2) * D.parity i)) =
      zsign k (D.parity i * D.parity i) * zsign k (D.parity i * (D.parity j + b)) := by
    push_cast at hab
    revert hab
    generalize D.parity i = x
    generalize D.parity j = y
    generalize (a : ZMod 2) = a'
    generalize (b : ZMod 2) = b'
    fin_cases x <;> fin_cases y <;> fin_cases a' <;> fin_cases b' <;> simp [zsign]
  linear_combination c * key

/-- Membership in a concatenation of blocks of repeated layers. -/
local macro "dots_mem" : tactic => `(tactic|
  (intro x hx; simp only [List.mem_append, List.mem_replicate] at hx; tauto))

local notation "rep" => List.replicate

/-- Dots on the three strands of `i j i`: the outer blocks exchange past the middle one. -/
theorem braidEq_dots_three (i j : I) (a q b : ℕ) (c : k)
    (hab : ((a + b + 1 : ℕ) : ZMod 2) * D.parity i = 0) (hq : (q : ZMod 2) * D.parity j = 0)
    (h : SChain [i, j, i] (List.replicate a ([], Shape.dot i, [j, i]) ++
      List.replicate q ([i], Shape.dot j, [i]) ++
      List.replicate b ([i, j], Shape.dot i, [])) [i, j, i])
    (h' : SChain [i, j, i] (List.replicate b ([i, j], Shape.dot i, []) ++
      List.replicate q ([i], Shape.dot j, [i]) ++
      List.replicate a ([], Shape.dot i, [j, i])) [i, j, i]) :
    (zsign k (D.parity i * (D.parity j + a)) * c) • (pres D Sc).diag (mkD D _ h) =
      zsign k (D.parity i * D.parity i) •
        ((zsign k (D.parity i * (D.parity j + b)) * c) • (pres D Sc).diag (mkD D _ h')) := by
  set A : LayerData I := ([], Shape.dot i, [j, i]) with hA
  set C : LayerData I := ([i], Shape.dot j, [i]) with hC
  set B : LayerData I := ([i, j], Shape.dot i, []) with hB
  have sc : ∀ L : List (LayerData I), (∀ x ∈ L, x = A ∨ x = C ∨ x = B) →
      SChain [i, j, i] L [i, j, i] := fun L hL => sChain_of_dots _ L fun x hx => by
    rcases hL x hx with rfl | rfl | rfl
    exacts [⟨i, rfl, rfl⟩, ⟨j, rfl, rfl⟩, ⟨i, rfl, rfl⟩]
  rw [diag_mkD_append D Sc (rep a A ++ rep q C) (rep b B) h _ _,
    diag_dots_swap D Sc (t := [i, j, i]) [] [] [i] i j a q A C rfl rfl rfl _ _,
    Linear.smul_comp, ← diag_mkD_append D Sc (rep q C ++ rep a A) (rep b B) _,
    diag_mkD_congr D Sc (A := rep q C ++ rep a A ++ rep b B)
      (B := rep q C ++ (rep a A ++ rep b B)) _ _ (List.append_assoc _ _ _),
    diag_mkD_append D Sc (rep q C) (rep a A ++ rep b B) _ _ _,
    diag_dots_swap D Sc (t := [i, j, i]) [] [j] [] i i a b A B rfl rfl rfl _ _,
    Linear.comp_smul, ← diag_mkD_append D Sc (rep q C) (rep b B ++ rep a A) _,
    diag_mkD_congr D Sc (A := rep q C ++ (rep b B ++ rep a A))
      (B := rep q C ++ rep b B ++ rep a A) _ _ (List.append_assoc _ _ _).symm,
    diag_mkD_append D Sc (rep q C ++ rep b B) (rep a A) _ _ _,
    diag_dots_swap D Sc (t := [i, j, i]) [i] [] [] j i q b C B rfl rfl rfl _ _,
    Linear.smul_comp, ← diag_mkD_append D Sc (rep b B ++ rep q C) (rep a A) h']
  all_goals try exact sc _ (by dots_mem)
  simp only [smul_smul]
  congr 1
  have key : zsign k (D.parity i * (D.parity j + a)) *
      (zsign k ((a : ZMod 2) * D.parity i * ((q : ZMod 2) * D.parity j)) *
        (zsign k ((a : ZMod 2) * D.parity i * ((b : ZMod 2) * D.parity i)) *
          zsign k ((q : ZMod 2) * D.parity j * ((b : ZMod 2) * D.parity i)))) =
      zsign k (D.parity i * D.parity i) * zsign k (D.parity i * (D.parity j + b)) := by
    push_cast at hab
    revert hab hq
    generalize D.parity i = x
    generalize D.parity j = y
    generalize (a : ZMod 2) = a'
    generalize (b : ZMod 2) = b'
    generalize (q : ZMod 2) = q'
    fin_cases x <;> fin_cases y <;> fin_cases a' <;> fin_cases b' <;> fin_cases q' <;>
      simp [zsign]
  linear_combination c * key

theorem braidEq_rearrange {M : Type*} [AddCommGroup M] [Module k M] (z : k)
    (T₁ T₂ S₁ S₁' S₂ S₂' : M) (h₁ : S₁ = z • S₁') (h₂ : S₂ = z • S₂') :
    -z • T₂ - -z • T₁ - S₁ - S₂ = z • T₁ - z • T₂ - z • S₁' - z • S₂' := by
  subst h₁ h₂
  module

theorem mirror_rel_braidEq (i j : I) (hij : i ≠ j) :
    (mirrorLin D Sc).map ((pres D Sc).rel (Rel.braidEq i j hij)) = 0 := by
  refine mirror_rel_of D Sc (.braidEq i j hij) rfl rfl (zsign k (D.parity i * D.parity i)) ?_
  mirror_expand
  simp only [List.prod_replicate, one_pow, one_smul, Functor.map_sum, Functor.map_smul,
    mirror_dg, lin_sum, Presentation.lin_smul, Presentation.lin_of, List.map_append,
    List.map_replicate, mirrorLD, Shape.mirror, mirrorWeight, List.reverse_nil,
    List.reverse_cons, List.nil_append, List.cons_append, List.prod_append, mul_one,
    eqToHom_refl, Category.id_comp, Category.comp_id]
  have hw : ∀ x y : ZMod 2, -zsign k (x * y) * (-zsign k (x * x) * -zsign k (y * x)) =
      -zsign k (x * x) := by
    intro x y
    fin_cases x <;> fin_cases y <;> simp [zsign]
  have hw' : ∀ x y : ZMod 2, -zsign k (y * x) * (-zsign k (x * x) * -zsign k (x * y)) =
      -zsign k (x * x) := by
    intro x y
    fin_cases x <;> fin_cases y <;> simp [zsign]
  rw [hw, hw']
  refine braidEq_rearrange _ _ _ _ _ _ _ ?_ ?_
  · rw [Finset.smul_sum, ← Finset.sum_range_reflect _ (D.dn i j)]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hx' := Finset.mem_range.mp hx
    have e : D.dn i j - 1 - (D.dn i j - 1 - x) = x := by omega
    simp only [e]
    refine braidEq_dots_two D Sc i j _ _ _ ?_ _ _
    rw [show D.dn i j - 1 - x + x + 1 = D.dn i j by omega, mul_comm]
    exact SKM.parity_mul_dn D i j
  · rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.smul_sum, ← Finset.sum_range_reflect _ x]
    refine Finset.sum_congr rfl fun z hz => ?_
    have hz' := Finset.mem_range.mp hz
    by_cases hs : Sc.s i j x y = 0
    · simp [hs]
    have e : x - 1 - (x - 1 - z) = z := by omega
    simp only [e]
    refine braidEq_dots_three D Sc i j _ _ _ _ ?_ ?_ _ _
    · rw [show x - 1 - z + z + 1 = x by omega]
      exact zmod2_eq_zero_of_ne_one fun h => hs (Sc.s_eq_zero i j x y h)
    · exact zmod2_eq_zero_of_ne_one fun h =>
        hs (by rw [Sc.s_symm]; exact Sc.s_eq_zero j i y x h)

/-- The weighted reflection kills every defining relation. -/
theorem mirror_rel (r : Rel D) : (mirrorLin D Sc).map ((pres D Sc).rel r) = 0 := by
  cases r with
  | quadEq i => exact mirror_rel_quadEq D Sc i
  | quadZero i j hij hd => exact mirror_rel_quadZero D Sc i j hij hd
  | quadNe i j hij hd => exact mirror_rel_quadNe D Sc i j hij hd
  | slideL i j hij => exact mirror_rel_slideL D Sc i j hij
  | slideLEq i => exact mirror_rel_slideLEq D Sc i
  | slideR i j hij => exact mirror_rel_slideR D Sc i j hij
  | slideREq i => exact mirror_rel_slideREq D Sc i
  | braid i j m h => exact mirror_rel_braid D Sc i j m h
  | braidEq i j hij => exact mirror_rel_braidEq D Sc i j hij

/-- **Reflection of the quiver Hecke supercategory** in a vertical axis. It reverses words,
sends a dot to a dot and the crossing of `i` and `j` to `-(-1)^{|i||j|}` times the crossing of
`j` and `i`. -/
def mirrorFunctor : (pres D Sc).Presented ⥤ (pres D Sc).Presented :=
  (mirrorSig D).lift (pres D Sc) (mirrorSig_odd D) (pres D Sc).wfDom_of_subsingleton
    (mirror_rel D Sc)

theorem mirrorFunctor_obj (t : List I) :
    (mirrorFunctor D Sc).obj ((pres D Sc).obj (ob D t)) = (pres D Sc).obj (ob D t.reverse) := by
  exact congrArg (pres D Sc).obj (mirrorSig_obj D t)

theorem mirrorFunctor_diag {a b : Obj (sig D)} (d : a ⟶ b) :
    (mirrorFunctor D Sc).map ((pres D Sc).diag d) =
      Diagram.weight (mirrorWeight (k := k) D) d •
        (pres D Sc).diag ((mirrorSig D).toLayerMap.map d) :=
  SigMirror.lift_diag _ _ _ _ d

end OddMath.QuiverHecke
