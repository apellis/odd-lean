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
def IsDotList (A : List (LayerData I)) : Prop := ∀ x ∈ A, x = dotI l m v i j ∨ x = dotJ l m v i j

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
