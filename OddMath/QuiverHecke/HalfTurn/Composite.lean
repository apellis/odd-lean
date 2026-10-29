/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.HalfTurn.SuperFlip

/-!
# The half-turn of the quiver Hecke supercategory

The map `U` of `docs/Nondegeneracy/SwappedVacuumCoordinates.md` §4: the composite of the
reflection `mirrorFunctor` in a vertical axis and the reflection `flipFunctor` in a horizontal
axis. It is a contravariant superfunctor from the quiver Hecke supercategory with parameters `Sc`
to the one with parameters `parameterTwist D Sc`. It reverses words, sends the layer `u ⊗ g ⊗ v`
to `v^rev ⊗ g ⊗ u^rev` (so a dot at position `r` of an `n`-strand word goes to a dot at position
`n + 1 - r`, and the crossing at `r` to the crossing at `n - r`), reverses vertical composition with
the Koszul sign of the super-opposite, and multiplies each crossing of `i` and `j` by
`ε_ij`, with `ε_ii = -1` and `ε_ij = 1` for `i ≠ j`: the two reflection weights
`-(-1)^{|i||j|}` and `-(-1)^{|i||j|} ε_ij` multiply to `ε_ij`.

## Main declarations

* `halfTurnFunctor D Sc`: the composite superfunctor.
* `halfTurnWeight`, `halfTurnC`: the weight `ε_ij` of a crossing and the scalar of a reflected
  normal-form diagram (weights and Koszul signs of the reversal).
* `halfTurn_mkD`: the image of a normal-form diagram.
* `halfTurn_dot`, `halfTurn_cross`: the generator table of §4.
-/
noncomputable section
open scoped Classical
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams Supercategory
open SKM (zsign)
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X) [CommRing k]
  (Sc : SKM.Scalars D k)

/-- **The half-turn** `U` of `SwappedVacuumCoordinates.md` §4: reflection in a vertical axis
followed by reflection in a horizontal axis. -/
def halfTurnFunctor : (pres D Sc).Presented ⥤ SOp k (pres D (parameterTwist D Sc)).Presented :=
  mirrorFunctor D Sc ⋙ flipFunctor D Sc

instance flipFunctor_linear : (flipFunctor D Sc).Linear k := by
  unfold flipFunctor; infer_instance

theorem flipFunctor_diag {a b : Obj (sig D)} (d : a ⟶ b) :
    (flipFunctor D Sc).map ((pres D Sc).diag d) =
      (SOpMap.functor (flipMap D) (flipImg D (parameterTwist D Sc))).map d := by
  unfold flipFunctor; exact SOpMap.liftGen_diag _ _ _ d

/-- The weight of the half-turn: `1` on dots and `ε_ij` on the crossing of `i` and `j`. -/
def halfTurnWeight : Shape I → k
  | .dot _ => 1
  | .cross i j => if i = j then -1 else 1

/-- The half-turn of a contextual generator: `u ⊗ g ⊗ v ↦ v^rev ⊗ g ⊗ u^rev`. -/
def halfTurnLD (x : LayerData I) : LayerData I := (x.2.2.reverse, x.2.1, x.1.reverse)

/-- The layers of the half-turned diagram, in reverse order. -/
def halfTurnL (ls : List (LayerData I)) : List (LayerData I) := (ls.map halfTurnLD).reverse

/-- The scalar of a half-turned normal-form diagram: the weights `ε_ij` and the Koszul signs of
the reversal of vertical composition. -/
def halfTurnC : List (LayerData I) → k
  | [] => 1
  | x :: ls => zsign k (x.2.1.parity D * psum D ls) * halfTurnWeight x.2.1 * halfTurnC ls

@[simp] theorem halfTurnC_nil : halfTurnC (k := k) D [] = 1 := rfl

theorem halfTurnC_cons (x : LayerData I) (ls : List (LayerData I)) :
    halfTurnC (k := k) D (x :: ls) =
      zsign k (x.2.1.parity D * psum D ls) * halfTurnWeight x.2.1 * halfTurnC D ls := rfl

@[simp] theorem halfTurnC_singleton (x : LayerData I) :
    halfTurnC (k := k) D [x] = halfTurnWeight x.2.1 := by
  simp [halfTurnC, psum, SKM.zsign]

theorem flipL_map_mirrorLD (ls : List (LayerData I)) :
    flipL (ls.map mirrorLD) = halfTurnL ls := by
  simp only [flipL, halfTurnL, List.map_map]
  congr 1
  refine List.map_congr_left fun x _ => ?_
  obtain ⟨u, g, v⟩ := x
  cases g <;> rfl

theorem sChain_halfTurnL {t t' : List I} {ls : List (LayerData I)} (h : SChain t ls t') :
    SChain t'.reverse (halfTurnL ls) t.reverse :=
  flipL_map_mirrorLD ls ▸ sChain_flipL (sChain_mirror h)

theorem psum_map_mirrorLD (ls : List (LayerData I)) : psum D (ls.map mirrorLD) = psum D ls := by
  simp only [psum, List.map_map]
  congr 1
  refine List.map_congr_left fun x _ => ?_
  exact Shape.parity_mirror D x.2.1

theorem mirrorWeight_mul_flipWeight (g : Shape I) :
    mirrorWeight (k := k) D g * flipWeight D g.mirror = halfTurnWeight g := by
  cases g with
  | dot i => simp [mirrorWeight, flipWeight, halfTurnWeight, Shape.mirror]
  | cross i j =>
    simp only [mirrorWeight, flipWeight, halfTurnWeight, Shape.mirror]
    have h2 : zsign k (D.parity i * D.parity j) * zsign k (D.parity j * D.parity i) = 1 := by
      rw [← SKM.zsign_add, mul_comm (D.parity j), ← two_mul,
        show (2 : ZMod 2) = 0 from rfl, zero_mul]
      simp [SKM.zsign]
    by_cases hij : i = j
    · subst hij; simp only [ite_true]; linear_combination -h2
    · simp only [hij, Ne.symm hij, ite_false]; linear_combination h2

/-- The mirror weights times the scalar of the flip are the scalar of the half-turn. -/
theorem mirror_prod_mul_flipC (ls : List (LayerData I)) :
    (ls.map fun x => mirrorWeight (k := k) D x.2.1).prod * flipC D (ls.map mirrorLD) =
      halfTurnC D ls := by
  induction ls with
  | nil => simp
  | cons x ls ih =>
    obtain ⟨u, g, v⟩ := x
    simp only [List.map_cons, List.prod_cons, flipC_cons, halfTurnC_cons, mirrorLD,
      psum_map_mirrorLD, Shape.parity_mirror, ← ih, ← mirrorWeight_mul_flipWeight D g]
    ring

theorem halfTurn_obj (t : List I) :
    (flipMap D).obj ((mirrorSig D).toLayerMap.obj (ob D t)) = ob D t.reverse := by
  rw [mirrorSig_obj]; rfl

set_option backward.isDefEq.respectTransparency false in
theorem flip_cast_mkD {t t' : List I} (ls : List (LayerData I)) (h : SChain t ls t')
    {a b : Obj (sig D)} (ha : ob D t = a) (hb : ob D t' = b) :
    SOp.unsop ((SOpMap.functor (flipMap D) (flipImg D Sc)).map (Diagram.cast (mkD D ls h) ha hb)) =
      flipC (k := k) D ls • (pres D Sc).diag
        (Diagram.cast (mkD D (flipL ls) (sChain_flipL h)) hb ha) := by
  subst ha hb
  exact flip_mkD D Sc ls h

set_option backward.isDefEq.respectTransparency false in
/-- **The half-turn of a normal-form diagram**: the half-turned layers in reverse order, times
`halfTurnC`, the product of the crossing weights `ε_ij` and the Koszul signs of the reversal. -/
theorem halfTurn_mkD {t t' : List I} (ls : List (LayerData I)) (h : SChain t ls t') :
    SOp.unsop ((halfTurnFunctor D Sc).map ((pres D Sc).diag (mkD D ls h))) =
      halfTurnC (k := k) D ls • (pres D (parameterTwist D Sc)).diag
        (Diagram.cast (mkD D (halfTurnL ls) (sChain_halfTurnL h)) (halfTurn_obj D t').symm
          (halfTurn_obj D t).symm) := by
  change SOp.unsop ((flipFunctor D Sc).map ((mirrorFunctor D Sc).map _)) = _
  rw [mirrorFunctor_diag, Functor.map_smul, SOp.unsop_smul,
    weight_mkD, mirror_map_mkD, flipFunctor_diag, flip_cast_mkD, smul_smul,
    mirror_prod_mul_flipC]
  congr 1
  apply Presentation.diag_eq_of_layers_eq
  simp only [Diagram.layers_cast, layers_mkD, flipL_map_mirrorLD]

/-- The half-turn of a dot in context: a dot on the reflected strand. -/
theorem halfTurn_dot (u : List I) (i : I) (v : List I) :
    SOp.unsop ((halfTurnFunctor D Sc).map ((pres D Sc).diag
      (mkD D [(u, Shape.dot i, v)] (t := u ++ [i] ++ v) (t' := u ++ [i] ++ v) ⟨rfl, rfl⟩))) =
      (pres D (parameterTwist D Sc)).diag
        (Diagram.cast (mkD D [(v.reverse, Shape.dot i, u.reverse)]
          (t := v.reverse ++ [i] ++ u.reverse) (t' := v.reverse ++ [i] ++ u.reverse)
          ⟨rfl, rfl⟩) ((congrArg (ob D) (by simp)).trans (halfTurn_obj D (u ++ [i] ++ v)).symm)
          ((congrArg (ob D) (by simp)).trans (halfTurn_obj D (u ++ [i] ++ v)).symm)) := by
  rw [halfTurn_mkD, halfTurnC_singleton, halfTurnWeight, one_smul]
  apply Presentation.diag_eq_of_layers_eq
  simp [halfTurnL, halfTurnLD]

/-- The half-turn of a crossing in context: `ε_ij` times the crossing of the reflected strands,
in the reverse direction. -/
theorem halfTurn_cross (u : List I) (i j : I) (v : List I) :
    SOp.unsop ((halfTurnFunctor D Sc).map ((pres D Sc).diag
      (mkD D [(u, Shape.cross i j, v)] (t := u ++ [i, j] ++ v) (t' := u ++ [j, i] ++ v)
        ⟨rfl, rfl⟩))) =
      (if i = j then -1 else 1 : k) • (pres D (parameterTwist D Sc)).diag
        (Diagram.cast (mkD D [(v.reverse, Shape.cross i j, u.reverse)]
          (t := v.reverse ++ [i, j] ++ u.reverse) (t' := v.reverse ++ [j, i] ++ u.reverse)
          ⟨rfl, rfl⟩) ((congrArg (ob D) (by simp)).trans (halfTurn_obj D (u ++ [j, i] ++ v)).symm)
          ((congrArg (ob D) (by simp)).trans (halfTurn_obj D (u ++ [i, j] ++ v)).symm)) := by
  rw [halfTurn_mkD, halfTurnC_singleton, halfTurnWeight]
  congr 1

end OddMath.QuiverHecke
