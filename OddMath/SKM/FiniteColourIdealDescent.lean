/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.FiniteColourContextLift

/-!
# Finite-colour descent of presentation-ideal derivations

The finite-span step of `SwappedActionAssembly`, §8, for Brundan–Ellis
Definition 1.5. A derivation supported on a finite colour set lifts into the
actual presentation ideal on the restricted datum, at fixed common endpoints.
The original weight group and arbitrary commutative coefficient ring are retained.
-/

noncomputable section
namespace OddMath.SKM.FiniteColour
open CategoryTheory StringDiagrams
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : Datum I X) (J : Finset I)
variable {k : Type w} [CommRing k] (Sc : Scalars D k)

/-- The linear inclusion at prescribed supported endpoints. -/
private def inclusionAt {a b : Obj (sig D)}
    (a' b' : Obj (sig (D.restrictColours J)))
    (ha : (inclusion D J).obj a' = a) (hb : (inclusion D J).obj b' = b) :
    LinDiagram k a' b' →ₗ[k] LinDiagram k a b where
  toFun f := LinDiagram.cast ((inclusion D J).toLayerMap.lin f) ha hb
  map_add' f g := by simp only [LayerMap.lin_add, LinDiagram.cast_add]
  map_smul' r f := by simp only [LayerMap.lin_smul, LinDiagram.cast_smul, RingHom.id_apply]

/-- A supported finite-span derivation lifts to the restricted presentation ideal
at any fixed restricted endpoints mapping to the original endpoints. -/
theorem supported_ideal_lift_at {a b : Obj (sig D)}
    (a' b' : Obj (sig (D.restrictColours J)))
    (ha : (inclusion D J).obj a' = a) (hb : (inclusion D J).obj b' = b)
    {f : LinDiagram k a b} (hf : f ∈ finiteColourIdeal D Sc a b J) :
    ∃ f' : LinDiagram k a' b',
      f' ∈ (pres (D.restrictColours J) (Sc.restrictColours D J)).ideal a' b' ∧
      LinDiagram.cast ((inclusion D J).toLayerMap.lin f') ha hb = f := by
  let φ := inclusionAt D J (k := k) a' b' ha hb
  change f ∈ finiteColourIdeal D Sc a b J at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, hc, rfl⟩ := hx
    obtain ⟨L⟩ := supported_context_lift D J Sc c hc
    have ea : L.source = a' := inclusion_obj_injective D J (L.source_eq.trans ha.symm)
    have eb : L.target = b' := inclusion_obj_injective D J (L.target_eq.trans hb.symm)
    cases ea
    cases eb
    refine ⟨L.context.value, Submodule.subset_span L.idealGen, ?_⟩
    exact L.value_eq
  | zero =>
    refine ⟨0, Submodule.zero_mem _, ?_⟩
    exact φ.map_zero
  | add x y _ _ hx hy =>
    obtain ⟨x', hx', ex⟩ := hx
    obtain ⟨y', hy', ey⟩ := hy
    refine ⟨x' + y', Submodule.add_mem _ hx' hy', ?_⟩
    change φ x' = x at ex
    change φ y' = y at ey
    change φ (x' + y') = x + y
    rw [map_add, ex, ey]
  | smul r x _ hx =>
    obtain ⟨x', hx', ex⟩ := hx
    refine ⟨r • x', Submodule.smul_mem _ r hx', ?_⟩
    change φ x' = x at ex
    change φ (r • x') = r • x
    rw [map_smul, ex]

end OddMath.SKM.FiniteColour
