import OddMath.SKM.SameColourSourceFrame
import OddMath.SKM.PairedSorting
import OddMath.SKM.SpanClosed
import OddMath.SKM.SpanLocal2

/-! Evaluation of the actual source serializers. On the original FE side
completion puts the cap dots on the downward (left) leg, hence the native
operator here is `dLM`, not `uRM`. -/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Presentation
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k}

private theorem source_repeat_chain {a : List (Letter I)} {ls : List (XLayer I)}
    (h : XChain a ls a) (n : ℕ) : XChain a (List.replicate n ls).flatten a := by
  induction n with
  | zero => exact rfl
  | succ n ih => simpa only [List.replicate_succ, List.flatten_cons] using h.append ih

private theorem source_repeat_eval (cs : CScalars Sc) (μ : X)
    {a : List (Letter I)} {ls : List (XLayer I)} (h : XChain a ls a) (n : ℕ) :
    xev cs μ a a (List.replicate n ls).flatten = cpow (xev cs μ a a ls) n := by
  induction n with
  | zero => simp [xev_nil, cl_nil]
  | succ n ih =>
    rw [List.replicate_succ, List.flatten_cons, xev_append cs _ h, ih, cpow_succ']

/-- The literal local cap layers, with all dots on the left selected endpoint. -/
def sourceCapLayers (ε : Bool) (i : I) (b : ℕ) : List (XLayer I) :=
  (List.replicate b ((xDotL (!ε, i)).map (xwhL [] [(ε, i)]))).flatten ++ xCapL (ε, i)

theorem sourceCapLayers_chain (ε : Bool) (i : I) (b : ℕ) :
    XChain [(!ε, i), (ε, i)] (sourceCapLayers ε i b) [] := by
  apply XChain.append (source_repeat_chain _ b) (xChain_xCapL (ε, i))
  simpa [flipL] using (xChain_xDotL (!ε, i)).whisk [] [(ε, i)]

theorem sourceCapLayers_context (P Q : List (Letter I)) (ε : Bool) (i : I) (b : ℕ) :
    (sourceCapLayers ε i b).map (xwhL P Q) =
      (List.replicate b (dotOn (P ++ (!ε, i) :: (ε, i) :: Q) P.length)).flatten ++
        (xCapL (ε, i)).map (xwhL P Q) := by
  simp only [sourceCapLayers, List.map_append, List.map_flatten, List.map_replicate, List.map_map]
  congr 3
  simp [dotOn, xwhL, Function.comp_def]

theorem sourceCapLayers_up_eval (cs : CScalars Sc) (μ : X) (i : I) (b : ℕ) :
    xev cs μ [dn i, up i] [] (sourceCapLayers true i b) =
      cpow (dLM D Sc i μ) b ≫ epsP cs i μ := by
  have hd : XChain [dn i, up i] ((xDotL (dn i)).map (xwhL [] [up i])) [dn i, up i] := by
    simpa using (xChain_xDotL (dn i)).whisk [] [up i]
  change xev cs μ [dn i, up i] []
    ((List.replicate b ((xDotL (dn i)).map (xwhL [] [up i]))).flatten ++ xCapL (up i)) = _
  rw [xev_append cs _ (source_repeat_chain hd b), source_repeat_eval cs μ hd,
    xCapL_up, xev_lcap, xDotL_dn, map_xwhL_map_ofL, xev_map_ofL]

theorem sourceCapLayers_dn_eval (cs : CScalars Sc) (μ : X) (i : I) (b : ℕ) :
    xev cs μ [up i, dn i] [] (sourceCapLayers false i b) = eLM D Sc i μ b := by
  have hd : XChain [up i, dn i] ((xDotL (up i)).map (xwhL [] [dn i])) [up i, dn i] := by
    simpa using (xChain_xDotL (up i)).whisk [] [dn i]
  change xev cs μ [up i, dn i] []
    ((List.replicate b ((xDotL (up i)).map (xwhL [] [dn i]))).flatten ++ xCapL (dn i)) = _
  rw [xev_append cs _ (source_repeat_chain hd b), source_repeat_eval cs μ hd]
  have he : xev cs μ [up i, dn i] [] (xCapL (dn i)) = eLM D Sc i μ 0 := by
    exact xev_map_ofL cs μ [up i, dn i] [] (epsL i 0)
  have hu : xev cs μ [up i, dn i] [up i, dn i]
      ((xDotL (up i)).map (xwhL [] [dn i])) = uLM D Sc i μ := by
    exact xev_map_ofL cs μ [up i, dn i] [up i, dn i] (dotsL [] i [dn i] 1)
  rw [he, hu, cpow_uL_eL, Nat.add_zero]

namespace SameColourSourceFrame
variable {P Q Z : List (Letter I)} {i : I} (F : SameColourSourceFrame P Q Z i)

/-- Actual complete original rows: downward dots followed by the left cap. -/
theorem original_row (cs : CScalars Sc) (μ : X) (b : ℕ) (r : F.residual.Labels) :
    xev cs μ (P ++ dn i :: up i :: Q) Z (F.original.layers (F.paired (b, r))) =
      plcW μ (P ++ dn i :: up i :: Q) (P ++ Q) P Q [dn i, up i] []
        (cpow (dLM D Sc i (wt D μ Q)) b ≫ epsP cs i (wt D μ Q)) ≫
          xev cs μ (P ++ Q) Z (F.residual.layers r) := by
  have hl : (sourceCapLayers true i b).map (xwhL P Q) =
      (List.replicate b (dotOn (P ++ dn i :: up i :: Q) P.length)).flatten ++
        (xCapL (up i)).map (xwhL P Q) := sourceCapLayers_context P Q true i b
  have hc : XChain (P ++ dn i :: up i :: Q)
      ((sourceCapLayers true i b).map (xwhL P Q)) (P ++ Q) := by
    simpa [up, dn, List.append_assoc] using
      (sourceCapLayers_chain true i b).whisk P Q
  rw [F.original_layers, ← hl]
  rw [xev_append cs _ hc,
    xev_eq_plcW (cs := cs) μ P Q (sourceCapLayers_chain true i b)
      (by simp [sourceCapLayers, xCapL])]
  exact congrArg (fun f => plcW μ (P ++ dn i :: up i :: Q) (P ++ Q) P Q
    [dn i, up i] [] f ≫ xev cs μ (P ++ Q) Z (F.residual.layers r))
      (sourceCapLayers_up_eval cs (wt D μ Q) i b)

/-- Actual complete swapped rows are the native right caps. -/
theorem swapped_row (cs : CScalars Sc) (μ : X) (b : ℕ) (r : F.residual.Labels) :
    xev cs μ (P ++ up i :: dn i :: Q) Z (F.swapped.layers (F.exchange (F.paired (b, r)))) =
      plcW μ (P ++ up i :: dn i :: Q) (P ++ Q) P Q [up i, dn i] []
        (eLM D Sc i (wt D μ Q) b) ≫ xev cs μ (P ++ Q) Z (F.residual.layers r) := by
  have hl : (sourceCapLayers false i b).map (xwhL P Q) =
      (List.replicate b (dotOn (P ++ up i :: dn i :: Q) P.length)).flatten ++
        (xCapL (dn i)).map (xwhL P Q) := sourceCapLayers_context P Q false i b
  have hc : XChain (P ++ up i :: dn i :: Q)
      ((sourceCapLayers false i b).map (xwhL P Q)) (P ++ Q) := by
    simpa [up, dn, List.append_assoc] using
      (sourceCapLayers_chain false i b).whisk P Q
  rw [F.swapped_layers, ← hl]
  rw [xev_append cs _ hc,
    xev_eq_plcW (cs := cs) μ P Q (sourceCapLayers_chain false i b)
      (by simp [sourceCapLayers, xCapL])]
  exact congrArg (fun f => plcW μ (P ++ up i :: dn i :: Q) (P ++ Q) P Q
    [up i, dn i] [] f ≫ xev cs μ (P ++ Q) Z (F.residual.layers r))
      (sourceCapLayers_dn_eval cs (wt D μ Q) i b)

end SameColourSourceFrame
end OddMath.SKM
