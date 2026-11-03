import OddMath.QuiverHecke.HalfTurn.PowerWordQuotientCoordinates
import OddMath.QuiverHecke.CyclotomicAction.ELVTensorHomContexts

/-! # The contextual half-turn table in actual old Homs

SwappedVacuumCoordinates §§4–7: the actual old append-dot and normalized
crossing, extended by the actual append functors, are exactly the old
quotients of the half-turned original affine layers. Reversal transports
both word endpoints; equal crossings retain their extra minus sign.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
namespace OddMath.QuiverHecke.ContextualOldGenerators
open ELVOld ELVOld.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The original affine generator with its two given strand contexts. -/
abbrev layerDiagram (u : List I) (g : Shape I) (v : List I) :
    (pres D Sc).obj (ob D (u ++ g.dom ++ v)) ⟶ (pres D Sc).obj (ob D (u ++ g.cod ++ v)) :=
  (pres D Sc).diag (mkD D [(u,g,v)] ⟨rfl,rfl⟩)

/-- Only canonical equal presentations of old word objects are transported. -/
def transport {s t s' t' : List I} (hs : s = s') (ht : t = t')
    (f : (OldCategory.mk s' : OldCategory D Sc cutoff) ⟶ OldCategory.mk t') :
    (OldCategory.mk s : OldCategory D Sc cutoff) ⟶ OldCategory.mk t :=
  eqToHom (congrArg (OldCategory.mk (D := D) (Sc := Sc) (cutoff := cutoff)) hs) ≫ f ≫
    eqToHom (congrArg (OldCategory.mk (D := D) (Sc := Sc) (cutoff := cutoff)) ht.symm)

private def oldDiagram {s t : List I} (ls : List (LayerData I)) (h : SChain s ls t) :
    (OldCategory.mk s : OldCategory D Sc cutoff) ⟶ OldCategory.mk t :=
  (ideal D Sc cutoff s t).mkQ (affineUnit D Sc cutoff s t ((pres D Sc).diag (mkD D ls h)))

private theorem transport_oldDiagram {s t s' t' : List I} (hs : s = s') (ht : t = t')
    {ls ls' : List (LayerData I)} (h : SChain s ls t) (h' : SChain s' ls' t') (hl : ls = ls') :
    transport D Sc cutoff hs ht (oldDiagram D Sc cutoff ls' h') = oldDiagram D Sc cutoff ls h := by
  subst s'
  subst t'
  subst ls'
  simp only [transport, eqToHom_refl, Category.id_comp, Category.comp_id]

private theorem transport_smul {s t s' t' : List I} (hs : s = s') (ht : t = t') (a : k)
    (f : (OldCategory.mk s' : OldCategory D Sc cutoff) ⟶ OldCategory.mk t') :
    transport D Sc cutoff hs ht (a • f) = a • transport D Sc cutoff hs ht f := by
  simp only [transport, Linear.comp_smul, Linear.smul_comp]

private theorem halfTurn_old_layer (u : List I) (g : Shape I) (v : List I) :
    halfTurnOldHom D Sc cutoff (u ++ g.dom ++ v) (u ++ g.cod ++ v)
      (sourceCoefficientHom D Sc 1 (layerDiagram D Sc u g v)) =
    halfTurnWeight (k := k) g • oldDiagram D (parameterTwist D Sc) cutoff
      (halfTurnL [(u,g,v)]) (sChain_halfTurnL (⟨rfl,rfl⟩ : SChain
        (u ++ g.dom ++ v) [(u,g,v)] (u ++ g.cod ++ v))) := by
  change sourceToOldHom D (parameterTwist D Sc) cutoff _ _
    (htCoef D Sc _ _ (sourceCoefficientHom D Sc 1 ((pres D Sc).diag (mkD D [(u,g,v)] ⟨rfl,rfl⟩)))) = _
  rw [htCoef_sourceCoefficientHom, htPres_diag_mkD, sourceCoefficientHom_smul_right, map_smul,
    halfTurnC_singleton]
  congr 1
  change (ideal D (parameterTwist D Sc) cutoff _ _).mkQ
    (elvQuotientMap D (parameterTwist D Sc) cutoff _ _ (sourceCoefficientHom _ _ 1 _)) = _
  rw [elvQuotientMap_source, map_one]
  rfl

private theorem contextChain {s t : List I} (gs : List PG) (h : SChain s (pl s gs) t)
    (hf : Fits s.length gs) (η : List I) :
    SChain (PowerWordContexts.extendedWord s η)
      (pl (PowerWordContexts.extendedWord s η) gs) (PowerWordContexts.extendedWord t η) := by
  rw [PowerWordContexts.extendedWord_eq, PowerWordContexts.extendedWord_eq, pl_append_right η hf]
  simpa only [List.nil_append] using sChain_wh h [] η

private theorem extended_cl {s t : List I} (gs : List PG) (h : SChain s (pl s gs) t)
    (hf : Fits s.length gs) (η : List I) :
    PowerWordContexts.extendedArrow D Sc cutoff t s η
      (oldDiagram D Sc cutoff (pl s gs) h) =
    oldDiagram D Sc cutoff (pl (PowerWordContexts.extendedWord s η) gs) (contextChain gs h hf η) := by
  induction η generalizing s t with
  | nil => rfl
  | cons i η ih =>
    have hf' : Fits (s ++ [i]).length gs := fun g hg =>
      (hf g hg).trans (by simp)
    have h' : SChain (s ++ [i]) (pl (s ++ [i]) gs) (t ++ [i]) := by
      rw [pl_append_right [i] hf]
      simpa only [List.nil_append] using sChain_wh h [] [i]
    change PowerWordContexts.extendedArrow D Sc cutoff (t ++ [i]) (s ++ [i]) η
      ((ideal D Sc cutoff _ _).mkQ (rightContext D Sc cutoff [i] s t
        (affineUnit D Sc cutoff s t (cl D Sc s t gs h)))) = _
    rw [rightContext_affineUnit]
    change PowerWordContexts.extendedArrow D Sc cutoff (t ++ [i]) (s ++ [i]) η
      ((ideal D Sc cutoff _ _).mkQ (affineUnit D Sc cutoff _ _
        (cl D Sc s t gs h ▷ (pres D Sc).obj (ob D [i])))) = _
    rw [cl_whiskerRight D Sc gs h [i] hf]
    exact ih h' hf'

private theorem extended_smul {s t : List I} (η : List I) (a : k)
    (g : (OldCategory.mk s : OldCategory D Sc cutoff) ⟶ OldCategory.mk t) :
    PowerWordContexts.extendedArrow D Sc cutoff t s η (a • g) =
      a • PowerWordContexts.extendedArrow D Sc cutoff t s η g := by
  induction η generalizing s t with
  | nil => rfl
  | cons i η ih =>
    change PowerWordContexts.extendedArrow D Sc cutoff _ _ η ((append D Sc cutoff i).map (a • g)) = _
    rw [Functor.map_smul]
    exact ih _

private theorem dot_layers (ν η : List I) (i : I) :
    pl (PowerWordContexts.extendedWord (ν ++ [i]) η) [PG.dot ν.length] = [(ν,Shape.dot i,η)] := by
  rw [PowerWordContexts.extendedWord_eq]
  simp [pl, PG.ld, List.append_assoc]

private theorem cross_layers (ν η : List I) (i j : I) :
    pl (PowerWordContexts.extendedWord ((ν ++ [i]) ++ [j]) η) [PG.cross ν.length] =
      [(ν,Shape.cross i j,η)] := by
  rw [PowerWordContexts.extendedWord_eq]
  simp [pl, PG.ld, List.append_assoc]

private theorem dot_fits (ν : List I) (i : I) : Fits (ν ++ [i]).length [PG.dot ν.length] := by
  intro g hg
  obtain rfl := List.mem_singleton.mp hg
  simp [PG.pos, PG.width]

private theorem cross_fits (ν : List I) (i j : I) :
    Fits ((ν ++ [i]) ++ [j]).length [PG.cross ν.length] := by
  intro g hg
  obtain rfl := List.mem_singleton.mp hg
  simp [PG.pos, PG.width]

private theorem old_dot_eq (ν : List I) (i : I) :
    oldAppendDotComponent D Sc cutoff i (OldCategory.mk ν) =
      oldDiagram D Sc cutoff (pl (ν ++ [i]) [PG.dot ν.length]) (sChain_pl _ _) := by
  rw [oldAppendDotComponent_eq]
  simp only [appendMovingPower, pow_one, dotE_eq]
  rfl

private theorem old_cross_eq (ν : List I) (i j : I) :
    PowerWordContentCross.normalizedOldCross D Sc cutoff ν i j =
      halfTurnWeight (k := k) (Shape.cross i j) •
        oldDiagram D Sc cutoff (pl ((ν ++ [i]) ++ [j]) [PG.cross ν.length])
          (by simpa using sChain_crossAt ν [] i j) := by
  classical
  by_cases h : i = j
  · subst j
    simp only [PowerWordContentCross.normalizedOldCross, ite_true, halfTurnWeight, neg_one_smul]
    rfl
  · simp only [PowerWordContentCross.normalizedOldCross, h, ite_false, halfTurnWeight, one_smul]
    rfl

private theorem dot_endpoint (ν η : List I) (i : I) :
    ((η.reverse ++ [i]) ++ ν.reverse).reverse = PowerWordContexts.extendedWord (ν ++ [i]) η := by
  simp [PowerWordContexts.extendedWord_eq, List.reverse_append, List.append_assoc]

private theorem cross_source_endpoint (ν η : List I) (i j : I) :
    ((η.reverse ++ [j,i]) ++ ν.reverse).reverse =
      PowerWordContexts.extendedWord ((ν ++ [i]) ++ [j]) η := by
  simp [PowerWordContexts.extendedWord_eq, List.reverse_append, List.append_assoc]

/-- The literal contextual appended dot is the old quotient of the original
half-turned affine layer, with both contexts and endpoint transports retained. -/
theorem dot (ν η : List I) (i : I) :
    halfTurnOldHom D Sc cutoff ((η.reverse ++ [i]) ++ ν.reverse) ((η.reverse ++ [i]) ++ ν.reverse)
      (sourceCoefficientHom D Sc 1 (layerDiagram D Sc η.reverse (.dot i) ν.reverse)) =
    transport D (parameterTwist D Sc) cutoff (dot_endpoint ν η i) (dot_endpoint ν η i)
      (PowerWordContexts.extendedArrow D (parameterTwist D Sc) cutoff (ν ++ [i]) (ν ++ [i]) η
        (oldAppendDotComponent D (parameterTwist D Sc) cutoff i (OldCategory.mk ν))) := by
  refine (halfTurn_old_layer D Sc cutoff η.reverse (.dot i) ν.reverse).trans ?_
  rw [old_dot_eq, extended_cl]
  · simp only [halfTurnWeight, one_smul]
    symm
    apply transport_oldDiagram
    simp only [halfTurnL, halfTurnLD, List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.reverse_reverse]
    exact (dot_layers ν η i).symm
  · exact dot_fits ν i

/-- The contextual normalized crossing is exactly the half-turned original
layer in the actual old quotient. The equal-colour minus is not discarded. -/
theorem cross (ν η : List I) (i j : I) :
    halfTurnOldHom D Sc cutoff ((η.reverse ++ [i,j]) ++ ν.reverse) ((η.reverse ++ [j,i]) ++ ν.reverse)
      (sourceCoefficientHom D Sc 1 (layerDiagram D Sc η.reverse (.cross i j) ν.reverse)) =
    transport D (parameterTwist D Sc) cutoff (cross_source_endpoint ν η i j) (cross_source_endpoint ν η j i)
      (PowerWordContexts.extendedArrow D (parameterTwist D Sc) cutoff ((ν ++ [j]) ++ [i])
        ((ν ++ [i]) ++ [j]) η (PowerWordContentCross.normalizedOldCross D (parameterTwist D Sc) cutoff ν i j)) := by
  refine (halfTurn_old_layer D Sc cutoff η.reverse (.cross i j) ν.reverse).trans ?_
  rw [old_cross_eq, extended_smul, extended_cl, transport_smul]
  · congr 1
    symm
    apply transport_oldDiagram
    simp only [halfTurnL, halfTurnLD, List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.reverse_reverse]
    exact (cross_layers ν η i j).symm
  · exact cross_fits ν i j

end OddMath.QuiverHecke.ContextualOldGenerators
