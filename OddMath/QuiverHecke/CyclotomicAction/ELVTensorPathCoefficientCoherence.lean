import OddMath.QuiverHecke.CyclotomicAction.ELVTensorWordCoefficientAction

/-! # Coefficient maps along tensor reservoir paths

SwappedVacuumCoordinates §§2–6: comparison of the direct reservoir-path
coefficient with the recursive whole-word coefficient, before evaluation.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld.TensorPathCoefficientCoherence
open CyclotomicAction SwappedAssembly VacuumTensorCoefficientMaps TensorWordCoefficientAction
universe u
section Generic
variable {k : Type*} [CommRing k] {C : Type*} [Category* C] [Preadditive C] [Linear k C]
private def eqAction {F G : C} (h : F = G) : End F →ₐ[k] End G := by
  subst G
  exact AlgHom.id k (End F)
private theorem eqAction_heq {F G : C} (h : F = G) (f : End F) :
    HEq (eqAction (k := k) h f) f := by
  subst G
  rfl
end Generic
variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m cutoff : I → ℕ)
  (L : I × ℕ → ℕ) (ΛP ΛR : X)
local notation "N" => PowerWordContent.powerBound D cutoff L
local notation "W" => elvRouquierData D Sc cutoff N ΛR
private def reindexAction {x y : X} (h : x = y)
    (F : probeOldWeightSpace D Sc m ΛP (-ΛP) ⟶ elvWeightSpace D Sc cutoff N ΛR x)
    (a : SKM.SYM D k →ₐ[k] End F) :
    SKM.SYM D k →ₐ[k] End (h ▸ F : probeOldWeightSpace D Sc m ΛP (-ΛP) ⟶
      elvWeightSpace D Sc cutoff N ΛR y) := by
  subst y
  exact a
private theorem reindexAction_heq {x y : X} (h : x = y)
    (F : probeOldWeightSpace D Sc m ΛP (-ΛP) ⟶ elvWeightSpace D Sc cutoff N ΛR x)
    (φ : SKM.SYM D k →ₐ[k] End F) (a : SKM.SYM D k) :
    HEq (reindexAction D Sc m cutoff L ΛP ΛR h F φ a) (φ a) := by
  subst y
  rfl

/-- Empty-word normalization retains the entire coefficient map. -/
theorem wordAction_nil_heq (a : SKM.SYM D k) :
    HEq (wordAction D Sc m cutoff L ΛP ΛR [] a)
      (pathCoefficientAction D Sc m cutoff L ΛP ΛR (SPath.nil (0,0)) (by simp) a) := by
  simp only [wordAction, List.reverseRecOn_nil]
  change HEq (eqAction (k := k)
    (TensorReservoirWords.pathHomAt_eq_wordHom D Sc m cutoff L ΛP ΛR (SPath.nil (0,0)) (by simp))
    (reindexAction D Sc m cutoff L ΛP ΛR
      (TensorReservoirWords.path_weight D ΛR (SPath.nil (0,0)) (by simp))
      (TensorReservoirWords.pathHom D Sc m cutoff L ΛP ΛR (SPath.nil (0,0)) (by simp))
      (pathCoefficientAction D Sc m cutoff L ΛP ΛR (SPath.nil (0,0)) (by simp)) a)) _
  exact (eqAction_heq (k := k) _ _).trans (reindexAction_heq D Sc m cutoff L ΛP ΛR _ _ _ _)

private theorem conjugate_heq {C : Type*} [Category* C] {F G : C}
    (h : F = G) (f : End F) : HEq (eqToHom h.symm ≫ f ≫ eqToHom h) f := by
  subst G
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

/-- Append normalization changes no coefficient map. -/
theorem wordAction_append_heq (ν : List I) (i : I) (a : SKM.SYM D k) :
    HEq (wordAction D Sc m cutoff L ΛP ΛR (ν ++ [i]) a)
      (Superfunctor.whiskerRight (wordAction D Sc m cutoff L ΛP ΛR ν a)
        (elvE D Sc cutoff N i ΛR (PowerWordWeight.wordWeight_append D ΛR ν i))) := by
  rw [wordAction_append]
  exact conjugate_heq _ _

private theorem postE_map_heq (i : I) {x y x' y' : X} (hx : x = x') (hy : y = y')
    (h : x + D.α i = y) (h' : x' + D.α i = y')
    {F : probeOldWeightSpace D Sc m ΛP (-ΛP) ⟶ elvWeightSpace D Sc cutoff N ΛR x}
    {F' : probeOldWeightSpace D Sc m ΛP (-ΛP) ⟶ elvWeightSpace D Sc cutoff N ΛR x'}
    (hF : HEq F F') {f : End F} {f' : End F'} (hf : HEq f f') :
    HEq (Superfunctor.whiskerRight f (elvE D Sc cutoff N i ΛR h))
      (Superfunctor.whiskerRight f' (elvE D Sc cutoff N i ΛR h')) := by
  cases hx
  cases hy
  cases hF
  cases hf
  rfl

omit [Fintype I] in
private theorem edge (i : I) (c : I →₀ ℕ) (hc : 1 ≤ c i) :
    ReservoirWord.weight D ΛR (c - Finsupp.single i 1) + D.α i = ReservoirWord.weight D ΛR c := by
  simp only [ReservoirWord.weight]
  rw [add_assoc, contentWeight_sub_single hc]

private theorem pathAction_cons_heq (i : I) (r : X) {l : List (SKM.Col I X)}
    {c : I →₀ ℕ} (hc : 1 ≤ c i) (p : SPath l (0,c - Finsupp.single i 1) (0,0))
    (hl : ∀ b ∈ l, b.l.1 = true) (a : SKM.SYM D k) :
    HEq (pathCoefficientAction D Sc m cutoff L ΛP ΛR
      (SPath.cons ⟨(true,i),r⟩ false (0,c) hc p) (by
        simp only [List.mem_cons, forall_eq_or_imp]; exact ⟨True.intro,hl⟩) a)
      (Superfunctor.whiskerRight (pathCoefficientAction D Sc m cutoff L ΛP ΛR p hl a)
        (elvE D Sc cutoff N i ΛR (edge D ΛR i c hc))) := by
  have hh := ReservoirWord.word_cons W ΛR i r hc p hl
  have hg : ∀ (G G' : elvWeightSpace D Sc cutoff N ΛR (ReservoirWord.weight D ΛR 0) ⟶
      elvWeightSpace D Sc cutoff N ΛR (ReservoirWord.weight D ΛR c)), G = G' →
      HEq (Superfunctor.whiskerRight
        (sourceCoefficientAction D Sc m cutoff L ΛP ΛR a) G)
        (Superfunctor.whiskerRight
          (sourceCoefficientAction D Sc m cutoff L ΛP ΛR a) G') := by
    intro G G' h
    subst G'
    rfl
  apply (hg _ _ hh).trans
  apply heq_of_eq
  apply Superfunctor.hom_ext
  intro q M
  rfl

private theorem wordAction_word_heq {ν τ : List I} (h : ν = τ) (a : SKM.SYM D k) :
    HEq (wordAction D Sc m cutoff L ΛP ΛR ν a) (wordAction D Sc m cutoff L ΛP ΛR τ a) := by
  subst τ
  rfl

/-- The direct path coefficient agrees with the recursive normalized word
coefficient on the entire input Hom, at their proved equal original weights. -/
theorem pathAction_heq {l : List (SKM.Col I X)} {c : I →₀ ℕ}
    (p : SPath l (0,c) (0,0)) (hl : ∀ a ∈ l, a.l.1 = true) (a : SKM.SYM D k) :
    HEq (pathCoefficientAction D Sc m cutoff L ΛP ΛR p hl a)
      (wordAction D Sc m cutoff L ΛP ΛR ((l.map (fun b => b.l.2)).reverse) a) := by
  induction l generalizing c with
  | nil =>
    cases p
    exact (wordAction_nil_heq D Sc m cutoff L ΛP ΛR a).symm
  | cons b l ih =>
    cases p with
    | cons b side s hv p =>
      have hb := hl b List.mem_cons_self
      have ht : ∀ d ∈ l, d.l.1 = true := fun d hd => hl d (List.mem_cons_of_mem _ hd)
      rcases b with ⟨⟨up,i⟩,r⟩
      cases up with
      | false => cases hb
      | true =>
        have hs := SPath.side_eq_false_of_upward_probe_zero i side p ht rfl
        subst side
        change SPath l (0,c - Finsupp.single i 1) (0,0) at p
        have hw := TensorReservoirWords.path_weight D ΛR p ht
        have hy : ReservoirWord.weight D ΛR c = PowerWordWeight.wordWeight D ΛR
            (((l.map (fun b => b.l.2)).reverse) ++ [i]) :=
          (edge D ΛR i c hv).symm.trans ((congrArg (fun x => x + D.α i) hw).trans
            (PowerWordWeight.wordWeight_append D ΛR ((l.map (fun b => b.l.2)).reverse) i))
        have hf := postE_map_heq D Sc m cutoff L ΛP ΛR i hw hy (edge D ΛR i c hv)
          (PowerWordWeight.wordWeight_append D ΛR ((l.map (fun b => b.l.2)).reverse) i)
          (TensorReservoirWords.pathHom_heq D Sc m cutoff L ΛP ΛR p ht) (ih p ht)
        have hwords : ((l.map (fun b => b.l.2)).reverse) ++ [i] =
            (((⟨(true,i),r⟩ :: l).map (fun b => b.l.2)).reverse) := by
          rw [List.map_cons, List.reverse_cons]
        exact (pathAction_cons_heq D Sc m cutoff L ΛP ΛR i r hv p ht a).trans
          (hf.trans ((wordAction_append_heq D Sc m cutoff L ΛP ΛR
            ((l.map (fun b => b.l.2)).reverse) i a).symm.trans
              (wordAction_word_heq D Sc m cutoff L ΛP ΛR hwords a)))
end OddMath.QuiverHecke.ELVOld.TensorPathCoefficientCoherence
