import OddMath.QuiverHecke.CyclotomicAction.ELVVacuumGeneratorCoordinates
import OddMath.QuiverHecke.CyclotomicAction.ELVContentYoneda

/-! # Reservoir Hom evaluation of normalized induction crossings

The represented-reservoir pairing for `DeformedActionAssembly.md` §5 evaluates
on the induced identity tensor. Crossing acts by signed postcomposition with
the reversed source arrow, retaining the full coefficient and diagram parity.
This does not compare block induction with iterated one-colour induction.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.VacuumHomAction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  {β γ : Multiset I}
  (J : ContentCategory D Sc cutoff N β ⥤ ContentCategory D Sc cutoff N γ)
  [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (v : ContentCategory D Sc cutoff N β) (r : ContentCategory D Sc cutoff N γ)

/-- The even identity tensor in the real induced representable. -/
def identityTensor : (BalancedInduction.induced J
    (contentRepresentable D Sc cutoff N β v)).obj (J.obj v) :=
  BalancedInduction.tensor J (contentRepresentableFunctor D Sc cutoff N β v)
    v (𝟙 (J.obj v)) (𝟙 v)

/-- A reservoir morphism is evaluated in the reversed source Hom. -/
def pairing (t : BalancedInduction.induced J (contentRepresentable D Sc cutoff N β v) ⟶
    contentRepresentable D Sc cutoff N γ r) : r ⟶ J.obj v :=
  t.app 0 (J.obj v) (identityTensor D Sc cutoff N J v) +
    t.app 1 (J.obj v) (identityTensor D Sc cutoff N J v)

theorem identityTensor_mem : identityTensor D Sc cutoff N J v ∈
    ((BalancedInduction.induced J (contentRepresentable D Sc cutoff N β v)).obj
      (J.obj v)).part 0 := by
  have hi : (𝟙 v : v ⟶ v) ∈ (contentHomSpace D Sc cutoff N β v v).part 0 := by
    rw [contentHomSpace_part]; exact id_mem v
  exact SVec.apply_mem_part
    (BalancedInduction.unit_mem J (contentRepresentable D Sc cutoff N β v) v) hi

theorem component_mem (t : BalancedInduction.induced J (contentRepresentable D Sc cutoff N β v) ⟶
    contentRepresentable D Sc cutoff N γ r) (q : ZMod 2) :
    t.app q (J.obj v) (identityTensor D Sc cutoff N J v) ∈
      parity (R := k) r (J.obj v) q := by
  have h := SVec.apply_mem_part (t.app_mem q (J.obj v))
    (identityTensor_mem D Sc cutoff N J v)
  change _ ∈ (contentHomSpace D Sc cutoff N γ r (J.obj v)).part (0 + q) at h
  simpa only [zero_add, contentHomSpace_part] using h

/-- Supernatural naturality along a homogeneous source arrow. -/
theorem app_tensor (t : BalancedInduction.induced J (contentRepresentable D Sc cutoff N β v) ⟶
    contentRepresentable D Sc cutoff N γ r) (q : ZMod 2)
    {w : ContentCategory D Sc cutoff N γ} {p : ZMod 2} (a : J.obj v ⟶ w)
    (ha : a ∈ parity (R := k) _ _ p) :
    t.app q w (BalancedInduction.tensor J (contentRepresentableFunctor D Sc cutoff N β v)
      v a (𝟙 v)) =
      twist k p (t.app q (J.obj v) (identityTensor D Sc cutoff N J v)) ≫ a := by
  have hn := congrArg (fun l => l (identityTensor D Sc cutoff N J v)) (t.naturality q a ha)
  change t.app q w (BalancedInduction.postcompose J
    (contentRepresentableFunctor D Sc cutoff N β v) a
    (identityTensor D Sc cutoff N J v)) =
    koszulSign q p • (t.app q (J.obj v) (identityTensor D Sc cutoff N J v) ≫ a) at hn
  rw [identityTensor, BalancedInduction.postcompose_tensor, Category.id_comp] at hn
  rw [twist_of_mem p (component_mem D Sc cutoff N J v r t q), Linear.smul_comp]
  simpa only [koszulSign_smul (R := k), mul_comm q p, identityTensor] using hn

/-- Evaluation of precomposition by a homogeneous induction map. -/
theorem pairing_comp
    (K : ContentCategory D Sc cutoff N β ⥤ ContentCategory D Sc cutoff N γ)
    [K.Additive] [K.Linear k] [IsSuperfunctor k K]
    {p : ZMod 2}
    (g : BalancedInduction.induced K (contentRepresentable D Sc cutoff N β v) ⟶
      BalancedInduction.induced J (contentRepresentable D Sc cutoff N β v))
    (hg : g ∈ parity (R := k) _ _ p)
    (a : J.obj v ⟶ K.obj v) (ha : a ∈ parity (R := k) _ _ p)
    (hu : g.app p (K.obj v) (identityTensor D Sc cutoff N K v) =
      BalancedInduction.tensor J (contentRepresentableFunctor D Sc cutoff N β v) v a (𝟙 v))
    (t : BalancedInduction.induced J (contentRepresentable D Sc cutoff N β v) ⟶
      contentRepresentable D Sc cutoff N γ r) :
    pairing D Sc cutoff N K v r (g ≫ t) =
      twist k p (pairing D Sc cutoff N J v r t) ≫ a := by
  have he : pairing D Sc cutoff N K v r (g ≫ t) =
      t.app 0 (K.obj v) (g.app p (K.obj v) (identityTensor D Sc cutoff N K v)) +
      t.app 1 (K.obj v) (g.app p (K.obj v) (identityTensor D Sc cutoff N K v)) := by
    rcases parity_eq_zero_or_one p with rfl | rfl
    · have hz := Superfunctor.app_eq_zero_of_mem hg (show (1 : ZMod 2) ≠ 0 by decide) (K.obj v)
      simp only [pairing, Superfunctor.comp_app, hz, SVec.add_apply, SVec.comp_apply,
        SVec.zero_apply, map_zero, add_zero]
    · have hz := Superfunctor.app_eq_zero_of_mem hg (show (0 : ZMod 2) ≠ 1 by decide) (K.obj v)
      simp only [pairing, Superfunctor.comp_app, hz, SVec.add_apply, SVec.comp_apply,
        SVec.zero_apply, map_zero, zero_add, SVec.zmod2_one_add_one]
      exact add_comm _ _
  rw [he, hu, app_tensor D Sc cutoff N J v r t 0 a ha,
    app_tensor D Sc cutoff N J v r t 1 a ha, pairing, map_add, Preadditive.add_comp]

/-- The normalized crossing acts on the represented reservoir by postcomposition.
Both contravariances are visible: induction reverses append, and the Hom
pairing reverses the module map. The twist is on the entire reservoir kernel. -/
theorem cross_postcompose (β : Multiset I) (i j : I)
    (v : ContentCategory D Sc cutoff N β)
    (r : ContentCategory D Sc cutoff N (β + ([i, j] : Multiset I)))
    (t : (contentInductionTo D Sc cutoff N β [i, j] _ rfl).obj
        (contentRepresentable D Sc cutoff N β v) ⟶
      contentRepresentable D Sc cutoff N _ r) :
    pairing D Sc cutoff N
      (contentAppendTo D Sc cutoff N β [j, i] _ (content_pair_swap β i j)) v r
      ((contentInductionCross D Sc cutoff N β i j).app (D.parity i * D.parity j)
        (contentRepresentable D Sc cutoff N β v) ≫ t) =
    twist k (D.parity i * D.parity j)
      (pairing D Sc cutoff N (contentAppendTo D Sc cutoff N β [i, j] _ rfl) v r t) ≫
      contentAppendToComponent D Sc cutoff N rfl (content_pair_swap β i j)
        (contentCrossAffine D Sc i j) v := by
  apply pairing_comp D Sc cutoff N
    (contentAppendTo D Sc cutoff N β [i, j] _ rfl) v r
    (contentAppendTo D Sc cutoff N β [j, i] _ (content_pair_swap β i j))
  · exact (contentInductionCross D Sc cutoff N β i j).app_mem _ _
  · exact (contentAppendTo_supernatural D Sc cutoff N rfl (content_pair_swap β i j)
      (contentCrossAffine_mem D Sc i j)).mem v
  · have h := contentInductionCross_tensor D Sc cutoff N β i j
      (contentRepresentable D Sc cutoff N β v) _ v (𝟙 _) (𝟙 v)
    exact h.trans (congrArg
      (fun a => BalancedInduction.tensor
        (contentAppendTo D Sc cutoff N β [i, j] _ rfl)
        (contentRepresentableFunctor D Sc cutoff N β v) v a (𝟙 v))
      (by rw [twist_id, Category.comp_id]))

/-- Distinct colours have no additional normalization sign. -/
theorem mixedCross_postcompose (β : Multiset I) (i j : I) (hij : i ≠ j)
    (v : ContentCategory D Sc cutoff N β)
    (r : ContentCategory D Sc cutoff N (β + ([i, j] : Multiset I)))
    (t : (contentInductionTo D Sc cutoff N β [i, j] _ rfl).obj
        (contentRepresentable D Sc cutoff N β v) ⟶
      contentRepresentable D Sc cutoff N _ r) :
    pairing D Sc cutoff N
      (contentAppendTo D Sc cutoff N β [j, i] _ (content_pair_swap β i j)) v r
      ((contentInductionCross D Sc cutoff N β i j).app (D.parity i * D.parity j)
        (contentRepresentable D Sc cutoff N β v) ≫ t) =
    twist k (D.parity i * D.parity j)
      (pairing D Sc cutoff N (contentAppendTo D Sc cutoff N β [i, j] _ rfl) v r t) ≫
      contentAppendToComponent D Sc cutoff N rfl (content_pair_swap β i j)
        (crossTwo D Sc i j) v := by
  rw [cross_postcompose, contentCrossAffine_distinct D Sc i j hij]

/-- Equal colours have the source normalization minus sign. -/
theorem equalCross_postcompose (β : Multiset I) (i : I)
    (v : ContentCategory D Sc cutoff N β)
    (r : ContentCategory D Sc cutoff N (β + ([i, i] : Multiset I)))
    (t : (contentInductionTo D Sc cutoff N β [i, i] _ rfl).obj
        (contentRepresentable D Sc cutoff N β v) ⟶
      contentRepresentable D Sc cutoff N _ r) :
    pairing D Sc cutoff N
      (contentAppendTo D Sc cutoff N β [i, i] _ (content_pair_swap β i i)) v r
      ((contentInductionCross D Sc cutoff N β i i).app (D.parity i * D.parity i)
        (contentRepresentable D Sc cutoff N β v) ≫ t) =
    -(twist k (D.parity i * D.parity i)
      (pairing D Sc cutoff N (contentAppendTo D Sc cutoff N β [i, i] _ rfl) v r t) ≫
      contentAppendToComponent D Sc cutoff N rfl (content_pair_swap β i i)
        (crossTwo D Sc i i) v) := by
  rw [cross_postcompose, contentCrossAffine_equal, contentAppendToComponent_neg,
    Preadditive.comp_neg]

/-- The pairing retains each total-parity projection. -/
theorem pairing_proj (t : BalancedInduction.induced J (contentRepresentable D Sc cutoff N β v) ⟶
    contentRepresentable D Sc cutoff N γ r) (q : ZMod 2) :
    proj k q (pairing D Sc cutoff N J v r t) =
      t.app q (J.obj v) (identityTensor D Sc cutoff N J v) := by
  unfold pairing
  rw [map_add]
  rcases parity_eq_zero_or_one q with rfl | rfl
  · rw [proj_of_mem (component_mem D Sc cutoff N J v r t 0),
      proj_of_mem_ne (component_mem D Sc cutoff N J v r t 1) (by decide), add_zero]
  · rw [proj_of_mem_ne (component_mem D Sc cutoff N J v r t 0) (by decide),
      proj_of_mem (component_mem D Sc cutoff N J v r t 1), zero_add]

/-- Homogeneous full kernels exhibit the Koszul sign explicitly. -/
theorem cross_postcompose_of_mem (β : Multiset I) (i j : I)
    (v : ContentCategory D Sc cutoff N β)
    (r : ContentCategory D Sc cutoff N (β + ([i, j] : Multiset I)))
    (t : (contentInductionTo D Sc cutoff N β [i, j] _ rfl).obj
        (contentRepresentable D Sc cutoff N β v) ⟶
      contentRepresentable D Sc cutoff N _ r) (q : ZMod 2)
    (ht : pairing D Sc cutoff N (contentAppendTo D Sc cutoff N β [i, j] _ rfl) v r t ∈
      parity (R := k) _ _ q) :
    pairing D Sc cutoff N
      (contentAppendTo D Sc cutoff N β [j, i] _ (content_pair_swap β i j)) v r
      ((contentInductionCross D Sc cutoff N β i j).app (D.parity i * D.parity j)
        (contentRepresentable D Sc cutoff N β v) ≫ t) =
    sign k ((D.parity i * D.parity j) * q) •
      (pairing D Sc cutoff N (contentAppendTo D Sc cutoff N β [i, j] _ rfl) v r t ≫
        contentAppendToComponent D Sc cutoff N rfl (content_pair_swap β i j)
          (contentCrossAffine D Sc i j) v) := by
  rw [cross_postcompose, twist_of_mem _ ht, Linear.smul_comp]

/-- Use the constructed vacuum-word isomorphism on the reservoir side only.
No block/iterated identification on the source side is assumed. -/
def wordPairing (ρ : List I) (hρ : VacuumRepresentable.content ρ = γ)
    (t : BalancedInduction.induced J (contentRepresentable D Sc cutoff N β v) ⟶
      VacuumRepresentable.wordModuleAt D Sc cutoff N ρ γ hρ) :
    VacuumRepresentable.wordObjectAt D Sc cutoff N ρ γ hρ ⟶ J.obj v :=
  pairing D Sc cutoff N J v _ (t ≫ (VacuumRepresentable.wordIsoAt D Sc cutoff N ρ γ hρ).hom)

/-- Normalized crossing on a real iterated reservoir target. -/
theorem cross_word_postcompose (β : Multiset I) (i j : I)
    (v : ContentCategory D Sc cutoff N β) (ρ : List I)
    (hρ : VacuumRepresentable.content ρ = β + ([i, j] : Multiset I))
    (t : (contentInductionTo D Sc cutoff N β [i, j] _ rfl).obj
        (contentRepresentable D Sc cutoff N β v) ⟶
      VacuumRepresentable.wordModuleAt D Sc cutoff N ρ _ hρ) :
    wordPairing D Sc cutoff N
      (contentAppendTo D Sc cutoff N β [j, i] _ (content_pair_swap β i j)) v ρ hρ
      ((contentInductionCross D Sc cutoff N β i j).app (D.parity i * D.parity j)
        (contentRepresentable D Sc cutoff N β v) ≫ t) =
    twist k (D.parity i * D.parity j)
      (wordPairing D Sc cutoff N (contentAppendTo D Sc cutoff N β [i, j] _ rfl) v ρ hρ t) ≫
      contentAppendToComponent D Sc cutoff N rfl (content_pair_swap β i j)
        (contentCrossAffine D Sc i j) v := by
  unfold wordPairing
  rw [Category.assoc, cross_postcompose]

end OddMath.QuiverHecke.ELVOld.VacuumHomAction
