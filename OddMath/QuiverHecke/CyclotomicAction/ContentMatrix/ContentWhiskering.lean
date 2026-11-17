import Mathlib.CategoryTheory.Whiskering
import OddMath.Algebra.FiniteSupermodule
import OddMath.Algebra.FiniteZeroCoordinate
import OddMath.QuiverHecke.CyclotomicAction.ContentModule.ContentModuleQuadratic
import OddMath.QuiverHecke.CyclotomicAction.InductionGridMate.InductionSquareTensors
import OddMath.SKM.RouquierCoupled

/-!
# Content matrix

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # Content induction and independent whiskering

The canonical content composition comparison intertwines the independently
defined inner and outer module transformations of an affine endomorphism.
Both content equality transports are retained. The source comparisons are
proved through tensor coefficients and the truncated quotient, not assumed.
These squares identify the transported positioned dots with whiskered
single-letter dots in the content E-action assembly.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
universe u
namespace OddMath.QuiverHecke.ELV.BalancedInduction
variable {k : Type u} [CommRing k]
variable {C D E : Type u} [Category.{u} C] [Category.{u} D] [Category.{u} E]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive D] [Linear k D] [Supercategory k D]
  [Preadditive E] [Linear k E] [Supercategory k E]
variable (J : C ⥤ D) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
variable (K : D ⥤ E) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
variable (L : C ⥤ E) [L.Additive] [L.Linear k] [IsSuperfunctor k L]

theorem compForward_inner_recast (e : J ⋙ K = L) {p : ZMod 2}
    {a : ∀ v, J.obj v ⟶ J.obj v} (ha : IsSupernatural k p a)
    {b : ∀ v, L.obj v ⟶ L.obj v} (hb : IsSupernatural k p b)
    (hab : ∀ v, HEq (K.map (a v)) (b v))
    (M : Superfunctor k C (SVec k)) (z : E) :
    let c := inductionComp J K ≪≫ eqToIso
      (show induction (k := k) (J ⋙ K) = induction L by subst L; rfl)
    (moduleIsoLinearEquiv (c.app M) z).toLinearMap ∘ₗ
        mapComponent K (transformComponent ha M) p z =
      transformLinear hb M z ∘ₗ (moduleIsoLinearEquiv (c.app M) z).toLinearMap := by
  subst L
  have hab' : (fun v => K.map (a v)) = b := funext (fun v => eq_of_heq (hab v))
  subst b
  dsimp only
  simp only [eqToIso_refl, Iso.trans_refl, moduleIsoLinearEquiv,
    Iso.app_hom, SuperNatTrans.total, inductionComp_hom_app_one, add_zero]
  exact compForward_transform_inner K ha M z

theorem compForward_outer_recast (e : J ⋙ K = L) {p : ZMod 2}
    {a : ∀ w, K.obj w ⟶ K.obj w} (ha : IsSupernatural k p a)
    {b : ∀ v, L.obj v ⟶ L.obj v} (hb : IsSupernatural k p b)
    (hab : ∀ v, HEq (a (J.obj v)) (b v))
    (M : Superfunctor k C (SVec k)) (z : E) :
    let c := inductionComp J K ≪≫ eqToIso
      (show induction (k := k) (J ⋙ K) = induction L by subst L; rfl)
    (moduleIsoLinearEquiv (c.app M) z).toLinearMap ∘ₗ
        transformLinear ha (induced J M) z =
      transformLinear hb M z ∘ₗ (moduleIsoLinearEquiv (c.app M) z).toLinearMap := by
  subst L
  have hab' : (fun v => a (J.obj v)) = b := funext (fun v => eq_of_heq (hab v))
  subst b
  dsimp only
  simp only [eqToIso_refl, Iso.trans_refl, moduleIsoLinearEquiv,
    Iso.app_hom, SuperNatTrans.total, inductionComp_hom_app_one, add_zero]
  exact compForward_transform_outer J ha M z

end OddMath.QuiverHecke.ELV.BalancedInduction
namespace OddMath.QuiverHecke.ELV
open MonoidalCategory
open scoped TensorProduct
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

private theorem whiskerRecast_map_heq {ι : Type*} {A B : ι → Type*}
    (F : ∀ i, A i → B i) {i j : ι} (h : i = j)
    {a : A i} {b : A j} (hab : HEq a b) : HEq (F i a) (F j b) := by
  cases h
  cases hab
  rfl

theorem appendComponent_rightContext_heq (v σ τ : List I)
    (a : End ((pres D Sc).obj (ob D σ))) :
    HEq (truncatedRightContext D Sc cutoff N τ (v ++ σ) (v ++ σ)
      (truncatedAppendComponent D Sc cutoff N a ⟨v⟩))
      (truncatedAppendComponent D Sc cutoff N
        (a ▷ (pres D Sc).obj (ob D τ)) ⟨v⟩) := by
  have h := MonoidalSupercategory.associator_naturality (R := k)
    (𝟙 ((pres D Sc).obj (ob D v))) a (𝟙 ((pres D Sc).obj (ob D τ)))
  simp only [MonoidalSupercategory.tensorHom_def (R := k),
    MonoidalSupercategory.id_whiskerRight (R := k),
    MonoidalSupercategory.whiskerLeft_id (R := k), Category.id_comp, Category.comp_id,
    Presentation.associator_eq, eqToIso.hom] at h
  have hh : HEq (((pres D Sc).obj (ob D v) ◁ a) ▷ (pres D Sc).obj (ob D τ))
      ((pres D Sc).obj (ob D v) ◁ (a ▷ (pres D Sc).obj (ob D τ))) := by
    apply (conj_eqToHom_iff_heq _ _
      (congrArg (fun x => (pres D Sc).obj (ob D x)) (List.append_assoc v σ τ))
      (congrArg (fun x => (pres D Sc).obj (ob D x)) (List.append_assoc v σ τ))).1
    rw [comp_eqToHom_iff] at h
    simp only [Category.assoc] at h
    exact h
  exact whiskerRecast_map_heq
    (A := fun w : List I => End ((pres D Sc).obj (ob D w)))
    (B := fun w : List I => TruncatedOld D Sc cutoff N w w)
    (fun w f => (truncatedIdeal D Sc cutoff N w w).mkQ
      ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] f))
    (List.append_assoc v σ τ) hh

theorem appendComponent_leftContext_heq (v σ τ : List I)
    (a : End ((pres D Sc).obj (ob D τ))) :
    HEq (truncatedAppendComponent D Sc cutoff N a ⟨v ++ σ⟩)
      (truncatedAppendComponent D Sc cutoff N
        ((pres D Sc).obj (ob D σ) ◁ a) ⟨v⟩) := by
  have h := MonoidalSupercategory.associator_naturality (R := k)
    (𝟙 ((pres D Sc).obj (ob D v))) (𝟙 ((pres D Sc).obj (ob D σ))) a
  simp only [MonoidalSupercategory.tensorHom_def (R := k),
    MonoidalSupercategory.id_whiskerRight (R := k),
    MonoidalSupercategory.whiskerLeft_id (R := k), Category.id_comp, Category.comp_id,
    Presentation.associator_eq, eqToIso.hom] at h
  have hh : HEq ((pres D Sc).obj (ob D (v ++ σ)) ◁ a)
      ((pres D Sc).obj (ob D v) ◁ ((pres D Sc).obj (ob D σ) ◁ a)) := by
    apply (conj_eqToHom_iff_heq _ _
      (congrArg (fun x => (pres D Sc).obj (ob D x)) (List.append_assoc v σ τ))
      (congrArg (fun x => (pres D Sc).obj (ob D x)) (List.append_assoc v σ τ))).1
    rw [comp_eqToHom_iff] at h
    simp only [Category.assoc] at h
    exact h
  exact whiskerRecast_map_heq
    (A := fun w : List I => End ((pres D Sc).obj (ob D w)))
    (B := fun w : List I => TruncatedOld D Sc cutoff N w w)
    (fun w f => (truncatedIdeal D Sc cutoff N w w).mkQ
      ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] f))
    (List.append_assoc v σ τ) hh

/-- Inner module whiskering equals right whiskering of the affine source. -/
theorem contentInductionComp_inner (β : Multiset I) (σ τ : List I)
    (γ : Multiset I) (h : (β + (σ : Multiset I)) + (τ : Multiset I) = γ)
    (h' : β + ((σ ++ τ : List I) : Multiset I) = γ)
    {p : ZMod 2} {a : End ((pres D Sc).obj (ob D σ))}
    (ha : a ∈ parity (R := k) _ _ p)
    (M : ContentModules D Sc cutoff N β) (z : ContentCategory D Sc cutoff N γ) :
    (moduleIsoLinearEquiv ((contentInductionComp D Sc cutoff N β σ τ γ h h').app M) z).toLinearMap ∘ₗ
      BalancedInduction.mapComponent (contentAppendTo D Sc cutoff N (β + (σ : Multiset I)) τ γ h)
        (BalancedInduction.transformComponent
          (contentAppendTo_supernatural D Sc cutoff N rfl rfl ha) M) p z =
      BalancedInduction.transformLinear
        (contentAppendTo_supernatural D Sc cutoff N h' h'
          (MonoidalSupercategory.whiskerRight_mem (R := k) ((pres D Sc).obj (ob D τ)) ha)) M z ∘ₗ
      (moduleIsoLinearEquiv ((contentInductionComp D Sc cutoff N β σ τ γ h h').app M) z).toLinearMap := by
  exact BalancedInduction.compForward_inner_recast
    (contentAppendTo D Sc cutoff N β σ _ rfl)
    (contentAppendTo D Sc cutoff N (β + (σ : Multiset I)) τ γ h)
    (contentAppendTo D Sc cutoff N β (σ ++ τ) γ h')
    (contentAppend_comp_eq D Sc cutoff N β σ τ γ h h')
    (contentAppendTo_supernatural D Sc cutoff N rfl rfl ha)
    (contentAppendTo_supernatural D Sc cutoff N h' h'
      (MonoidalSupercategory.whiskerRight_mem (R := k) ((pres D Sc).obj (ob D τ)) ha))
    (fun v => appendComponent_rightContext_heq D Sc cutoff N v.obj.word σ τ a) M z

/-- Outer module whiskering equals left whiskering of the affine source. -/
theorem contentInductionComp_outer (β : Multiset I) (σ τ : List I)
    (γ : Multiset I) (h : (β + (σ : Multiset I)) + (τ : Multiset I) = γ)
    (h' : β + ((σ ++ τ : List I) : Multiset I) = γ)
    {p : ZMod 2} {a : End ((pres D Sc).obj (ob D τ))}
    (ha : a ∈ parity (R := k) _ _ p)
    (M : ContentModules D Sc cutoff N β) (z : ContentCategory D Sc cutoff N γ) :
    (moduleIsoLinearEquiv ((contentInductionComp D Sc cutoff N β σ τ γ h h').app M) z).toLinearMap ∘ₗ
      BalancedInduction.transformLinear
        (contentAppendTo_supernatural D Sc cutoff N h h ha)
        (BalancedInduction.induced (contentAppendTo D Sc cutoff N β σ _ rfl) M) z =
      BalancedInduction.transformLinear
        (contentAppendTo_supernatural D Sc cutoff N h' h'
          (MonoidalSupercategory.whiskerLeft_mem (R := k) ((pres D Sc).obj (ob D σ)) ha)) M z ∘ₗ
      (moduleIsoLinearEquiv ((contentInductionComp D Sc cutoff N β σ τ γ h h').app M) z).toLinearMap := by
  exact BalancedInduction.compForward_outer_recast
    (contentAppendTo D Sc cutoff N β σ _ rfl)
    (contentAppendTo D Sc cutoff N (β + (σ : Multiset I)) τ γ h)
    (contentAppendTo D Sc cutoff N β (σ ++ τ) γ h')
    (contentAppend_comp_eq D Sc cutoff N β σ τ γ h h')
    (contentAppendTo_supernatural D Sc cutoff N h h ha)
    (contentAppendTo_supernatural D Sc cutoff N h' h'
      (MonoidalSupercategory.whiskerLeft_mem (R := k) ((pres D Sc).obj (ob D σ)) ha))
    (fun v => appendComponent_leftContext_heq D Sc cutoff N v.obj.word σ τ a) M z

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Common-content mixed braid and its source correction

`DeformedMixedBraid.md` §2, equations (4)–(5), for the induction operators
needed by `DeformedActionAssembly.md` §6. The two middle equal-colour
crossings carry minus signs. The contravariant transforms use the three
words with common content, not endomorphism substitutes. Their difference
is the signed source correction, with the residual outside-colour twist
on the entire kernel morphism. The ordered dotted polynomial comparison
with the original parameters is a separate obligation.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

theorem contentTripleTransform_tensor {β γ : Multiset I} {σ τ υ ω : List I}
    (hσ : β + (σ : Multiset I) = γ) (hτ : β + (τ : Multiset I) = γ)
    (hυ : β + (υ : Multiset I) = γ) (hω : β + (ω : Multiset I) = γ)
    {p q r : ZMod 2}
    {a : (pres D Sc).obj (ob D σ) ⟶ (pres D Sc).obj (ob D τ)}
    {b : (pres D Sc).obj (ob D τ) ⟶ (pres D Sc).obj (ob D υ)}
    {c : (pres D Sc).obj (ob D υ) ⟶ (pres D Sc).obj (ob D ω)}
    (ha : a ∈ parity (R := k) _ _ p) (hb : b ∈ parity (R := k) _ _ q)
    (hc : c ∈ parity (R := k) _ _ r)
    (M : ContentModules D Sc cutoff N β) (w : ContentCategory D Sc cutoff N γ)
    (v : ContentCategory D Sc cutoff N β)
    (h : (contentAppendTo D Sc cutoff N β ω γ hω).obj v ⟶ w) (m : M.obj v) :
    ((BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N hσ hτ ha) M w).comp
      ((BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N hτ hυ hb) M w).comp
        (BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N hυ hω hc) M w)))
      (BalancedInduction.tensor (contentAppendTo D Sc cutoff N β ω γ hω) M.toFunctor v h m) =
    sign k (q*r + p*(q+r)) •
      BalancedInduction.tensor (contentAppendTo D Sc cutoff N β σ γ hσ) M.toFunctor v
        (contentAppendToComponent D Sc cutoff N hσ hω (a ≫ b ≫ c) v ≫
          twist k (p+(q+r)) h) m := by
  rw [BalancedInduction.transformLinear_comp, LinearMap.comp_smul,
    BalancedInduction.transformLinear_comp, smul_smul, ← sign_add,
    LinearMap.smul_apply, BalancedInduction.transformLinear_tensor]
  congr 2
  change (contentAppendToComponent D Sc cutoff N hσ hτ a v ≫
    contentAppendToComponent D Sc cutoff N hτ hυ b v ≫
    contentAppendToComponent D Sc cutoff N hυ hω c v) ≫ _ = _
  rw [contentAppendToComponent_comp D Sc cutoff N hτ hυ hω b hc,
    contentAppendToComponent_comp D Sc cutoff N hσ hτ hω a (comp_mem hb hc)]

theorem content_triple_iij (β : Multiset I) (i j : I) :
    β + ([i,i,j] : Multiset I) = β + ([i,j,i] : Multiset I) := by
  congr 1
  change i ::ₘ i ::ₘ j ::ₘ (0 : Multiset I) = i ::ₘ j ::ₘ i ::ₘ 0
  rw [Multiset.cons_swap i j]

theorem content_triple_jii (β : Multiset I) (i j : I) :
    β + ([j,i,i] : Multiset I) = β + ([i,j,i] : Multiset I) := by
  congr 1
  change j ::ₘ i ::ₘ i ::ₘ (0 : Multiset I) = i ::ₘ j ::ₘ i ::ₘ 0
  exact Multiset.cons_swap _ _ _

def contentTripleLeft (i j c : I) :
    (pres D Sc).obj (ob D [i,j,c]) ⟶ (pres D Sc).obj (ob D [j,i,c]) :=
  tripleCrossLeft D Sc i j c ⟨[], rfl⟩
def contentTripleRight (i j c : I) :
    (pres D Sc).obj (ob D [i,j,c]) ⟶ (pres D Sc).obj (ob D [i,c,j]) :=
  tripleCrossRight D Sc i j c ⟨[], rfl⟩
theorem contentTripleLeft_parity (i j c : I) :
    contentTripleLeft D Sc i j c ∈ parity (R := k) _ _ (D.parity i * D.parity j) :=
  tripleCrossLeft_parity D Sc i j c ⟨[], rfl⟩
theorem contentTripleRight_parity (i j c : I) :
    contentTripleRight D Sc i j c ∈ parity (R := k) _ _ (D.parity j * D.parity c) :=
  tripleCrossRight_parity D Sc i j c ⟨[], rfl⟩
def contentBraidCorrection (i j : I) : End ((pres D Sc).obj (ob D [i,j,i])) :=
  tripleBraidCorrection D Sc i j ⟨[], rfl⟩
theorem contentTriple_braid (i j : I) (hij : i ≠ j) :
    (contentTripleLeft D Sc i j i ≫ contentTripleRight D Sc j i i ≫ contentTripleLeft D Sc j i i) -
    (contentTripleRight D Sc i j i ≫ contentTripleLeft D Sc i i j ≫ contentTripleRight D Sc i i j) =
      contentBraidCorrection D Sc i j :=
  tripleCross_braid_correction D Sc i j hij ⟨[], rfl⟩

/-- Normalized mixed braid difference on one common content. -/
def contentMixedBraid (β : Multiset I) (i j : I)
    (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + ([i,j,i] : Multiset I))) :=
  let A := BalancedInduction.transformLinear
    (contentAppendTo_supernatural D Sc cutoff N rfl (content_triple_iij β i j)
      (contentTripleRight_parity D Sc i j i)) M w
  let B := BalancedInduction.transformLinear
    (contentAppendTo_supernatural D Sc cutoff N (content_triple_iij β i j)
      (content_triple_iij β i j) (contentTripleLeft_parity D Sc i i j)) M w
  let C := BalancedInduction.transformLinear
    (contentAppendTo_supernatural D Sc cutoff N (content_triple_iij β i j) rfl
      (contentTripleRight_parity D Sc i i j)) M w
  let E := BalancedInduction.transformLinear
    (contentAppendTo_supernatural D Sc cutoff N rfl (content_triple_jii β i j)
      (contentTripleLeft_parity D Sc i j i)) M w
  let F := BalancedInduction.transformLinear
    (contentAppendTo_supernatural D Sc cutoff N (content_triple_jii β i j)
      (content_triple_jii β i j) (contentTripleRight_parity D Sc j i i)) M w
  let G := BalancedInduction.transformLinear
    (contentAppendTo_supernatural D Sc cutoff N (content_triple_jii β i j) rfl
      (contentTripleLeft_parity D Sc j i i)) M w
  A.comp ((-B).comp C) - E.comp ((-F).comp G)

/-- The residual twist acts on the entire kernel, not just its affine factor. -/
theorem contentMixedBraid_tensor (β : Multiset I) {i j : I} (hij : i ≠ j)
    (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + ([i,j,i] : Multiset I)))
    (v : ContentCategory D Sc cutoff N β)
    (h : (contentAppendTo D Sc cutoff N β [i,j,i] _ rfl).obj v ⟶ w) (m : M.obj v) :
    contentMixedBraid D Sc cutoff N β i j M w
      (BalancedInduction.tensor (contentAppendTo D Sc cutoff N β [i,j,i] _ rfl) M.toFunctor v h m) =
    sign k (D.parity i * D.parity j) •
      contentTensorEval D Sc cutoff N M w v (twist k (D.parity i) h) m
        (contentBraidCorrection D Sc i j) := by
  let p := D.parity i
  let q := D.parity j
  have hdeg : p*q + (p*p + q*p) = p := by
    rcases parity_eq_zero_or_one p with hp | hp <;>
      rcases parity_eq_zero_or_one q with hq | hq <;> simp [hp,hq]
  have hsign : (p*p)*(q*p) + (p*q)*(p*p + q*p) = p*q := by
    rcases parity_eq_zero_or_one p with hp | hp <;>
      rcases parity_eq_zero_or_one q with hq | hq <;> simp [hp,hq]
  unfold contentMixedBraid
  simp only [LinearMap.neg_comp, LinearMap.comp_neg, LinearMap.sub_apply, LinearMap.neg_apply]
  rw [contentTripleTransform_tensor, contentTripleTransform_tensor]
  simp only [mul_comm q p] at hdeg hsign
  simp only [show D.parity i = p from rfl, show D.parity j = q from rfl]
  simp only [mul_comm q p, hdeg, hsign]
  rw [sub_neg_eq_add, neg_add_eq_sub, ← smul_sub]
  congr 1
  change contentTensorEval D Sc cutoff N M w v (twist k p h) m _ -
    contentTensorEval D Sc cutoff N M w v (twist k p h) m _ = _
  rw [← map_sub, contentTriple_braid D Sc i j hij]
  all_goals first | exact contentTripleLeft_parity D Sc _ _ _ |
    exact contentTripleRight_parity D Sc _ _ _

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Ordered dotted correction for common-content mixed braid

`DeformedMixedBraid.md` §3, equations (6)–(10), and the mixed relation needed
by `DeformedActionAssembly.md` §6. Three arbitrary dot powers retain their
full residual twist. On the support forced by Sc the scalar signs agree
with parameterTwist Sc after reflecting the correction index. No dots are
commuted. The resulting linear-map identity has the original Sc leading
and interior coefficients and the order X₃^(r-1-l) X₂^s X₁^l.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

/-- Ordered three-power evaluation, with no even-block assumptions. -/
theorem contentInduction_three_powers {β : Multiset I} {σ : List I}
    {p q t : ZMod 2} {a b c : End ((pres D Sc).obj (ob D σ))}
    (ha : a ∈ parity (R := k) _ _ p) (hb : b ∈ parity (R := k) _ _ q)
    (hc : c ∈ parity (R := k) _ _ t)
    (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + (σ : Multiset I)))
    (l s n : ℕ) (v : ContentCategory D Sc cutoff N β)
    (h : (contentAppendTo D Sc cutoff N β σ _ rfl).obj v ⟶ w) (m : M.obj v) :
    ((contentInductionEndLinear D Sc cutoff N hc M w ^ n) *
      (contentInductionEndLinear D Sc cutoff N hb M w ^ s) *
      (contentInductionEndLinear D Sc cutoff N ha M w ^ l))
        (BalancedInduction.tensor (contentAppendTo D Sc cutoff N β σ _ rfl) M.toFunctor v h m) =
    sign k (p*(l/2 : ℕ) + q*(s/2 : ℕ) + t*(n/2 : ℕ) +
      (s : ZMod 2)*q*((l : ZMod 2)*p) +
      (n : ZMod 2)*t*((s : ZMod 2)*q + (l : ZMod 2)*p)) •
      contentTensorEval D Sc cutoff N M w v
        (twist k ((n : ZMod 2)*t + ((s : ZMod 2)*q + (l : ZMod 2)*p)) h) m
        (a ^ l * b ^ s * c ^ n) := by
  rw [Module.End.mul_apply, Module.End.mul_apply,
    contentInductionEndLinear_pow_tensor, map_smul, contentInductionEndLinear_pow_tensor,
    map_smul, map_smul, contentInductionEndLinear_pow_tensor]
  unfold contentTensorEval
  simp only [contentAppendToLinear_apply]
  simp only [twist_comp,
    twist_of_mem _ ((contentAppendTo_supernatural D Sc cutoff N rfl rfl
      (contentEnd_pow_parity D Sc ha l)).mem v),
    twist_of_mem _ ((contentAppendTo_supernatural D Sc cutoff N rfl rfl
      (contentEnd_pow_parity D Sc hb s)).mem v), map_smul, ← twist_add,
    Linear.smul_comp, Linear.comp_smul, BalancedInduction.tensor,
    ← TensorProduct.smul_tmul', smul_smul, ← sign_add]
  dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
  congr 1
  · congr 1
    ring
  congr 2
  change _ = contentAppendToComponent D Sc cutoff N rfl rfl (a^l*b^s*c^n) v ≫ _
  rw [← Category.assoc, contentAppendToComponent_comp D Sc cutoff N rfl rfl rfl _
    (contentEnd_pow_parity D Sc hb s), ← Category.assoc,
    contentAppendToComponent_comp D Sc cutoff N rfl rfl rfl _ (contentEnd_pow_parity D Sc ha l)]
  simp only [End.mul_def, Category.assoc]

/-- Arbitrary-exponent sign identity on the prescribed separate parity support. -/
theorem mixed_braid_sign_identity
    (p q : ZMod 2) (r s l a : ℕ)
    (hr : (r : ZMod 2) * p = 0)
    (hs : (s : ZMod 2) * q = 0)
    (hl : l < r) (ha : a = r - 1 - l) :
    p*q + p*(l : ZMod 2) +
      (p*(l/2 : ℕ) + q*(s/2 : ℕ) + p*(a/2 : ℕ) +
        p*q*(s : ZMod 2)*((l : ZMod 2)+(a : ZMod 2)) + p*(l : ZMod 2)*(a : ZMod 2)) =
    p*(a : ZMod 2) + (p*q + p*(r/2 : ℕ) + q*(s/2 : ℕ)) := by
  rcases parity_eq_zero_or_one p with rfl | rfl
  · simp
  · have hz : (2 : ZMod 2) = 0 := rfl
    have hr0 : (r : ZMod 2) = 0 := by simpa using hr
    have hrmod : r % 2 = 0 := by
      simpa using (ZMod.natCast_eq_natCast_iff' r 0 2).mp hr0
    have hsum : l + a + 1 = r := by omega
    have hh : l / 2 + a / 2 + 1 = r / 2 := by omega
    have hadd := congrArg (Nat.cast : ℕ → ZMod 2) hsum
    push_cast at hadd
    rw [hr0] at hadd
    have hhalf := congrArg (Nat.cast : ℕ → ZMod 2) hh
    push_cast at hhalf
    have hprod : (l : ZMod 2) * (a : ZMod 2) = 0 := by
      rcases parity_eq_zero_or_one (l : ZMod 2) with hl0 | hl1
      · simp [hl0]
      · rw [hl1, one_mul]
        rw [hl1] at hadd
        linear_combination hadd - hz
    have hcross : q*(s : ZMod 2)*((l : ZMod 2)+(a : ZMod 2)) = 0 := by
      rw [mul_comm q (s : ZMod 2), hs, zero_mul]
    simp only [one_mul, hcross, hprod, add_zero]
    linear_combination hadd + hhalf - ((a : ZMod 2) + 1) * hz

theorem mixed_braid_total_parity (p q : ZMod 2) (r s l : ℕ)
    (hr : (r : ZMod 2)*p = 0) (hs : (s : ZMod 2)*q = 0) (hl : l < r) :
    ((r-1-l : ℕ) : ZMod 2)*p + ((s : ZMod 2)*q + (l : ZMod 2)*p) = p := by
  have he : r - 1 - l + l + 1 = r := by omega
  have he' := congrArg (Nat.cast : ℕ → ZMod 2) he
  push_cast at he'
  have hz : (2 : ZMod 2) = 0 := rfl
  linear_combination p * he' + hr + hs - p * hz

/-- Supported intermediate calculation; support is derived from Sc in the polynomial theorem. -/
theorem contentInduction_three_supported {β : Multiset I} {σ : List I}
    {p q : ZMod 2} {a b c : End ((pres D Sc).obj (ob D σ))}
    (ha : a ∈ parity (R := k) _ _ p) (hb : b ∈ parity (R := k) _ _ q)
    (hc : c ∈ parity (R := k) _ _ p)
    (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + (σ : Multiset I)))
    (r s l : ℕ) (hr : (r : ZMod 2)*p = 0) (hs : (s : ZMod 2)*q = 0) (hl : l < r)
    (d : k) (v : ContentCategory D Sc cutoff N β)
    (h : (contentAppendTo D Sc cutoff N β σ _ rfl).obj v ⟶ w) (m : M.obj v) :
    ((sign k (p*(q+(l : ZMod 2))) * d) •
      ((contentInductionEndLinear D Sc cutoff N hc M w ^ (r-1-l)) *
        (contentInductionEndLinear D Sc cutoff N hb M w ^ s) *
        (contentInductionEndLinear D Sc cutoff N ha M w ^ l)))
        (BalancedInduction.tensor (contentAppendTo D Sc cutoff N β σ _ rfl) M.toFunctor v h m) =
    sign k (p*q) • contentTensorEval D Sc cutoff N M w v (twist k p h) m
      ((sign k (p*(q+((r-1-l : ℕ) : ZMod 2))) *
        (sign k (p*q+p*(r/2 : ℕ)+q*(s/2 : ℕ)) * d)) •
        (a^l*b^s*c^(r-1-l))) := by
  rw [LinearMap.smul_apply, contentInduction_three_powers,
    mixed_braid_total_parity p q r s l hr hs hl, map_smul, smul_smul, smul_smul]
  congr 1
  let n := r-1-l
  have hp : p*p = p := by
    rcases parity_eq_zero_or_one p with hp | hp <;> simp [hp]
  have he := mixed_braid_sign_identity p q r s l n hr hs hl rfl
  have hsign : sign k (p*(q+(l : ZMod 2))) *
      sign k (p*(l/2 : ℕ)+q*(s/2 : ℕ)+p*(n/2 : ℕ)+
        (s : ZMod 2)*q*((l : ZMod 2)*p)+(n : ZMod 2)*p*((s : ZMod 2)*q+(l : ZMod 2)*p)) =
      sign k (p*q) * (sign k (p*(q+(n : ZMod 2))) *
        sign k (p*q+p*(r/2 : ℕ)+q*(s/2 : ℕ))) := by
    simp only [← sign_add]
    congr 1
    have hz : (2 : ZMod 2) = 0 := rfl
    linear_combination he + (n : ZMod 2)*(l : ZMod 2)*(hp) - p*q*hz
  calc
    _ = (sign k (p*(q+(l : ZMod 2))) *
      sign k (p*(l/2 : ℕ)+q*(s/2 : ℕ)+p*(n/2 : ℕ)+
        (s : ZMod 2)*q*((l : ZMod 2)*p)+(n : ZMod 2)*p*((s : ZMod 2)*q+(l : ZMod 2)*p))) * d := by ring
    _ = _ := by rw [hsign]; ring

theorem contentTripleDot_one_parity (i j : I) :
    dotE D Sc [i,j,i] 1 ∈ parity (R := k) _ _ (D.parity j) := by
  simpa using positionedDot_parity D Sc [i] [i] j

theorem contentTripleDot_two_parity (i j : I) :
    dotE D Sc [i,j,i] 2 ∈ parity (R := k) _ _ (D.parity i) := by
  simpa using positionedDot_parity D Sc [i,j] [] i

def contentMixedDotSum (β : Multiset I) (i j : I) (r s : ℕ) (d : k)
    (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + ([i,j,i] : Multiset I))) :=
  let A := contentInductionEndLinear D Sc cutoff N (firstDot_parity D Sc i [j,i]) M w
  let B := contentInductionEndLinear D Sc cutoff N (contentTripleDot_one_parity D Sc i j) M w
  let C := contentInductionEndLinear D Sc cutoff N (contentTripleDot_two_parity D Sc i j) M w
  ∑ l ∈ Finset.range r, (SKM.zsign k (D.parity i*(D.parity j+l))*d) • (C^(r-1-l)*B^s*A^l)

def contentMixedSourceSum (i j : I) (r s : ℕ) (d : k) : End ((pres D Sc).obj (ob D [i,j,i])) :=
  ∑ l ∈ Finset.range r, (SKM.zsign k (D.parity i*(D.parity j+l))*d) •
    (dotE D Sc [i,j,i] 0 ^ (r-1-l) * dotE D Sc [i,j,i] 1 ^ s * dotE D Sc [i,j,i] 2 ^ l)

theorem contentMixedDotSum_tensor (β : Multiset I) (i j : I) (r s : ℕ) (d : k)
    (hd : d ≠ 0 → (r : ZMod 2)*D.parity i = 0 ∧ (s : ZMod 2)*D.parity j = 0)
    (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + ([i,j,i] : Multiset I)))
    (v : ContentCategory D Sc cutoff N β)
    (h : (contentAppendTo D Sc cutoff N β [i,j,i] _ rfl).obj v ⟶ w) (m : M.obj v) :
    contentMixedDotSum D Sc cutoff N β i j r s d M w
      (BalancedInduction.tensor (contentAppendTo D Sc cutoff N β [i,j,i] _ rfl) M.toFunctor v h m) =
    sign k (D.parity i*D.parity j) •
      contentTensorEval D Sc cutoff N M w v (twist k (D.parity i) h) m
        (contentMixedSourceSum D Sc i j r s
          (SKM.zsign k (parameterSignExponent D i j r s)*d)) := by
  by_cases hd0 : d = 0
  · simp [contentMixedDotSum, contentMixedSourceSum, hd0]
  obtain ⟨hr,hs⟩ := hd hd0
  unfold contentMixedDotSum contentMixedSourceSum
  rw [← Finset.sum_range_reflect (fun l =>
    (SKM.zsign k (D.parity i*(D.parity j+l)) *
      (SKM.zsign k (parameterSignExponent D i j r s)*d)) •
      (dotE D Sc [i,j,i] 0 ^ (r-1-l) * dotE D Sc [i,j,i] 1 ^ s * dotE D Sc [i,j,i] 2 ^ l)) r]
  simp only [LinearMap.sum_apply, map_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  have hl' := Finset.mem_range.mp hl
  have he : r-1-(r-1-l) = l := by omega
  rw [he]
  simpa only [sign_eq_zsign, parameterSignExponent] using
    contentInduction_three_supported D Sc cutoff N (firstDot_parity D Sc i [j,i])
      (contentTripleDot_one_parity D Sc i j) (contentTripleDot_two_parity D Sc i j)
      M w r s l hr hs hl' d v h m

theorem contentBraidCorrection_eq_sums (i j : I) :
    contentBraidCorrection D Sc i j =
      contentMixedSourceSum D Sc i j (D.dn i j) 0 (Sc.t i j : k) +
      ∑ r ∈ Finset.range (D.dn i j), ∑ s ∈ Finset.range (D.dn j i),
        contentMixedSourceSum D Sc i j r s (Sc.s i j r s) := by
  simp only [contentBraidCorrection, tripleBraidCorrection, contentMixedSourceSum,
    tripleWord, List.nil_append, List.length_nil, zero_add, pow_zero, mul_one]
  rfl

/-- The prescribed Sc correction, in ordered powers of the three induction dots. -/
def contentMixedBraidPolynomial (β : Multiset I) (i j : I)
    (M : ContentModules D (parameterTwist D Sc) cutoff N β)
    (w : ContentCategory D (parameterTwist D Sc) cutoff N (β + ([i,j,i] : Multiset I))) :=
  contentMixedDotSum D (parameterTwist D Sc) cutoff N β i j (D.dn i j) 0 (Sc.t i j : k) M w +
    ∑ r ∈ Finset.range (D.dn i j), ∑ s ∈ Finset.range (D.dn j i),
      contentMixedDotSum D (parameterTwist D Sc) cutoff N β i j r s (Sc.s i j r s) M w

theorem contentMixedBraidPolynomial_tensor (β : Multiset I) {i j : I} (hij : i ≠ j)
    (M : ContentModules D (parameterTwist D Sc) cutoff N β)
    (w : ContentCategory D (parameterTwist D Sc) cutoff N (β + ([i,j,i] : Multiset I)))
    (v : ContentCategory D (parameterTwist D Sc) cutoff N β)
    (h : (contentAppendTo D (parameterTwist D Sc) cutoff N β [i,j,i] _ rfl).obj v ⟶ w)
    (m : M.obj v) :
    contentMixedBraidPolynomial D Sc cutoff N β i j M w
      (BalancedInduction.tensor (contentAppendTo D (parameterTwist D Sc) cutoff N β [i,j,i] _ rfl)
        M.toFunctor v h m) =
    sign k (D.parity i*D.parity j) •
      contentTensorEval D (parameterTwist D Sc) cutoff N M w v (twist k (D.parity i) h) m
        (contentBraidCorrection D (parameterTwist D Sc) i j) := by
  have ht := contentMixedDotSum_tensor D (parameterTwist D Sc) cutoff N β i j
    (D.dn i j) 0 (Sc.t i j : k)
    (fun _ => ⟨CyclotomicAction.dn_cast_mul_parity D hij, by simp⟩) M w v h m
  have hs (r s : ℕ) := contentMixedDotSum_tensor D (parameterTwist D Sc) cutoff N β i j
    r s (Sc.s i j r s) (fun hc => elvParameter_support D Sc hc) M w v h m
  unfold contentMixedBraidPolynomial
  rw [contentBraidCorrection_eq_sums]
  simp only [LinearMap.add_apply, LinearMap.sum_apply, map_add, map_sum, smul_add,
    Finset.smul_sum, ht, hs, CyclotomicAction.parameterTwist_t_of_ne D Sc hij,
    CyclotomicAction.parameterTwist_s]

/-- The normalized mixed braid equals the prescribed ordered dotted polynomial. -/
theorem contentMixedBraid_polynomial_linear (β : Multiset I) {i j : I} (hij : i ≠ j)
    (M : ContentModules D (parameterTwist D Sc) cutoff N β)
    (w : ContentCategory D (parameterTwist D Sc) cutoff N (β + ([i,j,i] : Multiset I))) :
    contentMixedBraid D (parameterTwist D Sc) cutoff N β i j M w =
      contentMixedBraidPolynomial D Sc cutoff N β i j M w := by
  apply BalancedInduction.hom_ext
  intro v h m
  rw [contentMixedBraid_tensor D _ cutoff N β hij,
    contentMixedBraidPolynomial_tensor D Sc cutoff N β hij]

end OddMath.QuiverHecke.ELV
end

end

section

/-! # The ordered three-dot correction with the original scalar parameters

Brundan--Ellis (1.9), repeated outer colour. Retain the source correction
as an ordered polynomial in three arbitrary endomorphisms, before any
selected module chart or weight evaluation is substituted.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X)

/-- The ordered summand of the three-dot correction. -/
def tripleDotCorrectionSum {R : Type*} [Ring R] [Algebra k R]
    (i j : I) (r s : ℕ) (d : k) (A B C : R) : R :=
  ∑ t ∈ Finset.range r, (SKM.zsign k (D.parity i * (D.parity j + t)) * d) •
    (C ^ (r - 1 - t) * B ^ s * A ^ t)

/-- The original Sc correction, with all three operator orders retained. -/
def tripleDotCorrectionPolynomial {R : Type*} [Ring R] [Algebra k R]
    (Sc : SKM.Scalars D k) (i j : I) (A B C : R) : R :=
  tripleDotCorrectionSum D i j (D.dn i j) 0 (Sc.t i j : k) A B C +
    ∑ r ∈ Finset.range (D.dn i j), ∑ s ∈ Finset.range (D.dn j i),
      tripleDotCorrectionSum D i j r s (Sc.s i j r s) A B C

/-- Algebra maps preserve the ordered summand; no commutativity of the three operators is assumed. -/
theorem tripleDotCorrectionSum_map
    {R S : Type*} [Ring R] [Algebra k R] [Ring S] [Algebra k S]
    (φ : R →ₐ[k] S) (i j : I) (r s : ℕ) (d : k) (A B C : R) :
    φ (tripleDotCorrectionSum D i j r s d A B C) =
      tripleDotCorrectionSum D i j r s d (φ A) (φ B) (φ C) := by
  simp only [tripleDotCorrectionSum, map_sum, map_smul, map_mul, map_pow]

/-- Algebra maps retain the ORIGINAL Sc coefficients and all operator orders. -/
theorem tripleDotCorrectionPolynomial_map
    {R S : Type*} [Ring R] [Algebra k R] [Ring S] [Algebra k S]
    (Sc : SKM.Scalars D k) (φ : R →ₐ[k] S) (i j : I) (A B C : R) :
    φ (tripleDotCorrectionPolynomial D Sc i j A B C) =
      tripleDotCorrectionPolynomial D Sc i j (φ A) (φ B) (φ C) := by
  simp only [tripleDotCorrectionPolynomial, map_add, map_sum, tripleDotCorrectionSum_map]

/-- Exact binding to the checked canonical-content correction: the acting
scalars are parameterTwist Sc, while the polynomial coefficients are Sc. -/
theorem contentMixedBraidPolynomial_eq_ordered
    (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ) (β : Multiset I) (i j : I)
    (M : ContentModules D (parameterTwist D Sc) cutoff bound β)
    (w : ContentCategory D (parameterTwist D Sc) cutoff bound (β + ([i,j,i] : Multiset I))) :
    contentMixedBraidPolynomial D Sc cutoff bound β i j M w =
      tripleDotCorrectionPolynomial D Sc i j
        (contentInductionEndLinear D (parameterTwist D Sc) cutoff bound
          (firstDot_parity D (parameterTwist D Sc) i [j,i]) M w)
        (contentInductionEndLinear D (parameterTwist D Sc) cutoff bound
          (contentTripleDot_one_parity D (parameterTwist D Sc) i j) M w)
        (contentInductionEndLinear D (parameterTwist D Sc) cutoff bound
          (contentTripleDot_two_parity D (parameterTwist D Sc) i j) M w) := by
  rfl

end OddMath.QuiverHecke.ELV
end

end

section

/-! # The ordered correction as dotted whiskerings

Brundan--Ellis (1.9). The noncommutative three-position polynomial is
exactly the prescribed dotted correction, in every two-supercategory.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELV
universe u v w r
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  {I X : Type r} [AddCommGroup X] (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
  (i j : I) {a b c d : B} (F : a ⟶ b) (G : b ⟶ c) (H : c ⟶ d)
  (x : End F) (y : End G) (z : End H)

/-- The exact correction sum of the Rouquier multicolour braid field,
with every dot power in its prescribed position and order. -/
theorem tripleDotCorrectionPolynomial_whiskers :
    tripleDotCorrectionPolynomial (R := End (F ≫ G ≫ H)) D Sc i j
      (x ▷ (G ≫ H)) (F ◁ (y ▷ H)) (F ◁ G ◁ z) =
    ∑ s ∈ Finset.range (D.dn i j),
      (SKM.zsign k (D.parity i * (D.parity j + s)) * (Sc.t i j : k)) •
        (SKM.rouquierPower x s ▷ (G ≫ H) ≫ F ◁ G ◁ SKM.rouquierPower z (D.dn i j - 1 - s)) +
    ∑ p ∈ Finset.range (D.dn i j), ∑ q ∈ Finset.range (D.dn j i), ∑ s ∈ Finset.range p,
      (SKM.zsign k (D.parity i * (D.parity j + s)) * Sc.s i j p q) •
        (SKM.rouquierPower x s ▷ (G ≫ H) ≫ F ◁ (SKM.rouquierPower y q ▷ H) ≫
          F ◁ G ◁ SKM.rouquierPower z (p - 1 - s)) := by
  have hX (n : ℕ) := SKM.whiskerRight_rouquierPower (k := k) (B := B) x (G ≫ H) n
  have hY (n : ℕ) : (show End (F ≫ G ≫ H) from F ◁ (y ▷ H)) ^ n =
      F ◁ (SKM.rouquierPower y n ▷ H) := by
    rw [SKM.whiskerLeft_rouquierPower (k := k), SKM.rouquierPower_eq_pow, SKM.whiskerRight_rouquierPower (k := k)]
  have hZ (n : ℕ) : (show End (F ≫ G ≫ H) from F ◁ G ◁ z) ^ n =
      F ◁ G ◁ SKM.rouquierPower z n := by
    rw [SKM.whiskerLeft_rouquierPower (k := k), SKM.rouquierPower_eq_pow, SKM.whiskerLeft_rouquierPower (k := k)]
  simp only [tripleDotCorrectionPolynomial, tripleDotCorrectionSum, pow_zero, mul_one]
  simp_rw [hX, hY, hZ]
  simp only [End.mul_def]

end OddMath.QuiverHecke.ELV
end

end
