import OddMath.QuiverHecke.CyclotomicAction.EndpointPolynomials.PDescent
import OddMath.QuiverHecke.CyclotomicAction.LeadingMove.MoveHomLeading

/-!
# Chronological tails

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-!
# Full-ELV chronological short-image inclusion

The actual `pMap` sends the explicitly generated chronological short submodule
into the explicitly generated final equal-colour crossing submodule. The
old-factor balance twist is retained. This is the generator-factorization part
of `DeformedMackeyBoundary.md` (4)–(5), over the ground ring with full exterior
coefficients. Identification of the chronological short span with the PBW
short coordinate summand, and identification of the crossing span with the
prescribed balanced tensor target, are not asserted here.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Old insertion on the right, with the full coefficient Hom space. -/
abbrev appendInsert (i : I) (v w : List I) := rightContext D Sc cutoff [i] v w

/-- Chronological short generators at a fixed output. No PBW identification is asserted. -/
def chronologicalShortSpan (i : I) (v t : List I) :
    Submodule k (Target D Sc cutoff i v (t ++ [i])) :=
  Submodule.span k {z | ∃ s, ∃ r : hom D Sc cutoff v (s ++ [i]),
    ∃ h : hom D Sc cutoff (i :: s) t,
      projection D Sc cutoff i v (t ++ [i])
        (insert D Sc cutoff i v (s ++ [i]) r ≫
          rightContext D Sc cutoff [i] (i :: s) t h) = z}

/-- The explicit last equal-colour crossing span in the append quotient. -/
def chronologicalCrossingSpan (i : I) (v t : List I) :
    Submodule k (AppendTarget D Sc cutoff i v (t ++ [i])) :=
  Submodule.span k {z | ∃ s, ∃ r : hom D Sc cutoff v (s ++ [i]),
    ∃ g : hom D Sc cutoff (s ++ [i]) t,
      appendProjection D Sc cutoff i v (t ++ [i])
        (appendInsert D Sc cutoff i v (s ++ [i]) r ≫
          affineUnit D Sc cutoff _ _ (crossLast D Sc s i i) ≫
          rightContext D Sc cutoff [i] (s ++ [i]) t g) = z}

/-- Moving the old factor through W retains its full parity twist. -/
theorem pMap_chronologicalShort_generator (i : I) (v s t : List I)
    (r : hom D Sc cutoff v (s ++ [i])) (h : hom D Sc cutoff (i :: s) t) :
    pMap D Sc cutoff i v (t ++ [i])
      (projection D Sc cutoff i v (t ++ [i])
        (insert D Sc cutoff i v (s ++ [i]) r ≫
          rightContext D Sc cutoff [i] (i :: s) t h)) =
    appendProjection D Sc cutoff i v (t ++ [i])
      (appendInsert D Sc cutoff i v (s ++ [i]) (twist k (appendQ D cutoff i v) r) ≫
        affineUnit D Sc cutoff _ _ (crossLast D Sc s i i) ≫
        rightContext D Sc cutoff [i] (s ++ [i]) t (appendW D Sc cutoff i s ≫ h)) := by
  have he := appendError_mem_appendRelations D Sc cutoff i
    (twist k (appendQ D cutoff i v) r)
  rw [appendError_apply, twist_twist] at he
  have hc := appendRelations_comp D Sc cutoff i he
    (rightContext D Sc cutoff [i] (i :: s) t h)
  have hz := (appendProjection_eq_zero_iff D Sc cutoff i v (t ++ [i]) _).mpr hc
  rw [Preadditive.sub_comp, map_sub, sub_eq_zero] at hz
  change appendProjection D Sc cutoff i v (t ++ [i])
    (appendW D Sc cutoff i v ≫ (insert D Sc cutoff i v (s ++ [i]) r ≫
      rightContext D Sc cutoff [i] (i :: s) t h)) = _
  rw [← Category.assoc, ← hz, appendW_append]
  simp only [appendInsert, rightContext_comp, Category.assoc]

/-- The concrete P sends the chronological short span into the crossing span. -/
theorem pMap_chronologicalShortSpan_le (i : I) (v t : List I) :
    (chronologicalShortSpan D Sc cutoff i v t).map
      (pMap D Sc cutoff i v (t ++ [i])) ≤ chronologicalCrossingSpan D Sc cutoff i v t := by
  rw [Submodule.map_le_iff_le_comap]
  apply Submodule.span_le.mpr
  rintro _ ⟨s, r, h, rfl⟩
  change pMap D Sc cutoff i v (t ++ [i]) _ ∈ chronologicalCrossingSpan D Sc cutoff i v t
  rw [pMap_chronologicalShort_generator]
  exact Submodule.subset_span ⟨s, twist k (appendQ D cutoff i v) r,
    appendW D Sc cutoff i s ≫ h, rfl⟩

end OddMath.QuiverHecke.ELV
end

end

section

/-!
# Relative shortness by smaller-tail normalization

The bare smaller moving tail, extended by an untouched right strand, lies in
the full short prepend PBW span. Arbitrary old coefficients are reattached
using `replaceOld` and `rebase`, after the bare-tail crossing estimate.
`chronological_scalar_long_zero` and `chronological_scalar_output_stability`
provide actual relative-coset vanishing for `DeformedMackeyBoundary.md` (2).
No total crossing bound on the old coefficient is imposed.
-/

noncomputable section
open CategoryTheory StringDiagrams Categorification.TypeA Equiv MonoidalCategory
open scoped TensorProduct Classical
namespace OddMath.QuiverHecke.SmallerTailNormalization

theorem prepend_length_le (n : ℕ) (u : PrependShuffle n) :
    (canWord (n + 1) u.1⁻¹).length ≤ n := by
  rw [length_canWord, length_eq_invCount]
  have hmono : StrictMono (fun x : Fin n => u.1⁻¹ x.succ) := by
    intro x y hxy
    have he (z : Fin n) : blockEquiv (Nat.add_comm 1 n) (Sum.inr z) = z.succ := by
      apply Fin.ext
      simp [blockEquiv_inr_val, Nat.add_comm]
    simpa only [he] using u.2.2 hxy
  have hsub : invSet (n + 1) u.1⁻¹ ⊆
      Finset.univ.filter (fun p : Fin (n + 1) × Fin (n + 1) => p.1 = 0 ∧ p.2 ≠ 0) := by
    intro p hp
    have hp' := mem_invSet.mp hp
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · by_contra hn
      obtain ⟨a, ha⟩ := Fin.exists_succ_eq.mpr hn
      have hn' : p.2 ≠ 0 := by intro hz; simp [hz] at hp'
      obtain ⟨b, hb⟩ := Fin.exists_succ_eq.mpr hn'
      rw [← ha, ← hb] at hp'
      exact (not_lt_of_ge (hmono (Fin.succ_lt_succ_iff.mp hp'.1)).le) hp'.2
    · intro hz; simp [hz] at hp'
  have hc : (invSet (n + 1) u.1⁻¹).card ≤
      (Finset.univ.erase (0 : Fin (n + 1))).card := by
    apply Finset.card_le_card_of_injOn Prod.snd
    · intro p hp
      exact Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp (hsub hp)).2.2, Finset.mem_univ _⟩
    · intro p hp q hq he
      apply Prod.ext
      · exact (Finset.mem_filter.mp (hsub hp)).2.1.trans
          (Finset.mem_filter.mp (hsub hq)).2.1.symm
      · exact he
  simpa only [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_fin, Nat.add_sub_cancel, invCount] using hc

universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k)

/-- Relative shortness retains arbitrary old input normal forms. -/
def shortSpan (i : I) (s t : List I) :
    Submodule k ((pres D Sc).obj (ob D (i :: s)) ⟶ (pres D Sc).obj (ob D t)) :=
  Submodule.span k (prependBasis D Sc ''
    {x : PrependIdx i s t | x.1.2.2.2 ≠ longPrependShuffle s.length})

/-- Exact coordinate criterion, not a total crossing bound. -/
theorem mem_shortSpan_iff (i : I) (s t : List I)
    (f : (pres D Sc).obj (ob D (i :: s)) ⟶ (pres D Sc).obj (ob D t)) :
    f ∈ shortSpan D Sc i s t ↔
      ∀ x : PrependIdx i s t, x.1.2.2.2 = longPrependShuffle s.length →
        (prependBasis D Sc).repr f x = 0 := by
  rw [shortSpan, Module.Basis.mem_span_image]
  constructor
  · intro h x hx
    by_contra hn
    exact h (Finsupp.mem_support_iff.mpr hn) hx
  · intro h x hx he
    exact Finsupp.mem_support_iff.mp hx (h x he)

/-- The already available absolute low bound implies relative shortness. -/
theorem low_le_shortSpan (i : I) (s t : List I) :
    Low D Sc (i :: s) t s.length ≤ shortSpan D Sc i s t := by
  intro f hf
  exact (mem_shortSpan_iff D Sc i s t f).mpr fun x hx =>
    prependBasis_long_repr_eq_zero_of_low D Sc i s t f hf x hx
/-- Arbitrarily complicated old input coefficients remain short on a fixed short tail.
This isolates the old coefficient before any total-crossing estimate is applied. -/
theorem arbitrary_old_on_short_tail {i : I} {s t : List I}
    (x : PrependIdx i s t) (hx : x.1.2.2.2 ≠ longPrependShuffle s.length)
    (f : (pres D Sc).obj (ob D s) ⟶ (pres D Sc).obj (ob D x.oldTarget)) :
    ELV.affineInsert D Sc i s x.oldTarget f ≫ ELV.prependTail D Sc x ∈
      shortSpan D Sc i s t := by
  have hf : f ∈ Submodule.span k (Set.range (basisNF D Sc s x.oldTarget)) := by
    rw [Module.Basis.span_eq]
    trivial
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨y, rfl⟩ := hf
    rw [basisNF_apply, ← ELV.prependElt_replaceOld]
    apply Submodule.subset_span
    exact ⟨x.replaceOld y, hx, prependBasis_apply D Sc _⟩
  | zero => simp
  | add f g _ _ hf hg =>
    rw [map_add, Preadditive.add_comp]
    exact Submodule.add_mem _ hf hg
  | smul a f _ hf =>
    rw [map_smul, Linear.smul_comp]
    exact Submodule.smul_mem _ a hf

/-- Only the bare smaller tail is bounded; its old coefficient is excluded. -/
theorem extended_prependTail_low {i : I} {s t : List I}
    (x : PrependIdx i s t) (j : I) :
    ELV.prependTail D Sc x ▷ (pres D Sc).obj (ob D [j]) ∈
      Low D Sc (i :: (x.oldTarget ++ [j])) (t ++ [j]) (s.length + 1) := by
  unfold ELV.prependTail
  rw [cl_whiskerRight D Sc _ _ [j] (fits_append
    (fits_dots (by intro p hp; have he := (List.mem_replicate.mp hp).2; subst p; simp))
    (by simpa only [List.length_cons, PrependIdx.oldTarget, length_tgt]
      using fits_cw (isReduced_canWord (s.length + 1) x.1.2.2.2.1⁻¹).1))]
  apply cl_mem_low
  simp only [crossCount_append, crossCount_dots, crossCount_cw, zero_add]
  exact Nat.lt_succ_of_le (prepend_length_le s.length x.1.2.2.2)

theorem extended_prependTail_short {i : I} {s t : List I}
    (x : PrependIdx i s t) (j : I) :
    ELV.prependTail D Sc x ▷ (pres D Sc).obj (ob D [j]) ∈
      shortSpan D Sc i (x.oldTarget ++ [j]) (t ++ [j]) := by
  apply low_le_shortSpan
  have hf := extended_prependTail_low D Sc x j
  change (ELV.prependTail D Sc x ▷ (pres D Sc).obj (ob D [j]) :
    (pres D Sc).obj (ob D (i :: (x.oldTarget ++ [j]))) ⟶
      (pres D Sc).obj (ob D (t ++ [j]))) ∈
      Low D Sc (i :: (x.oldTarget ++ [j])) (t ++ [j]) (s.length + 1) at hf
  have hl : (x.oldTarget ++ [j]).length = s.length + 1 := by
    simp only [List.length_append, List.length_singleton, PrependIdx.oldTarget, length_tgt]
  rw [hl]
  exact hf

private theorem insert_tail_transport {i : I} {v t t' w : List I}
    (e : t = t') (r : (pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D t))
    (f : (pres D Sc).obj (ob D (i :: t)) ⟶ (pres D Sc).obj (ob D w))
    (g : (pres D Sc).obj (ob D (i :: t')) ⟶ (pres D Sc).obj (ob D w))
    (h : HEq f g) :
    ELV.affineInsert D Sc i v t r ≫ f =
    ELV.affineInsert D Sc i v t' (e ▸ r) ≫ g := by
  subst t'
  cases h
  rfl

theorem rebase_short {i : I} {v s t : List I} (z : PrependIdx i s t)
    (hz : z.1.2.2.2 ≠ longPrependShuffle s.length) (y : NFIdx v z.oldTarget) :
    (z.rebase y).1.2.2.2 ≠ longPrependShuffle v.length := by
  have hl : v.length = s.length := by
    have hh := congrArg List.length y.tgt_cw
    simpa only [length_tgt, PrependIdx.oldTarget] using hh
  change (hl.symm ▸ z.1.2.2.2) ≠ longPrependShuffle v.length
  exact (show ∀ {n m : ℕ} (h : n = m) (u : PrependShuffle m),
      u ≠ longPrependShuffle m → (h.symm ▸ u) ≠ longPrependShuffle n from
    by intro n m h; subst m; exact fun _ h => h) hl _ hz

theorem arbitrary_old_cross_source {i : I} {v s t : List I}
    (z : PrependIdx i s t) (hz : z.1.2.2.2 ≠ longPrependShuffle s.length)
    (r : (pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D z.oldTarget)) :
    ELV.affineInsert D Sc i v z.oldTarget r ≫ ELV.prependTail D Sc z ∈
      shortSpan D Sc i v t := by
  by_cases hr : r = 0
  · simp [hr]
  · have hn : Nonempty (NFIdx v z.oldTarget) := by
      by_contra hn
      have : IsEmpty (NFIdx v z.oldTarget) := not_nonempty_iff.mp hn
      apply hr
      apply (basisNF D Sc v z.oldTarget).repr.injective
      ext y
      exact isEmptyElim y
    obtain ⟨y⟩ := hn
    rw [insert_tail_transport D Sc (z.rebase_target y).symm r _ _
      (ELV.prependTail_rebase D Sc z y).symm]
    exact arbitrary_old_on_short_tail D Sc (z.rebase y) (rebase_short z hz y) _

theorem old_comp_short {i : I} {v s t : List I}
    (r : (pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D s))
    (f : (pres D Sc).obj (ob D (i :: s)) ⟶ (pres D Sc).obj (ob D t))
    (hf : f ∈ shortSpan D Sc i s t) :
    ELV.affineInsert D Sc i v s r ≫ f ∈ shortSpan D Sc i v t := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨z, hz, rfl⟩ := hf
    rw [prependBasis_apply, ELV.prependElt_insert_tail, ← Category.assoc]
    have he : ELV.affineInsert D Sc i v s r ≫
        ELV.affineInsert D Sc i s z.oldTarget z.old.nf =
        ELV.affineInsert D Sc i v z.oldTarget (r ≫ z.old.nf) := by
      exact (MonoidalSupercategory.whiskerLeft_comp (R := k) _ _ _).symm
    rw [he]
    exact arbitrary_old_cross_source D Sc z hz _
  | zero => simp
  | add f g _ _ hf hg =>
    rw [Preadditive.comp_add]
    exact Submodule.add_mem _ hf hg
  | smul a f _ hf =>
    rw [Linear.comp_smul]
    exact Submodule.smul_mem _ a hf

/-- Actual scalar chronological generators have no long coefficient. -/
theorem chronological_scalar_short {i j : I} {v s t : List I}
    (r : (pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D (s ++ [j])))
    (h : (pres D Sc).obj (ob D (i :: s)) ⟶ (pres D Sc).obj (ob D t)) :
    ELV.affineInsert D Sc i v (s ++ [j]) r ≫
      (h ▷ (pres D Sc).obj (ob D [j])) ∈ shortSpan D Sc i v (t ++ [j]) := by
  have hh : h ∈ Submodule.span k (Set.range (prependBasis D Sc (i := i) (s := s) (t := t))) := by
    rw [Module.Basis.span_eq]
    trivial
  induction hh using Submodule.span_induction with
  | mem h hh =>
    obtain ⟨x, rfl⟩ := hh
    rw [prependBasis_apply, ELV.prependElt_insert_tail]
    erw [MonoidalSupercategory.comp_whiskerRight (R := k), ← Category.assoc]
    have he : ELV.affineInsert D Sc i v (s ++ [j]) r ≫
        (ELV.affineInsert D Sc i s x.oldTarget x.old.nf ▷ (pres D Sc).obj (ob D [j])) =
        ELV.affineInsert D Sc i v (x.oldTarget ++ [j])
          (r ≫ (x.old.nf ▷ (pres D Sc).obj (ob D [j]))) := by
      change ((pres D Sc).obj (ob D [i]) ◁ r) ≫
        (((pres D Sc).obj (ob D [i]) ◁ x.old.nf) ▷ (pres D Sc).obj (ob D [j])) =
        (pres D Sc).obj (ob D [i]) ◁ (r ≫ (x.old.nf ▷ (pres D Sc).obj (ob D [j])))
      erw [MonoidalSupercategory.whiskerLeft_comp (R := k)]
      congr 1
      have hh := MonoidalSupercategory.associator_naturality_middle k
        ((pres D Sc).obj (ob D [i])) x.old.nf ((pres D Sc).obj (ob D [j]))
      change (((pres D Sc).obj (ob D [i]) ◁ x.old.nf) ▷ (pres D Sc).obj (ob D [j])) ≫ 𝟙 _ =
        𝟙 _ ≫ ((pres D Sc).obj (ob D [i]) ◁ (x.old.nf ▷ (pres D Sc).obj (ob D [j]))) at hh
      simp only [Category.comp_id, Category.id_comp] at hh
      exact hh
    rw [he]
    exact old_comp_short D Sc _ _ (extended_prependTail_short D Sc x j)
  | zero =>
    erw [MonoidalSupercategory.zero_whiskerRight k, Limits.comp_zero]
    exact Submodule.zero_mem _
  | add f g _ _ hf hg =>
    erw [MonoidalSupercategory.add_whiskerRight (R := k), Preadditive.comp_add]
    exact Submodule.add_mem _ hf hg
  | smul a f _ hf =>
    erw [MonoidalSupercategory.smul_whiskerRight, Linear.comp_smul]
    exact Submodule.smul_mem _ a hf

/-- The scalar chronological generator is killed by every long PBW coordinate. -/
theorem chronological_scalar_long_zero {i j : I} {v s t : List I}
    (r : (pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D (s ++ [j])))
    (h : (pres D Sc).obj (ob D (i :: s)) ⟶ (pres D Sc).obj (ob D t))
    (x : PrependIdx i v (t ++ [j]))
    (hx : x.1.2.2.2 = longPrependShuffle v.length) :
    (prependBasis D Sc).repr
      (ELV.affineInsert D Sc i v (s ++ [j]) r ≫
        (h ▷ (pres D Sc).obj (ob D [j]))) x = 0 :=
  (mem_shortSpan_iff D Sc i v (t ++ [j]) _).mp
    (chronological_scalar_short D Sc r h) x hx

end OddMath.QuiverHecke.SmallerTailNormalization
end

end

section

/-!
# Full-ELV chronological short kernel

`chronologicalShortSpan_le_ker_outputLongExtraction` proves the short-to-kernel
containment for the actual finite extractor on `Target`. Homogeneous tensor
induction lifts smaller-tail scalar normalization with the full Koszul sign.
All exterior coefficients and arbitrary total balance parity are retained.
This supplies one inclusion in `DeformedMackeyBoundary.md` (2), not equality of
the kernel with the short span, a canonical splitting, or the boundary S formula.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped TensorProduct Classical
namespace OddMath.QuiverHecke.ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

private theorem chronological_induction {v w : List I}
    {P : hom D Sc cutoff v w → Prop} (x : hom D Sc cutoff v w) (zero : P 0)
    (tmul : ∀ (p q : ZMod 2) (a : (obj D Sc cutoff v).fst ⟶ (obj D Sc cutoff w).fst)
      (f : (pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w)),
      a ∈ parity (R := k) _ _ p → f ∈ parity (R := k) _ _ q → P (BoxProd.tmulHom a f))
    (add : ∀ x y, P x → P y → P (x + y)) : P x :=
  BoxProd.induction_on_homogeneous (P := P) x zero tmul add

/-- Every long affine coordinate vanishes on chronological short generators,
with unrestricted full ELV coefficients. -/
theorem chronological_long_zero {i j : I} {v s t : List I}
    (r : hom D Sc cutoff v (s ++ [j])) (h : hom D Sc cutoff (i :: s) t)
    (x : PrependIdx i v (t ++ [j]))
    (hx : x.1.2.2.2 = longPrependShuffle v.length) :
    prependAffineEquiv D Sc cutoff i v (t ++ [j])
      (insert D Sc cutoff i v (s ++ [j]) r ≫
        rightContext D Sc cutoff [j] (i :: s) t h) x = 0 := by
  induction r using chronological_induction D Sc cutoff with
  | zero => simp only [map_zero, Limits.zero_comp, Finsupp.zero_apply]
  | add r r' hr hr' =>
    simp only [map_add, Preadditive.add_comp, Finsupp.add_apply, hr, hr', add_zero]
  | tmul p q a f ha hf =>
    induction h using chronological_induction D Sc cutoff with
    | zero => simp only [map_zero, Limits.comp_zero, Finsupp.zero_apply]
    | add h h' hh hh' =>
      simp only [map_add, Preadditive.comp_add, Finsupp.add_apply, hh, hh', add_zero]
    | tmul r z b g hb hg =>
      have hi : affineRightContext D Sc [j] (i :: s) t g ∈ parity (R := k) _ _ z :=
        MonoidalSupercategory.whiskerRight_mem ((pres D Sc).obj (ob D [j])) hg
      change prependAffineEquiv D Sc cutoff i v (t ++ [j])
        (BoxProd.tmulHom (X := obj D Sc cutoff (i :: v))
          (Y := obj D Sc cutoff (i :: (s ++ [j]))) a (affineInsert D Sc i v (s ++ [j]) f) ≫
        BoxProd.tmulHom (X := obj D Sc cutoff (i :: (s ++ [j])))
          (Y := obj D Sc cutoff (t ++ [j])) b (affineRightContext D Sc [j] (i :: s) t g)) x = 0
      erw [BoxProd.tmulHom_comp_tmulHom
        (X := obj D Sc cutoff (i :: v)) (Y := obj D Sc cutoff (i :: (s ++ [j])))
        (Z := obj D Sc cutoff (t ++ [j])) ha _ b hi]
      rw [map_zsmul]
      change koszulSign p z • (prependAffineEquiv D Sc cutoff i v (t ++ [j])
        (_ ⊗ₜ[k] (affineInsert D Sc i v (s ++ [j]) f ≫
          (g ▷ (pres D Sc).obj (ob D [j])))) x) = 0
      erw [prependAffineEquiv_tmul]
      erw [SmallerTailNormalization.chronological_scalar_long_zero D Sc f g x hx]
      simp only [zero_smul]
      exact zsmul_zero _

/-- Total-parity-normalized extraction vanishes before taking the old quotient. -/
theorem chronological_prependExtractOld_zero (p : ZMod 2) {i j : I} {v s t : List I}
    (r : hom D Sc cutoff v (s ++ [j])) (h : hom D Sc cutoff (i :: s) t)
    (x : PrependIdx i v (t ++ [j]))
    (hx : x.1.2.2.2 = longPrependShuffle v.length) :
    prependExtractOld D Sc cutoff p x
      (insert D Sc cutoff i v (s ++ [j]) r ≫
        rightContext D Sc cutoff [j] (i :: s) t h) = 0 := by
  have he := prependExtractOld_congr_long D Sc cutoff p x hx
    (insert D Sc cutoff i v (s ++ [j]) r ≫
      rightContext D Sc cutoff [j] (i :: s) t h) 0 (by
        intro y hy
        rw [chronological_long_zero D Sc cutoff r h y hy, map_zero, Finsupp.zero_apply])
  simpa only [map_zero] using he

private theorem chronological_cast_zero (i : I) (v w t t' : List I) (e : t = t')
    (f : Target D Sc cutoff i v w →ₗ[k] Old D Sc cutoff v t)
    (z : Target D Sc cutoff i v w) (hz : f z = 0) :
    (Eq.mp (congrArg (fun t => Target D Sc cutoff i v w →ₗ[k]
      Old D Sc cutoff v t) e) f) z = 0 := by
  cases e
  exact hz

/-- The actual finite normalized long extraction kills each full-coefficient
chronological short generator. -/
theorem outputLongExtraction_chronological_generator (p : ZMod 2) (i : I)
    (v s : List I) (r : hom D Sc cutoff v (s ++ [i]))
    (h : hom D Sc cutoff (i :: s) v) :
    outputLongExtraction D Sc cutoff p i v
      (projection D Sc cutoff i v (v ++ [i])
        (insert D Sc cutoff i v (s ++ [i]) r ≫
          rightContext D Sc cutoff [i] (i :: s) v h)) = 0 := by
  ext m
  rw [outputLongExtraction_apply, Finsupp.zero_apply]
  unfold outputLongCoordinate
  apply chronological_cast_zero D Sc cutoff i v (v ++ [i]) _ v
    (longOutputIndex_oldTarget i v m)
  rw [LinearMap.smul_apply, prependOldCoordinate_projection]
  change _ • (ideal D Sc cutoff v (longOutputIndex i v m).oldTarget).mkQ
    (prependExtractOld D Sc cutoff p (longOutputIndex i v m) _) = 0
  rw [chronological_prependExtractOld_zero D Sc cutoff p r h
    (longOutputIndex i v m) rfl, map_zero, smul_zero]

/-- Unconditional containment in the kernel of the actual finite extraction map. -/
theorem chronologicalShortSpan_le_ker_outputLongExtraction (p : ZMod 2) (i : I)
    (v : List I) :
    chronologicalShortSpan D Sc cutoff i v v ≤
      LinearMap.ker (outputLongExtraction D Sc cutoff p i v) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨s, r, h, rfl⟩
  exact outputLongExtraction_chronological_generator D Sc cutoff p i v s r h

end OddMath.QuiverHecke.ELV
end

end

section

noncomputable section
open CategoryTheory StringDiagrams MonoidalCategory Categorification.TypeA
namespace OddMath.QuiverHecke.ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

 theorem positioned_short_mem (i : I) (v s t : List I) (gs : List PG)
    (hf : Fits (i :: s).length gs)
    (hc : SChain ((i :: s) ++ [i]) (pl ((i :: s) ++ [i]) gs) (t ++ [i]))
    (r : hom D Sc cutoff v (s ++ [i])) :
    projection D Sc cutoff i v (t ++ [i])
      (insert D Sc cutoff i v (s ++ [i]) r ≫
        affineUnit D Sc cutoff _ _ (cl D Sc _ _ gs hc)) ∈
      chronologicalShortSpan D Sc cutoff i v t := by
  have ht : tgt (i :: s) gs = t := by
    have he := tgt_eq hc
    rw [tgt_append_right [i] hf] at he
    exact List.append_cancel_right he
  have hsmall : SChain (i :: s) (pl (i :: s) gs) t := by
    simpa only [ht] using sChain_pl (i :: s) gs
  apply Submodule.subset_span
  refine ⟨s, r, affineUnit D Sc cutoff _ _ (cl D Sc _ _ gs hsmall), ?_⟩
  rw [rightContext_affineUnit]
  congr 3
  exact (cl_whiskerRight D Sc gs hsmall [i] hf)

theorem positioned_short_mem_of_eq (i : I) (v q s t : List I) (hs : q = s ++ [i])
    (gs : List PG) (hf : Fits (i :: s).length gs)
    (hc : SChain (i :: q) (pl (i :: q) gs) (t ++ [i]))
    (r : hom D Sc cutoff v q) :
    projection D Sc cutoff i v (t ++ [i])
      (insert D Sc cutoff i v q r ≫ affineUnit D Sc cutoff _ _ (cl D Sc _ _ gs hc)) ∈
        chronologicalShortSpan D Sc cutoff i v t := by
  subst q
  exact positioned_short_mem D Sc cutoff i v s t gs hf hc r

theorem prepend_short_mem (i : I) (v t : List I)
    (x : PrependIdx i v (t ++ [i]))
    (hx : x.1.2.2.2 ≠ longPrependShuffle v.length)
    (r : hom D Sc cutoff v x.oldTarget) :
    projection D Sc cutoff i v (t ++ [i])
      (insert D Sc cutoff i v x.oldTarget r ≫
        affineUnit D Sc cutoff _ _ (prependTail D Sc x)) ∈
      chronologicalShortSpan D Sc cutoff i v t := by
  have hv : 0 < v.length := by
    cases v with
    | nil =>
      apply False.elim
      apply hx
      apply Subtype.ext
      apply Equiv.ext
      intro z
      apply Fin.ext
      have h₁ := (x.1.2.2.2.1 z).isLt
      have h₂ := ((longPrependShuffle (([] : List I).length)).1 z).isLt
      simp only [List.length_nil] at h₁ h₂ ⊢
      omega
    | cons a v => simp
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hv)
  have hlen : x.oldTarget.length = n + 1 := by
    simp [PrependIdx.oldTarget, hn]
  obtain ⟨s, j, hs⟩ : ∃ s j, x.oldTarget = s ++ [j] := by
    generalize x.oldTarget = q at hlen ⊢
    induction q using List.reverseRecOn with
    | nil => simp at hlen
    | append_singleton q j ih => exact ⟨q, j, rfl⟩
  have hsl : s.length = n := by rw [hs] at hlen; simp only [List.length_append,
    List.length_singleton] at hlen; omega
  have hf : Fits (i :: s).length (cw (canWord (v.length + 1) x.1.2.2.2.1⁻¹)) := by
    apply fits_cw
    intro b hb
    have hb' : b < n := by
      have aux (m : ℕ) (u : PrependShuffle m) (hu : u ≠ longPrependShuffle m)
          (hm : m = n + 1) : ∀ b ∈ canWord (m + 1) u.1⁻¹, b < n := by
        subst m
        exact canWord_prependShort_lt n u hu
      exact aux v.length x.1.2.2.2 hx hn b hb
    simp only [List.length_cons, hsl]
    omega
  have he := x.moving_target
  rw [hs] at he
  change tgt ((i :: s) ++ [j]) _ = _ at he
  rw [tgt_append_right [j] hf] at he
  have hj : j = i := by
    have hh := congrArg List.getLast? he
    simpa using hh
  subst j
  have hfull : Fits (i :: s).length
      (((List.replicate x.1.1 0).map PG.dot) ++
        cw (canWord (v.length + 1) x.1.2.2.2.1⁻¹)) := by
    intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hg
      have hb0 := (List.mem_replicate.mp hb).2
      subst b
      simp [PG.pos, PG.width]
    · exact hf g hg
  unfold prependTail
  exact positioned_short_mem_of_eq D Sc cutoff i v x.oldTarget s t hs _ hfull _ r

end OddMath.QuiverHecke.ELV
end

end
