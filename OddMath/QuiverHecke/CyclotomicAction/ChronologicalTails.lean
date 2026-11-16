import OddMath.QuiverHecke.CyclotomicAction.EndpointPolynomials
import OddMath.QuiverHecke.CyclotomicAction.CyclotomicQuotientTop
import OddMath.QuiverHecke.CyclotomicAction.ContentModules
import OddMath.QuiverHecke.CyclotomicAction.PrependCoordinates
import OddMath.QuiverHecke.CyclotomicAction.LeadingMove
import OddMath.QuiverHecke.CyclotomicAction.AppendContent

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

/-! # Short columns into the old-only resolution

The balanced columns land in the original prepend and append quotients.
Their square uses the literal moving-word map, before the final cyclotomic quotient.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory TensorProduct
namespace OddMath.QuiverHecke.ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
namespace CyclotomicCrossingTensor

/-- The short source column in signed old-only coordinates. -/
def alphaPair (i : I) (v s t : List I) :
    hom D Sc cutoff (i :: s) t →ₗ[k] Old D Sc cutoff v (s ++ [i]) →ₗ[k]
      Target D Sc cutoff i v (t ++ [i]) where
  toFun h := pair D Sc cutoff (epsilon D cutoff i v) i (rightContext D Sc cutoff [i] _ _ h)
  map_add' h h' := by
    apply LinearMap.ext
    intro b
    obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v (s ++ [i])).mkQ_surjective b
    simp only [pair_mk, map_add, Preadditive.comp_add, LinearMap.add_apply]
  map_smul' a h := by
    apply LinearMap.ext
    intro b
    obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v (s ++ [i])).mkQ_surjective b
    simp only [pair_mk, map_smul, Linear.comp_smul, LinearMap.smul_apply, RingHom.id_apply]

@[simp] theorem alphaPair_mk (i : I) (v s t : List I)
    (h : hom D Sc cutoff (i :: s) t) (b : hom D Sc cutoff v (s ++ [i])) :
    alphaPair D Sc cutoff i v s t h ((ideal D Sc cutoff _ _).mkQ b) =
      projection D Sc cutoff i v (t ++ [i])
        (insert D Sc cutoff i _ _ (twist k (epsilon D cutoff i v) b) ≫
          rightContext D Sc cutoff [i] _ _ h) := rfl

theorem alphaPair_balance (i : I) (v s s' t : List I)
    (r : hom D Sc cutoff s s') (h : hom D Sc cutoff (i :: s') t)
    (b : Old D Sc cutoff v (s ++ [i])) :
    alphaPair D Sc cutoff i v s t (insert D Sc cutoff i s s' r ≫ h) b =
      alphaPair D Sc cutoff i v s' t h
        ((coefficient D Sc cutoff (epsilon D cutoff i v) i v).map
          ((ideal D Sc cutoff s s').mkQ r) b) := by
  obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v (s ++ [i])).mkQ_surjective b
  change projection D Sc cutoff i v (t ++ [i]) _ =
    projection D Sc cutoff i v (t ++ [i]) _
  simp only [LinearMap.comp_apply, Linear.rightComp_apply]
  rw [rightContext_comp, rightContext_insert, twist_comp, ← rightContext_twist,
    twist_twist, insert_comp, Category.assoc]

/-- The prescribed short source column into the original Mackey source. -/
def alpha (i : I) (v t : List I) : PprimeDomain D Sc cutoff i v t →ₗ[k]
    Target D Sc cutoff i v (t ++ [i]) :=
  BalancedInduction.lift (affinePrepend D Sc cutoff i)
    (quotient D Sc cutoff ⋙ coefficient D Sc cutoff (epsilon D cutoff i v) i v) ⟨t⟩
    (fun s => TensorProduct.lift (alphaPair D Sc cutoff i v s.word t))
    (fun s s' r h b => alphaPair_balance D Sc cutoff i v s.word s'.word t r h b)

@[simp] theorem alpha_tensor (i : I) (v s t : List I)
    (h : hom D Sc cutoff (i :: s) t) (b : Old D Sc cutoff v (s ++ [i])) :
    alpha D Sc cutoff i v t (pprimeTensor D Sc cutoff i v s t h b) =
      alphaPair D Sc cutoff i v s t h b := by
  exact BalancedInduction.lift_tensor (affinePrepend D Sc cutoff i)
    (quotient D Sc cutoff ⋙ coefficient D Sc cutoff (epsilon D cutoff i v) i v) ⟨t⟩ _ _ ⟨s⟩ h b

/-- The crossing column before imposing the enlarged cyclotomic ideal. -/
def shortCrossPair (i : I) (v s t : List I) :
    hom D Sc cutoff (s ++ [i]) t →ₗ[k] Old D Sc cutoff v (s ++ [i]) →ₗ[k]
      AppendTarget D Sc cutoff i v (t ++ [i]) where
  toFun c := appendPair D Sc cutoff 0 i
    (affineUnit D Sc cutoff _ _ (crossLast D Sc s i i) ≫ rightContext D Sc cutoff [i] _ _ c)
  map_add' c c' := by
    apply LinearMap.ext
    intro b
    obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v (s ++ [i])).mkQ_surjective b
    simp only [appendPair_mk, map_add, Preadditive.comp_add, LinearMap.add_apply]
  map_smul' a c := by
    apply LinearMap.ext
    intro b
    obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v (s ++ [i])).mkQ_surjective b
    simp only [appendPair_mk, map_smul, Linear.comp_smul, LinearMap.smul_apply, RingHom.id_apply]

@[simp] theorem shortCrossPair_mk (i : I) (v s t : List I)
    (c : hom D Sc cutoff (s ++ [i]) t) (b : hom D Sc cutoff v (s ++ [i])) :
    shortCrossPair D Sc cutoff i v s t c ((ideal D Sc cutoff _ _).mkQ b) =
      appendProjection D Sc cutoff i v (t ++ [i])
        (rightContext D Sc cutoff [i] _ _ b ≫
          affineUnit D Sc cutoff _ _ (crossLast D Sc s i i) ≫
          rightContext D Sc cutoff [i] _ _ c) := by
  change appendProjection D Sc cutoff i v (t ++ [i]) _ = _
  simp only [LinearMap.comp_apply, Linear.rightComp_apply, twist_zero]

theorem shortCrossPair_balance (i : I) (v s s' t : List I)
    (r : hom D Sc cutoff s s') (c : hom D Sc cutoff (s' ++ [i]) t)
    (b : Old D Sc cutoff v (s ++ [i])) :
    shortCrossPair D Sc cutoff i v s t (rightContext D Sc cutoff [i] _ _ r ≫ c) b =
      shortCrossPair D Sc cutoff i v s' t c
        ((coefficient D Sc cutoff (D.parity i) i v).map
          ((ideal D Sc cutoff s s').mkQ r) b) := by
  obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v (s ++ [i])).mkQ_surjective b
  change shortCrossPair D Sc cutoff i v s t _ ((ideal D Sc cutoff _ _).mkQ b) =
    shortCrossPair D Sc cutoff i v s' t _ ((ideal D Sc cutoff _ _).mkQ
      (b ≫ rightContext D Sc cutoff [i] _ _ (twist k (D.parity i) r)))
  rw [shortCrossPair_mk, shortCrossPair_mk]
  have hp : D.parity i * D.parity i = D.parity i := by
    rcases parity_eq_zero_or_one (D.parity i) with h | h <;> simp [h]
  have h := crossLast_comp_rightContext D Sc cutoff i i r
  rw [hp] at h
  simp only [rightContext_comp, Category.assoc]
  rw [← Category.assoc (affineUnit D Sc cutoff _ _ (crossLast D Sc s i i)), h]
  simp only [Category.assoc]

/-- The balanced short crossing column into the old-only append target. -/
def shortCross (i : I) (v t : List I) : ShortTarget D Sc cutoff i v t →ₗ[k]
    AppendTarget D Sc cutoff i v (t ++ [i]) :=
  BalancedInduction.lift (affineAppend D Sc cutoff i)
    (quotient D Sc cutoff ⋙ coefficient D Sc cutoff (D.parity i) i v) ⟨t⟩
    (fun s => TensorProduct.lift (shortCrossPair D Sc cutoff i v s.word t))
    (fun s s' r c b => shortCrossPair_balance D Sc cutoff i v s.word s'.word t r c b)

@[simp] theorem shortCross_tensor (i : I) (v s t : List I)
    (c : hom D Sc cutoff (s ++ [i]) t) (b : Old D Sc cutoff v (s ++ [i])) :
    shortCross D Sc cutoff i v t (shortTensor D Sc cutoff i v s t c b) =
      shortCrossPair D Sc cutoff i v s t c b := by
  exact BalancedInduction.lift_tensor (affineAppend D Sc cutoff i)
    (quotient D Sc cutoff ⋙ coefficient D Sc cutoff (D.parity i) i v) ⟨t⟩ _ _ ⟨s⟩ c b

/-- The short-column square with the original moving-word map. -/
theorem shortColumn_square (i : I) (v t : List I) :
    pMap D Sc cutoff i v (t ++ [i]) ∘ₗ alpha D Sc cutoff i v t =
      shortCross D Sc cutoff i v t ∘ₗ pprime D Sc cutoff i v t := by
  apply BalancedInduction.hom_ext
  intro s h b
  change pMap D Sc cutoff i v (t ++ [i])
    (alpha D Sc cutoff i v t (pprimeTensor D Sc cutoff i v s.word t h b)) =
    shortCross D Sc cutoff i v t
      (pprime D Sc cutoff i v t (pprimeTensor D Sc cutoff i v s.word t h b))
  rw [alpha_tensor, pprime_tensor, shortCross_tensor]
  obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v (s.word ++ [i])).mkQ_surjective b
  rw [alphaPair_mk, shortCrossPair_mk, pMap_chronologicalShort_generator]
  change appendProjection D Sc cutoff i v (t ++ [i])
    (rightContext D Sc cutoff [i] _ _
      (twist k (appendQ D cutoff i v) (twist k (appendQ D cutoff i v) b)) ≫ _) = _
  rw [twist_twist]

/-- The right square lands in the independently prescribed cyclotomic source. -/
theorem shortColumn_quotient_square (i : I) (v t : List I) :
    canonicalAppendTarget D Sc cutoff i v (t ++ [i]) ∘ₗ shortCross D Sc cutoff i v t =
      toCyclotomic D Sc cutoff i v t ∘ₗ q D Sc cutoff i v t := by
  apply BalancedInduction.hom_ext
  intro s c b
  change canonicalAppendTarget D Sc cutoff i v (t ++ [i])
    (shortCross D Sc cutoff i v t (shortTensor D Sc cutoff i v s.word t c b)) =
    toCyclotomic D Sc cutoff i v t
      (q D Sc cutoff i v t (shortTensor D Sc cutoff i v s.word t c b))
  obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v (s.word ++ [i])).mkQ_surjective b
  rw [shortCross_tensor, shortCrossPair_mk, canonicalAppendTarget_projection,
    toCyclotomic_q_shortTensor]

end CyclotomicCrossingTensor
end OddMath.QuiverHecke.ELV
end

end

section

/-! # Full-coefficient extraction for the short source column

`extract_comp_alpha` constructs the left inverse on every prescribed
balanced class. Its downstream consequences are `alpha_injective` and
`pprime_injective`, the latter using the actual short-column square.

The complete old PBW coefficient is transferred through epsilon balance.
The coefficient involution across the moving tail and the total-Hom epsilon
involution are separate. The decoder takes values in `PprimeDomain`, not in
an image span. All old quotient coefficients and all source words are retained.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory TensorProduct
open scoped Classical
namespace OddMath.QuiverHecke.PrependShuffle
open Categorification.TypeA Equiv

private theorem blockPerm_castSucc {n : ℕ} (u : Perm (Fin (n + 1))) (x : Fin (n + 1)) :
    blockPerm rfl u (1 : Perm (Fin 1)) x.castSucc = (u x).castSucc := by
  exact blockPerm_inl rfl u 1 x

private theorem blockPerm_last {n : ℕ} (u : Perm (Fin (n + 1))) :
    blockPerm rfl u (1 : Perm (Fin 1)) (Fin.last (n + 1)) = Fin.last (n + 1) := by
  exact blockPerm_inr rfl u 1 0

/-- Extend a prepend shuffle by a final fixed strand. -/
def extend {n : ℕ} (u : PrependShuffle n) : PrependShuffle (n + 1) :=
  ⟨blockPerm rfl u.1 (1 : Perm (Fin 1)), by
    refine ⟨fun a b hab => False.elim (by simp [Subsingleton.elim a b] at hab), ?_⟩
    intro a b hab
    have he (z : Fin (n + 1)) :
        blockEquiv (Nat.add_comm 1 (n + 1)) (Sum.inr z) = z.succ := by
      apply Fin.ext
      simp [Nat.add_comm]
    dsimp only
    rw [he, he, blockPerm_inv, inv_one]
    revert hab
    refine Fin.lastCases ?_ (fun b => ?_) b
    · refine Fin.lastCases ?_ (fun a => ?_) a
      · intro hab; exact False.elim (lt_irrefl _ hab)
      · intro _
        rw [← Fin.castSucc_succ, Fin.succ_last, blockPerm_castSucc, blockPerm_last]
        exact Fin.castSucc_lt_last _
    · refine Fin.lastCases ?_ (fun a => ?_) a
      · intro hab; exact False.elim (not_lt_of_ge (Fin.le_last _) hab)
      · intro hab
        rw [← Fin.castSucc_succ, ← Fin.castSucc_succ, blockPerm_castSucc, blockPerm_castSucc]
        have he' (z : Fin n) : blockEquiv (Nat.add_comm 1 n) (Sum.inr z) = z.succ := by
          apply Fin.ext
          simp [Nat.add_comm]
        simpa only [he', Fin.castSucc_lt_castSucc_iff] using
          u.2.2 (show a < b from hab)⟩

/-- Adding a fixed final strand preserves the canonical inverse word literally. -/
theorem canWord_extend {n : ℕ} (u : PrependShuffle n) :
    canWord (n + 2) (extend u).1⁻¹ = canWord (n + 1) u.1⁻¹ := by
  have hw := wordProd_eq_blockPerm_left (show (n + 1) + 1 = n + 2 from rfl)
    (validWord_canWord (n + 1) u.1⁻¹)
  rw [wordProd_canWord] at hw
  change canWord (n + 2)
    (blockPerm (show (n + 1) + 1 = n + 2 from rfl) u.1 (1 : Perm (Fin 1)))⁻¹ = _
  rw [blockPerm_inv, inv_one, ← hw]
  have hc : IsCode ((n + 1) :: code (n + 1) u.1⁻¹) := by
    exact ⟨by rw [length_code]; omega, isCode_code _ _⟩
  have hp : codeWord ((n + 1) :: code (n + 1) u.1⁻¹) = canWord (n + 1) u.1⁻¹ := by
    simp [codeWord_cons, length_code, canWord]
  rw [← hp]
  exact canWord_wordProd_codeWord hc (by simp [length_code])

/-- Transport a shuffle only along an equality of the old heights. -/
def cast {n m : ℕ} (e : n = m) (u : PrependShuffle n) : PrependShuffle m := e ▸ u

theorem canWord_cast {n m : ℕ} (e : n = m) (u : PrependShuffle n) :
    canWord (m + 1) (cast e u).1⁻¹ = canWord (n + 1) u.1⁻¹ := by
  subst m
  rfl

end OddMath.QuiverHecke.PrependShuffle

namespace OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The lower balance on the prescribed source, for a full affine morphism. -/
theorem pprimeTensor_balance (i : I) (v s s' t : List I)
    (r : hom D Sc cutoff s s') (h : hom D Sc cutoff (i :: s') t)
    (b : Old D Sc cutoff v (s ++ [i])) :
    pprimeTensor D Sc cutoff i v s t (insert D Sc cutoff i s s' r ≫ h) b =
      pprimeTensor D Sc cutoff i v s' t h
        ((coefficient D Sc cutoff (epsilon D cutoff i v) i v).map
          ((ideal D Sc cutoff s s').mkQ r) b) :=
  BalancedInduction.balance (affinePrepend D Sc cutoff i)
    (quotient D Sc cutoff ⋙ coefficient D Sc cutoff (epsilon D cutoff i v) i v)
    (v := ⟨s⟩) (v' := ⟨s'⟩) r h b

/-- Normalized old PBW coefficient before its action on the coefficient module. -/
def alphaOldFactor {i : I} {s t : List I} (x : PrependIdx i s t) :
    SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff →ₗ[k]
      hom D Sc cutoff s x.oldTarget :=
  ((TensorProduct.mk k _ _).flip x.old.nf).comp
    (coefficientTwist D cutoff (prependTailParity D x))

/-- One full-coefficient normalized term in the prescribed balanced source. -/
def alphaNormalizedTerm (i : I) (v s t : List I) (x : PrependIdx i s t)
    (b : Old D Sc cutoff v (s ++ [i])) :
    SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff →ₗ[k]
      PprimeDomain D Sc cutoff i v t :=
  (BalancedInduction.inclusion (affinePrepend D Sc cutoff i)
      (quotient D Sc cutoff ⋙ coefficient D Sc cutoff (epsilon D cutoff i v) i v)
      ⟨t⟩ ⟨x.oldTarget⟩) ∘ₗ
    (TensorProduct.mk k _ _ (affineUnit D Sc cutoff _ _ (prependTail D Sc x))) ∘ₗ
      ((oldComp D Sc cutoff v (s ++ [i]) (x.oldTarget ++ [i])) b) ∘ₗ
        (ideal D Sc cutoff (s ++ [i]) (x.oldTarget ++ [i])).mkQ ∘ₗ
          rightContext D Sc cutoff [i] s x.oldTarget ∘ₗ
            twist k (epsilon D cutoff i v) ∘ₗ alphaOldFactor D Sc cutoff x

/-- Transfer of every exterior coefficient through epsilon balance.
No homogeneity or evenness of the coefficient is required. -/
theorem alphaNormalizedTerm_eq (i : I) (v s t : List I) (x : PrependIdx i s t)
    (b : Old D Sc cutoff v (s ++ [i]))
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    alphaNormalizedTerm D Sc cutoff i v s t x b a =
      pprimeTensor D Sc cutoff i v s t (a ⊗ₜ[k] prependElt D Sc x) b := by
  rw [← prepend_insert_twisted_coefficient D Sc cutoff x a,
    pprimeTensor_balance]
  rfl

/-- Finite normalization of an affine first factor, retaining its old coefficient action. -/
def alphaNormalize (i : I) (v s t : List I)
    (b : Old D Sc cutoff v (s ++ [i])) :
    hom D Sc cutoff (i :: s) t →ₗ[k] PprimeDomain D Sc cutoff i v t :=
  (Finsupp.lsum k (alphaNormalizedTerm D Sc cutoff i v s t · b)) ∘ₗ
    (prependAffineEquiv D Sc cutoff i s t).toLinearMap

/-- Literal word of a bare moving tail, including all moving dots. -/
def alphaTailWord {i : I} {v w : List I} (x : PrependIdx i v w) : List PG :=
  (List.replicate x.1.1 0).map PG.dot ++
    cw (Categorification.TypeA.canWord (v.length + 1) x.1.2.2.2.1⁻¹)

/-- A tail can be stripped when its literal word avoids the final strand. -/
def AlphaStrippable {i : I} {v t : List I} (x : PrependIdx i v (t ++ [i])) : Prop :=
  ∃ s : List I, x.oldTarget = s ++ [i] ∧ Fits (i :: s).length (alphaTailWord x)

private theorem alphaStripChain {i : I} {v t : List I}
    (x : PrependIdx i v (t ++ [i])) (s : List I)
    (hs : x.oldTarget = s ++ [i]) (hf : Fits (i :: s).length (alphaTailWord x)) :
    SChain (i :: s) (pl (i :: s) (alphaTailWord x)) t := by
  have ht : tgt (i :: x.oldTarget) (alphaTailWord x) = t ++ [i] := by
    simpa only [alphaTailWord, tgt_append, tgt_map_dot] using x.moving_target
  rw [hs] at ht
  change tgt ((i :: s) ++ [i]) (alphaTailWord x) = _ at ht
  rw [tgt_append_right [i] hf] at ht
  simpa only [List.append_cancel_right ht] using sChain_pl (i :: s) (alphaTailWord x)

/-- A literal short word gives a map from the actual old quotient to the prescribed coend. -/
def alphaWordLift (i : I) (v q s t : List I) (hs : q = s ++ [i])
    (gs : List PG) (hc : SChain (i :: s) (pl (i :: s) gs) t) :
    Old D Sc cutoff v q →ₗ[k] PprimeDomain D Sc cutoff i v t := by
  subst q
  exact (BalancedInduction.inclusion (affinePrepend D Sc cutoff i)
    (quotient D Sc cutoff ⋙ coefficient D Sc cutoff (epsilon D cutoff i v) i v)
    ⟨t⟩ ⟨s⟩) ∘ₗ
      TensorProduct.mk k _ _ (affineUnit D Sc cutoff _ _ (cl D Sc _ _ gs hc))

/-- Decode one old quotient coordinate, with zero on tails meeting the final strand. -/
def alphaStripTerm (i : I) (v t : List I) (x : PrependIdx i v (t ++ [i])) :
    Old D Sc cutoff v x.oldTarget →ₗ[k] PprimeDomain D Sc cutoff i v t :=
  if hx : AlphaStrippable x then
    alphaWordLift D Sc cutoff i v x.oldTarget hx.choose t hx.choose_spec.1
      (alphaTailWord x) (alphaStripChain x hx.choose hx.choose_spec.1 hx.choose_spec.2)
  else 0

/-- Stripping is independent of the witness of the shorter source word. -/
theorem alphaStripTerm_eq (i : I) (v t : List I) (x : PrependIdx i v (t ++ [i]))
    (s : List I) (hs : x.oldTarget = s ++ [i])
    (hf : Fits (i :: s).length (alphaTailWord x)) :
    alphaStripTerm D Sc cutoff i v t x =
      alphaWordLift D Sc cutoff i v x.oldTarget s t hs (alphaTailWord x)
        (alphaStripChain x s hs hf) := by
  have hx : AlphaStrippable x := ⟨s, hs, hf⟩
  rw [alphaStripTerm, dite_eq_left hx]
  have he : hx.choose = s := List.append_cancel_right (hx.choose_spec.1.symm.trans hs)
  subst s
  rfl

/-- Changing the old PBW representative of a fixed moving tail does not
change the decoded balanced class. -/
theorem alphaStripTerm_tailKey (i : I) (v t : List I)
    (x y : PrependIdx i v (t ++ [i])) (hk : x.tailKey = y.tailKey)
    (b : Old D Sc cutoff v x.oldTarget) :
    alphaStripTerm D Sc cutoff i v t x b =
      alphaStripTerm D Sc cutoff i v t y (x.oldTarget_eq_of_tailKey_eq y hk ▸ b) := by
  have ht := x.oldTarget_eq_of_tailKey_eq y hk
  have hw : alphaTailWord x = alphaTailWord y := by
    have hm := congrArg Prod.fst hk
    have hu := congrArg Prod.snd hk
    simp only [PrependIdx.tailKey] at hm hu
    simp only [alphaTailWord, hm, hu]
  have hh : AlphaStrippable x ↔ AlphaStrippable y := by
    constructor
    · rintro ⟨s, hs, hf⟩
      exact ⟨s, ht.symm.trans hs, hw ▸ hf⟩
    · rintro ⟨s, hs, hf⟩
      exact ⟨s, ht.trans hs, hw.symm ▸ hf⟩
  by_cases hx : AlphaStrippable x
  · obtain ⟨s, hs, hf⟩ := hx
    rw [alphaStripTerm_eq D Sc cutoff i v t x s hs hf,
      alphaStripTerm_eq D Sc cutoff i v t y s (ht.symm.trans hs) (hw ▸ hf)]
    have aux {q q' : List I} (e : q = q') (hs : q = s ++ [i])
        (hs' : q' = s ++ [i]) (gs gs' : List PG) (hgs : gs = gs')
        (hc : SChain (i :: s) (pl (i :: s) gs) t)
        (hc' : SChain (i :: s) (pl (i :: s) gs') t) (c : Old D Sc cutoff v q) :
        alphaWordLift D Sc cutoff i v q s t hs gs hc c =
          alphaWordLift D Sc cutoff i v q' s t hs' gs' hc' (e ▸ c) := by
      subst q'; subst gs'; rfl
    exact aux ht hs (ht.symm.trans hs) _ _ hw _ _ b
  · rw [alphaStripTerm, dite_eq_right hx, alphaStripTerm,
      dite_eq_right (fun hy => hx (hh.mpr hy))]
    rfl

private theorem alphaWordLift_column (i : I) (v q s t : List I) (hs : q = s ++ [i])
    (gs : List PG) (hc : SChain (i :: s) (pl (i :: s) gs) t)
    (hf : Fits (i :: s).length gs)
    (hc' : SChain (i :: q) (pl (i :: q) gs) (t ++ [i])) (b : Old D Sc cutoff v q) :
    alpha D Sc cutoff i v t (alphaWordLift D Sc cutoff i v q s t hs gs hc b) =
      pair D Sc cutoff (epsilon D cutoff i v) i
        (affineUnit D Sc cutoff _ _ (cl D Sc _ _ gs hc')) b := by
  subst q
  change alpha D Sc cutoff i v t
    (pprimeTensor D Sc cutoff i v s t (affineUnit D Sc cutoff _ _ (cl D Sc _ _ gs hc)) b) = _
  rw [alpha_tensor]
  change pair D Sc cutoff (epsilon D cutoff i v) i
    (rightContext D Sc cutoff [i] _ _ (affineUnit D Sc cutoff _ _ (cl D Sc _ _ gs hc))) b = _
  rw [rightContext_affineUnit]
  congr 2
  exact congrArg (affineUnit D Sc cutoff _ _) (cl_whiskerRight D Sc gs hc [i] hf)

/-- Applying the actual column after stripping a short coordinate recovers that coordinate. -/
theorem alpha_stripTerm (i : I) (v t : List I) (x : PrependIdx i v (t ++ [i]))
    (hx : AlphaStrippable x) (b : Old D Sc cutoff v x.oldTarget) :
    alpha D Sc cutoff i v t (alphaStripTerm D Sc cutoff i v t x b) =
      pair D Sc cutoff (epsilon D cutoff i v) i
        (affineUnit D Sc cutoff _ _ (prependTail D Sc x)) b := by
  obtain ⟨s, hs, hf⟩ := hx
  rw [alphaStripTerm_eq D Sc cutoff i v t x s hs hf]
  exact alphaWordLift_column D Sc cutoff i v x.oldTarget s t hs (alphaTailWord x)
    (alphaStripChain x s hs hf) hf _ b

/-- The actual coordinate decoder into the independently prescribed balanced source.
Its definition uses old quotient coordinates, so old-ideal descent is intrinsic.
The left-inverse identity is a separate assertion. -/
def extract (i : I) (v t : List I) :
    Target D Sc cutoff i v (t ++ [i]) →ₗ[k] PprimeDomain D Sc cutoff i v t :=
  (DirectSum.toModule k _ _ fun q : PrependIdx.Tail i v (t ++ [i]) =>
    alphaStripTerm D Sc cutoff i v t q.representative) ∘ₗ
      (prependOldCoordinateEquiv D Sc cutoff (epsilon D cutoff i v) i v
        (t ++ [i])).toLinearMap

/-- The decoder on a canonical coordinate uses its full old quotient coefficient. -/
theorem extract_reconstruct_of (i : I) (v t : List I)
    (q : PrependIdx.Tail i v (t ++ [i]))
    (b : Old D Sc cutoff v q.representative.oldTarget) :
    extract D Sc cutoff i v t
      (prependOldReconstruct D Sc cutoff (epsilon D cutoff i v) i v (t ++ [i])
        (DirectSum.lof k _ _ q b)) = alphaStripTerm D Sc cutoff i v t q.representative b := by
  simp only [extract, LinearMap.comp_apply, LinearEquiv.coe_coe,
    prependOldCoordinateEquiv_reconstruct, DirectSum.toModule_lof]

/-- Extraction is independent of the old normal-form representative of a tail. -/
theorem extract_pair_tail (i : I) (v t : List I) (x : PrependIdx i v (t ++ [i]))
    (b : Old D Sc cutoff v x.oldTarget) :
    extract D Sc cutoff i v t
      (pair D Sc cutoff (epsilon D cutoff i v) i
        (affineUnit D Sc cutoff _ _ (prependTail D Sc x)) b) =
      alphaStripTerm D Sc cutoff i v t x b := by
  let q : PrependIdx.Tail i v (t ++ [i]) := ⟨x.tailKey, x, rfl⟩
  have hk : x.tailKey = q.representative.tailKey := q.representative_tailKey.symm
  have ht := x.oldTarget_eq_of_tailKey_eq q.representative hk
  have aux {s s' : List I} (e : s = s')
      (h : (pres D Sc).obj (ob D (i :: s)) ⟶ (pres D Sc).obj (ob D (t ++ [i])))
      (h' : (pres D Sc).obj (ob D (i :: s')) ⟶ (pres D Sc).obj (ob D (t ++ [i])))
      (hh : HEq h h') (c : Old D Sc cutoff v s) :
      pair D Sc cutoff (epsilon D cutoff i v) i (affineUnit D Sc cutoff _ _ h) c =
        pair D Sc cutoff (epsilon D cutoff i v) i (affineUnit D Sc cutoff _ _ h') (e ▸ c) := by
    subst s'; cases hh; rfl
  rw [aux ht _ _ (prependTail_heq_of_tailKey_eq D Sc x q.representative hk) b]
  have hu : affineUnit D Sc cutoff _ _ (prependTail D Sc q.representative) =
      ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
        prependTail D Sc q.representative) := rfl
  rw [hu, alphaStripTerm_tailKey D Sc cutoff i v t x q.representative hk]
  simpa only [prependOldReconstruct, DirectSum.toModule_lof] using
    extract_reconstruct_of D Sc cutoff i v t q (ht ▸ b)

/-- The bare moving word fits its smaller source. -/
theorem alphaTailWord_fits {i : I} {s t : List I} (x : PrependIdx i s t) :
    Fits (i :: x.oldTarget).length (alphaTailWord x) := by
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
    have ha0 := (List.mem_replicate.mp ha).2
    subst a
    simp [PG.pos, PG.width]
  · apply fits_cw _ g hg
    simpa [PrependIdx.oldTarget] using
      Categorification.TypeA.validWord_canWord (s.length + 1) x.1.2.2.2.1⁻¹

private theorem alphaExtendedHeight {i : I} {v s t : List I}
    (x : PrependIdx i s t) (y : NFIdx v (x.oldTarget ++ [i])) : s.length + 1 = v.length := by
  have he := congrArg List.length y.tgt_cw
  simpa [PrependIdx.oldTarget] using he.symm

/-- Extend the smaller moving tail and retain an arbitrary old source normal form. -/
def alphaExtendedIndex {i : I} {v s t : List I} (x : PrependIdx i s t)
    (y : NFIdx v (x.oldTarget ++ [i])) : PrependIdx i v (t ++ [i]) :=
  ⟨(x.1.1, y.1.1, y.1.2,
    PrependShuffle.cast (alphaExtendedHeight x y) (PrependShuffle.extend x.1.2.2.2)),
    y.2.1, y.2.2.1, by
      have he := tgt_shift [i] v (cw (Categorification.TypeA.canWord v.length y.1.2))
      simp only [List.length_singleton, cw_map_shift, List.singleton_append] at he
      simp only [prependCrossingWord, cw_append, tgt_append, he, y.tgt_cw,
        PrependShuffle.canWord_cast, PrependShuffle.canWord_extend]
      change tgt ((i :: x.oldTarget) ++ [i]) _ = _
      rw [tgt_append_right [i]]
      · rw [x.moving_target]
      · simpa [PrependIdx.oldTarget] using
          fits_cw (Categorification.TypeA.validWord_canWord (s.length + 1) x.1.2.2.2.1⁻¹)⟩

@[simp] theorem alphaExtendedIndex_target {i : I} {v s t : List I}
    (x : PrependIdx i s t) (y : NFIdx v (x.oldTarget ++ [i])) :
    (alphaExtendedIndex x y).oldTarget = x.oldTarget ++ [i] := y.tgt_cw

@[simp] theorem alphaExtendedIndex_word {i : I} {v s t : List I}
    (x : PrependIdx i s t) (y : NFIdx v (x.oldTarget ++ [i])) :
    alphaTailWord (alphaExtendedIndex x y) = alphaTailWord x := by
  simp only [alphaTailWord, alphaExtendedIndex,
    PrependShuffle.canWord_cast, PrependShuffle.canWord_extend]

/-- Every extended smaller tail satisfies the literal stripping condition. -/
theorem alphaExtendedIndex_strippable {i : I} {v s t : List I}
    (x : PrependIdx i s t) (y : NFIdx v (x.oldTarget ++ [i])) :
    AlphaStrippable (alphaExtendedIndex x y) := by
  refine ⟨x.oldTarget, alphaExtendedIndex_target x y, ?_⟩
  rw [alphaExtendedIndex_word]
  exact alphaTailWord_fits x

/-- Stripping an extended tail returns the smaller bare tail in the actual coend. -/
theorem alphaStripTerm_extended (i : I) (v s t : List I) (x : PrependIdx i s t)
    (y : NFIdx v (x.oldTarget ++ [i])) (b : Old D Sc cutoff v (x.oldTarget ++ [i])) :
    alphaStripTerm D Sc cutoff i v t (alphaExtendedIndex x y)
      ((alphaExtendedIndex_target x y).symm ▸ b) =
        pprimeTensor D Sc cutoff i v x.oldTarget t
          (affineUnit D Sc cutoff _ _ (prependTail D Sc x)) b := by
  have hf : Fits (i :: x.oldTarget).length (alphaTailWord (alphaExtendedIndex x y)) := by
    rw [alphaExtendedIndex_word]
    exact alphaTailWord_fits x
  rw [alphaStripTerm_eq D Sc cutoff i v t (alphaExtendedIndex x y) x.oldTarget
    (alphaExtendedIndex_target x y) hf]
  have aux {q : List I} (hs : q = x.oldTarget ++ [i]) (gs : List PG)
      (hgs : gs = alphaTailWord x)
      (hc : SChain (i :: x.oldTarget) (pl (i :: x.oldTarget) gs) t) :
      alphaWordLift D Sc cutoff i v q x.oldTarget t hs gs hc (hs.symm ▸ b) =
        pprimeTensor D Sc cutoff i v x.oldTarget t
          (affineUnit D Sc cutoff _ _ (prependTail D Sc x)) b := by
    subst q; subst gs; rfl
  exact aux _ _ (alphaExtendedIndex_word x y) _

/-- The decoder recovers every smaller bare tail, for every coefficient source
and every full old quotient coefficient, including empty Hom corners. -/
theorem extract_alpha_tail (i : I) (v s t : List I) (x : PrependIdx i s t)
    (b : Old D Sc cutoff v (x.oldTarget ++ [i])) :
    extract D Sc cutoff i v t (alpha D Sc cutoff i v t
      (pprimeTensor D Sc cutoff i v x.oldTarget t
        (affineUnit D Sc cutoff _ _ (prependTail D Sc x)) b)) =
      pprimeTensor D Sc cutoff i v x.oldTarget t
        (affineUnit D Sc cutoff _ _ (prependTail D Sc x)) b := by
  by_cases hy : Nonempty (NFIdx v (x.oldTarget ++ [i]))
  · obtain ⟨y⟩ := hy
    rw [← alphaStripTerm_extended D Sc cutoff i v s t x y b,
      alpha_stripTerm D Sc cutoff i v t (alphaExtendedIndex x y)
        (alphaExtendedIndex_strippable x y), extract_pair_tail]
  · have hb : b = 0 := by
      obtain ⟨r, rfl⟩ := (ideal D Sc cutoff v (x.oldTarget ++ [i])).mkQ_surjective b
      have hr : r = 0 := by
        apply (oldAffineEquiv D Sc cutoff v (x.oldTarget ++ [i])).injective
        apply Finsupp.ext
        intro y
        exact (hy ⟨y⟩).elim
      rw [hr, map_zero]
    rw [hb]
    simp only [pprimeTensor, BalancedInduction.tensor, tmul_zero, map_zero]

/-- The full coefficient transfer is used by extraction, not merely in the image. -/
theorem extract_alpha_normalizedTerm (i : I) (v s t : List I)
    (x : PrependIdx i s t) (b : Old D Sc cutoff v (s ++ [i]))
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    extract D Sc cutoff i v t
      (alpha D Sc cutoff i v t (alphaNormalizedTerm D Sc cutoff i v s t x b a)) =
        alphaNormalizedTerm D Sc cutoff i v s t x b a := by
  change extract D Sc cutoff i v t (alpha D Sc cutoff i v t
    (pprimeTensor D Sc cutoff i v x.oldTarget t
      (affineUnit D Sc cutoff _ _ (prependTail D Sc x)) _)) = _
  exact extract_alpha_tail D Sc cutoff i v s t x _

/-- Extraction recovers every prescribed pure balanced class. -/
theorem extract_alpha_tensor (i : I) (v s t : List I)
    (h : hom D Sc cutoff (i :: s) t) (b : Old D Sc cutoff v (s ++ [i])) :
    extract D Sc cutoff i v t (alpha D Sc cutoff i v t
      (pprimeTensor D Sc cutoff i v s t h b)) = pprimeTensor D Sc cutoff i v s t h b := by
  obtain ⟨f, rfl⟩ := (prependAffineEquiv D Sc cutoff i s t).symm.surjective h
  induction f using Finsupp.induction_linear with
  | zero => simp [pprimeTensor, BalancedInduction.tensor]
  | add f g hf hg =>
    have hadd (h h' : hom D Sc cutoff (i :: s) t) :
        pprimeTensor D Sc cutoff i v s t (h + h') b =
          pprimeTensor D Sc cutoff i v s t h b + pprimeTensor D Sc cutoff i v s t h' b := by
      simp only [pprimeTensor, BalancedInduction.tensor, add_tmul, map_add]
    simp only [map_add, hadd, hf, hg]
  | single x a =>
    rw [prependAffineEquiv_symm_single, ← alphaNormalizedTerm_eq]
    exact extract_alpha_normalizedTerm D Sc cutoff i v s t x b a

/-- The full-coefficient decoder is a left inverse on every balanced class. -/
theorem extract_comp_alpha (i : I) (v t : List I) :
    extract D Sc cutoff i v t ∘ₗ alpha D Sc cutoff i v t = LinearMap.id := by
  apply BalancedInduction.hom_ext
  intro s h b
  exact extract_alpha_tensor D Sc cutoff i v s.word t h b

@[simp] theorem extract_alpha (i : I) (v t : List I)
    (z : PprimeDomain D Sc cutoff i v t) :
    extract D Sc cutoff i v t (alpha D Sc cutoff i v t z) = z :=
  LinearMap.congr_fun (extract_comp_alpha D Sc cutoff i v t) z

end OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
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

section

/-! # Balanced crossing-column coordinates

`decode_comp_shortCross` proves a left inverse on every balanced class.
`range_shortCross` and `crossingEquiv` identify that independently prescribed
source with the original append crossing span. These are the crossing-column
prerequisites for the short-column diagram in `DeformedCyclotomicTopRow.md`.

The decoder takes values in the prescribed balanced short source. On a
nonidentity append tail it retains the crossing term of the triangular
crossing/dot identity, including its self-crossing sign. The polynomial
correction is killed only after its separate vanishing law is proved.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped Classical DirectSum TensorProduct
namespace OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
namespace ShortCrossCoordinates
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Insert a shorter crossing word with its unchanged old quotient coefficient. -/
def wordLift (i : I) (v q s t : List I) (hs : q = s ++ [i])
    (L : List PG) (m : ℕ) (ht : SChain (s ++ [i]) (pl (s ++ [i]) L) t) :
    Old D Sc cutoff v q →ₗ[k] ShortTarget D Sc cutoff i v t := by
  subst q
  exact (BalancedInduction.inclusion (affineAppend D Sc cutoff i)
    (quotient D Sc cutoff ⋙ coefficient D Sc cutoff (D.parity i) i v) ⟨t⟩ ⟨s⟩) ∘ₗ
      TensorProduct.mk k _ _ (appendMovingPower D Sc cutoff i s m ≫
        affineUnit D Sc cutoff _ _ (cl D Sc _ _ L ht))

/-- Decode the crossing part of a normalized append tail. -/
def data (i : I) (v q t : List I) (L : List PG) (m : ℕ) :
    Old D Sc cutoff v q →ₗ[k] ShortTarget D Sc cutoff i v t := by
  by_cases hL : L = []
  · exact 0
  · by_cases hs : q = q.dropLast ++ [i]
    · by_cases ht : SChain (q.dropLast ++ [i]) (pl (q.dropLast ++ [i]) L.tail) t
      · exact SKM.zsign k (D.parity i * D.parity i) ^ m •
          wordLift D Sc cutoff i v q q.dropLast t hs L.tail m ht
      · exact 0
    · exact 0

/-- Full old quotient coordinates are decoded without choosing representatives in the ideal. -/
def decode (i : I) (v t : List I) :
    AppendTarget D Sc cutoff i v (t ++ [i]) →ₗ[k] ShortTarget D Sc cutoff i v t :=
  (DirectSum.toModule k _ _ fun q : AppendIdx.Tail i v (t ++ [i]) =>
    data D Sc cutoff i v q.representative.oldTarget t
      (cw (Categorification.TypeA.canWord (v ++ [i]).length
        q.representative.1.2.2.2.1⁻¹)) q.representative.1.1) ∘ₗ
      (appendOldCoordinateEquiv D Sc cutoff 0 i v (t ++ [i])).toLinearMap

@[simp] theorem data_nil (i : I) (v q t : List I) (m : ℕ) :
    data D Sc cutoff i v q t [] m = 0 := by
  simp [data]

private theorem appendTailPair_transport {i : I} {v s s' w : List I}
    (e : s = s') (r : hom D Sc cutoff v s)
    (a : (pres D Sc).obj (ob D (s ++ [i])) ⟶ (pres D Sc).obj (ob D w))
    (b : (pres D Sc).obj (ob D (s' ++ [i])) ⟶ (pres D Sc).obj (ob D w))
    (hab : HEq a b) :
    appendPair D Sc cutoff 0 i (affineUnit D Sc cutoff _ _ a)
      ((ideal D Sc cutoff v s).mkQ r) =
    appendPair D Sc cutoff 0 i (affineUnit D Sc cutoff _ _ b)
      ((ideal D Sc cutoff v s').mkQ (e ▸ r)) := by
  subst s'
  cases hab
  rfl

private def appendIdentityShuffle (i : I) (v : List I) : AppendShuffle (appendLen v i) :=
  AppendShuffle.cast rfl (appendLen v i) (appendRun v.length (Fin.last v.length))

private theorem appendIdentityShuffle_word (i : I) (v : List I) :
    Categorification.TypeA.canWord (v ++ [i]).length (appendIdentityShuffle i v).1⁻¹ = [] := by
  rw [appendIdentityShuffle, AppendShuffle.canWord_cast, canWord_appendRun]
  simp

private def appendIdentityIndex (i : I) {v t : List I} (y : NFIdx v t) (m : ℕ) :
    AppendIdx i v (t ++ [i]) :=
  ⟨(m, y.1.1, y.1.2, appendIdentityShuffle i v), y.2.1, y.2.2.1, by
    have he := tgt_append_right [i] (t := v)
      (fits_cw (Categorification.TypeA.validWord_canWord v.length y.1.2))
    simpa only [appendCrossingWord, appendIdentityShuffle_word, List.append_nil,
      cw_append, tgt_append, cw, List.reverse_nil, List.map_nil,
      List.nil_append] using he.trans (congrArg (· ++ [i]) y.tgt_cw)⟩

private theorem appendIdentityIndex_target (i : I) {v t : List I} (y : NFIdx v t) (m : ℕ) :
    (appendIdentityIndex i y m).oldTarget = t := y.tgt_cw

private theorem append_cl_heq {s s' t t' : List I} {L L' : List PG}
    (hs : s = s') (ht : t = t') (hL : L = L')
    (h : SChain s (pl s L) t) (h' : SChain s' (pl s' L') t') :
    HEq (cl D Sc s t L h) (cl D Sc s' t' L' h') := by
  subst s'
  subst t'
  subst L'
  rfl

private theorem appendIdentityIndex_tail (i : I) {v t : List I}
    (y : NFIdx v t) (m : ℕ) :
    HEq (appendTail D Sc (appendIdentityIndex i y m))
      ((dotE D Sc (t ++ [i]) t.length) ^ m) := by
  have ht := appendIdentityIndex_target i y m
  have hl : v.length = t.length := by
    have he := congrArg List.length y.tgt_cw
    simpa only [length_tgt] using he
  unfold appendTail
  rw [dotE_pow]
  apply append_cl_heq D Sc (congrArg (· ++ [i]) ht) rfl
  simp only [appendIdentityIndex, appendIdentityShuffle_word, cw,
    List.reverse_nil, List.map_nil, List.append_nil, List.map_replicate, hl]

private theorem appendTail_cross_heq (i : I) (v s t : List I)
    (x : AppendIdx i v (t ++ [i])) (e : x.oldTarget = s ++ [i])
    (L : List PG)
    (hw : cw (Categorification.TypeA.canWord (v ++ [i]).length x.1.2.2.2.1⁻¹) =
      PG.cross s.length :: L)
    (hf : Fits (s ++ [i]).length L)
    (h : SChain (s ++ [i]) (pl (s ++ [i]) L) t) :
    HEq (appendTail D Sc x)
      (((dotE D Sc (s ++ [i] ++ [i]) (s.length + 1)) ^ x.1.1) ≫
        crossLast D Sc s i i ≫ affineRightContext D Sc [i] _ _ (cl D Sc _ _ L h)) := by
  have hl : v.length = s.length + 1 := by
    have hh := congrArg List.length e
    simpa only [AppendIdx.oldTarget, length_tgt, List.length_append,
      List.length_singleton] using hh
  change HEq (appendTail D Sc x)
    (_ ≫ crossLast D Sc s i i ≫ (cl D Sc _ _ L h ▷ (pres D Sc).obj (ob D [i])))
  rw [dotE_pow, crossLast, cl_whiskerRight D Sc _ _ [i] hf, cl_comp, cl_comp]
  unfold appendTail
  apply append_cl_heq D Sc (congrArg (· ++ [i]) e) rfl
  simp only [hw, hl, List.map_replicate, List.singleton_append]

private def appendShuffleSizeCast {n n' : ℕ} (e : n = n') :
    AppendShuffle (show n + 1 = n + 1 from rfl) ≃
      AppendShuffle (show n' + 1 = n' + 1 from rfl) := by
  subst n'
  exact Equiv.refl _

private theorem appendShuffleSizeCast_word {n n' : ℕ} (e : n = n')
    (d : AppendShuffle (show n + 1 = n + 1 from rfl)) :
    Categorification.TypeA.canWord (n' + 1) (appendShuffleSizeCast e d).1⁻¹ =
    Categorification.TypeA.canWord (n + 1) d.1⁻¹ := by
  subst n'
  rfl

private def appendIndexWithTail (i : I) {v u w : List I} (y : NFIdx v u)
    (d : AppendShuffle (appendLen v i)) (m : ℕ)
    (h : tgt (u ++ [i]) (cw (Categorification.TypeA.canWord (v ++ [i]).length d.1⁻¹)) = w) :
    AppendIdx i v w :=
  ⟨(m, y.1.1, y.1.2, d), y.2.1, y.2.2.1, by
    rw [appendCrossingWord, cw_append, tgt_append,
      tgt_append_right [i] (fits_cw (Categorification.TypeA.validWord_canWord v.length y.1.2)),
      y.tgt_cw]
    exact h⟩

private theorem appendIndexWithTail_target (i : I) {v u w : List I} (y : NFIdx v u)
    (d : AppendShuffle (appendLen v i)) (m : ℕ)
    (h : tgt (u ++ [i]) (cw (Categorification.TypeA.canWord (v ++ [i]).length d.1⁻¹)) = w) :
    (appendIndexWithTail i y d m h).oldTarget = u := y.tgt_cw

private theorem appendTail_cross_chain {i : I} {s t : List I} (z : AppendIdx i s t) :
    SChain (z.oldTarget ++ [i])
      (pl (z.oldTarget ++ [i]) (cw (Categorification.TypeA.canWord (s ++ [i]).length z.1.2.2.2.1⁻¹))) t := by
  have hz := z.2.2.2
  rw [appendCrossingWord, cw_append, tgt_append,
    tgt_append_right [i] (fits_cw (Categorification.TypeA.validWord_canWord s.length z.1.2.2.1))] at hz
  change tgt (z.oldTarget ++ [i])
    (cw (Categorification.TypeA.canWord (s ++ [i]).length z.1.2.2.2.1⁻¹)) = t at hz
  simpa only [hz] using sChain_pl (z.oldTarget ++ [i])
    (cw (Categorification.TypeA.canWord (s ++ [i]).length z.1.2.2.2.1⁻¹))

private theorem appendTail_cross_fits {i : I} {s t : List I} (z : AppendIdx i s t) :
    Fits (z.oldTarget ++ [i]).length
      (cw (Categorification.TypeA.canWord (s ++ [i]).length z.1.2.2.2.1⁻¹)) := by
  simpa only [AppendIdx.oldTarget, List.length_append, length_tgt] using
    fits_cw (Categorification.TypeA.validWord_canWord (s ++ [i]).length z.1.2.2.2.1⁻¹)

private theorem appendRunWord_castSucc (n : ℕ) (j : Fin (n + 1)) :
    cw (Categorification.TypeA.canWord (n + 2) (appendRun (n + 1) j.castSucc).1⁻¹) =
      PG.cross n :: cw (Categorification.TypeA.canWord (n + 1) (appendRun n j).1⁻¹) := by
  rw [canWord_appendRun, canWord_appendRun, Fin.val_castSucc]
  have hj : j.val ≤ n := Nat.lt_succ_iff.mp j.2
  rw [show n + 1 - j.val = (n - j.val) + 1 by omega, List.range'_concat, cw_append]
  simp only [cw, List.reverse_singleton, List.map_singleton, List.cons_append, List.nil_append]
  congr 2
  omega

private theorem appendCrossingShuffle_exists (i : I) (v s t : List I)
    (z : AppendIdx i s t) (hv : s.length + 1 = v.length) :
    ∃ d : AppendShuffle (appendLen v i),
      cw (Categorification.TypeA.canWord (v ++ [i]).length d.1⁻¹) =
        PG.cross s.length ::
          cw (Categorification.TypeA.canWord (s ++ [i]).length z.1.2.2.2.1⁻¹) := by
  let d0 := AppendShuffle.cast (appendLen s i) rfl z.1.2.2.2
  let j := (appendRunEquiv s.length).symm d0
  let d1 := appendShuffleSizeCast hv (appendRun (s.length + 1) j.castSucc)
  refine ⟨AppendShuffle.cast rfl (appendLen v i) d1, ?_⟩
  rw [AppendShuffle.canWord_cast, appendShuffleSizeCast_word]
  rw [appendRunWord_castSucc]
  have hj : appendRun s.length j = d0 := (appendRunEquiv s.length).apply_symm_apply d0
  rw [hj, AppendShuffle.canWord_cast]

private theorem appendTail_power_cross (i : I) (s t : List I) (z : AppendIdx i s t) :
    affineUnit D Sc cutoff _ _ (appendTail D Sc z) =
      appendMovingPower D Sc cutoff i z.oldTarget z.1.1 ≫
        affineUnit D Sc cutoff _ _
          (cl D Sc _ _ (cw (Categorification.TypeA.canWord (s ++ [i]).length z.1.2.2.2.1⁻¹))
            (appendTail_cross_chain z)) := by
  have hl : z.oldTarget.length = s.length := by simp only [AppendIdx.oldTarget, length_tgt]
  unfold appendMovingPower
  rw [← affineUnit_comp]
  apply congrArg (affineUnit D Sc cutoff _ _)
  unfold appendTail
  rw [dotE_pow, cl_comp]
  apply eq_of_heq
  apply append_cl_heq D Sc rfl rfl
  simp only [hl, List.map_replicate]

@[simp] theorem data_cross (i : I) (v s t : List I) (L : List PG) (m : ℕ)
    (h : SChain (s ++ [i]) (pl (s ++ [i]) L) t)
    (b : Old D Sc cutoff v (s ++ [i])) :
    data D Sc cutoff i v (s ++ [i]) t (PG.cross s.length :: L) m b =
      SKM.zsign k (D.parity i * D.parity i) ^ m •
        shortTensor D Sc cutoff i v s t
          (appendMovingPower D Sc cutoff i s m ≫
            affineUnit D Sc cutoff _ _ (cl D Sc _ _ L h)) b := by
  dsimp only [data]
  rw [dite_eq_right (List.cons_ne_nil _ _)]
  have he : (s ++ [i]).dropLast = s := List.dropLast_concat
  rw [dite_eq_left (congrArg (· ++ [i]) he).symm]
  have ht : SChain ((s ++ [i]).dropLast ++ [i])
      (pl ((s ++ [i]).dropLast ++ [i]) (PG.cross s.length :: L).tail) t := by
    simpa only [he, List.tail_cons] using h
  rw [dite_eq_left ht, LinearMap.smul_apply]
  congr 1
  have aux (s' : List I) (e : s' = s) (hs : s ++ [i] = s' ++ [i])
      (hc : SChain (s' ++ [i]) (pl (s' ++ [i]) L) t) :
      wordLift D Sc cutoff i v (s ++ [i]) s' t hs L m hc b =
        shortTensor D Sc cutoff i v s t
          (appendMovingPower D Sc cutoff i s m ≫
            affineUnit D Sc cutoff _ _ (cl D Sc _ _ L h)) b := by
    subst s'; rfl
  exact aux _ he _ ht

theorem decode_pair_representative (i : I) (v t : List I)
    (q : AppendIdx.Tail i v (t ++ [i]))
    (b : Old D Sc cutoff v q.representative.oldTarget) :
    decode D Sc cutoff i v t
      (appendPair D Sc cutoff 0 i (affineUnit D Sc cutoff _ _
        (appendTail D Sc q.representative)) b) =
    data D Sc cutoff i v q.representative.oldTarget t
      (cw (Categorification.TypeA.canWord (v ++ [i]).length
        q.representative.1.2.2.2.1⁻¹)) q.representative.1.1 b := by
  have he : decode D Sc cutoff i v t
      (appendOldReconstruct D Sc cutoff 0 i v (t ++ [i]) (DirectSum.lof k _ _ q b)) =
      data D Sc cutoff i v q.representative.oldTarget t
        (cw (Categorification.TypeA.canWord (v ++ [i]).length
          q.representative.1.2.2.2.1⁻¹)) q.representative.1.1 b := by
    simp only [decode, LinearMap.comp_apply, LinearEquiv.coe_coe,
      appendOldCoordinateEquiv_reconstruct, DirectSum.toModule_lof]
  have hu : affineUnit D Sc cutoff _ _ (appendTail D Sc q.representative) =
      ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
        appendTail D Sc q.representative : hom D Sc cutoff
          (q.representative.oldTarget ++ [i]) (t ++ [i])) := rfl
  rw [hu]
  simpa only [appendOldReconstruct, DirectSum.toModule_lof] using he

private theorem data_transport (i : I) {v s s' t : List I}
    (e : s = s') (L : List PG) (m : ℕ) (r : hom D Sc cutoff v s) :
    data D Sc cutoff i v s t L m ((ideal D Sc cutoff v s).mkQ r) =
    data D Sc cutoff i v s' t L m ((ideal D Sc cutoff v s').mkQ (e ▸ r)) := by
  subst s'; rfl

/-- Repeated old normal forms with the same tail give the same decoded balanced class. -/
theorem decode_pair (i : I) (v t : List I)
    (x : AppendIdx i v (t ++ [i])) (r : hom D Sc cutoff v x.oldTarget) :
    decode D Sc cutoff i v t
      (appendPair D Sc cutoff 0 i (affineUnit D Sc cutoff _ _ (appendTail D Sc x))
        ((ideal D Sc cutoff v x.oldTarget).mkQ r)) =
    data D Sc cutoff i v x.oldTarget t
      (cw (Categorification.TypeA.canWord (v ++ [i]).length x.1.2.2.2.1⁻¹)) x.1.1
        ((ideal D Sc cutoff v x.oldTarget).mkQ r) := by
  let q : AppendIdx.Tail i v (t ++ [i]) := ⟨x.tailKey, x, rfl⟩
  have hk : x.tailKey = q.representative.tailKey := q.representative_tailKey.symm
  have ht := x.oldTarget_eq_of_tailKey_eq q.representative hk
  rw [appendTailPair_transport D Sc cutoff ht r _ _
    (appendTail_heq_of_tailKey_eq D Sc x q.representative hk), decode_pair_representative]
  have hm := congrArg Prod.fst hk
  have hd := congrArg Prod.snd hk
  change x.1.1 = q.representative.1.1 at hm
  change x.1.2.2.2 = q.representative.1.2.2.2 at hd
  rw [← hm, ← hd]
  exact (data_transport D Sc cutoff i ht _ _ r).symm

/-- Identity output tails have zero crossing coordinate. -/
theorem decode_embedding_single (i : I) (v t : List I) (m : ℕ)
    (g : hom D Sc cutoff v t) :
    decode D Sc cutoff i v t
      (appendOutputEmbedding D Sc cutoff i v t
        (Finsupp.single m ((ideal D Sc cutoff v t).mkQ g))) = 0 := by
  by_cases hg : g = 0
  · simp [hg]
  obtain ⟨y⟩ := exists_oldIndex_of_ne_zero D Sc cutoff g hg
  let x := appendIdentityIndex i y m
  have ht : x.oldTarget = t := appendIdentityIndex_target i y m
  let r : hom D Sc cutoff v x.oldTarget := ht.symm ▸ g
  have hr : ht ▸ r = g := by
    exact (show ∀ {a b : List I} (e : a = b) (z : hom D Sc cutoff v b),
      e ▸ (e.symm ▸ z : hom D Sc cutoff v a) = z from
        by intro a b e z; cases e; rfl) ht g
  have he := appendTailPair_transport D Sc cutoff ht r
    (appendTail D Sc x) ((dotE D Sc (t ++ [i]) t.length) ^ m)
    (appendIdentityIndex_tail D Sc i y m)
  rw [hr] at he
  have hc := decode_pair D Sc cutoff i v t x r
  rw [he] at hc
  have hw : cw (Categorification.TypeA.canWord (v ++ [i]).length x.1.2.2.2.1⁻¹) = [] := by
    simp only [x, appendIdentityIndex, appendIdentityShuffle_word, cw,
      List.reverse_nil, List.map_nil]
  rw [hw, data_nil, LinearMap.zero_apply] at hc
  simpa only [appendOutputEmbedding_single, appendPair_mk, twist_zero,
    appendMovingPower, x, appendIdentityIndex] using hc

theorem decode_embedding (i : I) (v t : List I)
    (f : ℕ →₀ Old D Sc cutoff v t) :
    decode D Sc cutoff i v t (appendOutputEmbedding D Sc cutoff i v t f) = 0 := by
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add f g hf hg => simp only [map_add, hf, hg, add_zero]
  | single m b =>
    obtain ⟨g, rfl⟩ := (ideal D Sc cutoff v t).mkQ_surjective b
    exact decode_embedding_single D Sc cutoff i v t m g

/-- The entire long correction vanishes under the decoder, with full old coefficients. -/
theorem decode_outputPolynomial_precomp (i : I) (v s t : List I)
    (r : hom D Sc cutoff v s) (f : ℕ →₀ hom D Sc cutoff s t) :
    decode D Sc cutoff i v t
      (appendProjection D Sc cutoff i v (t ++ [i])
        (rightContext D Sc cutoff [i] _ _ r ≫ appendOutputPolynomial D Sc cutoff i s t f)) = 0 := by
  rw [appendOutputPolynomial_precomp, ← appendOutputEmbedding_map, decode_embedding]

/-- Recover a canonical crossing only after applying the full triangular law.
The identity-row correction is present and is annihilated by the preceding theorem. -/
theorem decode_canonical_crossing (i : I) (v s t : List I)
    (x : AppendIdx i v (t ++ [i])) (e : x.oldTarget = s ++ [i])
    (L : List PG)
    (hw : cw (Categorification.TypeA.canWord (v ++ [i]).length x.1.2.2.2.1⁻¹) =
      PG.cross s.length :: L)
    (hf : Fits (s ++ [i]).length L)
    (h : SChain (s ++ [i]) (pl (s ++ [i]) L) t)
    (r : hom D Sc cutoff v x.oldTarget) :
    decode D Sc cutoff i v t
      (appendCrossingClass D Sc cutoff i v s t (e ▸ r)
        (appendMovingPower D Sc cutoff i s x.1.1 ≫
          affineUnit D Sc cutoff _ _ (cl D Sc _ _ L h))) =
      shortTensor D Sc cutoff i v s t
        (appendMovingPower D Sc cutoff i s x.1.1 ≫
          affineUnit D Sc cutoff _ _ (cl D Sc _ _ L h))
        ((ideal D Sc cutoff v (s ++ [i])).mkQ (e ▸ r)) := by
  have he := appendTailPair_transport D Sc cutoff e r _ _
    (appendTail_cross_heq D Sc i v s t x e L hw hf h)
  have hc := decode_pair D Sc cutoff i v t x r
  rw [he, hw, data_transport D Sc cutoff i e, data_cross D Sc cutoff i v s t L x.1.1 h] at hc
  simp only [appendPair_mk, twist_zero, affineUnit_comp,
    ← rightContext_affineUnit] at hc
  have hp : appendMovingPower D Sc cutoff i (s ++ [i]) x.1.1 =
      affineUnit D Sc cutoff _ _ ((dotE D Sc (s ++ [i] ++ [i]) (s.length + 1)) ^ x.1.1) := by
    simp only [appendMovingPower, List.length_append, List.length_singleton]
  rw [← hp, appendProjection_crossing_power_triangular, map_add, map_smul,
    decode_outputPolynomial_precomp, add_zero] at hc
  have hu : IsUnit (SKM.zsign k (D.parity i * D.parity i) ^ x.1.1) := by
    apply IsUnit.pow
    unfold SKM.zsign
    split <;> simp
  exact hu.smul_left_cancel.mp hc

/-- Recover every smaller append tail, including zero Hom corners. -/
theorem decode_crossing_tail (i : I) (v s t : List I)
    (z : AppendIdx i s t) (r : hom D Sc cutoff v (z.oldTarget ++ [i])) :
    decode D Sc cutoff i v t
      (appendCrossingClass D Sc cutoff i v z.oldTarget t r
        (affineUnit D Sc cutoff _ _ (appendTail D Sc z))) =
      shortTensor D Sc cutoff i v z.oldTarget t
        (affineUnit D Sc cutoff _ _ (appendTail D Sc z))
        ((ideal D Sc cutoff v (z.oldTarget ++ [i])).mkQ r) := by
  by_cases hr : r = 0
  · simp [hr, appendCrossingClass, shortTensor, BalancedInduction.tensor]
  obtain ⟨y⟩ := exists_oldIndex_of_ne_zero D Sc cutoff r hr
  have hv : s.length + 1 = v.length := by
    have hh := congrArg List.length y.tgt_cw
    simpa only [length_tgt, List.length_append, List.length_singleton,
      AppendIdx.oldTarget] using hh.symm
  obtain ⟨d, hd⟩ := appendCrossingShuffle_exists i v s t z hv
  have hzlen : z.oldTarget.length = s.length := by simp only [AppendIdx.oldTarget, length_tgt]
  let L := cw (Categorification.TypeA.canWord (s ++ [i]).length z.1.2.2.2.1⁻¹)
  have hc := appendTail_cross_chain z
  have hf := appendTail_cross_fits z
  have htarget : tgt (z.oldTarget ++ [i] ++ [i])
      (cw (Categorification.TypeA.canWord (v ++ [i]).length d.1⁻¹)) = t ++ [i] := by
    rw [hd, show PG.cross s.length = PG.cross z.oldTarget.length from congrArg PG.cross hzlen.symm,
      tgt_cons]
    have hcross : tgt (z.oldTarget ++ [i] ++ [i]) [PG.cross z.oldTarget.length] =
        z.oldTarget ++ [i] ++ [i] := tgt_eq (by simpa using sChain_crossAt z.oldTarget [] i i)
    simp only [tgt_cons, tgt_nil] at hcross
    rw [hcross]
    exact (tgt_append_right [i] hf).trans (congrArg (· ++ [i]) (tgt_eq hc))
  let x := appendIndexWithTail i y d z.1.1 htarget
  have he : x.oldTarget = z.oldTarget ++ [i] := appendIndexWithTail_target i y d z.1.1 htarget
  let r' : hom D Sc cutoff v x.oldTarget := he.symm ▸ r
  have hr' : he ▸ r' = r := by
    exact (show ∀ {a b : List I} (e : a = b) (q : hom D Sc cutoff v b),
      e ▸ (e.symm ▸ q : hom D Sc cutoff v a) = q from
        by intro a b e q; cases e; rfl) he r
  have hword : cw (Categorification.TypeA.canWord (v ++ [i]).length x.1.2.2.2.1⁻¹) =
      PG.cross z.oldTarget.length :: L := by simpa only [x, appendIndexWithTail, hzlen] using hd
  have hh := decode_canonical_crossing D Sc cutoff i v z.oldTarget t
    x he L hword hf hc r'
  rw [hr'] at hh
  rw [appendTail_power_cross]
  exact hh

/-- Full affine balance in the independently defined short source. -/
theorem tensor_balance (i : I) (v s s' t : List I)
    (r : hom D Sc cutoff s s') (c : hom D Sc cutoff (s' ++ [i]) t)
    (b : Old D Sc cutoff v (s ++ [i])) :
    shortTensor D Sc cutoff i v s t (rightContext D Sc cutoff [i] _ _ r ≫ c) b =
      shortTensor D Sc cutoff i v s' t c
        ((coefficient D Sc cutoff (D.parity i) i v).map
          ((ideal D Sc cutoff s s').mkQ r) b) :=
  BalancedInduction.balance (affineAppend D Sc cutoff i)
    (quotient D Sc cutoff ⋙ coefficient D Sc cutoff (D.parity i) i v)
    (v := ⟨s⟩) (v' := ⟨s'⟩) r c b

/-- The prescribed column on an arbitrary lifted old quotient coefficient. -/
theorem column_mk (i : I) (v s t : List I)
    (c : hom D Sc cutoff (s ++ [i]) t) (r : hom D Sc cutoff v (s ++ [i])) :
    shortCross D Sc cutoff i v t
      (shortTensor D Sc cutoff i v s t c ((ideal D Sc cutoff _ _).mkQ r)) =
      appendCrossingClass D Sc cutoff i v s t r c := by
  rw [shortCross_tensor, shortCrossPair_mk]
  rfl

/-- Recovery on a smaller tail for every old quotient coefficient. -/
theorem decode_short_tail (i : I) (v s t : List I) (z : AppendIdx i s t)
    (b : Old D Sc cutoff v (z.oldTarget ++ [i])) :
    decode D Sc cutoff i v t (shortCross D Sc cutoff i v t
      (shortTensor D Sc cutoff i v z.oldTarget t
        (affineUnit D Sc cutoff _ _ (appendTail D Sc z)) b)) =
      shortTensor D Sc cutoff i v z.oldTarget t
        (affineUnit D Sc cutoff _ _ (appendTail D Sc z)) b := by
  obtain ⟨r, rfl⟩ := (ideal D Sc cutoff v (z.oldTarget ++ [i])).mkQ_surjective b
  rw [column_mk]
  exact decode_crossing_tail D Sc cutoff i v s t z r

/-- Every full-coefficient balanced generator is recovered. -/
theorem decode_tensor (i : I) (v s t : List I)
    (c : hom D Sc cutoff (s ++ [i]) t) (b : Old D Sc cutoff v (s ++ [i])) :
    decode D Sc cutoff i v t (shortCross D Sc cutoff i v t
      (shortTensor D Sc cutoff i v s t c b)) = shortTensor D Sc cutoff i v s t c b := by
  obtain ⟨f, rfl⟩ := (appendAffineEquiv D Sc cutoff i s t).symm.surjective c
  induction f using Finsupp.induction_linear with
  | zero => simp [shortTensor, BalancedInduction.tensor]
  | add f g hf hg =>
    have hadd (c c' : hom D Sc cutoff (s ++ [i]) t) :
        shortTensor D Sc cutoff i v s t (c + c') b =
          shortTensor D Sc cutoff i v s t c b + shortTensor D Sc cutoff i v s t c' b := by
      simp only [shortTensor, BalancedInduction.tensor, TensorProduct.add_tmul, map_add]
    simp only [map_add, hadd, hf, hg]
  | single z a =>
    rw [appendAffineEquiv_symm_single]
    have hfactor : (a ⊗ₜ[k] appendElt D Sc z : hom D Sc cutoff (s ++ [i]) t) =
        rightContext D Sc cutoff [i] _ _
          (coefficientTwist D cutoff (appendTailParity D z) a ⊗ₜ[k] z.old.nf) ≫
            affineUnit D Sc cutoff _ _ (appendTail D Sc z) := by
      have he : affineUnit D Sc cutoff _ _ (appendTail D Sc z) =
          ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] appendTail D Sc z :
            hom D Sc cutoff (z.oldTarget ++ [i]) t) := rfl
      rw [he]
      exact (append_insert_twisted_coefficient D Sc cutoff z a).symm
    rw [hfactor, tensor_balance]
    exact decode_short_tail D Sc cutoff i v s t z _

/-- Left inverse on all balanced classes, not only their chosen representatives. -/
theorem decode_comp_shortCross (i : I) (v t : List I) :
    decode D Sc cutoff i v t ∘ₗ shortCross D Sc cutoff i v t = LinearMap.id := by
  apply BalancedInduction.hom_ext
  intro s c b
  exact decode_tensor D Sc cutoff i v s.word t c b

@[simp] theorem decode_shortCross (i : I) (v t : List I)
    (z : ShortTarget D Sc cutoff i v t) :
    decode D Sc cutoff i v t (shortCross D Sc cutoff i v t z) = z :=
  LinearMap.congr_fun (decode_comp_shortCross D Sc cutoff i v t) z

theorem shortCross_injective (i : I) (v t : List I) :
    Function.Injective (shortCross D Sc cutoff i v t) :=
  Function.LeftInverse.injective (decode_shortCross D Sc cutoff i v t)

/-- The range is the original crossing span with arbitrary full old arrows on both sides. -/
theorem range_shortCross (i : I) (v t : List I) :
    LinearMap.range (shortCross D Sc cutoff i v t) = appendCrossingSpan D Sc cutoff i v t := by
  apply le_antisymm
  · have hc : appendC0 D Sc cutoff i v t ∘ₗ shortCross D Sc cutoff i v t = 0 := by
      apply BalancedInduction.hom_ext
      intro s c b
      obtain ⟨r, rfl⟩ := (ideal D Sc cutoff v (s.word ++ [i])).mkQ_surjective b
      change appendC0 D Sc cutoff i v t
        (shortCross D Sc cutoff i v t (shortTensor D Sc cutoff i v s.word t c
          ((ideal D Sc cutoff _ _).mkQ r))) = 0
      rw [column_mk, appendC0_crossing]
    rintro z ⟨a, rfl⟩
    rw [← appendC0_ker]
    exact LinearMap.congr_fun hc a
  · apply Submodule.span_le.mpr
    rintro z ⟨s, r, c, rfl⟩
    exact ⟨shortTensor D Sc cutoff i v s t c ((ideal D Sc cutoff _ _).mkQ r),
      column_mk D Sc cutoff i v s t c r⟩

/-- The independently balanced short source identifies with the genuine crossing span. -/
def crossingEquiv (i : I) (v t : List I) :
    ShortTarget D Sc cutoff i v t ≃ₗ[k] appendCrossingSpan D Sc cutoff i v t where
  toFun z := ⟨shortCross D Sc cutoff i v t z, by
    rw [← range_shortCross]; exact ⟨z, rfl⟩⟩
  invFun z := decode D Sc cutoff i v t z.1
  left_inv := decode_shortCross D Sc cutoff i v t
  right_inv z := by
    apply Subtype.ext
    have hz : z.1 ∈ LinearMap.range (shortCross D Sc cutoff i v t) := by
      rw [range_shortCross]; exact z.2
    obtain ⟨a, ha⟩ := hz
    change shortCross D Sc cutoff i v t (decode D Sc cutoff i v t z.1) = z.1
    rw [← ha, decode_shortCross]
  map_add' a b := Subtype.ext (map_add _ a b)
  map_smul' a b := Subtype.ext (map_smul _ a b)

end ShortCrossCoordinates
end OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
end

end
