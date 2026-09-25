import OddMath.Frontier.NilHeckeBasis

/-! EKL arXiv:1111.1320v1 §2.2, (2.36)–(2.37), Proposition 2.11.
The separate three-relation quotient, not the subring or an imposed basis carrier.
The combinatorial descent argument is replayed in THIS quotient before injectivity.
Rank a=n+2; indices start at zero; products act rightmost first.
-/
namespace OddMath.Frontier.NilCoxeterPresentation
open NilCoxeterWords
open OddMath.SkewPolynomial (SkewPolynomial)
open scoped BigOperators
noncomputable section

abbrev Free (n : ℕ) := FreeAlgebra ℤ (Fin (n+1))
def crossingFree (n : ℕ) (i : Fin (n+1)) : Free n := FreeAlgebra.ι ℤ i

/-- Exactly the three nilCoxeter relation families; no kernel relations added. -/
inductive Relator (n : ℕ) : Free n → Prop
  | square (i : Fin (n+1)) : Relator n (crossingFree n i * crossingFree n i)
  | braid (i j : Fin (n+1)) (h : j.val = i.val+1) :
      Relator n (crossingFree n i * crossingFree n j * crossingFree n i -
        crossingFree n j * crossingFree n i * crossingFree n j)
  | distant (i j : Fin (n+1)) (h : i.val+1 < j.val ∨ j.val+1 < i.val) :
      Relator n (crossingFree n i * crossingFree n j + crossingFree n j * crossingFree n i)

def relSet (n : ℕ) : Set (Free n) := {r | Relator n r}
def relTwoSided (n : ℕ) : TwoSidedIdeal (Free n) := TwoSidedIdeal.span (relSet n)
def relIdeal (n : ℕ) : Ideal (Free n) := (relTwoSided n).asIdeal
instance relIdealTwoSided (n : ℕ) : (relIdeal n).IsTwoSided :=
  inferInstanceAs ((relTwoSided n).asIdeal.IsTwoSided)
def Presented (n : ℕ) : Type := Free n ⧸ relIdeal n
instance presentedRing (n : ℕ) : Ring (Presented n) := Ideal.Quotient.ring (relIdeal n)
def crossing (n : ℕ) (i : Fin (n+1)) : Presented n :=
  Ideal.Quotient.mk (relIdeal n) (crossingFree n i)

private theorem relator_zero {n : ℕ} (r : Free n) (h : Relator n r) :
    Ideal.Quotient.mk (relIdeal n) r = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  change r ∈ (relTwoSided n).asIdeal
  rw [TwoSidedIdeal.mem_asIdeal]
  exact TwoSidedIdeal.subset_span h

theorem crossing_square {n : ℕ} (i : Fin (n+1)) :
    crossing n i * crossing n i = 0 := by
  simpa only [map_mul, crossing] using relator_zero _ (Relator.square i)

theorem crossing_braid {n : ℕ} (i j : Fin (n+1)) (h : j.val = i.val+1) :
    crossing n i * crossing n j * crossing n i = crossing n j * crossing n i * crossing n j := by
  simpa only [map_sub, map_mul, crossing, sub_eq_zero] using relator_zero _ (Relator.braid i j h)

theorem crossing_distant {n : ℕ} (i j : Fin (n+1))
    (h : i.val+1 < j.val ∨ j.val+1 < i.val) :
    crossing n i * crossing n j = -(crossing n j * crossing n i) := by
  simpa only [map_add, map_mul, crossing, add_eq_zero_iff_eq_neg] using
    relator_zero _ (Relator.distant i j h)

def freeToNilHecke (n : ℕ) : Free n →ₐ[ℤ] NilHeckeAction.Presented n :=
  FreeAlgebra.lift ℤ (NilHeckeAction.crossing n)

@[simp] theorem freeToNilHecke_crossing (n : ℕ) (i : Fin (n+1)) :
    freeToNilHecke n (crossingFree n i) = NilHeckeAction.crossing n i := by
  simp [freeToNilHecke, crossingFree]

theorem relation_killed (n : ℕ) (r : Free n) (hr : r ∈ relSet n) :
    freeToNilHecke n r = 0 := by
  cases hr with
  | square i => simpa using NilCoxeterWords.crossing_square i
  | braid i j h =>
      simpa only [map_sub, map_mul, freeToNilHecke_crossing, sub_eq_zero] using
        NilCoxeterWords.crossing_braid i j h
  | distant i j h =>
      simpa only [map_add, map_mul, freeToNilHecke_crossing, add_eq_zero_iff_eq_neg] using
        NilCoxeterWords.crossing_distant i j h

theorem ideal_killed (n : ℕ) (r : Free n) (hr : r ∈ relIdeal n) :
    freeToNilHecke n r = 0 := by
  rw [relIdeal, relTwoSided, TwoSidedIdeal.mem_asIdeal] at hr
  induction hr using TwoSidedIdeal.span_induction with
  | mem x h => exact relation_killed n x h
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | neg x _ hx => rw [map_neg, hx, neg_zero]
  | left_absorb a x _ hx => rw [map_mul, hx, mul_zero]
  | right_absorb a x _ hx => rw [map_mul, hx, zero_mul]

/-- Canonical homomorphism; its injectivity is NOT used for normalization. -/
def toNilHecke (n : ℕ) : Presented n →+* NilHeckeAction.Presented n :=
  Ideal.Quotient.lift (relIdeal n) (freeToNilHecke n).toRingHom (ideal_killed n)

@[simp] theorem toNilHecke_crossing (n : ℕ) (i : Fin (n+1)) :
    toNilHecke n (crossing n i) = NilHeckeAction.crossing n i := freeToNilHecke_crossing n i

def product {n : ℕ} : Word n → Presented n
  | [] => 1
  | i::w => crossing n i * product w

@[simp] theorem product_append {n : ℕ} (u v : Word n) :
    product (u++v) = product u * product v := by
  induction u with
  | nil => simp [product]
  | cons i u ih => simp [product, ih, mul_assoc]

@[simp] theorem product_singleton {n : ℕ} (i : Fin (n+1)) : product [i] = crossing n i := by
  simp [product]

@[simp] theorem toNilHecke_product {n : ℕ} (w : Word n) :
    toNilHecke n (product w) = NilCoxeterWords.product w := by
  induction w with
  | nil => simp [product, NilCoxeterWords.product]
  | cons i w ih => simp [product, NilCoxeterWords.product, ih]

/-- The natural polynomial representation, factored through the canonical map. -/
def action (n : ℕ) : Presented n →+* Module.End ℤ (SkewPolynomial (n+2)) :=
  (NilHeckeAction.action n).comp (toNilHecke n)

@[simp] theorem action_crossing (n : ℕ) (i : Fin (n+1)) :
    action n (crossing n i) = AllRankDivided.divided i := by
  simp [action]

theorem action_product {n : ℕ} (w : Word n) :
    action n (product w) = LongestDivided.applyWord w := by
  simpa [action] using NilCoxeterWords.action_product w

theorem action_mul_apply (n : ℕ) (a b : Presented n) (f : SkewPolynomial (n+2)) :
    action n (a*b) f = action n a (action n b f) := by rw [map_mul]; rfl

/- The following descent joins and induction reprove normalization in Presented.
Only permutation/length lemmas are inherited; no nilHecke product equality is
pulled backwards across toNilHecke. This bounded duplication avoids editing the
NilCoxeterWords interface. -/
private theorem descent_join_distant {n : ℕ} (p : Perm n) (i j : Fin (n+1))
    (hi : Descent p i) (hj : Descent p j)
    (h : i.val+1 < j.val ∨ j.val+1 < i.val) :
    ∃ a b : Word n, permutation a = p * simple i ∧ permutation b = p * simple j ∧
      Reduced a ∧ Reduced b ∧ Signed (product a * crossing n i) (product b * crossing n j) := by
  obtain ⟨u, hu, hul⟩ := exists_reduced (p * simple i * simple j)
  have hpi : permutation (u++[j]) = p * simple i := by simp [hu, mul_assoc]
  have hpj : permutation (u++[i]) = p * simple j := by
    simp only [permutation_append, permutation_singleton, hu]
    calc
      p * simple i * simple j * simple i = p * (simple i * simple j) * simple i := by simp [mul_assoc]
      _ = p * (simple j * simple i) * simple i := by rw [simple_distant i j h]
      _ = p * simple j := by simp [mul_assoc]
  have hli := length_descend p i hi
  have hlj := length_descend p j hj
  have hlq := length_descend (p * simple i) j ((descent_distant p i j h).mpr hj)
  refine ⟨u++[j], u++[i], hpi, hpj, ?_, ?_, ?_⟩
  · unfold Reduced; rw [hpi]; simp only [List.length_append, List.length_singleton]; omega
  · unfold Reduced; rw [hpj]; simp only [List.length_append, List.length_singleton]; omega
  · apply Or.inr
    simp only [product_append, product_singleton, mul_assoc]
    rw [crossing_distant j i (by omega), mul_neg]

private theorem descent_join_adjacent {n : ℕ} (p : Perm n) (i j : Fin (n+1))
    (hi : Descent p i) (hj : Descent p j) (h : j.val = i.val+1) :
    ∃ a b : Word n, permutation a = p * simple i ∧ permutation b = p * simple j ∧
      Reduced a ∧ Reduced b ∧ Signed (product a * crossing n i) (product b * crossing n j) := by
  obtain ⟨u, hu, hul⟩ := exists_reduced (p * simple i * simple j * simple i)
  have hb : p * simple i * simple j * simple i = p * simple j * simple i * simple j := by
    simpa only [mul_assoc] using congrArg (p * ·) (simple_braid i j h)
  have hpi : permutation (u++[i,j]) = p * simple i := by
    simp [permutation_append, hu, permutation, ← mul_assoc]
  have hpj : permutation (u++[j,i]) = p * simple j := by
    rw [permutation_append, hu, hb]
    simp [permutation, ← mul_assoc]
  have hli := length_descend p i hi
  have hlj := length_descend p j hj
  have hd := descent_adjacent p i j h hi hj
  have hlq := length_descend (p * simple i) j hd.1
  have hlr := length_descend (p * simple i * simple j) i hd.2
  refine ⟨u++[i,j], u++[j,i], hpi, hpj, ?_, ?_, ?_⟩
  · unfold Reduced; rw [hpi]; simp only [List.length_append, List.length_cons, List.length_nil]; omega
  · unfold Reduced; rw [hpj]; simp only [List.length_append, List.length_cons, List.length_nil]; omega
  · apply Or.inl
    simpa only [product_append, product, mul_one, mul_assoc] using
      congrArg (product u * ·) (crossing_braid i j h)

/-- Local descent joins use only the length-two commuting and length-three braid
polygons of ACTUAL adjacent permutations, with their actual quotient signs. -/
theorem descent_join {n : ℕ} (p : Perm n) (i j : Fin (n+1))
    (hi : Descent p i) (hj : Descent p j) :
    ∃ a b : Word n, permutation a = p * simple i ∧ permutation b = p * simple j ∧
      Reduced a ∧ Reduced b ∧ Signed (product a * crossing n i) (product b * crossing n j) := by
  by_cases he : i = j
  · subst j
    obtain ⟨u, hu, hl⟩ := exists_reduced (p * simple i)
    exact ⟨u,u,hu,hu,by simpa [Reduced,hu] using hl,by simpa [Reduced,hu] using hl,Signed.refl _⟩
  · by_cases h₁ : j.val = i.val+1
    · exact descent_join_adjacent p i j hi hj h₁
    · by_cases h₂ : i.val = j.val+1
      · obtain ⟨a,b,ha,hb,hra,hrb,hs⟩ := descent_join_adjacent p j i hj hi h₂
        exact ⟨b,a,hb,ha,hrb,hra,hs.symm⟩
      · apply descent_join_distant p i j hi hj
        have : i.val ≠ j.val := fun h => he (Fin.ext h)
        omega

/-- Signed Matsumoto conclusion proved here by induction on actual inversion
number and the local descent joins, not assumed from an abstract presentation. -/
theorem reduced_signed {n : ℕ} (w v : Word n) (hw : Reduced w) (hv : Reduced v)
    (hp : permutation w = permutation v) : Signed (product w) (product v) := by
  induction h : w.length using Nat.strong_induction_on generalizing w v with
  | h k ih =>
    cases w using List.reverseRecOn with
    | nil =>
        have hv0 : v.length = 0 := by simpa [Reduced, ← hp, permutation] using hv
        have : v = [] := List.length_eq_zero_iff.mp hv0
        subst v
        exact Signed.refl _
    | append_singleton w i =>
        cases v using List.reverseRecOn with
        | nil =>
            simp [Reduced, hp, permutation] at hw
        | append_singleton v j =>
            obtain ⟨hwr, hwi⟩ := reduced_prefix w i hw
            obtain ⟨hvr, hvj⟩ := reduced_prefix v j hv
            let p := permutation (w++[i])
            have hpi : p * simple i = permutation w := by simp [p, mul_assoc]
            have hpj : p * simple j = permutation v := by simp [p, hp, mul_assoc]
            have hd₁ : Descent p i := by simpa [p] using descent_after_ascend (permutation w) i hwi
            have hd₂ : Descent p j := by simpa [p, hp] using descent_after_ascend (permutation v) j hvj
            obtain ⟨a,b,ha,hb,hra,hrb,hs⟩ := descent_join p i j hd₁ hd₂
            have hwa := ih w.length (by simp only [List.length_append,List.length_singleton] at h; omega)
              w a hwr hra (by rw [ha,hpi]) rfl
            have hvb := ih v.length (by
                have he : v.length = w.length := by
                  unfold Reduced at hw hv
                  rw [← hp] at hv
                  simp only [List.length_append,List.length_singleton] at hw hv
                  omega
                simp only [List.length_append,List.length_singleton] at h
                omega) v b hvr hrb (by rw [hb,hpj]) rfl
            simp only [product_append, product_singleton]
            exact (hwa.mul (Signed.refl _)).trans (hs.trans (hvb.mul (Signed.refl _)).symm)

/-- An arbitrary NONREDUCED word is zero in the presented ring itself. -/
theorem nonreduced_zero {n : ℕ} (w : Word n) (hw : ¬Reduced w) : product w = 0 := by
  induction w using List.reverseRecOn with
  | nil => exact (hw (by simp [Reduced, permutation])).elim
  | append_singleton w i ih =>
      by_cases hr : Reduced w
      · have hd : Descent (permutation w) i := by
          by_contra hn
          exact hw (reduced_append w i hr hn)
        obtain ⟨v,hv,hvl⟩ := exists_reduced (permutation w * simple i)
        have hp : permutation (v++[i]) = permutation w := by simp [hv]
        have hl := length_descend (permutation w) i hd
        have hvr : Reduced (v++[i]) := by
          unfold Reduced; rw [hp]; simp only [List.length_append,List.length_singleton]; omega
        have hs := (reduced_signed w (v++[i]) hr hvr hp.symm).mul (Signed.refl (crossing n i))
        have hz : product (v++[i]) * crossing n i = 0 := by
          simp only [product_append, product_singleton, mul_assoc, crossing_square, mul_zero]
        rw [hz] at hs
        simpa only [product_append, product_singleton] using hs.zero
      · simp [ih hr]

/-- Source (2.36), with choice ambiguity recorded rather than suppressed. -/
noncomputable def dividedElement {n : ℕ} (p : Perm n) : Presented n := product (chosenWord p)

theorem reduced_dividedElement {n : ℕ} (w : Word n) (hw : Reduced w) :
    Signed (product w) (dividedElement (permutation w)) :=
  reduced_signed w _ hw (chosenWord_reduced _) (chosenWord_permutation _).symm

/-- EKL (2.37), the length-additive branch IN THE PRESENTED QUOTIENT. -/
theorem dividedElement_mul_additive {n : ℕ} (p q : Perm n)
    (h : length (p*q) = length p + length q) :
    Signed (dividedElement p * dividedElement q) (dividedElement (p*q)) := by
  have hr : Reduced (chosenWord p ++ chosenWord q) := by simp [Reduced,h]
  simpa only [product_append, chosenWord_permutation, permutation_append, dividedElement] using
    reduced_dividedElement _ hr

/-- EKL (2.37), the nonadditive branch, WITHOUT any faithfulness premise. -/
theorem dividedElement_mul_nonadditive {n : ℕ} (p q : Perm n)
    (h : length (p*q) ≠ length p + length q) : dividedElement p * dividedElement q = 0 := by
  have hr : ¬Reduced (chosenWord p ++ chosenWord q) := by simpa [Reduced,eq_comm] using h
  simpa only [product_append, dividedElement] using nonreduced_zero _ hr

/-- Both source cases in a single statement. -/
theorem dividedElement_mul {n : ℕ} (p q : Perm n) :
    if length (p*q) = length p + length q
    then Signed (dividedElement p * dividedElement q) (dividedElement (p*q))
    else dividedElement p * dividedElement q = 0 := by
  split_ifs with h
  · exact dividedElement_mul_additive p q h
  · exact dividedElement_mul_nonadditive p q h

/-- Every arbitrary word has the source reduced/nonreduced alternative. -/
theorem word_normalization {n : ℕ} (w : Word n) :
    if Reduced w then Signed (product w) (dividedElement (permutation w)) else product w = 0 := by
  split_ifs with h
  · exact reduced_dividedElement w h
  · exact nonreduced_zero w h


theorem reduced_global_sign {n : ℕ} (w v : Word n) (hw : Reduced w) (hv : Reduced v)
    (hp : permutation w = permutation v) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ product w = ε • product v ∧
      ∀ f : SkewPolynomial (n+2), action n (product w) f = ε • action n (product v) f := by
  rcases reduced_signed w v hw hv hp with h | h
  · exact ⟨1, Or.inl rfl, by simpa using h, fun f => by simp [h]⟩
  · exact ⟨-1, Or.inr rfl, by simpa using h, fun f => by simp [h]⟩

@[simp] theorem toNilHecke_dividedElement {n : ℕ} (p : Perm n) :
    toNilHecke n (dividedElement p) = NilCoxeterWords.dividedElement p :=
  toNilHecke_product _

/-- The inherited chosenWord is literally empty at the identity. -/
@[simp] theorem dividedElement_one (n : ℕ) : dividedElement (1 : Perm n) = 1 := by
  have h : chosenWord (1 : Perm n) = [] := List.length_eq_zero_iff.mp (by simp)
  simp [dividedElement, h, product]

def wordSpan (n : ℕ) : Submodule ℤ (Presented n) :=
  Submodule.span ℤ (Set.range (@product n))

theorem word_mem {n : ℕ} (w : Word n) : product w ∈ wordSpan n :=
  Submodule.subset_span ⟨w, rfl⟩

theorem crossing_mul_mem {n : ℕ} (i : Fin (n+1)) {x : Presented n} (hx : x ∈ wordSpan n) :
    crossing n i * x ∈ wordSpan n := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨w,rfl⟩ := hx
      exact word_mem (i::w)
  | zero => simpa only [mul_zero] using (wordSpan n).zero_mem
  | add x y _ _ hx hy => simpa only [mul_add] using (wordSpan n).add_mem hx hy
  | smul r x _ hx => simpa only [mul_smul_comm] using (wordSpan n).smul_mem r hx

def quotientMap (n : ℕ) : Free n →+* Presented n := Ideal.Quotient.mk (relIdeal n)

/-- Spanning is proved on the free algebra and descended, not inferred from the image. -/
theorem free_mul_mem {n : ℕ} (a : Free n) (x : Presented n) (hx : x ∈ wordSpan n) :
    quotientMap n a * x ∈ wordSpan n := by
  induction a using FreeAlgebra.induction generalizing x with
  | grade0 r => simpa [zsmul_eq_mul] using (wordSpan n).smul_mem r hx
  | grade1 i => exact crossing_mul_mem i hx
  | add a b ha hb =>
      rw [map_add, add_mul]
      exact (wordSpan n).add_mem (ha x hx) (hb x hx)
  | mul a b ha hb =>
      rw [map_mul, mul_assoc]
      exact ha _ (hb x hx)

theorem mem_wordSpan {n : ℕ} (x : Presented n) : x ∈ wordSpan n := by
  obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective x
  have h1 : (1 : Presented n) ∈ wordSpan n := word_mem []
  simpa only [mul_one] using free_mul_mem a 1 h1

def basisSpan (n : ℕ) : Submodule ℤ (Presented n) :=
  Submodule.span ℤ (Set.range (@dividedElement n))

theorem product_mem_basisSpan {n : ℕ} (w : Word n) : product w ∈ basisSpan n := by
  by_cases hw : Reduced w
  · rcases reduced_dividedElement w hw with h | h
    · rw [h]; exact Submodule.subset_span ⟨permutation w, rfl⟩
    · rw [h]; exact (basisSpan n).neg_mem (Submodule.subset_span ⟨permutation w, rfl⟩)
  · rw [nonreduced_zero w hw]; exact (basisSpan n).zero_mem

theorem mem_basisSpan {n : ℕ} (x : Presented n) : x ∈ basisSpan n := by
  have hle : wordSpan n ≤ basisSpan n := by
    apply Submodule.span_le.mpr
    rintro _ ⟨w,rfl⟩
    exact product_mem_basisSpan w
  exact hle (mem_wordSpan x)

theorem basisSpan_eq_top (n : ℕ) : basisSpan n = ⊤ := by
  apply top_unique
  intro x _
  exact mem_basisSpan x

/-- Finite integral expansion of EVERY element of the separate quotient. -/
theorem exists_expansion {n : ℕ} (x : Presented n) :
    ∃ c : Perm n →₀ ℤ, c.sum (fun p a => a • dividedElement p) = x :=
  Finsupp.mem_span_range_iff_exists_finsupp.mp (mem_basisSpan x)

/-- The zero-dot slice of the inherited basis is independent; this is a forward map only. -/
theorem image_linearIndependent (n : ℕ) :
    LinearIndependent ℤ (fun p : Perm n => toNilHecke n (dividedElement p)) := by
  have h := (NilHeckeBasis.basisElement_linearIndependent n).comp
    (fun p : Perm n => ((0 : Fin (n+2) → ℕ), p))
    (fun _ _ h => congrArg Prod.snd h)
  simpa [Function.comp_def, NilHeckeBasis.basisElement, NilHeckeBasis.dotMonomial] using h

theorem dividedElement_linearIndependent (n : ℕ) : LinearIndependent ℤ (@dividedElement n) := by
  apply linearIndependent_iff'.mpr
  intro s c hc
  apply (linearIndependent_iff'.mp (image_linearIndependent n)) s c
  simpa only [map_sum, map_zsmul, map_zero] using congrArg (toNilHecke n) hc

/-- A genuine integral permutation Basis of the separately presented ring. -/
def basis (n : ℕ) : Basis (Perm n) ℤ (Presented n) :=
  Basis.mk (dividedElement_linearIndependent n) (by rw [← basisSpan_eq_top n]; exact le_rfl)

@[simp] theorem basis_apply {n : ℕ} (p : Perm n) : basis n p = dividedElement p :=
  Basis.mk_apply _ _ _

theorem expansion_unique {n : ℕ} (c d : Perm n →₀ ℤ)
    (h : c.sum (fun p a => a • dividedElement p) = d.sum (fun p a => a • dividedElement p)) :
    c = d := (dividedElement_linearIndependent n).finsuppLinearCombination_injective h

theorem existsUnique_expansion {n : ℕ} (x : Presented n) :
    ∃! c : Perm n →₀ ℤ, c.sum (fun p a => a • dividedElement p) = x := by
  obtain ⟨c,hc⟩ := exists_expansion x
  exact ⟨c,hc,fun d hd => expansion_unique d c (hd.trans hc.symm)⟩

/-- Injectivity is concluded only AFTER separate quotient-side normalization and spanning. -/
theorem toNilHecke_injective (n : ℕ) : Function.Injective (toNilHecke n) := by
  intro x y h
  obtain ⟨c,hc⟩ := exists_expansion x
  obtain ⟨d,hd⟩ := exists_expansion y
  have he : c.sum (fun p a => a • toNilHecke n (dividedElement p)) =
      d.sum (fun p a => a • toNilHecke n (dividedElement p)) := by
    have hh := (congrArg (toNilHecke n) hc).trans (h.trans (congrArg (toNilHecke n) hd).symm)
    simpa only [Finsupp.sum, map_sum, map_zsmul] using hh
  have hcd := (image_linearIndependent n).finsuppLinearCombination_injective he
  subst d
  exact hc.symm.trans hd

/-- EKL Proposition 2.11, the separate nilCoxeter natural representation is faithful. -/
theorem action_injective (n : ℕ) : Function.Injective (action n) :=
  (NilHeckeBasis.action_injective n).comp (toNilHecke_injective n)

theorem faithful_action (n : ℕ) (x y : Presented n) :
    (∀ f : SkewPolynomial (n+2), action n x f = action n y f) ↔ x = y := by
  constructor
  · intro h; exact action_injective n (LinearMap.ext h)
  · rintro rfl; exact fun _ => rfl

instance presentedNontrivial (n : ℕ) : Nontrivial (Presented n) :=
  (toNilHecke n).domain_nontrivial

end
end OddMath.Frontier.NilCoxeterPresentation
