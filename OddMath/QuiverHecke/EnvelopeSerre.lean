/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.DividedPowerSpan
import OddMath.QuiverHecke.SerreClass
import OddMath.QuiverHecke.GrothendieckPresentation

/-!
# The quantum Serre relations in `K₀(Ḣ_{q,π})`

Brundan–Ellis, arXiv:1701.04133v2, §11: the input to the construction of `γ̄` in Theorem 11.3.
Proposition 11.2 (`SerreComplex.class_alternating_sum`) gives `∑_a (-1)^a [term a] = 0`, where
`term a` is a shifted summand `(i^a j i^{M-a}, e_a)`. Here:

* `K₀(Ḣ_{q,π})` with BE2's multiplication is an `ℒ`-module (end of §6; `KHop.module`), and the
  map from `K₀` of the hom category is `ℒ`-linear on summand classes (`hcls_smul`): the
  entrywise shifts agree with multiplication by `[q]` and `[π]`;
* `e_a` is the tensor product `1_{i^{(a)}} ⊗ 1_j ⊗ 1_{i^{(M-a)}}` of divided-power idempotents
  (`eIdem_eq_tailT`, `hcls_dp_mul`): whiskering is a ring homomorphism carrying dots and
  crossings to dots and crossings, so it carries Demazure products to Demazure products;
* Lemma 11.1 holds for every colour and every `r` in one form (`class_word_rep`,
  `wordCls_rep`): `[iʳ] = [r]^!_{q_i,π_i} [P(i^{(r)})]` with
  `P(i^{(r)}) = Q^{d_i r(r-1)/2} Π^{|i| r(r-1)/2} (iʳ, 1_{i^{(r)}})` (ERRATA [BE2] 13);
* hence the quantum Serre relations hold for the classes of words (`serre_words`): for `i ≠ j`
  and `M = d_ij + 1`,
  `∑_{r ≤ M} (-1)^r π_i^{r|j| + r(r-1)/2} [M, r]_{q_i,π_i} [i^{M-r} j i^r] = 0`
  in `K₀(Ḣ_{q,π})`, with the coefficients of `CoveringQuantum.SuperCartanDatum.serreElt`.
-/

noncomputable section

open CategoryTheory StringDiagrams MonoidalCategory GradedSupercategory
open CategoryTheory.Idempotents OddMath.SKM.Summands
open OddMath.QuiverHecke.SignedNilHecke

namespace OddMath.QuiverHecke

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  {k : Type w} [Field k] (Sc : SKM.Scalars D k) (sy : SKM.Symmetrizer D)
  (hc : Sc.Homogeneous)

/-! ## Whiskering words -/

section Whiskering

/-- Whiskering on the right by a word, `End(t) → End(t r)`. -/
def whiskerRightHom (t r : List I) :
    End (hObj D Sc sy hc t) →+* End (hObj D Sc sy hc (t ++ r)) where
  toFun x := x ▷ hObj D Sc sy hc r
  map_one' := MonoidalSupercategory.id_whiskerRight (R := k) _ _
  map_mul' x y := MonoidalSupercategory.comp_whiskerRight (R := k) y x _
  map_zero' := MonoidalSupercategory.zero_whiskerRight k _
  map_add' x y := MonoidalSupercategory.add_whiskerRight (R := k) x y _

/-- Whiskering on the left by a word, `End(t) → End(l t)`. -/
def whiskerLeftHom (l t : List I) :
    End (hObj D Sc sy hc t) →+* End (hObj D Sc sy hc (l ++ t)) where
  toFun x := hObj D Sc sy hc l ◁ x
  map_one' := MonoidalSupercategory.whiskerLeft_id (R := k) _ _
  map_mul' x y := MonoidalSupercategory.whiskerLeft_comp (R := k) _ y x
  map_zero' := MonoidalSupercategory.whiskerLeft_zero k _
  map_add' x y := MonoidalSupercategory.whiskerLeft_add (R := k) _ x y

variable {D Sc sy hc}

theorem whiskerRightHom_genE {t : List I} (r : List I) {g : PG} (h : SChain t (pl t [g]) t)
    (hg : g.pos + g.width ≤ t.length) :
    whiskerRightHom D Sc sy hc t r (genE D Sc t g) = genE D Sc (t ++ r) g := by
  change genE D Sc t g ▷ (pres D Sc).obj (ob D r) = _
  rw [genE_eq D Sc h, cl_whiskerRight D Sc [g] h r (by simpa [Fits] using hg)]
  exact (genE_eq D Sc _).symm

theorem whiskerLeftHom_genE (l : List I) {t : List I} {g : PG} (h : SChain t (pl t [g]) t) :
    whiskerLeftHom D Sc sy hc l t (genE D Sc t g) = genE D Sc (l ++ t) (g.shift l.length) := by
  change (pres D Sc).obj (ob D l) ◁ genE D Sc t g = _
  rw [genE_eq D Sc h, cl_whiskerLeft D Sc l [g] h]
  exact (genE_eq D Sc _).symm

theorem sChain_append_right {t : List I} (r : List I) {g : PG} (h : SChain t (pl t [g]) t)
    (hg : g.pos + g.width ≤ t.length) : SChain (t ++ r) (pl (t ++ r) [g]) (t ++ r) := by
  rw [pl_append_right r (by simpa [Fits] using hg)]; simpa using sChain_wh h [] r

theorem sChain_dot_replicate (i : I) {n a : ℕ} (ha : a < n) :
    SChain (List.replicate n i) (pl (List.replicate n i) [.dot a]) (List.replicate n i) :=
  sChain_dot _ _ i (replicate_eq_dot i ha) (List.length_replicate ..)

theorem sChain_cross_replicate (i : I) {n a : ℕ} (ha : a + 1 < n) :
    SChain (List.replicate n i) (pl (List.replicate n i) [.cross a]) (List.replicate n i) :=
  sChain_cross _ _ i (replicate_eq_cross i ha) (List.length_replicate ..)

end Whiskering

/-! ## The Serre idempotents as tensor products -/

section Tensor

variable {D Sc sy hc} {i j : I} {M : ℕ}

open SerreComplex in
/-- `1_{i^{(a)}} ⊗ 1_{j i^{M-a}}` is the doubly whiskered divided-power idempotent. -/
theorem lIdem_eq_whisker (a : ℕ) :
    (lIdem D Sc i j M a : End (hObj D Sc sy hc (SerreComplex.word i j M a))) =
      whiskerRightHom D Sc sy hc (List.replicate a i ++ [j]) (List.replicate (M - a) i)
        (whiskerRightHom D Sc sy hc (List.replicate a i) [j] (SerreComplex.dpIdem D Sc i a)) := by
  let φ := (whiskerRightHom D Sc sy hc (List.replicate a i ++ [j]) (List.replicate (M - a) i)).comp
    (whiskerRightHom D Sc sy hc (List.replicate a i) [j])
  refine (map_idem φ (eps D i) (s := 0) (fun a' ha' => ?_) (fun a' ha' => ?_)).symm
  · show φ (genE D Sc _ (.dot a')) = genE D Sc _ (.dot (0 + a'))
    rw [RingHom.comp_apply,
      whiskerRightHom_genE [j] (sChain_dot_replicate i ha') (by simp [PG.pos, PG.width]; omega),
      whiskerRightHom_genE _ (sChain_append_right [j] (sChain_dot_replicate i ha')
        (by simp [PG.pos, PG.width]; omega)) (by simp [PG.pos, PG.width]; omega), zero_add]
  · show φ (genE D Sc _ (.cross a')) = genE D Sc _ (.cross (0 + a'))
    rw [RingHom.comp_apply, whiskerRightHom_genE [j] (sChain_cross_replicate i ha')
        (by simp [PG.pos, PG.width]; omega),
      whiskerRightHom_genE _ (sChain_append_right [j] (sChain_cross_replicate i ha')
        (by simp [PG.pos, PG.width]; omega)) (by simp [PG.pos, PG.width]; omega), zero_add]

open SerreComplex in
/-- `1_{i^a j} ⊗ 1_{i^{(M-a)}}` is the whiskered divided-power idempotent. -/
theorem rIdem_eq_whisker (a : ℕ) :
    (rIdem D Sc i j M a : End (hObj D Sc sy hc (SerreComplex.word i j M a))) =
      whiskerLeftHom D Sc sy hc (List.replicate a i ++ [j]) (List.replicate (M - a) i)
        (SerreComplex.dpIdem D Sc i (M - a)) := by
  have hl : (List.replicate a i ++ [j]).length = a + 1 := by simp
  have h := map_idem (whiskerLeftHom D Sc sy hc (List.replicate a i ++ [j])
      (List.replicate (M - a) i)) (eps D i) (n := M - a)
      (X := dotE D Sc (List.replicate (M - a) i)) (T := crossE D Sc (List.replicate (M - a) i))
      (X' := dotE D Sc (SerreComplex.word i j M a)) (T' := crossE D Sc (SerreComplex.word i j M a))
      (fun a' ha' => by
        show whiskerLeftHom D Sc sy hc _ _ (genE D Sc _ (.dot a')) = _
        rw [whiskerLeftHom_genE _ (sChain_dot_replicate i ha'), PG.shift_dot]
        rfl)
      (fun a' ha' => by
        show whiskerLeftHom D Sc sy hc _ _ (genE D Sc _ (.cross a')) = _
        rw [whiskerLeftHom_genE _ (sChain_cross_replicate i ha'), PG.shift_cross]
        rfl)
  rw [hl] at h
  exact h.symm

theorem tailT_one {s : List I} {ε : ℕ} (z : HEnd D Sc sy hc s) :
    tailT s (𝟙 (hObj D Sc sy hc (List.replicate ε i))) z =
      z ▷ hObj D Sc sy hc (List.replicate ε i) := by
  rw [tailT, MonoidalSupercategory.whiskerLeft_id (R := k)]
  exact Category.id_comp _

open SerreComplex in
/-- **`e_a = 1_{i^{(a)}} ⊗ 1_j ⊗ 1_{i^{(M-a)}}`** as a tensor product in `H`. -/
theorem eIdem_eq_tailT (a : ℕ) :
    (eIdem D Sc i j M a : HEnd D Sc sy hc (SerreComplex.word i j M a)) =
      tailT (List.replicate a i ++ [j]) (SerreComplex.dpIdem D Sc i (M - a))
        (tailT (List.replicate a i) (𝟙 (hObj D Sc sy hc (List.replicate 1 j)))
          (SerreComplex.dpIdem D Sc i a)) := by
  rw [tailT_one]
  have h1 := lIdem_eq_whisker (D := D) (Sc := Sc) (sy := sy) (hc := hc) (i := i) (j := j) (M := M) a
  have h2 := rIdem_eq_whisker (D := D) (Sc := Sc) (sy := sy) (hc := hc) (i := i) (j := j) (M := M) a
  change (rIdem D Sc i j M a : End (hObj D Sc sy hc (SerreComplex.word i j M a))) ≫
    (lIdem D Sc i j M a : End (hObj D Sc sy hc (SerreComplex.word i j M a))) = _
  rw [h1, h2]
  rfl

/-- The two descriptions of the divided-power idempotent agree. -/
theorem dpIdem_eq_serre (i : I) (r : ℕ) :
    (dpIdem D Sc sy hc i r : HEnd D Sc sy hc (List.replicate r i)) =
      SerreComplex.dpIdem D Sc i r := by
  unfold dpIdem
  split_ifs with hi
  · rw [evenCornerProjector_eq_idem D Sc i hi r, SerreComplex.dpIdem, SerreComplex.eps, hi]
    rfl
  · exact oddCornerProjector_eq_idem D Sc i _ r

end Tensor

/-! ## `K₀(Ḣ_{q,π})` as an `ℒ`-module and its products -/

section Products

open LaurentPolynomial

variable {D Sc sy hc}

/-- `K₀(Ḣ_{q,π})` with BE2's multiplication is an `ℒ`-module (end of §6). -/
instance KHop.module : Module (LaurentPolynomial Zπ) (KHop D Sc sy hc) :=
  letI := GSKAR.moduleLaurent k (MonoidalTwo (HGr D Sc sy hc))
  inferInstanceAs (Module _ (K₀Ring (HDot D Sc sy hc))ᵐᵒᵖ)

instance : IsScalarTower (LaurentPolynomial Zπ) (KHop D Sc sy hc) (KHop D Sc sy hc) where
  smul_assoc r x y := by
    change MulOpposite.op (y.unop *
        (letI := GSKAR.moduleLaurent k (MonoidalTwo (HGr D Sc sy hc)); r • x.unop)) =
      MulOpposite.op (letI := GSKAR.moduleLaurent k (MonoidalTwo (HGr D Sc sy hc));
        r • (y.unop * x.unop))
    rw [GSKAR.mul_smul]

instance : SMulCommClass (LaurentPolynomial Zπ) (KHop D Sc sy hc) (KHop D Sc sy hc) where
  smul_comm r x y := by
    change MulOpposite.op (letI := GSKAR.moduleLaurent k (MonoidalTwo (HGr D Sc sy hc));
        r • (y.unop * x.unop)) =
      MulOpposite.op ((letI := GSKAR.moduleLaurent k (MonoidalTwo (HGr D Sc sy hc));
        r • y.unop) * x.unop)
    rw [GSKAR.smul_mul]

variable {t : List I} {e : HEnd D Sc sy hc t} (he : e ≫ e = e)
  (hd : e ∈ GradedSupercategory.degree (R := k) _ _ 0)
  (hp : e ∈ Supercategory.parity (R := k) _ _ 0)

/-- The class of the summand `Q^n Π^p (t, e)` in `K₀(Ḣ_{q,π})` with BE2's multiplication. -/
abbrev hcls (n : ℤ) (p : ZMod 2) : KHop D Sc sy hc :=
  MulOpposite.op (hKarToKH D Sc sy hc (K₀.mk (raw he hd hp n p)))

variable (D Sc sy hc) in
/-- The shifted identity `Q^m Π^s 1` of the unique object. -/
abbrev unitRawH (m : ℤ) (s : ZMod 2) :=
  raw (k := k) (f := 𝟙 (MonoidalTwo.star (HGr D Sc sy hc))) (Category.id_comp _)
    (GradedSupercategory.id_mem_degree (R := k) _) (Supercategory.id_mem (R := k) _) m s

theorem unit_whiskerLeft (x : HEnd D Sc sy hc t) :
    TwoSupercategory.hcomp (B := MonoidalTwo (HGr D Sc sy hc)) (a := MonoidalTwo.star _)
      (b := MonoidalTwo.star _) (c := MonoidalTwo.star _) (𝟙 (𝟙 (MonoidalTwo.star _))) x = x := by
  simp only [TwoSupercategory.hcomp]
  rw [TwoSupercategory.id_whiskerRight (R := k), Category.id_comp,
    TwoSupercategory.id_whiskerLeft (R := k)]
  change (eqToIso _).hom ≫ x ≫ (eqToIso _).inv = x
  simp

theorem raw_mul_unitRaw (n m : ℤ) (p s : ZMod 2) :
    hKarToKH D Sc sy hc (K₀.mk (raw he hd hp n p)) *
      K₀Ring.mk (B := HDot D Sc sy hc) (a := HDot.star D Sc sy hc) (b := HDot.star D Sc sy hc)
        (unitRawH D Sc sy hc m s) =
    hKarToKH D Sc sy hc (K₀.mk (raw he hd hp (m + n) (s + p))) := by
  have h := mk_raw_mul_mk_raw (k := k) (B := MonoidalTwo (HGr D Sc sy hc))
    (a := MonoidalTwo.star _) (b := MonoidalTwo.star _) (c := MonoidalTwo.star _)
    (f := 𝟙 (MonoidalTwo.star (HGr D Sc sy hc))) (g := hObj D Sc sy hc t) (Category.id_comp _)
    (GradedSupercategory.id_mem_degree (R := k) _) (Supercategory.id_mem (R := k) _) he hd hp
    m n s p
  rw [hKarToKH_mk, hKarToKH_mk, h]
  exact congrArg _ (raw_congr (unit_whiskerLeft e) _ _ _ _ _ _ rfl rfl)

variable (D Sc sy hc) in
theorem q_eq_unitRawH :
    QPiTwoCategory.q (R := k) (HDot.star D Sc sy hc) = unitRawH D Sc sy hc 1 0 := by
  rw [unitRawH, SerreComplex.raw_id]
  rfl

variable (D Sc sy hc) in
theorem qinv_eq_unitRawH :
    QPiTwoCategory.qinv (R := k) (HDot.star D Sc sy hc) = unitRawH D Sc sy hc (-1) 0 := by
  rw [unitRawH, SerreComplex.raw_id]
  rfl

variable (D Sc sy hc) in
theorem pi_eq_unitRawH :
    PiTwoCategory.pi (R := k) (HDot.star D Sc sy hc) = unitRawH D Sc sy hc 0 1 := by
  rw [unitRawH, SerreComplex.raw_id]
  rfl

theorem T_one_smul_hcls (n : ℤ) (p : ZMod 2) :
    (T 1 : LaurentPolynomial Zπ) • hcls he hd hp n p = hcls he hd hp (n + 1) p := by
  let := GSKAR.moduleLaurent k (MonoidalTwo (HGr D Sc sy hc))
  change MulOpposite.op ((T 1 : LaurentPolynomial Zπ) • hKarToKH D Sc sy hc _) = _
  rw [hKarToKH_mk, K₀Ring.mk, K₀Ring.T_smul_of']
  change MulOpposite.op (hKarToKH D Sc sy hc (K₀.mk (raw he hd hp n p)) * K₀Ring.mk _) = _
  rw [q_eq_unitRawH, raw_mul_unitRaw, add_comm (1 : ℤ), zero_add]

theorem T_neg_one_smul_hcls (n : ℤ) (p : ZMod 2) :
    (T (-1) : LaurentPolynomial Zπ) • hcls he hd hp n p = hcls he hd hp (n + -1) p := by
  let := GSKAR.moduleLaurent k (MonoidalTwo (HGr D Sc sy hc))
  change MulOpposite.op ((T (-1) : LaurentPolynomial Zπ) • hKarToKH D Sc sy hc _) = _
  rw [hKarToKH_mk, K₀Ring.mk, K₀Ring.T_neg_one_smul_of']
  change MulOpposite.op (hKarToKH D Sc sy hc (K₀.mk (raw he hd hp n p)) * K₀Ring.mk _) = _
  rw [qinv_eq_unitRawH, raw_mul_unitRaw, add_comm (-1 : ℤ), zero_add]

theorem pi_smul_hcls (n : ℤ) (p : ZMod 2) :
    (C Zπ.π : LaurentPolynomial Zπ) • hcls he hd hp n p = hcls he hd hp n (p + 1) := by
  let := GSKAR.moduleLaurent k (MonoidalTwo (HGr D Sc sy hc))
  change MulOpposite.op ((C Zπ.π : LaurentPolynomial Zπ) • hKarToKH D Sc sy hc _) = _
  rw [hKarToKH_mk, K₀Ring.mk, K₀Ring.C_π_smul_of']
  change MulOpposite.op (hKarToKH D Sc sy hc (K₀.mk (raw he hd hp n p)) * K₀Ring.mk _) = _
  rw [pi_eq_unitRawH, raw_mul_unitRaw, add_comm (1 : ZMod 2), zero_add]

theorem T_smul_hcls (z n : ℤ) (p : ZMod 2) :
    (T z : LaurentPolynomial Zπ) • hcls he hd hp n p = hcls he hd hp (n + z) p := by
  induction z using Int.induction_on generalizing n with
  | zero => simp
  | succ z ih =>
    rw [T_add, mul_smul, T_one_smul_hcls, ih]
    congr 1; ring
  | pred z ih =>
    rw [show -(z : ℤ) - 1 = -(z : ℤ) + -1 by ring, T_add, mul_smul, T_neg_one_smul_hcls, ih]
    congr 1; ring

/-- **`K₀(HKar) → K₀(Ḣ_{q,π})` is `ℒ`-linear on summand classes**: the entrywise shifts of
`HKar` and the action of BE2 §6 (multiplication by `[q]`, `[π]`) agree on `Q^n Π^p (t, e)`. -/
theorem hcls_smul (r : LaurentPolynomial Zπ) (n : ℤ) (p : ZMod 2) :
    MulOpposite.op (hKarToKH D Sc sy hc (letI := K₀.moduleLaurent k (HKar D Sc sy hc)
      r • K₀.mk (raw he hd hp n p))) = r • hcls he hd hp n p := by
  let := K₀.moduleLaurent k (HKar D Sc sy hc)
  exact SerreComplex.smul_shift_family
    ((MulOpposite.opAddEquiv.toAddMonoidHom).comp (hKarToKH D Sc sy hc))
    (fun n p => K₀.mk (raw he hd hp n p)) (hcls he hd hp) (fun _ _ => rfl)
    (fun z n p => class_raw_shift he hd hp n z p) (fun n p => class_raw_pi he hd hp n p)
    (T_smul_hcls he hd hp) (pi_smul_hcls he hd hp) r n p

end Products

/-! ## Lemma 11.1 for every colour -/

section DividedPowers

open LaurentPolynomial
open SKM.K0Relations (qUnit piCoeff)

variable {D Sc sy hc}

theorem mk_raw_eq_smul {t : List I} {e : HEnd D Sc sy hc t} (he : e ≫ e = e)
    (hd : e ∈ GradedSupercategory.degree (R := k) _ _ 0)
    (hp : e ∈ Supercategory.parity (R := k) _ _ 0) (n : ℤ) (p : ZMod 2) :
    K₀.mk (raw (k := k) he hd hp n p) =
      (letI := K₀.moduleLaurent k (HKar D Sc sy hc);
        (T n * piCoeff p) • K₀.mk (raw (k := k) he hd hp 0 0)) := by
  let := K₀.moduleLaurent k (HKar D Sc sy hc)
  rw [mul_smul]
  rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) p with rfl | rfl
  · rw [show piCoeff 0 = 1 by simp [piCoeff], one_smul, class_raw_shift, zero_add]
  · rw [show piCoeff 1 = C Zπ.π by simp [piCoeff, ZMod.val_one], class_raw_pi, class_raw_shift,
      zero_add, zero_add]

variable (D Sc sy hc) in
/-- **BE2 (11.3)**: the divided power `P(i^{(r)}) = Q^{d_i r(r-1)/2} Π^{|i| r(r-1)/2}
(iʳ, 1_{i^{(r)}})`, with the normalization of ERRATA [BE2] 13. -/
abbrev dpObj (i : I) (r : ℕ) : HKar D Sc sy hc :=
  raw (dpIdem_idem D Sc sy hc i r) (dpIdem_mem D Sc sy hc i r).1 (dpIdem_mem D Sc sy hc i r).2
    (sy.d i * (r.choose 2 : ℕ)) (((r.choose 2 : ℕ) : ZMod 2) * D.parity i)

/-- **BE2 Lemma 11.1 in `K₀(Ḣ_{q,π})`**, for every colour and every `r`:
`[iʳ] = [r]^!_{q_i,π_i} [P(i^{(r)})]`. -/
theorem class_word_rep (i : I) (r : ℕ) :
    K₀.mk (word D Sc sy hc (List.replicate r i)) =
      (letI := K₀.moduleLaurent k (HKar D Sc sy hc);
        CoveringQuantum.qpFact (qUnit (sy.d i)) (piCoeff (D.parity i)) r •
          K₀.mk (dpObj D Sc sy hc i r)) := by
  let := K₀.moduleLaurent k (HKar D Sc sy hc)
  rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) (D.parity i) with hi | hi
  · have h := class_word_even D Sc sy hc i hi r
    rw [SerreComplex.smul_int, SerreComplex.map_qfact] at h
    rw [h, hi]
    congr 1
    refine congrArg K₀.mk (raw_congr ?_ _ _ _ _ _ _ (by ring) (by rw [hi, mul_zero]))
    unfold dpIdem
    rw [dite_eq_left_of_eq_true (eq_true hi)]
  · match r with
    | 0 | 1 =>
      have hq : ∀ n ≤ 1, CoveringQuantum.qpFact (qUnit (sy.d i)) (piCoeff (D.parity i)) n = 1 := by
        intro n hn
        interval_cases n <;> simp [CoveringQuantum.qpFact, CoveringQuantum.qpNat]
      first
        | rw [hq 0 (by omega)] | rw [hq 1 le_rfl]
      rw [one_smul]
      refine congrArg K₀.mk ((SerreComplex.raw_id _ 0 0).symm.trans ?_)
      refine raw_congr ?_ _ _ _ _ _ _ (by simp) (by simp)
      rw [dpIdem_eq_serre]
      rfl
    | n + 2 =>
      have h := class_word_odd D Sc sy hc i hi n
      rw [hi, SerreComplex.piCoeff_one, ← SerreComplex.qUnitPi_eq, h]
      congr 1
      refine congrArg K₀.mk (raw_congr ?_ _ _ _ _ _ _ (by ring) (by rw [hi, mul_one]))
      rw [dpIdem_eq_serre]
      exact oddCornerProjector_eq_idem D Sc i hi (n + 2)

end DividedPowers


omit [Field k] in
private theorem smul_mul_three {R A : Type*} [CommMonoid R] [Mul A] [MulAction R A]
    [IsScalarTower R A A] [SMulCommClass R A A] (s c c' : R) (x y z : A) :
    s • ((c • x) * y * (c' • z)) = (s * c * c') • (x * y * z) := by
  rw [mul_smul_comm, smul_mul_assoc, smul_mul_assoc, smul_smul, smul_smul, mul_right_comm s]

omit [Field k] in
private theorem smul_int_smul {R A : Type*} [CommRing R] [AddCommGroup A] [Module R A]
    (c d : R) (n : ℤ) (x : A) : (c * ((n : R) * d)) • x = c • (n • (d • x)) := by
  rw [← Int.cast_smul_eq_zsmul R, smul_smul, smul_smul, mul_assoc]

/-! ## The Serre relation for words -/

section Serre

open LaurentPolynomial
open SKM.K0Relations (qUnit piCoeff)

variable {D Sc sy hc} {i j : I} {M : ℕ}

/-- The summand `Q^n Π^p (i^a j i^{M-a}, e_a)` of the Serre complex. -/
abbrev termRaw (a : ℕ) (n : ℤ) (p : ZMod 2) : HKar D Sc sy hc :=
  raw (f := hObj D Sc sy hc (SerreComplex.word i j M a)) (SerreComplex.eIdem_idem_all a)
    (SerreComplex.eIdem_degree sy hc a) (SerreComplex.eIdem_even sy hc a) n p

/-- **`P(i^{(a)}) P(j) P(i^{(M-a)}) = (i^a j i^{M-a}, e_a)`** on unshifted summands, in BE2's
order. -/
theorem hcls_dp_mul (a : ℕ) :
    hcls (dpIdem_idem D Sc sy hc i a) (dpIdem_mem D Sc sy hc i a).1
        (dpIdem_mem D Sc sy hc i a).2 0 0 *
      hcls (Category.id_comp (𝟙 (hObj D Sc sy hc (List.replicate 1 j))))
        (GradedSupercategory.id_mem_degree (R := k) _) (Supercategory.id_mem (R := k) _) 0 0 *
      hcls (dpIdem_idem D Sc sy hc i (M - a)) (dpIdem_mem D Sc sy hc i (M - a)).1
        (dpIdem_mem D Sc sy hc i (M - a)).2 0 0 =
    MulOpposite.op (hKarToKH D Sc sy hc (K₀.mk (termRaw (i := i) (j := j) (M := M) a 0 0))) := by
  have hj : 𝟙 (hObj D Sc sy hc (List.replicate 1 j)) ∈
      homPiece D Sc sy hc (List.replicate 1 j) (List.replicate 1 j) 0 0 :=
    ⟨GradedSupercategory.id_mem_degree _, Supercategory.id_mem _⟩
  have h1 := hKarToKH_raw_tailT (Category.id_comp _) hj (dpIdem_idem D Sc sy hc i a)
    (dpIdem_mem D Sc sy hc i a) 0 0
  have h2 := hKarToKH_raw_tailT (dpIdem_idem D Sc sy hc i (M - a))
    (dpIdem_mem D Sc sy hc i (M - a))
    (tailT_idem (Category.id_comp _) hj (dpIdem_idem D Sc sy hc i a) (dpIdem_mem D Sc sy hc i a))
    (tailT_mem_homPiece hj (dpIdem_mem D Sc sy hc i a)) 0 0
  rw [h1] at h2
  apply MulOpposite.unop_injective
  rw [MulOpposite.unop_mul, MulOpposite.unop_mul, MulOpposite.unop_op, MulOpposite.unop_op,
    MulOpposite.unop_op, MulOpposite.unop_op, ← h2]
  exact congrArg _ (congrArg K₀.mk (raw_congr
    (by rw [eIdem_eq_tailT (sy := sy) (hc := hc), dpIdem_eq_serre, dpIdem_eq_serre]; rfl)
    _ _ _ _ _ _ rfl rfl))

theorem wordCls_rep (i : I) (r : ℕ) :
    wordCls D Sc sy hc (List.replicate r i) =
      (CoveringQuantum.qpFact (qUnit (sy.d i)) (piCoeff (D.parity i)) r *
        (T (sy.d i * (r.choose 2 : ℕ)) * piCoeff (((r.choose 2 : ℕ) : ZMod 2) * D.parity i))) •
      hcls (dpIdem_idem D Sc sy hc i r) (dpIdem_mem D Sc sy hc i r).1
        (dpIdem_mem D Sc sy hc i r).2 0 0 := by
  let := K₀.moduleLaurent k (HKar D Sc sy hc)
  rw [← hcls_smul, mul_smul, ← mk_raw_eq_smul, ← class_word_rep, wordCls, hKarToKH_word]

theorem wordCls_single (j : I) :
    wordCls D Sc sy hc [j] =
      hcls (Category.id_comp (𝟙 (hObj D Sc sy hc (List.replicate 1 j))))
        (GradedSupercategory.id_mem_degree (R := k) _) (Supercategory.id_mem (R := k) _) 0 0 := by
  rw [wordCls, ← hKarToKH_word]
  exact congrArg (fun x => MulOpposite.op (hKarToKH D Sc sy hc (K₀.mk x)))
    (SerreComplex.raw_id (k := k) (hObj D Sc sy hc [j]) 0 0).symm

variable (hij : i ≠ j) (hM : M = D.dn i j + 1)
include hij hM

variable (sy hc) in
/-- Proposition 11.2 with all parities shifted by `c`. -/
theorem class_alternating_sum_par (c : ZMod 2) :
    ∑ a ∈ Finset.range (M + 1), ((-1 : ℤ) ^ a) •
      K₀.mk (termRaw (D := D) (Sc := Sc) (sy := sy) (hc := hc) (i := i) (j := j) (M := M) a
        (SerreComplex.sh sy i M a)
        (SerreComplex.par D i j M a + c)) = 0 := by
  have h := SerreComplex.class_alternating_sum sy hc hij hM
  rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
  · simp only [add_zero]; exact h
  · let := K₀.moduleLaurent k (HKar D Sc sy hc)
    have h' := congrArg ((C Zπ.π : LaurentPolynomial Zπ) • ·) h
    simp only [smul_zero, Finset.smul_sum] at h'
    rw [← h']
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [smul_comm (C Zπ.π : LaurentPolynomial Zπ), SerreComplex.term, class_raw_pi]

theorem serre_coeff {a : ℕ} (ha : a ≤ M) :
    SerreComplex.serreC sy i j M (M - a) *
        (CoveringQuantum.qpFact (qUnit (sy.d i)) (piCoeff (D.parity i)) a *
          (T (sy.d i * (a.choose 2 : ℕ)) * piCoeff (((a.choose 2 : ℕ) : ZMod 2) * D.parity i))) *
        (CoveringQuantum.qpFact (qUnit (sy.d i)) (piCoeff (D.parity i)) (M - a) *
          (T (sy.d i * ((M - a).choose 2 : ℕ)) *
            piCoeff ((((M - a).choose 2 : ℕ) : ZMod 2) * D.parity i))) =
      CoveringQuantum.qpFact (qUnit (sy.d i)) (piCoeff (D.parity i)) M * (-1) ^ M *
        ((((-1 : ℤ) ^ a : ℤ) : LaurentPolynomial Zπ) *
          (T (SerreComplex.sh sy i M a) *
            piCoeff (SerreComplex.par D i j M a + ((M.choose 2 : ℕ) : ZMod 2) * D.parity i))) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le ha
  have hr : a + r - a = r := by omega
  have h1 := SerreComplex.serreC_mul sy i j (a + r) (r := r) (by omega)
  rw [show a + r - r = a by omega] at h1
  have hc := SerreComplex.parity_mul_eq_zero hij hM a
  rw [hr] at hc
  have hch := SerreComplex.choose_two_add a r
  have hpar : D.parity i * ((r : ZMod 2) * D.parity j + ((r.choose 2 : ℕ) : ZMod 2)) +
      (((a.choose 2 : ℕ) : ZMod 2) * D.parity i + ((r.choose 2 : ℕ) : ZMod 2) * D.parity i) =
      SerreComplex.par D i j (a + r) a + (((a + r).choose 2 : ℕ) : ZMod 2) * D.parity i := by
    rw [SerreComplex.par, hr, hch]
    push_cast at hc ⊢
    linear_combination -hc
  have hsh : sy.d i * (a.choose 2 : ℕ) + sy.d i * (r.choose 2 : ℕ) =
      SerreComplex.sh sy i (a + r) a := by
    rw [SerreComplex.sh, hr]; ring
  have hs : (-1 : LaurentPolynomial Zπ) ^ r =
      (-1) ^ (a + r) * (((-1 : ℤ) ^ a : ℤ) : LaurentPolynomial Zπ) := by
    push_cast
    rw [pow_add, mul_comm ((-1 : LaurentPolynomial Zπ) ^ a), mul_assoc, ← pow_add, ← two_mul,
      pow_mul]
    simp
  rw [hr, ← hsh, ← hpar, T_add, SerreComplex.piCoeff_add, SerreComplex.piCoeff_add]
  calc _ = (SerreComplex.serreC sy i j (a + r) r *
        CoveringQuantum.qpFact (qUnit (sy.d i)) (piCoeff (D.parity i)) a *
        CoveringQuantum.qpFact (qUnit (sy.d i)) (piCoeff (D.parity i)) r) *
        (T (sy.d i * (a.choose 2 : ℕ)) * T (sy.d i * (r.choose 2 : ℕ)) *
          (piCoeff (((a.choose 2 : ℕ) : ZMod 2) * D.parity i) *
            piCoeff (((r.choose 2 : ℕ) : ZMod 2) * D.parity i))) := by ring
    _ = _ := by rw [h1, hs]; ring

theorem serre_term {a : ℕ} (ha : a ≤ M) :
    SerreComplex.serreC sy i j M (M - a) •
        wordCls D Sc sy hc (List.replicate a i ++ [j] ++ List.replicate (M - a) i) =
      (CoveringQuantum.qpFact (qUnit (sy.d i)) (piCoeff (D.parity i)) M * (-1) ^ M :
          LaurentPolynomial Zπ) •
        ((-1 : ℤ) ^ a • MulOpposite.op (hKarToKH D Sc sy hc (K₀.mk
          (termRaw (D := D) (Sc := Sc) (sy := sy) (hc := hc) (i := i) (j := j) (M := M) a
            (SerreComplex.sh sy i M a)
            (SerreComplex.par D i j M a + ((M.choose 2 : ℕ) : ZMod 2) * D.parity i))))) := by
  have e1 :=
    (wordCls_mul D Sc sy hc (List.replicate a i ++ [j]) (List.replicate (M - a) i)).symm.trans
    ((congrArg (· * wordCls D Sc sy hc (List.replicate (M - a) i))
      (wordCls_mul D Sc sy hc (List.replicate a i) [j]).symm).trans
    (congrArg₂ (· * ·) (congrArg₂ (· * ·) (wordCls_rep i a) (wordCls_single j))
      (wordCls_rep i (M - a))))
  have e3 := (congrArg (fun x => MulOpposite.op (hKarToKH D Sc sy hc x))
    (mk_raw_eq_smul (SerreComplex.eIdem_idem_all (D := D) (Sc := Sc) (i := i) (j := j) (M := M) a)
      (SerreComplex.eIdem_degree sy hc a) (SerreComplex.eIdem_even sy hc a)
      (SerreComplex.sh sy i M a)
      (SerreComplex.par D i j M a + ((M.choose 2 : ℕ) : ZMod 2) * D.parity i))).trans
    (hcls_smul _ _ _ _ _ _)
  refine ((congrArg (SerreComplex.serreC sy i j M (M - a) • ·) e1).trans
    (smul_mul_three (R := LaurentPolynomial Zπ) (A := KHop D Sc sy hc) _ _ _ _ _ _)).trans ?_
  refine (congrArg₂ (· • ·) (serre_coeff hij hM ha) (hcls_dp_mul (M := M) (j := j) a)).trans ?_
  refine (smul_int_smul (R := LaurentPolynomial Zπ) (A := KHop D Sc sy hc) _ _ _ _).trans ?_
  exact congrArg ((CoveringQuantum.qpFact (qUnit (sy.d i)) (piCoeff (D.parity i)) M * (-1) ^ M :
    LaurentPolynomial Zπ) • ·) (congrArg ((-1 : ℤ) ^ a • ·) e3.symm)

/-- **The quantum Serre relations in `K₀(Ḣ_{q,π})`** (BE2 §11, input to Theorem 11.3): for
`i ≠ j` and `M = d_ij + 1`, the classes of words satisfy
`∑_{r ≤ M} (-1)^r π_i^{r|j| + r(r-1)/2} [M, r]_{q_i,π_i} [i^{M-r} j i^r] = 0`, with BE2's
multiplication. It follows from Proposition 11.2 (`SerreComplex.class_alternating_sum`) and
Lemma 11.1 (`class_word_rep`), using `[M, r] [r]! [M-r]! = [M]!`. -/
theorem serre_words :
    ∑ r ∈ Finset.range (M + 1), SerreComplex.serreC sy i j M r •
      wordCls D Sc sy hc (List.replicate (M - r) i ++ [j] ++ List.replicate r i) = 0 := by
  have h0 := class_alternating_sum_par (Sc := Sc) sy hc hij hM
    (((M.choose 2 : ℕ) : ZMod 2) * D.parity i)
  have h1 := congrArg ((MulOpposite.opAddEquiv.toAddMonoidHom).comp (hKarToKH D Sc sy hc)) h0
  rw [map_sum, map_zero] at h1
  simp only [map_zsmul] at h1
  rw [← Finset.sum_range_reflect]
  refine Eq.trans ?_ ((congrArg (fun x => (CoveringQuantum.qpFact (qUnit (sy.d i))
    (piCoeff (D.parity i)) M * (-1) ^ M : LaurentPolynomial Zπ) • x) h1).trans (smul_zero _))
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  have ha' : a ≤ M := Nat.le_of_lt_succ (Finset.mem_range.mp ha)
  have e : M + 1 - 1 - a = M - a := by omega
  have e2 : M - (M - a) = a := Nat.sub_sub_self ha'
  simp only [e, e2]
  exact serre_term hij hM ha'

end Serre

end OddMath.QuiverHecke
