import OddMath.QuiverHecke.CyclotomicAction.PrefixScalarRelations.PrefixQPDistinct

/-!
# Reverse intertwiner

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-!
# Reverse moving chains and their local norms

The affine reverse of the moving chain in Kang–Kashiwara–Oh, with the
local squares used in `DeformedBoundaryDivision.md` §2.
The reverse chain reverses factors; it is not asserted to be an inverse.
-/

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams SignedNilHecke IntertwinerMeet
open scoped Classical

variable {I : Type*} {X : Type*} [AddCommGroup X] (D : SKM.Datum I X)
  {k : Type*} [CommRing k] (Sc : SKM.Scalars D k)

/-- The moving chain with its factors reversed, from the append word to the prepend word. -/
def reverseMoveHom (i : I) : (l ν : List I) →
    (pres D Sc).obj (ob D (l ++ ν ++ [i])) ⟶ (pres D Sc).obj (ob D (l ++ i :: ν))
  | l, [] => eqToHom (by simp)
  | l, j :: ν =>
      eqToHom (congrArg (fun t => (pres D Sc).obj (ob D t)) (by simp)) ≫
        reverseMoveHom i (l ++ [j]) ν ≫
          eqToHom (congrArg (fun t => (pres D Sc).obj (ob D t))
            (show (l ++ [j]) ++ i :: ν = l ++ [j, i] ++ ν by simp)) ≫
            intertwinerHom D Sc l ν j i ≫
              eqToHom (congrArg (fun t => (pres D Sc).obj (ob D t)) (by simp))

/-- The even repeated-colour square, with categorical composition in its affine block. -/
theorem intertwinerHom_square_even (l r : List I) (i : I) (hp : D.parity i = 0) :
    intertwinerHom D Sc l r i i ≫ intertwinerHom D Sc l r i i =
      -((dotE D Sc (l ++ [i, i] ++ r) (l.length + 1) -
        dotE D Sc (l ++ [i, i] ++ r) l.length) ^ 2) := by
  rw [intertwinerHom_self, ← End.mul_def]
  simp only [sameIntertwiner, hp, zero_ne_one, ite_false]
  simpa only [pow_two] using (evenTwo_block D Sc l r i hp).gEven_mul_gEven

/-- The odd repeated-colour square; no commutativity of the two odd dots is assumed. -/
theorem intertwinerHom_square_odd (l r : List I) (i : I) (hp : D.parity i = 1) :
    intertwinerHom D Sc l r i i ≫ intertwinerHom D Sc l r i i =
      -((dotE D Sc (l ++ [i, i] ++ r) (l.length + 1) ^ 2 -
        dotE D Sc (l ++ [i, i] ++ r) l.length ^ 2) ^ 2 *
        (dotE D Sc (l ++ [i, i] ++ r) l.length ^ 2 +
          dotE D Sc (l ++ [i, i] ++ r) (l.length + 1) ^ 2)) := by
  rw [intertwinerHom_self, ← End.mul_def]
  simp only [sameIntertwiner, hp, ite_true]
  simpa only [pow_two, OddNilHecke.Intertwiner.squareDiff] using
    (oddTwo_block D Sc l r i hp).element_identities.1

/-- The unequal-colour square for a nonzero Cartan entry. -/
theorem intertwinerHom_square_ne (l r : List I) {i j : I}
    (hij : i ≠ j) (hd : D.d i j ≠ 0) :
    intertwinerHom D Sc l r i j ≫ intertwinerHom D Sc l r j i =
      qLeft (dotE D Sc (l ++ [i, j] ++ r) l.length)
        (dotE D Sc (l ++ [i, j] ++ r) (l.length + 1))
        (D.dn i j) (D.dn j i) (Sc.t i j : k) (Sc.t j i : k) (Sc.s i j) := by
  rw [intertwinerHom_of_ne D Sc l r hij,
    intertwinerHom_of_ne D Sc l r (Ne.symm hij), cl_comp]
  exact crossSq_gen D Sc l r hij hd rfl rfl _

/-- The unequal-colour square for disconnected colours. -/
theorem intertwinerHom_square_ne_zero (l r : List I) {i j : I}
    (hij : i ≠ j) (hd : D.d i j = 0) :
    intertwinerHom D Sc l r i j ≫ intertwinerHom D Sc l r j i =
      (Sc.t i j : k) • 𝟙 _ := by
  rw [intertwinerHom_of_ne D Sc l r hij,
    intertwinerHom_of_ne D Sc l r (Ne.symm hij), cl_comp]
  exact crossSq_zero_gen D Sc l r hij hd rfl rfl _

/-- Polynomial local norm at the source word of an adjacent intertwiner. -/
def intertwinerSquare (l r : List I) (i j : I) :
    End ((pres D Sc).obj (ob D (l ++ [i, j] ++ r))) :=
  let u := dotE D Sc (l ++ [i, j] ++ r) l.length
  let v := dotE D Sc (l ++ [i, j] ++ r) (l.length + 1)
  if i = j then
    if D.parity i = 1 then -((v ^ 2 - u ^ 2) ^ 2 * (u ^ 2 + v ^ 2))
    else -((v - u) ^ 2)
  else if D.d i j = 0 then (Sc.t i j : k) • 𝟙 _
  else qLeft u v (D.dn i j) (D.dn j i) (Sc.t i j : k) (Sc.t j i : k) (Sc.s i j)

/-- The local square in all parity and Cartan cases. -/
theorem intertwinerHom_comp_reverse (l r : List I) (i j : I) :
    intertwinerHom D Sc l r i j ≫ intertwinerHom D Sc l r j i =
      intertwinerSquare D Sc l r i j := by
  by_cases hij : i = j
  · subst j
    by_cases hp : D.parity i = 1
    · simpa only [intertwinerSquare, ite_true, hp] using
        intertwinerHom_square_odd D Sc l r i hp
    · simpa only [intertwinerSquare, ite_true, hp, ite_false] using
        intertwinerHom_square_even D Sc l r i (parity_eq_zero_of_ne_one hp)
  · by_cases hd : D.d i j = 0
    · simpa only [intertwinerSquare, hij, hd, ite_false, ite_true] using
        intertwinerHom_square_ne_zero D Sc l r hij hd
    · simpa only [intertwinerSquare, hij, hd, ite_false] using
        intertwinerHom_square_ne D Sc l r hij hd

/-- The norm of the empty chain is the identity on the append word. -/
theorem reverseMoveHom_comp_moveHom_nil (i : I) (l : List I) :
    reverseMoveHom D Sc i l [] ≫ moveHom D Sc i l [] = 𝟙 _ := by
  simp [reverseMoveHom, moveHom]

/-- Remove the adjacent pair in the append-end norm. The local factor is at the
swapped word `(l,j,i,ν)`, as required by the order of categorical composition. -/
theorem reverseMoveHom_comp_moveHom_cons (i j : I) (l ν : List I) :
    reverseMoveHom D Sc i l (j :: ν) ≫ moveHom D Sc i l (j :: ν) =
      eqToHom (congrArg (fun t => (pres D Sc).obj (ob D t))
        (show l ++ (j :: ν) ++ [i] = (l ++ [j]) ++ ν ++ [i] by simp)) ≫
      reverseMoveHom D Sc i (l ++ [j]) ν ≫
      eqToHom (congrArg (fun t => (pres D Sc).obj (ob D t))
        (show (l ++ [j]) ++ i :: ν = l ++ [j, i] ++ ν by simp)) ≫
      intertwinerSquare D Sc l ν j i ≫
      eqToHom (congrArg (fun t => (pres D Sc).obj (ob D t))
        (show l ++ [j, i] ++ ν = (l ++ [j]) ++ i :: ν by simp)) ≫
      moveHom D Sc i (l ++ [j]) ν ≫
      eqToHom (congrArg (fun t => (pres D Sc).obj (ob D t))
        (show (l ++ [j]) ++ ν ++ [i] = l ++ (j :: ν) ++ [i] by simp)) := by
  simp only [reverseMoveHom, moveHom, Category.assoc]
  simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [← Category.assoc (intertwinerHom D Sc l ν j i),
    intertwinerHom_comp_reverse]

end OddMath.QuiverHecke
end

end

section

/-!
# Endpoint polynomials for reverse moving chains

The independently defined append-end norm factors in
`DeformedBoundaryDivision.md` §2. The headline theorem
`reverseMoveHom_comp_moveHom_eq_endpointNorm` identifies the actual chain
composite, supplying the affine polynomial identity for quotient regularity.
-/

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams SignedNilHecke IntertwinerMeet
open scoped Classical

universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k)

/-- One endpoint norm factor, in the order old strand, moving strand.
This definition involves only dots, not either moving chain. -/
def endpointNormFactor {B : Type*} [Ring B] [Algebra k B]
    (j i : I) (u v : B) : B :=
  if j = i then
    if D.parity j = 1 then -((v ^ 2 - u ^ 2) ^ 2 * (u ^ 2 + v ^ 2))
    else -((v - u) ^ 2)
  else if D.d j i = 0 then algebraMap k B (Sc.t j i : k)
  else qLeft u v (D.dn j i) (D.dn i j) (Sc.t j i : k) (Sc.t i j : k) (Sc.s j i)

/-- An ordered product evaluated in one fixed affine word. No intertwiner occurs
in this definition; the recursion just increments the old-strand dot position. -/
def endpointNormAux (i : I) (w : List I) (moving : ℕ) :
    ℕ → List I → End ((pres D Sc).obj (ob D w))
  | _, [] => 1
  | old, j :: ν => endpointNormFactor D Sc j i (dotE D Sc w old)
      (dotE D Sc w moving) * endpointNormAux i w moving (old + 1) ν

/-- The independent ordered endpoint polynomial. The first encountered factor
is on the left in the endomorphism ring, hence last in categorical composition. -/
def endpointNorm (i : I) (l ν : List I) :
    End ((pres D Sc).obj (ob D (l ++ ν ++ [i]))) :=
  endpointNormAux D Sc i (l ++ ν ++ [i]) (l.length + ν.length) l.length ν

/-- The independent polynomial definition agrees with the adjacent local square. -/
theorem endpointNormFactor_local (l r : List I) (j i : I) :
    endpointNormFactor D Sc j i
      (dotE D Sc (l ++ [j, i] ++ r) l.length)
      (dotE D Sc (l ++ [j, i] ++ r) (l.length + 1)) =
      intertwinerSquare D Sc l r j i := by
  simp only [endpointNormFactor, intertwinerSquare, Algebra.algebraMap_eq_smul_one,
    End.one_def]

@[simp] theorem endpointNorm_nil (i : I) (l : List I) :
    endpointNorm D Sc i l [] = 1 := by simp [endpointNorm, endpointNormAux]

/-- The zero-length norm is the empty ordered polynomial. -/
theorem reverseMoveHom_comp_moveHom_eq_endpointNorm_nil (i : I) (l : List I) :
    reverseMoveHom D Sc i l [] ≫ moveHom D Sc i l [] =
      endpointNorm D Sc i l [] := by
  simpa using reverseMoveHom_comp_moveHom_nil D Sc i l

private theorem norm_comp_sub {C : Type*} [Category C] [Preadditive C]
    {A B : C} (g : A ⟶ B) (a b : End B) :
    g ≫ (a - b : End B) = g ≫ a - g ≫ b := Preadditive.comp_sub _ _ _

private theorem norm_sub_comp {C : Type*} [Category C] [Preadditive C]
    {A B : C} (g : A ⟶ B) (a b : End A) :
    (a - b : End A) ≫ g = a ≫ g - b ≫ g := Preadditive.sub_comp _ _ _

private theorem norm_comp_neg {C : Type*} [Category C] [Preadditive C]
    {A B : C} (g : A ⟶ B) (a : End B) :
    g ≫ (-a : End B) = -(g ≫ a) := Preadditive.comp_neg _ _

private theorem norm_neg_comp {C : Type*} [Category C] [Preadditive C]
    {A B : C} (g : A ⟶ B) (a : End A) :
    (-a : End A) ≫ g = -(a ≫ g) := Preadditive.neg_comp _ _

/-- Polynomial transport requires no inverse to the intertwiner. The parity support
of `Q` and the even powers in the repeated-colour factors remove all signs. -/
theorem comp_endpointNormFactor {A B : (pres D Sc).Presented} (g : A ⟶ B)
    (u' v' : End A) (u v : End B) (j i : I) (ea eb : k)
    (hu : g ≫ u = ea • (u' ≫ g)) (hv : g ≫ v = eb • (v' ≫ g))
    (hea : ∀ n : ℕ, (n : ZMod 2) * D.parity j = 0 → ea ^ n = 1)
    (heb : ∀ n : ℕ, (n : ZMod 2) * D.parity i = 0 → eb ^ n = 1) :
    g ≫ endpointNormFactor D Sc (B := End B) j i u v =
      endpointNormFactor D Sc (B := End A) j i u' v' ≫ g := by
  by_cases hji : j = i
  · subst j
    by_cases hp : D.parity i = 1
    · have hu2 : g ≫ (u ^ 2 : End B) = (u' ^ 2 : End A) ≫ g := by
        simpa only [hea 2 (by rw [show ((2 : ℕ) : ZMod 2) = 0 from rfl, zero_mul]), one_smul] using
          comp_pow_of_signed g u' u ea hu 2
      have hv2 : g ≫ (v ^ 2 : End B) = (v' ^ 2 : End A) ≫ g := by
        simpa only [heb 2 (by rw [show ((2 : ℕ) : ZMod 2) = 0 from rfl, zero_mul]), one_smul] using
          comp_pow_of_signed g v' v eb hv 2
      have hsub : g ≫ (v ^ 2 - u ^ 2 : End B) =
          (1 : k) • ((v' ^ 2 - u' ^ 2 : End A) ≫ g) := by
        simp only [one_smul, norm_comp_sub, norm_sub_comp, hu2, hv2]
      have hadd : g ≫ (u ^ 2 + v ^ 2 : End B) =
          (1 : k) • ((u' ^ 2 + v' ^ 2 : End A) ≫ g) := by
        simp only [one_smul, comp_end_add, end_add_comp, hu2, hv2]
      have h := comp_monomial_of_signed g (v' ^ 2 - u' ^ 2) (u' ^ 2 + v' ^ 2)
        (v ^ 2 - u ^ 2) (u ^ 2 + v ^ 2) 1 1 hsub hadd 2 1
      simpa only [endpointNormFactor, ite_true, hp, norm_comp_neg,
        norm_neg_comp, one_pow, one_mul, one_smul, pow_one] using congrArg Neg.neg h
    · have hp0 := parity_eq_zero_of_ne_one hp
      have hea1 : ea = 1 := by simpa using hea 1 (by rw [hp0, mul_zero])
      have heb1 : eb = 1 := by simpa using heb 1 (by rw [hp0, mul_zero])
      have hsub : g ≫ (v - u : End B) = (1 : k) • ((v' - u' : End A) ≫ g) := by
        simp only [one_smul, norm_comp_sub, norm_sub_comp,
          hu, hv, hea1, heb1]
      have h := comp_pow_of_signed g (v' - u') (v - u) 1 hsub 2
      simpa only [endpointNormFactor, ite_true, hp, ite_false, norm_comp_neg,
        norm_neg_comp, one_pow, one_smul] using congrArg Neg.neg h
  · simpa only [endpointNormFactor, hji, ite_false, qPoly, qLeft,
      Algebra.algebraMap_eq_smul_one] using comp_qPoly D Sc g u' v' u v j i ea eb hu hv hea heb

/-- Transport the first norm factor along the forward tail. This is the concrete
producer: its hypotheses are only the datum, colours and word. -/
theorem endpointNormFactor_comp_moveHom (i j : I) (l ν : List I) :
    endpointNormFactor D Sc (B := End ((pres D Sc).obj (ob D ((l ++ [j]) ++ i :: ν)))) j i
      (dotE D Sc ((l ++ [j]) ++ i :: ν) l.length)
      (dotE D Sc ((l ++ [j]) ++ i :: ν) (l ++ [j]).length) ≫
        moveHom D Sc i (l ++ [j]) ν =
    moveHom D Sc i (l ++ [j]) ν ≫
      endpointNormFactor D Sc (B := End ((pres D Sc).obj (ob D ((l ++ [j]) ++ ν ++ [i])))) j i
        (dotE D Sc ((l ++ [j]) ++ ν ++ [i]) l.length)
        (dotE D Sc ((l ++ [j]) ++ ν ++ [i]) ((l ++ [j]).length + ν.length)) := by
  symm
  apply comp_endpointNormFactor D Sc _ _ _ _ _ j i
    (SKM.zsign k (D.parity j * (D.parity i * wordSumParity D ν)))
    (SKM.zsign k (D.parity i * wordSumParity D ν))
  · have h := dot_left_comp_moveHom D Sc i j l ν (l ++ [j]) [] (by simp)
    have h' := congrArg (SKM.zsign k (D.parity j * (D.parity i * wordSumParity D ν)) • ·) h
    simpa only [smul_smul, zsign_mul_self, one_smul] using h'.symm
  · have h := dot_comp_moveHom D Sc i (l ++ [j]) ν
    have h' := congrArg (SKM.zsign k (D.parity i * wordSumParity D ν) • ·) h
    simpa only [smul_smul, zsign_mul_self, one_smul] using h'.symm
  · intro n hn
    apply zsign_pow_eq_one
    rw [← mul_assoc, hn, zero_mul]
  · intro n hn
    apply zsign_pow_eq_one
    rw [← mul_assoc, hn, zero_mul]

private theorem normFactor_conj (i j : I) {w w' : List I} (h : w = w') (a b : ℕ) :
    eqToHom (congrArg (fun t => (pres D Sc).obj (ob D t)) h) ≫
      endpointNormFactor D Sc (B := End ((pres D Sc).obj (ob D w'))) j i
        (dotE D Sc w' a) (dotE D Sc w' b) ≫
      eqToHom (congrArg (fun t => (pres D Sc).obj (ob D t)) h.symm) =
    endpointNormFactor D Sc j i (dotE D Sc w a) (dotE D Sc w b) := by
  subst w'
  simp

private theorem normFactor_comp_eqToHom (i j : I) {w w' : List I} (h : w = w')
    (a b : ℕ) :
    endpointNormFactor D Sc (B := End ((pres D Sc).obj (ob D w))) j i
        (dotE D Sc w a) (dotE D Sc w b) ≫
      eqToHom (congrArg (fun t => (pres D Sc).obj (ob D t)) h) =
    eqToHom (congrArg (fun t => (pres D Sc).obj (ob D t)) h) ≫
      endpointNormFactor D Sc (B := End ((pres D Sc).obj (ob D w'))) j i
        (dotE D Sc w' a) (dotE D Sc w' b) := by
  subst w'
  simp

private theorem normAux_conj (i : I) {w w' : List I} (h : w = w')
    (moving old : ℕ) (ν : List I) :
    eqToHom (congrArg (fun t => (pres D Sc).obj (ob D t)) h) ≫
      endpointNormAux D Sc i w' moving old ν ≫
      eqToHom (congrArg (fun t => (pres D Sc).obj (ob D t)) h.symm) =
    endpointNormAux D Sc i w moving old ν := by
  subst w'
  simp

/-- The affine append-end norm of an arbitrary chain is its independently defined
ordered endpoint polynomial. No injectivity or assumed square identity is used. -/
theorem reverseMoveHom_comp_moveHom_eq_endpointNorm (i : I) (l ν : List I) :
    reverseMoveHom D Sc i l ν ≫ moveHom D Sc i l ν = endpointNorm D Sc i l ν := by
  induction ν generalizing l with
  | nil => exact reverseMoveHom_comp_moveHom_eq_endpointNorm_nil D Sc i l
  | cons j ν ih =>
    have hloc := normFactor_conj D Sc i j
      (show (l ++ [j]) ++ i :: ν = l ++ [j, i] ++ ν by simp) l.length (l.length + 1)
    rw [endpointNormFactor_local] at hloc
    have hslide := endpointNormFactor_comp_moveHom D Sc i j l ν
    simp only [List.length_append, List.length_singleton] at hslide
    rw [reverseMoveHom_comp_moveHom_cons]
    rw [reassoc_of% hloc, reassoc_of% hslide]
    rw [← Category.assoc (reverseMoveHom D Sc i (l ++ [j]) ν), ih]
    rw [normFactor_comp_eqToHom]
    simp only [endpointNorm, List.length_append, List.length_singleton]
    rw [reassoc_of% normAux_conj]
    simp only [endpointNormAux, List.length_cons, End.mul_def]
    simp only [Nat.add_assoc, Nat.add_comm 1 ν.length]
    all_goals simp

end OddMath.QuiverHecke
end

end

section

/-!
# Reverse all-equal intertwiner braid

The reverse-product form of Kang–Kashiwara–Oh Lemma 8.3 for the variants
from (8.8), in an arbitrary signed nilHecke block. Passing to the opposite
ring reverses the braid identity; the two-strand variants are op-invariant.
The categorical specialization includes both parities and arbitrary contexts.
-/

namespace OddMath.QuiverHecke.SignedNilHecke
variable {B : Type*} [Ring B]

/-- Reversing products preserves the signed nilHecke relations. -/
theorem IsSignedNilHeckeFamily.op {ε : ℤˣ} {s n : ℕ} {X T : ℕ → B}
    (hF : IsSignedNilHeckeFamily ε s n X T) :
    IsSignedNilHeckeFamily ε s n (fun j => MulOpposite.op (X j))
      (fun j => MulOpposite.op (T j)) where
  x_comm a b ha hb hc hd he := by
    apply MulOpposite.unop_injective
    simpa only [MulOpposite.unop_mul, MulOpposite.unop_smul, MulOpposite.unop_op] using
      hF.x_comm b a hc hd ha hb he.symm
  x_t_comm a j ha hb hc hd he hf := by
    apply MulOpposite.unop_injective
    simp only [MulOpposite.unop_mul, MulOpposite.unop_smul, MulOpposite.unop_op]
    rw [hF.x_t_comm a j ha hb hc hd he hf, eps_smul_eps_smul]
  t_comm j l ha hb hc := by
    apply MulOpposite.unop_injective
    simp only [MulOpposite.unop_mul, MulOpposite.unop_smul, MulOpposite.unop_op]
    rw [hF.t_comm j l ha hb hc, eps_smul_eps_smul]
  t_sq j ha hb := by
    apply MulOpposite.unop_injective
    simpa using hF.t_sq j ha hb
  braid j ha hb := by
    apply MulOpposite.unop_injective
    simpa only [MulOpposite.unop_mul, MulOpposite.unop_op, ← mul_assoc] using hF.braid j ha hb
  t_x j ha hb := by
    apply MulOpposite.unop_injective
    simpa only [MulOpposite.unop_sub, MulOpposite.unop_smul,
      MulOpposite.unop_mul, MulOpposite.unop_op, MulOpposite.unop_one] using hF.x_t j ha hb
  x_t j ha hb := by
    apply MulOpposite.unop_injective
    simpa only [MulOpposite.unop_sub, MulOpposite.unop_smul,
      MulOpposite.unop_mul, MulOpposite.unop_op, MulOpposite.unop_one] using hF.t_x j ha hb

/-- The odd variant is unchanged by reversing products. -/
theorem OddTwo.unop_element {u v T : B} (h : OddTwo u v T) :
    MulOpposite.unop (OddNilHecke.Intertwiner.element
      (MulOpposite.op u) (MulOpposite.op v) (MulOpposite.op T)) =
      OddNilHecke.Intertwiner.element u v T := by
  simp only [OddNilHecke.Intertwiner.element, OddNilHecke.Intertwiner.squareDiff,
    MulOpposite.unop_mul, MulOpposite.unop_sub, MulOpposite.unop_op,
    pow_two, mul_sub, sub_mul, mul_assoc, h.tu', h.tv', h.vu, h.vu',
    mul_one, one_mul, mul_neg, neg_mul, neg_neg]
  noncomm_ring

/-- The even variant is unchanged by reversing products. -/
theorem EvenTwo.unop_gEven {u v T : B} (h : EvenTwo u v T) :
    MulOpposite.unop (gEven (MulOpposite.op u) (MulOpposite.op v) (MulOpposite.op T)) =
      gEven u v T := by
  simp only [gEven, phiEven, MulOpposite.unop_mul, MulOpposite.unop_sub,
    MulOpposite.unop_add, MulOpposite.unop_op,
    mul_add, add_mul, mul_sub, sub_mul, mul_assoc, h.tu', h.tv', h.vu,
    mul_one, one_mul]
  noncomm_ring

variable {s n : ℕ} {X T : ℕ → B}

/-- The reverse braid identity for the odd variants. -/
theorem IsSignedNilHeckeFamily.reverse_braid_element
    (hF : IsSignedNilHeckeFamily (-1) s n X T) {j : ℕ}
    (h₁ : s ≤ j) (h₂ : j + 2 < s + n) :
    OddNilHecke.Intertwiner.element (X j) (X (j + 1)) (T j) *
        OddNilHecke.Intertwiner.element (X (j + 1)) (X (j + 2)) (T (j + 1)) * T j =
      T (j + 1) * (OddNilHecke.Intertwiner.element (X j) (X (j + 1)) (T j) *
        OddNilHecke.Intertwiner.element (X (j + 1)) (X (j + 2)) (T (j + 1))) := by
  have h := congrArg MulOpposite.unop (hF.op.braid_element h₁ h₂)
  simpa only [MulOpposite.unop_mul, MulOpposite.unop_op,
    (hF.oddTwo h₁ (by omega)).unop_element,
    (hF.oddTwo (j := j + 1) (by omega) (by omega)).unop_element] using h

/-- The reverse braid identity for the even variants. -/
theorem IsSignedNilHeckeFamily.reverse_braid_gEven
    (hF : IsSignedNilHeckeFamily 1 s n X T) {j : ℕ}
    (h₁ : s ≤ j) (h₂ : j + 2 < s + n) :
    gEven (X j) (X (j + 1)) (T j) *
        gEven (X (j + 1)) (X (j + 2)) (T (j + 1)) * T j =
      T (j + 1) * (gEven (X j) (X (j + 1)) (T j) *
        gEven (X (j + 1)) (X (j + 2)) (T (j + 1))) := by
  have h := congrArg MulOpposite.unop (hF.op.braid_gEven h₁ h₂)
  simpa only [MulOpposite.unop_mul, MulOpposite.unop_op,
    (hF.evenTwo h₁ (by omega)).unop_gEven,
    (hF.evenTwo (j := j + 1) (by omega) (by omega)).unop_gEven] using h

end OddMath.QuiverHecke.SignedNilHecke

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams SignedNilHecke
variable {I X : Type*} [AddCommGroup X] (D : SKM.Datum I X)
  {k : Type*} [CommRing k] (Sc : SKM.Scalars D k)

/-- Reverse chronological all-equal braid, in arbitrary prefix and suffix contexts.
This reverses products using the opposite signed nilHecke family, rather than
merely taking the symmetry of the forward meet identity. -/
theorem cross_comp_sameIntertwiner_sameIntertwiner (l v : List I) (i : I) :
    crossE D Sc (l ++ [i, i, i] ++ v) l.length ≫
      sameIntertwiner D Sc (l ++ [i, i, i] ++ v) (l.length + 1) i ≫
        sameIntertwiner D Sc (l ++ [i, i, i] ++ v) l.length i =
    sameIntertwiner D Sc (l ++ [i, i, i] ++ v) (l.length + 1) i ≫
      sameIntertwiner D Sc (l ++ [i, i, i] ++ v) l.length i ≫
        crossE D Sc (l ++ [i, i, i] ++ v) (l.length + 1) := by
  have hF : IsSignedNilHeckeFamily (zunit (D.parity i)) l.length 3
      (dotE D Sc (l ++ [i, i, i] ++ v)) (crossE D Sc (l ++ [i, i, i] ++ v)) :=
    isSignedNilHeckeFamily_block D Sc l v i 3
  rw [← Category.assoc, ← Category.assoc, ← End.mul_def, ← End.mul_def,
    ← End.mul_def, ← End.mul_def]
  by_cases hp : D.parity i = 1
  · rw [hp, show zunit (1 : ZMod 2) = -1 by simp [zunit]] at hF
    simp only [sameIntertwiner, hp, ite_true]
    simpa only [mul_assoc] using hF.reverse_braid_element (j := l.length) le_rfl (by omega)
  · have hp0 := parity_eq_zero_of_ne_one hp
    rw [hp0, show zunit (0 : ZMod 2) = 1 by simp [zunit]] at hF
    simp only [sameIntertwiner, hp, ite_false]
    simpa only [mul_assoc] using hF.reverse_braid_gEven (j := l.length) le_rfl (by omega)

end OddMath.QuiverHecke
end

end

section

/-!
# Reverse three-strand intertwiner meet

The reverse chronological form `ψ₀ g₁ g₀ = g₁ g₀ ψ₁` of the intertwiner
meet in Kang–Kashiwara–Oh Lemma 8.3, with arbitrary surrounding words and
all colour coincidences. The factors are the concrete `intertwinerHom`.
The single-colour case uses the opposite-ring braid from `ReverseIntertwinerEqual`;
the adjacent equal-colour case transports both dots and the crossing through
two unequal-colour crossings. Only the palindromic case uses symmetry of the
forward meet. The pair-chain corollary has no colour restrictions.
-/

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams SignedNilHecke
open SKM (zsign)
variable {I X : Type*} [AddCommGroup X] (D : SKM.Datum I X)
  {k : Type*} [CommRing k] (Sc : SKM.Scalars D k)
namespace ReverseIntertwinerMeet

def g0 (l v : List I) (a b c : I) :
    (pres D Sc).obj (ob D (l ++ a :: b :: c :: v)) ⟶
      (pres D Sc).obj (ob D (l ++ b :: a :: c :: v)) :=
  eqToHom (by simp) ≫ intertwinerHom D Sc l (c :: v) a b ≫ eqToHom (by simp)
def g1 (l v : List I) (a b c : I) :
    (pres D Sc).obj (ob D (l ++ a :: b :: c :: v)) ⟶
      (pres D Sc).obj (ob D (l ++ a :: c :: b :: v)) :=
  eqToHom (by simp) ≫ intertwinerHom D Sc (l ++ [a]) v b c ≫ eqToHom (by simp)
def p0 (l v : List I) (a b c : I) :=
  cl D Sc (l ++ a :: b :: c :: v) (l ++ b :: a :: c :: v) [.cross l.length]
    (sChain_ofShape' l (c :: v) (.cross a b) (by simp [Shape.dom])
      (by simp [Shape.cod]) rfl)
def p1 (l v : List I) (a b c : I) :=
  cl D Sc (l ++ a :: b :: c :: v) (l ++ a :: c :: b :: v)
    [.cross (l.length + 1)] (sChain_cross_succ l v a b c)

theorem g0_ne (l v : List I) {a b : I} (c : I) (h : a ≠ b) :
    g0 D Sc l v a b c = p0 D Sc l v a b c := by
  unfold g0 p0
  rw [intertwinerHom_of_ne D Sc _ _ h, eqToHom_comp_cl_assoc, cl_comp_eqToHom]
  all_goals simp

theorem g1_ne (l v : List I) (a : I) {b c : I} (h : b ≠ c) :
    g1 D Sc l v a b c = p1 D Sc l v a b c := by
  unfold g1 p1
  rw [intertwinerHom_of_ne D Sc _ _ h, eqToHom_comp_cl_assoc, cl_comp_eqToHom]
  all_goals simp

theorem g0_self (l v : List I) (i c : I) :
    g0 D Sc l v i i c = sameIntertwiner D Sc (l ++ i :: i :: c :: v) l.length i := by
  unfold g0
  rw [intertwinerHom_self, sameIntertwiner_congr D Sc
    (w := l ++ i :: i :: c :: v) (by simp) rfl]
  simp

theorem g1_self (l v : List I) (a i : I) :
    g1 D Sc l v a i i = sameIntertwiner D Sc (l ++ a :: i :: i :: v) (l.length + 1) i := by
  unfold g1
  rw [intertwinerHom_self, sameIntertwiner_congr D Sc
    (w := l ++ a :: i :: i :: v) (a := l.length + 1) (by simp) (by simp)]
  simp
end ReverseIntertwinerMeet
open ReverseIntertwinerMeet
/-- The chronological reverse meet `ψ₀ g₁ g₀`, with arbitrary surrounding words. -/
def reverseMeetLeft (l v : List I) (i j c : I) :
    (pres D Sc).obj (ob D (l ++ j :: c :: i :: v)) ⟶
      (pres D Sc).obj (ob D (l ++ i :: c :: j :: v)) :=
  p0 D Sc l v j c i ≫ g1 D Sc l v c j i ≫ g0 D Sc l v c i j
/-- The chronological reverse meet `g₁ g₀ ψ₁`, with arbitrary surrounding words. -/
def reverseMeetRight (l v : List I) (i j c : I) :
    (pres D Sc).obj (ob D (l ++ j :: c :: i :: v)) ⟶
      (pres D Sc).obj (ob D (l ++ i :: c :: j :: v)) :=
  g1 D Sc l v j c i ≫ g0 D Sc l v j i c ≫ p1 D Sc l v i j c

/-- The reverse meet when neither old colour is the moving colour. -/
theorem reverseMeetLeft_eq_ne (l v : List I) {i j c : I} (hji : j ≠ i) (hci : c ≠ i) :
    reverseMeetLeft D Sc l v i j c = reverseMeetRight D Sc l v i j c := by
  simp only [reverseMeetLeft, reverseMeetRight, g0_ne D Sc _ _ _ hji,
    g0_ne D Sc _ _ _ hci, g1_ne D Sc _ _ _ hji, g1_ne D Sc _ _ _ hci, p0, p1]
  rw [cl_comp, cl_comp, cl_comp, cl_comp]
  symm
  refine braid_ne_gen D Sc l v j c i (fun h => hji h.1) ?_ ?_ rfl rfl _ _ <;> simp

/-- The reverse meet in a single-colour block. -/
theorem reverseMeetLeft_eq_self (l v : List I) (i : I) :
    reverseMeetLeft D Sc l v i i i = reverseMeetRight D Sc l v i i i := by
  simp only [reverseMeetLeft, reverseMeetRight, g0_self, g1_self, p0, p1, ← crossE_eq_cl]
  have h := cross_comp_sameIntertwiner_sameIntertwiner D Sc l v i
  have hw : l ++ [i, i, i] ++ v = l ++ i :: i :: i :: v := by simp
  rw [hw] at h
  exact h

/-- The palindromic reverse meet, with its two outer colours equal. -/
theorem reverseMeetLeft_eq_iji (l v : List I) {i c : I} (hic : i ≠ c) :
    reverseMeetLeft D Sc l v i i c = reverseMeetRight D Sc l v i i c := by
  have h := meetLeft_eq_meetRight_iji D Sc l v hic
  rw [IntertwinerMeet.meetLeft_iji D Sc l v hic,
    IntertwinerMeet.meetRight_iji D Sc l v hic] at h
  simp only [← Category.assoc] at h
  rw [cancel_mono] at h
  simpa only [reverseMeetLeft, reverseMeetRight, g1_self, g0_self, Category.assoc,
    g0_ne D Sc _ _ _ hic.symm, g1_ne D Sc _ _ _ hic.symm, p0, p1] using h.symm

/-- Transport the same-colour variant through the two crossings from `j,i,i` to `i,i,j`. -/
theorem reverse_meet_core (l v : List I) {i j : I} (hij : i ≠ j) :
    sameIntertwiner D Sc (l ++ j :: i :: i :: v) (l.length + 1) i ≫
      (p0 D Sc l v j i i ≫ p1 D Sc l v i j i) =
    (p0 D Sc l v j i i ≫ p1 D Sc l v i j i) ≫
      sameIntertwiner D Sc (l ++ i :: i :: j :: v) l.length i := by
  have hu : dotE D Sc (l ++ j :: i :: i :: v) (l.length + 1) ≫
      (p0 D Sc l v j i i ≫ p1 D Sc l v i j i) =
      (p0 D Sc l v j i i ≫ p1 D Sc l v i j i) ≫
        dotE D Sc (l ++ i :: i :: j :: v) l.length := by
    unfold p0 p1
    rw [← Category.assoc, IntertwinerMeet.push_u_P1' D Sc l v hij,
      Linear.smul_comp, Category.assoc,
      eq_zsign_smul_symm (IntertwinerMeet.push_P_u D Sc l v (i := i) (j := j)),
      Linear.comp_smul, smul_smul, zsign_mul_self, one_smul, Category.assoc]
  have hv : dotE D Sc (l ++ j :: i :: i :: v) (l.length + 2) ≫
      (p0 D Sc l v j i i ≫ p1 D Sc l v i j i) =
      (p0 D Sc l v j i i ≫ p1 D Sc l v i j i) ≫
        dotE D Sc (l ++ i :: i :: j :: v) (l.length + 1) := by
    unfold p0 p1
    rw [← Category.assoc, IntertwinerMeet.push_v_P1' D Sc l v (i := i) (j := j),
      Linear.smul_comp, Category.assoc,
      eq_zsign_smul_symm (IntertwinerMeet.push_P_v D Sc l v hij),
      Linear.comp_smul, smul_smul, zsign_mul_self, one_smul, Category.assoc]
  have ht : crossE D Sc (l ++ j :: i :: i :: v) (l.length + 1) ≫
      (p0 D Sc l v j i i ≫ p1 D Sc l v i j i) =
      (p0 D Sc l v j i i ≫ p1 D Sc l v i j i) ≫
        crossE D Sc (l ++ i :: i :: j :: v) l.length := by
    rw [crossE_eq_cl D Sc (sChain_cross_succ l v j i i),
      crossE_eq_cl D Sc (sChain_ofShape' l (j :: v) (.cross i i)
        (by simp [Shape.dom]) (by simp [Shape.cod]) rfl)]
    unfold p0 p1
    simp only [cl_comp]
    refine braid_ne_gen D Sc l v j i i (fun h => hij h.1.symm) ?_ ?_ rfl rfl _ _ <;> simp
  have hs := variants_comp_of D Sc (p0 D Sc l v j i i ≫ p1 D Sc l v i j i) 0
    (by simpa only [zsign, zero_ne_one, ite_false, one_smul] using hu)
    (by simpa only [zsign, zero_ne_one, ite_false, one_smul] using hv)
    (by simpa only [zsign, zero_ne_one, ite_false, one_smul] using ht)
  unfold sameIntertwiner
  split_ifs
  · simpa only [zsign, zero_ne_one, ite_false, one_smul] using hs.1
  · simpa only [zsign, zero_ne_one, ite_false, one_smul] using hs.2

/-- The reverse meet when the middle and moving colours coincide. -/
theorem reverseMeetLeft_eq_jii (l v : List I) {i j : I} (hji : j ≠ i) :
    reverseMeetLeft D Sc l v i j i = reverseMeetRight D Sc l v i j i := by
  simp only [reverseMeetLeft, reverseMeetRight, g1_ne D Sc _ _ _ hji,
    g0_ne D Sc _ _ _ hji, g0_self, g1_self]
  simpa only [Category.assoc] using (reverse_meet_core D Sc l v hji.symm).symm

/-- The reverse three-strand meet for arbitrary colours, including every coincidence. -/
theorem reverseMeetLeft_eq_all (l v : List I) (i j c : I) :
    reverseMeetLeft D Sc l v i j c = reverseMeetRight D Sc l v i j c := by
  by_cases hji : j = i
  · subst j
    by_cases hci : c = i
    · subst c
      exact reverseMeetLeft_eq_self D Sc l v i
    · exact reverseMeetLeft_eq_iji D Sc l v (Ne.symm hci)
  · by_cases hci : c = i
    · subst c
      exact reverseMeetLeft_eq_jii D Sc l v hji
    · exact reverseMeetLeft_eq_ne D Sc l v hji hci

end OddMath.QuiverHecke
end

end

section

/-!
# Dot naturality of reverse moving chains

Reverse-direction dot transport for the moving chains of Kang–Kashiwara–Oh.
`dot_mem_comp_reverseMoveHom` supplies the old-dot case required for reverse
old-ideal descent. The crossing theorem below covers only two old strands
which both differ from the moving colour; unrestricted descent is not asserted.
No inverse to an intertwiner is used.
-/
noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams
open SKM (zsign)
variable {I X : Type*} [AddCommGroup X] (D : SKM.Datum I X)
  {k : Type*} [CommRing k] (Sc : SKM.Scalars D k)

/-- A fixed dot strictly to the left of the chain supercommutes with the reverse chain. -/
theorem dot_left_comp_reverseMoveHom (i x : I) (l₁ : List I) (ν : List I) :
    ∀ (l l₂ : List I), l = l₁ ++ [x] ++ l₂ →
      dotE D Sc (l ++ ν ++ [i]) l₁.length ≫ reverseMoveHom D Sc i l ν =
        zsign k (D.parity x * (D.parity i * wordSumParity D ν)) •
          (reverseMoveHom D Sc i l ν ≫ dotE D Sc (l ++ i :: ν) l₁.length) := by
  induction ν with
  | nil =>
    intro l l₂ _
    simp only [reverseMoveHom, wordSumParity, List.map_nil, List.sum_nil, mul_zero]
    rw [show zsign k (0 : ZMod 2) = 1 by simp [zsign], one_smul]
    exact dotE_comp_eqToHom D Sc (by simp) _
  | cons j ν ih =>
    intro l l₂ hl
    subst hl
    simp only [reverseMoveHom]
    rw [← Category.assoc, dotE_comp_eqToHom D Sc
        (show (l₁ ++ [x] ++ l₂) ++ (j :: ν) ++ [i] =
          (l₁ ++ [x] ++ l₂ ++ [j]) ++ ν ++ [i] by simp),
      Category.assoc, ← Category.assoc (dotE D Sc _ _),
      ih (l₁ ++ [x] ++ l₂ ++ [j]) (l₂ ++ [j]) (by simp),
      Linear.smul_comp, Category.assoc, ← Category.assoc (dotE D Sc _ _),
      dotE_comp_eqToHom D Sc
        (show (l₁ ++ [x] ++ l₂ ++ [j]) ++ i :: ν =
          (l₁ ++ [x] ++ l₂) ++ [j, i] ++ ν by simp),
      Category.assoc, ← Category.assoc (dotE D Sc _ _), dot_left_comp_intertwinerHom,
      Linear.smul_comp, Category.assoc,
      dotE_comp_eqToHom D Sc
        (show (l₁ ++ [x] ++ l₂) ++ [i, j] ++ ν =
          (l₁ ++ [x] ++ l₂) ++ i :: j :: ν by simp)]
    simp only [Linear.comp_smul, smul_smul, Category.assoc, wordSumParity, List.map_cons,
      List.sum_cons, mul_add, zsign_add_eq, mul_comm, mul_left_comm]

/-- Every old-strand dot passes through the reverse chain with its full word-parity sign. -/
theorem dot_mem_comp_reverseMoveHom (i x : I) (v : List I) (m : List I) :
    ∀ (l ν : List I), ν = m ++ [x] ++ v →
      dotE D Sc (l ++ ν ++ [i]) (l.length + m.length) ≫ reverseMoveHom D Sc i l ν =
        zsign k (D.parity x * (D.parity i * wordSumParity D ν)) •
          (reverseMoveHom D Sc i l ν ≫ dotE D Sc (l ++ i :: ν) (l.length + 1 + m.length)) := by
  induction m with
  | nil =>
    intro l ν hν
    obtain rfl : ν = x :: v := by simp [hν]
    simp only [reverseMoveHom, List.length_nil, add_zero]
    rw [← Category.assoc, dotE_comp_eqToHom D Sc
        (show l ++ (x :: v) ++ [i] = (l ++ [x]) ++ v ++ [i] by simp),
      Category.assoc, ← Category.assoc (dotE D Sc _ _),
      dot_left_comp_reverseMoveHom D Sc i x l v (l ++ [x]) [] (by simp),
      Linear.smul_comp, Category.assoc, ← Category.assoc (dotE D Sc _ _),
      dotE_comp_eqToHom D Sc (show (l ++ [x]) ++ i :: v = l ++ [x, i] ++ v by simp),
      Category.assoc, ← Category.assoc (dotE D Sc _ _), dot_comp_intertwinerHom,
      Linear.smul_comp, Category.assoc,
      dotE_comp_eqToHom D Sc (show l ++ [i, x] ++ v = l ++ i :: x :: v by simp)]
    simp only [Linear.comp_smul, smul_smul, Category.assoc, ← zsign_add_eq]
    congr 2
    simp only [wordSumParity, List.map_cons, List.sum_cons]
    linear_combination (-D.parity i) * parity_sq (D.parity x)
  | cons j m ih =>
    intro l ν hν
    obtain rfl : ν = j :: (m ++ [x] ++ v) := by simp [hν]
    simp only [reverseMoveHom]
    rw [← Category.assoc, dotE_comp_eqToHom D Sc
        (show l ++ (j :: (m ++ [x] ++ v)) ++ [i] =
          (l ++ [j]) ++ (m ++ [x] ++ v) ++ [i] by simp),
      Category.assoc,
      show l.length + (j :: m).length = (l ++ [j]).length + m.length by simp; omega,
      ← Category.assoc (dotE D Sc _ _), ih (l ++ [j]) _ rfl,
      Linear.smul_comp, Category.assoc, ← Category.assoc (dotE D Sc _ _),
      dotE_comp_eqToHom D Sc
        (show (l ++ [j]) ++ i :: (m ++ [x] ++ v) = l ++ [j, i] ++ (m ++ [x] ++ v) by simp),
      show (l ++ [j]).length + 1 + m.length = (l ++ [j, i] ++ m).length by simp; omega,
      Category.assoc, ← Category.assoc (dotE D Sc _ _), dot_right_comp_intertwinerHom,
      Linear.smul_comp, Category.assoc,
      dotE_comp_eqToHom D Sc
        (show l ++ [i, j] ++ (m ++ [x] ++ v) = l ++ i :: j :: (m ++ [x] ++ v) by simp),
      show (l ++ [j, i] ++ m).length = l.length + 1 + (j :: m).length by simp; omega]
    simp only [Linear.comp_smul, smul_smul, Category.assoc, wordSumParity, List.map_cons,
      List.sum_cons, mul_add, zsign_add_eq, mul_comm, mul_left_comm]

end OddMath.QuiverHecke
end

end

section

/-!
# Crossing naturality of reverse moving chains

The reverse-direction old-crossing identity associated to Kang–Kashiwara–Oh
Lemma 8.3 and (8.13), for arbitrary surrounding words and all colour coincidences.
The factors are `reverseMoveHom`; no inverse or assumed transport is used.
-/

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams
open SKM (zsign)
variable {I X : Type*} [AddCommGroup X] (D : SKM.Datum I X)
  {k : Type*} [CommRing k] (Sc : SKM.Scalars D k)

/-- A crossing in the fixed prefix supercommutes with a reverse moving chain. -/
theorem cross_left_comp_reverseMoveHom (i x y : I) (l₁ ν : List I) :
    ∀ (L L' l₂ : List I) (hL : L = l₁ ++ [x, y] ++ l₂) (hL' : L' = l₁ ++ [y, x] ++ l₂),
      cl D Sc (L ++ ν ++ [i]) (L' ++ ν ++ [i]) [.cross l₁.length]
          (by simpa only [List.append_assoc] using
            sChain_cross_split (s := ν ++ [i]) hL hL') ≫ reverseMoveHom D Sc i L' ν =
        zsign k (D.parity x * D.parity y * (D.parity i * wordSumParity D ν)) •
          (reverseMoveHom D Sc i L ν ≫
            cl D Sc (L ++ i :: ν) (L' ++ i :: ν) [.cross l₁.length]
              (sChain_cross_split hL hL')) := by
  induction ν with
  | nil =>
    intro L L' l₂ hL hL'
    simp only [reverseMoveHom, wordSumParity, List.map_nil, List.sum_nil, mul_zero]
    rw [show zsign k (0 : ZMod 2) = 1 by simp [zsign], one_smul,
      cl_comp_eqToHom, eqToHom_comp_cl]
    all_goals simp
  | cons j ν ih =>
    intro L L' l₂ hL hL'
    subst hL hL'
    simp only [reverseMoveHom]
    rw [← Category.assoc, cl_comp_eqToHom D Sc _
        (show (l₁ ++ [y, x] ++ l₂) ++ (j :: ν) ++ [i] =
          (l₁ ++ [y, x] ++ l₂ ++ [j]) ++ ν ++ [i] by simp),
      cl_eq_eqToHom_comp D Sc
        (show (l₁ ++ [x, y] ++ l₂) ++ (j :: ν) ++ [i] =
          (l₁ ++ [x, y] ++ l₂ ++ [j]) ++ ν ++ [i] by simp),
      Category.assoc, ← Category.assoc (cl D Sc _ _ _ _),
      ih (l₁ ++ [x, y] ++ l₂ ++ [j]) (l₁ ++ [y, x] ++ l₂ ++ [j]) (l₂ ++ [j])
        (by simp) (by simp),
      Linear.smul_comp, Linear.comp_smul, Category.assoc,
      ← Category.assoc (cl D Sc _ _ _ _), cl_comp_eqToHom D Sc _
        (show (l₁ ++ [y, x] ++ l₂ ++ [j]) ++ i :: ν =
          (l₁ ++ [y, x] ++ l₂) ++ [j, i] ++ ν by simp),
      cl_eq_eqToHom_comp D Sc
        (show (l₁ ++ [x, y] ++ l₂ ++ [j]) ++ i :: ν =
          (l₁ ++ [x, y] ++ l₂) ++ [j, i] ++ ν by simp),
      Category.assoc, ← Category.assoc (cl D Sc _ _ _ _),
      cross_left_comp_intertwinerHom, Linear.smul_comp, Linear.comp_smul,
      Category.assoc, cl_comp_eqToHom]
    simp only [Category.assoc]
    rw [eqToHom_comp_cl]
    · simp only [Linear.comp_smul, smul_smul, ← zsign_add_eq, wordSumParity,
        List.map_cons, List.sum_cons]
      exact congrArg (fun z => zsign k z • _) (by ring)
    all_goals simp

/-- The crossing adjacent to the old-word boundary passes through the reverse chain. -/
theorem cross_comp_reverseMoveHom_base (l v : List I) (i j c : I)
    (h₁ : SChain (l ++ (j :: c :: v) ++ [i])
      (pl (l ++ (j :: c :: v) ++ [i]) [.cross l.length]) (l ++ (c :: j :: v) ++ [i]))
    (h₂ : SChain (l ++ i :: j :: c :: v)
      (pl (l ++ i :: j :: c :: v) [.cross (l.length + 1)]) (l ++ i :: c :: j :: v)) :
    cl D Sc _ _ [.cross l.length] h₁ ≫ reverseMoveHom D Sc i l (c :: j :: v) =
      zsign k (D.parity j * D.parity c * (D.parity i * wordSumParity D v)) •
        (reverseMoveHom D Sc i l (j :: c :: v) ≫
          cl D Sc _ _ [.cross (l.length + 1)] h₂) := by
  have hc := cross_left_comp_reverseMoveHom D Sc i j c l v (l ++ [j] ++ [c])
    (l ++ [c] ++ [j]) [] (by simp) (by simp)
  have hm := reverseMeetLeft_eq_all D Sc l v i j c
  unfold reverseMeetLeft reverseMeetRight ReverseIntertwinerMeet.g0
    ReverseIntertwinerMeet.g1 ReverseIntertwinerMeet.p0 ReverseIntertwinerMeet.p1 at hm
  simp only [Category.assoc, eqToHom_trans_assoc] at hm
  simp only [reverseMoveHom, Category.assoc, eqToHom_trans_assoc]
  rw [cl_comp_eqToHom_assoc, cl_eq_eqToHom_comp D Sc
    (show l ++ (j :: c :: v) ++ [i] = (l ++ [j] ++ [c]) ++ v ++ [i] by simp),
    Category.assoc, reassoc_of% hc]
  simp only [Linear.comp_smul, Linear.smul_comp, Category.assoc]
  congr 1
  have hm' := congrArg (fun f =>
    eqToHom (congrArg (fun s => (pres D Sc).obj (ob D s))
      (show (l ++ [j] ++ [c]) ++ i :: v = l ++ j :: c :: i :: v by simp)) ≫ f) hm
  simp only [eqToHom_trans_assoc] at hm'
  rw [eqToHom_comp_cl_assoc, cl_comp_eqToHom_assoc] at hm'
  · rw [cl_comp_eqToHom_assoc]
    · exact congrArg (fun f => eqToHom _ ≫ reverseMoveHom D Sc i (l ++ [j] ++ [c]) v ≫ f) hm'
    · simp
  all_goals simp

/-- Every old crossing passes through the reverse moving chain, including all colour
coincidences, with the parity of the old strands outside the crossing. -/
theorem cross_comp_reverseMoveHom_all (v : List I) (i j c : I) (m : List I) :
    ∀ l : List I,
      cl D Sc _ _ [.cross (l.length + m.length)] (sChain_mid₂ l m v i j c) ≫
          reverseMoveHom D Sc i l (m ++ c :: j :: v) =
        zsign k (D.parity j * D.parity c * (D.parity i * (wordSumParity D m + wordSumParity D v))) •
          (reverseMoveHom D Sc i l (m ++ j :: c :: v) ≫
            cl D Sc _ _ [.cross (l.length + 1 + m.length)] (sChain_mid₁ l m v i j c)) := by
  induction m with
  | nil =>
    intro l
    have hw : wordSumParity D ([] : List I) = 0 := by simp [wordSumParity]
    rw [hw, zero_add]
    exact cross_comp_reverseMoveHom_base D Sc l v i j c _ _
  | cons x m ih =>
    intro l
    simp only [List.cons_append, reverseMoveHom]
    rw [← Category.assoc, cl_comp_eqToHom D Sc _
        (show l ++ (x :: (m ++ c :: j :: v)) ++ [i] =
          (l ++ [x]) ++ (m ++ c :: j :: v) ++ [i] by simp),
      cl_eq_eqToHom_comp D Sc
        (show l ++ (x :: (m ++ j :: c :: v)) ++ [i] =
          (l ++ [x]) ++ (m ++ j :: c :: v) ++ [i] by simp),
      cl_cross_pos D Sc (p' := (l ++ [x]).length + m.length) (by simp; omega),
      Category.assoc, ← Category.assoc (cl D Sc _ _ _ _), ih (l ++ [x]),
      Linear.smul_comp, Linear.comp_smul, Category.assoc,
      ← Category.assoc (cl D Sc _ _ _ _), cl_comp_eqToHom D Sc _
        (show (l ++ [x]) ++ i :: (m ++ c :: j :: v) = l ++ [x, i] ++ (m ++ c :: j :: v) by simp),
      cl_eq_eqToHom_comp D Sc
        (show (l ++ [x]) ++ i :: (m ++ j :: c :: v) = l ++ [x, i] ++ (m ++ j :: c :: v) by simp),
      cl_cross_pos D Sc (p' := (l ++ [x, i] ++ m).length) (by simp; omega),
      Category.assoc, ← Category.assoc (cl D Sc _ _ _ _), cross_right_comp_intertwinerHom,
      Linear.smul_comp, Linear.comp_smul, Category.assoc, cl_comp_eqToHom]
    simp only [Category.assoc]
    rw [eqToHom_comp_cl, cl_cross_pos D Sc (p := l.length + 1 + (x :: m).length)
      (p' := (l ++ [i, x] ++ m).length) (by simp; omega)]
    · simp only [Linear.comp_smul, smul_smul, ← zsign_add_eq, wordSumParity,
        List.map_cons, List.sum_cons]
      exact congrArg (fun z => zsign k z • _) (by ring)
    all_goals simp

end OddMath.QuiverHecke
end

end

section

/-!
# Reverse moving-chain balance

Reverse old-diagram transport for the moving chains of Kang–Kashiwara–Oh.
The concrete dot and crossing slides extend to positioned words and arbitrary
old morphisms. No inverse of a moving chain is used.
-/
noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams MonoidalCategory
open SKM (zsign)
variable {I X : Type*} [AddCommGroup X] (D : SKM.Datum I X)
  {k : Type*} [CommRing k] (Sc : SKM.Scalars D k)

/-- Reverse transport of a positioned generator, with word-parity invariance. -/
theorem gen_comp_reverseMoveHom (i : I) {ν ν' : List I} (g : PG) (h : SChain ν (pl ν [g]) ν')
    (hfit : Fits ν.length [g]) :
    cl D Sc (ν ++ [i]) (ν' ++ [i]) [g] (sChain_append_one i h hfit) ≫
        reverseMoveHom D Sc i [] ν' =
      zsign k (g.par D ν * (D.parity i * wordSumParity D ν)) •
        (reverseMoveHom D Sc i [] ν ≫ cl D Sc (i :: ν) (i :: ν') ([g].map (PG.shift 1)) (sChain_shift_one i h)) ∧
      wordSumParity D ν' = wordSumParity D ν := by
  obtain ⟨m, s, v, hν, hg, -, -⟩ := exists_split g 0 ν (Nat.zero_le _)
    (by simpa using hfit g (by simp))
  subst hg
  have ht := tgt_eq h
  cases s with
  | dot x =>
    obtain rfl : ν = m ++ x :: v := by simpa [Shape.dom] using hν
    obtain rfl : ν' = m ++ x :: v := by simpa [PG.ofShape, PG.act] using ht.symm
    refine ⟨?_, rfl⟩
    have key : dotE D Sc (m ++ x :: v ++ [i]) ([].length + m.length) ≫
          reverseMoveHom D Sc i [] (m ++ x :: v) =
        zsign k (D.parity x * (D.parity i * wordSumParity D (m ++ x :: v))) •
          (reverseMoveHom D Sc i [] (m ++ x :: v) ≫ dotE D Sc (i :: (m ++ x :: v)) ([].length + 1 + m.length)) :=
      dot_mem_comp_reverseMoveHom D Sc i x v m [] (m ++ x :: v) (by simp)
    rw [cl_congr_gs D Sc (t := m ++ x :: v ++ [i]) (gs' := [.dot ([].length + m.length)])
        (by simp [PG.ofShape]) _ (sChain_dotAny _ _), ← dotE_eq_cl,
      cl_congr_gs D Sc (t := i :: (m ++ x :: v)) (gs' := [.dot ([].length + 1 + m.length)])
        (by simp [PG.ofShape, PG.shift]) _ (sChain_dotAny _ _), ← dotE_eq_cl]
    have hp : PG.par D (m ++ x :: v) (PG.ofShape (Shape.dot x) (0 + m.length)) = D.parity x := by
      simp [PG.par, PG.ofShape]
    rw [hp]
    exact key
  | cross j c =>
    obtain rfl : ν = m ++ j :: c :: v := by simpa [Shape.dom] using hν
    obtain rfl : ν' = m ++ c :: j :: v := by
      simpa [PG.ofShape, PG.act, List.take_append, List.drop_append] using ht.symm
    refine ⟨?_, ?_⟩
    · have key := cross_comp_reverseMoveHom_all D Sc v i j c m []
      simp only [List.nil_append] at key
      rw [cl_congr_gs D Sc (t := m ++ j :: c :: v ++ [i]) (t' := m ++ c :: j :: v ++ [i])
          (gs' := [.cross ([].length + m.length)]) (by simp [PG.ofShape]) _
          (sChain_mid₂ [] m v i j c),
        cl_congr_gs D Sc (t := i :: (m ++ j :: c :: v)) (t' := i :: (m ++ c :: j :: v))
          (gs' := [.cross ([].length + 1 + m.length)])
          (by simp [PG.ofShape, PG.shift, Nat.add_comm]) _ (sChain_mid₁ [] m v i j c)]
      rw [key]
      congr 1
      have hp : PG.par D (m ++ j :: c :: v) (PG.ofShape (Shape.cross j c) (0 + m.length)) =
          D.parity j * D.parity c := by simp [PG.par, PG.ofShape]
      rw [hp]
      simp only [wordSumParity, List.map_append, List.map_cons, List.sum_append, List.sum_cons]
      generalize D.parity i = a
      generalize D.parity j = b
      generalize D.parity c = d
      generalize (List.map D.parity m).sum = e
      generalize (List.map D.parity v).sum = f
      congr 1
      revert a b d e f
      decide
    · simp only [wordSumParity, List.map_append, List.map_cons, List.sum_append, List.sum_cons]
      abel

/-- Reverse transport of every fitting positioned word. -/
theorem cl_comp_reverseMoveHom (i : I) : ∀ {ν ν' : List I} (gs : List PG) (h : SChain ν (pl ν gs) ν')
    (hfit : Fits ν.length gs),
    cl D Sc (ν ++ [i]) (ν' ++ [i]) gs (sChain_append_one i h hfit) ≫
        reverseMoveHom D Sc i [] ν' =
      zsign k (chainParity D ν gs * (D.parity i * wordSumParity D ν)) •
        (reverseMoveHom D Sc i [] ν ≫ cl D Sc (i :: ν) (i :: ν') (gs.map (PG.shift 1)) (sChain_shift_one i h)) ∧
      wordSumParity D ν' = wordSumParity D ν
  | ν, ν', [], h, _ => by
    obtain rfl : ν = ν' := h
    refine ⟨?_, rfl⟩
    simp [cl_nil, zsign]
  | ν, ν', g :: gs, h, hfit => by
    have h₁ : SChain ν (pl ν [g]) (g.act ν) := sChain_pl ν [g]
    have h₂ : SChain (g.act ν) (pl (g.act ν) gs) ν' := by
      have := tgt_eq h
      simpa [← this] using sChain_pl (g.act ν) gs
    have hfit₁ : Fits ν.length [g] := fun g' hg' => hfit g' (by simp_all)
    have hfit₂ : Fits (g.act ν).length gs := by
      rw [length_act]; exact fun g' hg' => hfit g' (by simp [hg'])
    obtain ⟨e₁, p₁⟩ := gen_comp_reverseMoveHom D Sc i g h₁ hfit₁
    obtain ⟨e₂, p₂⟩ := cl_comp_reverseMoveHom i gs h₂ hfit₂
    refine ⟨?_, p₂.trans p₁⟩
    have s₁ : cl D Sc (i :: ν) (i :: ν') ((g :: gs).map (PG.shift 1)) (sChain_shift_one i h) =
        cl D Sc (i :: ν) (i :: g.act ν) ([g].map (PG.shift 1)) (sChain_shift_one i h₁) ≫
          cl D Sc (i :: g.act ν) (i :: ν') (gs.map (PG.shift 1)) (sChain_shift_one i h₂) := by
      rw [cl_comp]; rfl
    have s₂ : cl D Sc (ν ++ [i]) (ν' ++ [i]) (g :: gs) (sChain_append_one i h hfit) =
        cl D Sc (ν ++ [i]) (g.act ν ++ [i]) [g] (sChain_append_one i h₁ hfit₁) ≫
          cl D Sc (g.act ν ++ [i]) (ν' ++ [i]) gs (sChain_append_one i h₂ hfit₂) := by
      rw [cl_comp]; rfl
    rw [s₂, s₁, Category.assoc, e₂, Linear.comp_smul, ← Category.assoc, e₁, Linear.smul_comp,
      smul_smul, Category.assoc, p₁, chainParity_cons, ← zsign_add_eq]
    congr 2
    ring

open Categorification.TypeA

/-- Reverse balance on arbitrary, possibly inhomogeneous, old diagrams. -/
theorem hom_comp_reverseMoveHom (i : I) {t t' : List I}
    (f : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')) :
    (f ▷ (pres D Sc).obj (ob D [i])) ≫ reverseMoveHom D Sc i [] t' =
      reverseMoveHom D Sc i [] t ≫
        ((pres D Sc).obj (ob D [i]) ◁
          Supercategory.twist k (D.parity i * wordSumParity D t) f) := by
  have hf : f ∈ Submodule.span k {f : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t') |
      ∃ l : List ℕ, l.Pairwise (· ≤ ·) ∧ (∀ x ∈ l, x < t.length) ∧
        ∃ w : Equiv.Perm (Fin t.length),
          ∃ h, cl D Sc t t' (l.map PG.dot ++ cw (canWord t.length w)) h = f} := by
    rw [span_normalForms]; trivial
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨l, -, hl, w, h, rfl⟩ := hf
    have hfit := fits_append (fits_dots hl) (fits_cw (validWord_canWord t.length w))
    rw [Supercategory.twist_of_mem _ (cl_mem_chainParity D Sc _ h hfit),
      (MonoidalSupercategory.whiskerLeft_smul (R := k)), Linear.comp_smul,
      cl_whiskerRight D Sc _ h [i] hfit, cl_whiskerLeft]
    have hs : ∀ p : ZMod 2, Supercategory.sign k p = zsign k p := by
      intro p
      rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) p with rfl | rfl <;>
        simp [Supercategory.sign, zsign]
    simpa only [List.singleton_append, List.length_singleton, hs, mul_comm] using
      (cl_comp_reverseMoveHom D Sc i _ h hfit).1
  | zero => simp [MonoidalSupercategory.whiskerLeft_zero (R := k),
      MonoidalSupercategory.zero_whiskerRight (R := k)]
  | add f g _ _ hf hg =>
    simp only [map_add, (MonoidalSupercategory.whiskerLeft_add (R := k)),
      (MonoidalSupercategory.add_whiskerRight (R := k)), Preadditive.add_comp,
      Preadditive.comp_add, hf, hg]
  | smul r f _ hf =>
    simp only [map_smul, (MonoidalSupercategory.whiskerLeft_smul (R := k)),
      (MonoidalSupercategory.smul_whiskerRight (R := k)), Linear.smul_comp,
      Linear.comp_smul, hf]

end OddMath.QuiverHecke
end

end
