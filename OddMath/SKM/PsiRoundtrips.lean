import OddMath.SKM.PsiInverseParameters

/-!
# Double ψ on the original generators

`psiGenerator_parameter_roundtrip` and its reverse-order counterpart cover every
presentation shape at arbitrary weights. The second quotient map uses the
negative square root and the rescaled units `psiInverseCScalars`.

The diamond images are derived from the two inverse-matrix blocks: annihilation,
scalar pairings, and completeness determine the images of the dual entries. The
out-of-range entries are handled by the presentation's zero relations. The
remaining signs are removed by the actual homogeneous Π conjugation, not by an
assumed endpoint twist. No nonzero-weight, field, or characteristic restriction
is imposed.

These are transported generator identities. Extending them to arbitrary
quotient morphisms or a coherent inverse two-functor requires further arguments.
-/

noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Supercategory BicategoryStruct Finset
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D} {hc : Sc.Homogeneous}

/-- The underlying reversed quotient map between signed words. -/
def psiWordReverse (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc) (ν μ : X)
    {s r : List (Letter I)} (hs : wt D μ s = ν) (hr : wt D μ r = ν)
    (x : (pres D Sc).obj (ob D μ s) ⟶ (pres D Sc).obj (ob D μ r)) :
    (pres D Sc).obj (ob D μ r) ⟶ (pres D Sc).obj (ob D μ s) :=
  QPiTwoEnvelope.toHom (SOp.unsop
    (psiMap₂ (sy := sy) (hc := hc) t ht cs (psiWordAt ν μ s hs) (psiWordAt ν μ r hr) x))

@[simp] theorem psiWordReverse_smul (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc) (ν μ : X)
    {s r : List (Letter I)} (hs : wt D μ s = ν) (hr : wt D μ r = ν)
    (a : k) (x : (pres D Sc).obj (ob D μ s) ⟶ (pres D Sc).obj (ob D μ r)) :
    psiWordReverse (sy := sy) (hc := hc) t ht cs ν μ hs hr (a • x) =
      a • psiWordReverse (sy := sy) (hc := hc) t ht cs ν μ hs hr x := by
  unfold psiWordReverse
  rw [map_smul]
  rfl

/-- Computation of the quotient map on every bare generator. -/
theorem psiMap₂_gen (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc)
    (ν μ : X) (g : Shape I) (hs : wt D μ g.dom = ν) :
    psiMap₂ (sy := sy) (hc := hc) t ht cs (psiWordAt ν μ g.dom hs)
      (psiWordAt ν μ g.cod ((g.wt_dom_eq_wt_cod D μ).symm.trans hs))
      (cl D Sc μ g.dom g.cod [([], g, [])]) = psiGen t cs ν μ g hs := by
  rw [cl_of (by simp [SChain]), psiMap₂_diag, psiDiagram_mkD, psiRaw_gen]

/-- The quotient dot computation, without a scalar-only replacement. -/
theorem psiMap₂_dot (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc) (μ : X) (i : I) :
    psiMap₂ (sy := sy) (hc := hc) t ht cs
      (psiWordAt (wt D μ [up i]) μ [up i] rfl) (psiWordAt (wt D μ [up i]) μ [up i] rfl)
      (cl D Sc μ [up i] [up i] (dotsL [] i [] 1)) = psiDot t μ i := by
  exact psiMap₂_gen t ht cs _ μ (.dot i) rfl

private theorem wt_swap (μ : X) (i j : I) :
    wt D μ [up j, up i] = wt D μ [up i, up j] := by
  simp only [wt_cons, wt_nil]
  exact add_left_comm _ _ _

/-- The quotient crossing computation at arbitrary boundaries. -/
theorem psiMap₂_cross (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc)
    (ν μ : X) (i j : I) (h : wt D μ [up i, up j] = ν) :
    psiMap₂ (sy := sy) (hc := hc) t ht cs
      (psiWordAt ν μ [up i, up j] h) (psiWordAt ν μ [up j, up i] ((wt_swap μ i j).trans h))
      (cl D Sc μ [up i, up j] [up j, up i] (crossL [] i j [])) = psiCross t ν μ i j h := by
  exact psiMap₂_gen t ht cs ν μ (.cross i j) h

@[simp] theorem psiWordReverse_dot (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc) (μ : X) (i : I) :
    psiWordReverse (sy := sy) (hc := hc) t ht cs (wt D μ [up i]) μ rfl rfl
      (cl D Sc μ [up i] [up i] (dotsL [] i [] 1)) =
      psiCoeff t (D.parity i) • cl D Sc μ [up i] [up i] (dotsL [] i [] 1) := by
  unfold psiWordReverse
  rw [psiMap₂_dot]
  change psiCoeff t (1 * D.parity i) • _ = _
  rw [one_mul]

@[simp] theorem psiWordReverse_cross (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc)
    (ν μ : X) (i j : I) (hs : wt D μ [up i, up j] = ν)
    (hr : wt D μ [up j, up i] = ν) :
    psiWordReverse (sy := sy) (hc := hc) t ht cs ν μ hs hr
      (cl D Sc μ [up i, up j] [up j, up i] (crossL [] i j [])) =
      psiCoeff t (D.parity i * D.parity j) •
        cl D Sc μ [up j, up i] [up i, up j] (crossL [] j i []) := by
  unfold psiWordReverse
  rw [psiMap₂_cross]
  rfl

/-- Both quotient maps occur in the dot roundtrip. -/
theorem psiDot_parameter_roundtrip (t : k) (ht : t ^ 2 = -1)
    (cs : CScalars Sc) (μ : X) (i : I) :
    psiWordReverse (sy := sy) (hc := hc) (-t) (psi_neg_sq ht) (psiInverseCScalars t ht cs)
      (wt D μ [up i]) μ rfl rfl
      (psiWordReverse (sy := sy) (hc := hc) t ht cs (wt D μ [up i]) μ rfl rfl
        (cl D Sc μ [up i] [up i] (dotsL [] i [] 1))) =
      cl D Sc μ [up i] [up i] (dotsL [] i [] 1) := by
  rw [psiWordReverse_dot, psiWordReverse_smul, psiWordReverse_dot,
    smul_smul, mul_comm, psiCoeff_neg_mul ht, one_smul]

/-- Both quotient maps occur in the crossing roundtrip. -/
theorem psiCross_parameter_roundtrip (t : k) (ht : t ^ 2 = -1)
    (cs : CScalars Sc) (ν μ : X) (i j : I) (hs : wt D μ [up i, up j] = ν)
    (hr : wt D μ [up j, up i] = ν) :
    psiWordReverse (sy := sy) (hc := hc) (-t) (psi_neg_sq ht) (psiInverseCScalars t ht cs)
      ν μ hr hs
      (psiWordReverse (sy := sy) (hc := hc) t ht cs ν μ hs hr
        (cl D Sc μ [up i, up j] [up j, up i] (crossL [] i j []))) =
      cl D Sc μ [up i, up j] [up j, up i] (crossL [] i j []) := by
  rw [psiWordReverse_cross, psiWordReverse_smul, psiWordReverse_cross,
    mul_comm (D.parity j), smul_smul, mul_comm, psiCoeff_neg_mul ht, one_smul]

private theorem homPar_mem {μ : X} {s r : List (Letter I)} {p : ZMod 2}
    {x : (pres D Sc).obj (ob D μ s) ⟶ (pres D Sc).obj (ob D μ r)}
    (hx : x ∈ homPar D Sc μ s r p) :
    x ∈ (pres D Sc).homDeg (Presentation.parityDeg (sig D)) _ _ p := by
  refine Submodule.span_le.mpr ?_ hx
  rintro x ⟨L, hL, hp, rfl⟩
  rw [cl_of hL]
  apply Presentation.diag_mem_homDeg'
  rw [degree_parity_mkD]
  exact hp

/-- The reversed quotient map retains the super-opposite composition sign. -/
theorem psiWordReverse_comp (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc) (ν μ : X)
    {s r q : List (Letter I)} (hs : wt D μ s = ν) (hr : wt D μ r = ν) (hq : wt D μ q = ν)
    {x : (pres D Sc).obj (ob D μ s) ⟶ (pres D Sc).obj (ob D μ r)}
    {y : (pres D Sc).obj (ob D μ r) ⟶ (pres D Sc).obj (ob D μ q)}
    {p z : ZMod 2} (hx : x ∈ homPar D Sc μ s r p) (hy : y ∈ homPar D Sc μ r q z) :
    psiWordReverse (sy := sy) (hc := hc) t ht cs ν μ hs hq (x ≫ y) =
      sign k (p * z) • (psiWordReverse (sy := sy) (hc := hc) t ht cs ν μ hr hq y ≫
        psiWordReverse (sy := sy) (hc := hc) t ht cs ν μ hs hr x) := by
  have E := congrArg (fun z => QPiTwoEnvelope.toHom (SOp.unsop z))
    (psiMap₂_comp (sy := sy) (hc := hc) t ht cs (f := psiWordAt (Sc := Sc) ν μ s hs)
      (g := psiWordAt ν μ r hr) (h := psiWordAt ν μ q hq) x y)
  refine E.trans ?_
  rw [SOp.comp_of_mem
    (f := psiMap₂ (sy := sy) (hc := hc) t ht cs (psiWordAt ν μ s hs) (psiWordAt ν μ r hr) x)
    (g := psiMap₂ (sy := sy) (hc := hc) t ht cs (psiWordAt ν μ r hr) (psiWordAt ν μ q hq) y)
    (psiMap₂_mem_parity (sy := sy) (hc := hc) t ht cs (f := psiWordAt (Sc := Sc) ν μ s hs)
      (g := psiWordAt ν μ r hr) (homPar_mem hx))
    (psiMap₂_mem_parity (sy := sy) (hc := hc) t ht cs (f := psiWordAt (Sc := Sc) ν μ r hr)
      (g := psiWordAt ν μ q hq) (homPar_mem hy))]
  rfl

/-- The quotient image of the derived rightward mixed crossing. -/
theorem psiWordReverse_sigma (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc)
    (ν μ : X) (i j : I) (hs : wt D μ [up j, dn i] = ν)
    (hr : wt D μ [dn i, up j] = ν) :
    psiWordReverse (sy := sy) (hc := hc) t ht cs ν μ hs hr
      (cl D Sc μ [up j, dn i] [dn i, up j] (sigmaL i j)) =
      (psiCoeff t (D.parity i * D.parity j) * sign k (D.parity i * D.parity j * ipar D i μ)) •
        cl D Sc μ [dn i, up j] [up j, dn i] (lcrossL i j) := by
  subst ν
  unfold psiWordReverse
  rw [cl_of (sChain_sigmaL i j), psiMap₂_diag, psiDiagram_mkD,
    psiRaw_eq_primary t cs _ μ _ _ _ _ (primaryLayers_sigmaL i j), psiPrimaryRaw_sigma_eq]
  rfl

/-- The quotient image of the adjoined leftward mixed crossing. -/
theorem psiWordReverse_lcross (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc)
    (ν μ : X) (i j : I) (hs : wt D μ [dn i, up j] = ν)
    (hr : wt D μ [up j, dn i] = ν) :
    psiWordReverse (sy := sy) (hc := hc) t ht cs ν μ hs hr
      (cl D Sc μ [dn i, up j] [up j, dn i] (lcrossL i j)) =
      (psiCoeff t (D.parity i * D.parity j) * sign k (D.parity i * D.parity j * ipar D i μ)) •
        cl D Sc μ [up j, dn i] [dn i, up j] (sigmaL i j) := by
  have E := congrArg (fun z => QPiTwoEnvelope.toHom (SOp.unsop z))
    (psiMap₂_gen (sy := sy) (hc := hc) t ht cs ν μ (.lcross i j) hs)
  refine E.trans ?_
  rw [psiGen, psiRebase_unsop]
  rfl

private theorem coeff_sign_cancel (t : k) (ht : t ^ 2 = -1) (p q : ZMod 2) :
    (psiCoeff t p * sign k q) * (psiCoeff (-t) p * sign k q) = 1 := by
  calc
    _ = (psiCoeff (-t) p * psiCoeff t p) * (sign k q * sign k q) := by ring
    _ = 1 := by rw [psiCoeff_neg_mul ht, sign_mul_self, mul_one]

/-- The leftward mixed crossing returns for equal and distinct colours alike. -/
theorem psiLCross_parameter_roundtrip (t : k) (ht : t ^ 2 = -1)
    (cs : CScalars Sc) (ν μ : X) (i j : I) (hs : wt D μ [dn i, up j] = ν)
    (hr : wt D μ [up j, dn i] = ν) :
    psiWordReverse (sy := sy) (hc := hc) (-t) (psi_neg_sq ht) (psiInverseCScalars t ht cs)
      ν μ hr hs
      (psiWordReverse (sy := sy) (hc := hc) t ht cs ν μ hs hr
        (cl D Sc μ [dn i, up j] [up j, dn i] (lcrossL i j))) =
      cl D Sc μ [dn i, up j] [up j, dn i] (lcrossL i j) := by
  rw [psiWordReverse_lcross, psiWordReverse_smul, psiWordReverse_sigma,
    smul_smul, coeff_sign_cancel t ht, one_smul]

private theorem left_ud (μ : X) (i : I) : wt D μ [up i, dn i] = μ := by simp [wt, sh]
private theorem left_du (μ : X) (i : I) : wt D μ [dn i, up i] = μ := by simp [wt, sh]

private theorem raw_rebase (t : k) (cs : CScalars Sc) (ν ν' μ : X)
    (L : List (LayerData I)) {s r : List (Letter I)}
    (hs : wt D μ s = ν) (hr : wt D μ r = ν) (hL : SChain s L r) (h : ν = ν') :
    psiRaw (sy := sy) (hc := hc) t cs ν' μ L (hs.trans h) (hr.trans h) hL =
      psiRebase h (psiRaw t cs ν μ L hs hr hL) := by subst ν'; rfl

private theorem raw_dots (t : k) (cs : CScalars Sc) (μ : X) (i : I) (n : ℕ) :
    psiRaw (sy := sy) (hc := hc) t cs (wt D μ [up i]) μ (dotsL [] i [] n)
      rfl rfl (sChain_dotsL [] i [] n) = cpow (psiDot t μ i) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [cpow_succ']
    simp only [dotsL, List.replicate_succ, psiRaw, eqToHom_refl, Category.id_comp] at *
    rw [ih]
    congr 1
    simp [psiLayer, psiGen, psiPrimaryGen, psiPlace, Shape.dom, Shape.cod,
      psiWhiskerLeft_nil, psiWhiskerRight_nil]

private theorem raw_dots_left (t : k) (cs : CScalars Sc) (μ : X) (i : I) (n : ℕ) :
    psiRaw (sy := sy) (hc := hc) t cs μ μ (dotsL [] i [dn i] n)
      (left_ud μ i) (left_ud μ i) (sChain_dL i n) = psiSameDotsLeft t μ i n := by
  rw [raw_rebase t cs (wt D μ [up i, dn i]) μ μ _ rfl rfl _ (left_ud μ i)]
  unfold psiSameDotsLeft
  congr 1
  have E := psiRaw_whisk (sy := sy) (hc := hc) t cs
    (wt D μ [up i, dn i]) (wt D (wt D μ [dn i]) [up i]) (wt D μ [dn i]) μ
    [] [dn i] (dotsL [] i [] n) rfl rfl rfl rfl (sChain_dotsL [] i [] n)
  simp only [dotsL, List.map_replicate, whL, List.nil_append, List.append_nil] at E
  simp only [dotsL]
  erw [E]
  rw [show psiRaw (sy := sy) (hc := hc) t cs (wt D (wt D μ [dn i]) [up i])
      (wt D μ [dn i]) (List.replicate n ([], Shape.dot i, [])) rfl rfl _ =
      cpow (psiDot t (wt D μ [dn i]) i) n from raw_dots t cs _ i n]
  simp [psiPlace, psiWhiskerLeft_nil]

private theorem raw_dots_right (t : k) (cs : CScalars Sc) (μ : X) (i : I) (n : ℕ) :
    psiRaw (sy := sy) (hc := hc) t cs μ μ (dotsL [dn i] i [] n)
      (left_du μ i) (left_du μ i) (sChain_dR i n) = psiSameDotsRight t μ i n := by
  have E := psiRaw_whisk (sy := sy) (hc := hc) t cs
    μ (wt D μ [up i]) μ μ [dn i] [] (dotsL [] i [] n)
    (left_du μ i) rfl rfl rfl (sChain_dotsL [] i [] n)
  simp only [dotsL, List.map_replicate, whL, List.append_nil] at E
  simp only [dotsL]
  erw [E]
  rw [show psiRaw (sy := sy) (hc := hc) t cs (wt D μ [up i]) μ
      (List.replicate n ([], Shape.dot i, [])) rfl rfl _ =
      cpow (psiDot t μ i) n from raw_dots t cs μ i n]
  simp [psiSameDotsRight, psiPlace, psiWhiskerRight_nil]
/-- The dot power on the left of the downward strand under the quotient map. -/
theorem psiWordReverse_dotsLeft (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc)
    (μ : X) (i : I) (n : ℕ) :
    psiWordReverse (sy := sy) (hc := hc) t ht cs μ μ (left_ud μ i) (left_ud μ i)
      (cl D Sc μ [up i, dn i] [up i, dn i] (dotsL [] i [dn i] n)) =
      (psiCoeff t (n * D.parity i) * sign k (ipar D i μ * (n * D.parity i))) •
        cl D Sc μ [up i, dn i] [up i, dn i] (dotsL [] i [dn i] n) := by
  unfold psiWordReverse
  conv_lhs => rw [cl_of (sChain_dL i n), psiMap₂_diag, psiDiagram_mkD, raw_dots_left,
    psiSameDotsLeft_raw t ht]
  rfl

/-- The dot power on the right of the downward strand under the quotient map. -/
theorem psiWordReverse_dotsRight (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc)
    (μ : X) (i : I) (n : ℕ) :
    psiWordReverse (sy := sy) (hc := hc) t ht cs μ μ (left_du μ i) (left_du μ i)
      (cl D Sc μ [dn i, up i] [dn i, up i] (dotsL [dn i] i [] n)) =
      (psiCoeff t (n * D.parity i) * sign k (ipar D i μ * (n * D.parity i))) •
        cl D Sc μ [dn i, up i] [dn i, up i] (dotsL [dn i] i [] n) := by
  unfold psiWordReverse
  conv_lhs => rw [cl_of (sChain_dR i n), psiMap₂_diag, psiDiagram_mkD, raw_dots_right,
    psiSameDotsRight_raw t ht]
  rfl

/-- The reversed left cup is computed by the established quotient identity. -/
theorem psiWordReverse_etaP (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc) (μ : X) (i : I) :
    psiWordReverse (sy := sy) (hc := hc) t ht cs μ μ rfl (left_ud μ i) (etaP cs i μ) =
      psiCoeff t (ipar D i μ) • cl D Sc μ [up i, dn i] [] (epsL i 0) := by
  unfold psiWordReverse
  rw [psiMap₂_etaP]
  rfl

/-- The reversed left cap is computed by the established quotient identity. -/
theorem psiWordReverse_epsP (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc) (μ : X) (i : I) :
    psiWordReverse (sy := sy) (hc := hc) t ht cs μ μ (left_du μ i) rfl (epsP cs i μ) =
      (psiCoeff t (ipar D i μ) * sign k (ipar D i μ)) • cl D Sc μ [] [dn i, up i] (etaL i 0) := by
  unfold psiWordReverse
  rw [psiMap₂_epsP]
  rfl

/-- The dotted left cup maps to a right cap with a computed coefficient. -/
theorem psiWordReverse_sameCup (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc)
    (μ : X) (i : I) (n : ℕ) :
    psiWordReverse (sy := sy) (hc := hc) t ht cs μ μ rfl (left_ud μ i)
      (psiSameCup cs i μ n) =
      (psiCoeff t (n * D.parity i) * psiCoeff t (ipar D i μ)) •
        cl D Sc μ [up i, dn i] [] (epsL i n) := by
  rw [psiSameCup, psiWordReverse_comp t ht cs μ μ rfl (left_ud μ i) (left_ud μ i)
    (etaP_mem cs i μ) (cl_mem_homPar (sChain_dL i n) (parsum_dotsL [] i [dn i] n)),
    psiWordReverse_dotsLeft, psiWordReverse_etaP, Linear.smul_comp, Linear.comp_smul,
    cl_comp (sChain_dL i n) (sChain_epsL i 0)]
  rw [show dotsL [] i [dn i] n ++ epsL i 0 = epsL i n by simp [epsL, dotsL]]
  simp only [smul_smul]
  congr 1
  calc
    _ = (sign k (ipar D i μ * (n * D.parity i)) * sign k (ipar D i μ * (n * D.parity i))) *
      (psiCoeff t (n * D.parity i) * psiCoeff t (ipar D i μ)) := by ring
    _ = _ := by rw [sign_mul_self, one_mul]

/-- The dotted left cap maps to a right cup with a computed coefficient. -/
theorem psiWordReverse_sameCap (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc)
    (μ : X) (i : I) (n : ℕ) :
    psiWordReverse (sy := sy) (hc := hc) t ht cs μ μ (left_du μ i) rfl
      (psiSameCap cs i μ n) =
      (psiCoeff t (n * D.parity i) * psiCoeff t (ipar D i μ) * sign k (ipar D i μ)) •
        cl D Sc μ [] [dn i, up i] (etaL i n) := by
  rw [psiSameCap, psiWordReverse_comp t ht cs μ μ (left_du μ i) (left_du μ i) rfl
    (cl_mem_homPar (sChain_dR i n) (parsum_dotsL [dn i] i [] n)) (epsP_mem cs i μ),
    psiWordReverse_dotsRight, psiWordReverse_epsP, Linear.smul_comp, Linear.comp_smul,
    cl_comp (sChain_etaL i 0) (sChain_dR i n)]
  rw [show etaL i 0 ++ dotsL [dn i] i [] n = etaL i n by simp [etaL, dotsL]]
  simp only [smul_smul]
  rw [mul_comm (n * D.parity i) (ipar D i μ)]
  congr 1
  calc
    _ = (sign k (ipar D i μ * (n * D.parity i)) * sign k (ipar D i μ * (n * D.parity i))) *
      (psiCoeff t (n * D.parity i) * psiCoeff t (ipar D i μ) * sign k (ipar D i μ)) := by ring
    _ = _ := by rw [sign_mul_self, one_mul]

private theorem psiWordReverse_zero (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc) (ν μ : X)
    {s r : List (Letter I)} (hs : wt D μ s = ν) (hr : wt D μ r = ν) :
    psiWordReverse (sy := sy) (hc := hc) t ht cs ν μ hs hr 0 = 0 := by
  unfold psiWordReverse
  rw [map_zero]
  rfl

private theorem psiWordReverse_id (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc) (ν μ : X)
    {s : List (Letter I)} (hs : wt D μ s = ν) :
    psiWordReverse (sy := sy) (hc := hc) t ht cs ν μ hs hs (𝟙 _) = 𝟙 _ := by
  exact congrArg (fun z => QPiTwoEnvelope.toHom (SOp.unsop z))
    (psiMap₂_id (sy := sy) (hc := hc) t ht cs (psiWordAt ν μ s hs))

private theorem inverse_sameCup (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc)
    (μ : X) (i : I) (n : ℕ) :
    psiWordReverse (sy := sy) (hc := hc) (-t) (psi_neg_sq ht) (psiInverseCScalars t ht cs)
      μ μ rfl (left_ud μ i) (psiSameCup cs i μ n) =
      (sign k (ipar D i μ) * psiCoeff (-t) (n * D.parity i)) •
        cl D Sc μ [up i, dn i] [] (epsL i n) := by
  have he : psiSameCup cs i μ n = psiCoeff (-t) (ipar D i μ) •
      psiSameCup (psiInverseCScalars t ht cs) i μ n := by
    unfold psiSameCup
    rw [etaP_psiInverseCScalars, Linear.smul_comp, smul_smul, psiCoeff_neg_mul ht, one_smul]
  rw [he, psiWordReverse_smul, psiWordReverse_sameCup, smul_smul]
  congr 1
  calc
    _ = (psiCoeff (-t) (ipar D i μ) * psiCoeff (-t) (ipar D i μ)) *
      psiCoeff (-t) (n * D.parity i) := by ring
    _ = _ := by rw [psiCoeff_mul_self (psi_neg_sq ht)]

private theorem inverse_sameCap (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc)
    (μ : X) (i : I) (n : ℕ) :
    psiWordReverse (sy := sy) (hc := hc) (-t) (psi_neg_sq ht) (psiInverseCScalars t ht cs)
      μ μ (left_du μ i) rfl (psiSameCap cs i μ n) =
      (sign k (ipar D i μ) * psiCoeff (-t) (n * D.parity i)) •
        cl D Sc μ [] [dn i, up i] (etaL i n) := by
  have he : psiSameCap cs i μ n = psiCoeff t (ipar D i μ) •
      psiSameCap (psiInverseCScalars t ht cs) i μ n := by
    unfold psiSameCap
    rw [epsP_psiInverseCScalars, Linear.comp_smul, smul_smul,
      mul_comm (psiCoeff t _), psiCoeff_neg_mul ht, one_smul]
  rw [he, psiWordReverse_smul, psiWordReverse_sameCap, smul_smul]
  congr 1
  calc
    _ = (psiCoeff (-t) (ipar D i μ) * psiCoeff t (ipar D i μ)) *
      (sign k (ipar D i μ) * psiCoeff (-t) (n * D.parity i)) := by ring
    _ = _ := by rw [psiCoeff_neg_mul ht, one_mul]

private theorem cup_ext (μ : X) (i : I) (hh : 0 ≤ D.h i μ)
    {T : (pres D Sc).Presented} {x y : T ⟶ (pres D Sc).obj (ob D μ [up i, dn i])}
    (hσ : x ≫ cl D Sc μ [up i, dn i] [dn i, up i] (sigmaL i i) =
      y ≫ cl D Sc μ [up i, dn i] [dn i, up i] (sigmaL i i))
    (hε : ∀ n : ℕ, (n : ℤ) < D.h i μ →
      x ≫ cl D Sc μ [up i, dn i] [] (epsL i n) =
      y ≫ cl D Sc μ [up i, dn i] [] (epsL i n)) : x = y := by
  have E := cl_invP₁ Sc i μ hh
  simp only [← cl_comp (sChain_sigmaL i i) (sChain_lcrossL i i),
    ← cl_comp (sChain_epsL i _) (sChain_dcupL i _), cl_nil] at E
  rw [← Category.comp_id x, ← Category.comp_id y, ← E]
  simp only [Preadditive.comp_add, Preadditive.comp_neg, Preadditive.comp_sum, ← Category.assoc]
  rw [hσ]
  congr 1
  apply sum_congr rfl
  intro n hn
  rw [hε n (by rw [mem_range] at hn; omega)]

private theorem cap_ext (μ : X) (i : I) (hh : D.h i μ ≤ 0)
    {T : (pres D Sc).Presented} {x y : (pres D Sc).obj (ob D μ [dn i, up i]) ⟶ T}
    (hσ : cl D Sc μ [up i, dn i] [dn i, up i] (sigmaL i i) ≫ x =
      cl D Sc μ [up i, dn i] [dn i, up i] (sigmaL i i) ≫ y)
    (hη : ∀ n : ℕ, (n : ℤ) < -D.h i μ →
      cl D Sc μ [] [dn i, up i] (etaL i n) ≫ x =
      cl D Sc μ [] [dn i, up i] (etaL i n) ≫ y) : x = y := by
  have E := cl_invM₁ Sc i μ hh
  simp only [← cl_comp (sChain_lcrossL i i) (sChain_sigmaL i i),
    ← cl_comp (sChain_dcapL i _) (sChain_etaL i _), cl_nil] at E
  rw [← Category.id_comp x, ← Category.id_comp y, ← E]
  simp only [Preadditive.add_comp, Preadditive.neg_comp, Preadditive.sum_comp, Category.assoc]
  rw [hσ]
  congr 1
  apply sum_congr rfl
  intro n hn
  rw [hη n (by rw [mem_range] at hn; omega)]

private theorem cancel_factor {M : Type*} [AddCommGroup M] [Module k M]
    (t : k) (ht : t ^ 2 = -1) (a b q : ZMod 2) {x y : M}
    (h : (sign k a * (psiCoeff (-t) q * sign k b)) • x =
      (sign k a * (psiCoeff (-t) q * sign k b)) • y) : x = y := by
  have hi : (sign k a * (psiCoeff t q * sign k b)) *
      (sign k a * (psiCoeff (-t) q * sign k b)) = 1 := by
    calc
      _ = (sign k a * sign k a) * (sign k b * sign k b) *
        (psiCoeff (-t) q * psiCoeff t q) := by ring
      _ = 1 := by rw [sign_mul_self, sign_mul_self, psiCoeff_neg_mul ht, mul_one, mul_one]
  have H := congrArg ((sign k a * (psiCoeff t q * sign k b)) • ·) h
  simpa only [smul_smul, hi, one_smul] using H

private theorem inverse_pair_coeff (t : k) (ht : t ^ 2 = -1) (p q : ZMod 2) :
    (sign k ((p + q) * (p + q)) * (psiCoeff (-t) q * sign k p)) * psiCoeff (-t) q = 1 := by
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    rcases parity_eq_zero_or_one q with rfl | rfl <;>
    simp [psiCoeff, ← pow_two, ht, show (1 : ZMod 2) + 1 = 0 from rfl]

/-- The inverse-parameter quotient map on the positive inverse-matrix entry.
The proof uses its annihilation and pairing identities, not an assumed image. -/
theorem psiWordReverse_inverse_cupDual (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc)
    (μ : X) (i : I) (r : ℕ) :
    psiWordReverse (sy := sy) (hc := hc) (-t) (psi_neg_sq ht) (psiInverseCScalars t ht cs)
      μ μ (left_ud μ i) rfl (psiSameCupDual cs i μ r) =
      psiCoeff (-t) (r * D.parity i) • cl D Sc μ [] [up i, dn i] (dcupL i r) := by
  by_cases hr : (r : ℤ) < D.h i μ
  · apply cup_ext μ i (by omega)
    · rw [Linear.smul_comp, cl_comp (sChain_dcupL i r) (sChain_sigmaL i i),
        cl_invP₄ Sc i μ r hr, smul_zero]
      have H := congrArg (psiWordReverse (sy := sy) (hc := hc) (-t) (psi_neg_sq ht)
        (psiInverseCScalars t ht cs) μ μ (left_du μ i) rfl)
        (psiSameCup_lcross_dual cs i μ r)
      rw [psiWordReverse_comp (-t) (psi_neg_sq ht) (psiInverseCScalars t ht cs)
        μ μ (left_du μ i) (left_ud μ i) rfl
        (cl_mem_homPar (sChain_lcrossL i i) (parsum_lcrossL i i))
        (psiSameCupDual_mem cs i μ r), psiWordReverse_lcross, Linear.comp_smul,
        smul_smul, psiWordReverse_zero] at H
      exact cancel_factor t ht _ _ _ (H.trans (smul_zero _).symm)
    · intro n hn
      rw [Linear.smul_comp, cl_comp (sChain_dcupL i r) (sChain_epsL i n),
        cl_invP₅ Sc i μ n r hn hr]
      have H := congrArg (psiWordReverse (sy := sy) (hc := hc) (-t) (psi_neg_sq ht)
        (psiInverseCScalars t ht cs) μ μ rfl rfl) (psiSameCup_pair cs i μ n r hn hr)
      rw [psiWordReverse_comp (-t) (psi_neg_sq ht) (psiInverseCScalars t ht cs)
        μ μ rfl (left_ud μ i) rfl (psiSameCup_mem cs i μ n) (psiSameCupDual_mem cs i μ r),
        inverse_sameCup, Linear.comp_smul, smul_smul] at H
      rw [mul_comm (sign k (ipar D i μ)) (psiCoeff (-t) _)] at H
      apply cancel_factor t ht ((ipar D i μ + D.parity i * n) * (ipar D i μ + D.parity i * r))
        (ipar D i μ) (n * D.parity i)
      rw [H]
      by_cases hnr : n = r
      · subst n
        simp only [↓reduceIte]
        rw [psiWordReverse_id, cl_nil, smul_smul,
          mul_comm (D.parity i) (r : ZMod 2), inverse_pair_coeff t ht, one_smul]
      · simp only [ite_eq_right hnr, psiWordReverse_zero, smul_zero]
  · rw [psiSameCupDual_zero cs i μ r (by omega), psiWordReverse_zero,
      cl_dcupZero Sc i μ r (by omega), smul_zero]

/-- The inverse-parameter quotient map on the negative inverse-matrix entry.
Both matrix blocks are used, including the totalized zero range. -/
theorem psiWordReverse_inverse_capDual (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc)
    (μ : X) (i : I) (r : ℕ) :
    psiWordReverse (sy := sy) (hc := hc) (-t) (psi_neg_sq ht) (psiInverseCScalars t ht cs)
      μ μ rfl (left_du μ i) (psiSameCapDual cs i μ r) =
      psiCoeff (-t) (r * D.parity i) • cl D Sc μ [dn i, up i] [] (dcapL i r) := by
  by_cases hr : (r : ℤ) < -D.h i μ
  · apply cap_ext μ i (by omega)
    · rw [Linear.comp_smul, cl_comp (sChain_sigmaL i i) (sChain_dcapL i r),
        cl_invM₄ Sc i μ r hr, smul_zero]
      have H := congrArg (psiWordReverse (sy := sy) (hc := hc) (-t) (psi_neg_sq ht)
        (psiInverseCScalars t ht cs) μ μ rfl (left_ud μ i))
        (psiSameCap_dual_lcross cs i μ r)
      rw [psiWordReverse_comp (-t) (psi_neg_sq ht) (psiInverseCScalars t ht cs)
        μ μ rfl (left_du μ i) (left_ud μ i) (psiSameCapDual_mem cs i μ r)
        (cl_mem_homPar (sChain_lcrossL i i) (parsum_lcrossL i i)),
        psiWordReverse_lcross, Linear.smul_comp, smul_smul, psiWordReverse_zero] at H
      exact cancel_factor t ht _ _ _ (H.trans (smul_zero _).symm)
    · intro n hn
      rw [Linear.comp_smul, cl_comp (sChain_etaL i n) (sChain_dcapL i r),
        cl_invM₅ Sc i μ n r hn hr]
      have H := congrArg (psiWordReverse (sy := sy) (hc := hc) (-t) (psi_neg_sq ht)
        (psiInverseCScalars t ht cs) μ μ rfl rfl) (psiSameCap_pair cs i μ n r hn hr)
      rw [psiWordReverse_comp (-t) (psi_neg_sq ht) (psiInverseCScalars t ht cs)
        μ μ rfl (left_du μ i) rfl (psiSameCapDual_mem cs i μ r) (psiSameCap_mem cs i μ n),
        inverse_sameCap, Linear.smul_comp, smul_smul] at H
      rw [mul_comm (sign k (ipar D i μ)) (psiCoeff (-t) _)] at H
      apply cancel_factor t ht ((D.parity i * r + ipar D i μ) * (D.parity i * n + ipar D i μ))
        (ipar D i μ) (n * D.parity i)
      rw [H]
      by_cases hnr : n = r
      · subst n
        simp only [↓reduceIte]
        rw [psiWordReverse_id, cl_nil, smul_smul,
          mul_comm (D.parity i) (r : ZMod 2), add_comm (r * D.parity i), inverse_pair_coeff t ht, one_smul]
      · simp only [ite_eq_right hnr, psiWordReverse_zero, smul_zero]
  · rw [psiSameCapDual_zero cs i μ r (by omega), psiWordReverse_zero,
      cl_dcapZero Sc i μ r (by omega), smul_zero]

/-- Computation on a diamond cup in the original quotient. -/
theorem psiWordReverse_dcup (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc)
    (μ : X) (i : I) (r : ℕ) :
    psiWordReverse (sy := sy) (hc := hc) t ht cs μ μ rfl (left_ud μ i)
      (cl D Sc μ [] [up i, dn i] (dcupL i r)) =
      (psiCoeff t (r * D.parity i) * sign k (ipar D i μ * (r * D.parity i + 1))) •
        psiSameCupDual cs i μ r := by
  have E := congrArg (fun z => QPiTwoEnvelope.toHom (SOp.unsop z))
    (psiMap₂_gen (sy := sy) (hc := hc) t ht cs μ μ (.dcup i r) rfl)
  refine E.trans ?_
  rw [psiGen, psiRebase_unsop]
  rfl

/-- Computation on a diamond cap in the original quotient. -/
theorem psiWordReverse_dcap (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc)
    (μ : X) (i : I) (r : ℕ) :
    psiWordReverse (sy := sy) (hc := hc) t ht cs μ μ (left_du μ i) rfl
      (cl D Sc μ [dn i, up i] [] (dcapL i r)) =
      (psiCoeff t (r * D.parity i) * sign k (ipar D i μ * (r * D.parity i))) •
        psiSameCapDual cs i μ r := by
  have E := congrArg (fun z => QPiTwoEnvelope.toHom (SOp.unsop z))
    (psiMap₂_gen (sy := sy) (hc := hc) t ht cs μ μ (.dcap i r) (left_du μ i))
  refine E.trans ?_
  rw [psiGen, psiRebase_unsop]
  rfl

private theorem inverse_sign_coeff (t : k) (ht : t ^ 2 = -1) (p q : ZMod 2) :
    (psiCoeff t q * sign k p) * psiCoeff (-t) q = sign k p := by
  calc
    _ = (psiCoeff (-t) q * psiCoeff t q) * sign k p := by ring
    _ = _ := by rw [psiCoeff_neg_mul ht, one_mul]

/-- The diamond-cup double quotient map, before the Π-conjugation sign. -/
theorem psiDCup_parameter_double (t : k) (ht : t ^ 2 = -1)
    (cs : CScalars Sc) (μ : X) (i : I) (r : ℕ) :
    psiWordReverse (sy := sy) (hc := hc) (-t) (psi_neg_sq ht) (psiInverseCScalars t ht cs)
      μ μ (left_ud μ i) rfl
      (psiWordReverse (sy := sy) (hc := hc) t ht cs μ μ rfl (left_ud μ i)
        (cl D Sc μ [] [up i, dn i] (dcupL i r))) =
      sign k (ipar D i μ * (r * D.parity i + 1)) •
        cl D Sc μ [] [up i, dn i] (dcupL i r) := by
  rw [psiWordReverse_dcup, psiWordReverse_smul, psiWordReverse_inverse_cupDual,
    smul_smul, inverse_sign_coeff t ht]

/-- The diamond-cap double quotient map, before the Π-conjugation sign. -/
theorem psiDCap_parameter_double (t : k) (ht : t ^ 2 = -1)
    (cs : CScalars Sc) (μ : X) (i : I) (r : ℕ) :
    psiWordReverse (sy := sy) (hc := hc) (-t) (psi_neg_sq ht) (psiInverseCScalars t ht cs)
      μ μ rfl (left_du μ i)
      (psiWordReverse (sy := sy) (hc := hc) t ht cs μ μ (left_du μ i) rfl
        (cl D Sc μ [dn i, up i] [] (dcapL i r))) =
      sign k (ipar D i μ * (r * D.parity i)) •
        cl D Sc μ [dn i, up i] [] (dcapL i r) := by
  rw [psiWordReverse_dcap, psiWordReverse_smul, psiWordReverse_inverse_capDual,
    smul_smul, inverse_sign_coeff t ht]

/-- Apply the two quotient maps and the actual intervening Π conjugation.
The result retains its shifted endpoint transports. -/
def psiWordDouble (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc) (ν μ : X)
    {s r : List (Letter I)} (hs : wt D μ s = ν) (hr : wt D μ r = ν)
    (x : (pres D Sc).obj (ob D μ s) ⟶ (pres D Sc).obj (ob D μ r)) :=
  QPiTwoEnvelope.toHom (SOp.unsop
    (psiPiConjugate (psiParity (sy := sy) (hc := hc) (psiWordAt (Sc := Sc) ν μ r hr))
      (psiParity (sy := sy) (hc := hc) (psiWordAt (Sc := Sc) ν μ s hs))
      (psiMap₂ (sy := sy) (hc := hc) (-t) (psi_neg_sq ht) (psiInverseCScalars t ht cs)
        (psiWordAt ν μ r hr) (psiWordAt ν μ s hs)
        (psiWordReverse (sy := sy) (hc := hc) t ht cs ν μ hs hr x))))

/-- The Π-conjugation sign for a homogeneous double quotient image. -/
theorem psiWordDouble_heq (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc) (ν μ : X)
    {s r : List (Letter I)} (hs : wt D μ s = ν) (hr : wt D μ r = ν)
    {x : (pres D Sc).obj (ob D μ s) ⟶ (pres D Sc).obj (ob D μ r)} {p : ZMod 2}
    (hx : x ∈ homPar D Sc μ s r p) :
    let a := psiParity (sy := sy) (hc := hc) (psiWordAt (Sc := Sc) ν μ r hr)
    let b := psiParity (sy := sy) (hc := hc) (psiWordAt (Sc := Sc) ν μ s hs)
    HEq (psiWordDouble (sy := sy) (hc := hc) t ht cs ν μ hs hr x)
      (sign k (a * (p + (a + b)) + (a + (p + (a + b))) * b + b) •
        psiWordReverse (sy := sy) (hc := hc) (-t) (psi_neg_sq ht) (psiInverseCScalars t ht cs)
          ν μ hr hs (psiWordReverse (sy := sy) (hc := hc) t ht cs ν μ hs hr x)) := by
  have H := psiMap₂_mem_parity (sy := sy) (hc := hc) t ht cs
    (f := psiWordAt ν μ s hs) (g := psiWordAt ν μ r hr) (homPar_mem hx)
  change psiWordReverse (sy := sy) (hc := hc) t ht cs ν μ hs hr x ∈
    (pres D Sc).homDeg (Presentation.parityDeg (sig D)) _ _
      (p + (psiParity (sy := sy) (hc := hc) (psiWordAt (Sc := Sc) ν μ r hr) +
        psiParity (sy := sy) (hc := hc) (psiWordAt (Sc := Sc) ν μ s hs))) at H
  exact psiPiConjugate_heq _ _ _
    (psiMap₂_mem_parity (sy := sy) (hc := hc) (-t) (psi_neg_sq ht) (psiInverseCScalars t ht cs)
      (f := psiWordAt ν μ r hr) (g := psiWordAt ν μ s hs) H)

/-- Diamond cups return after the actual Π conjugation, including all zero ranges. -/
theorem psiDCup_parameter_roundtrip (t : k) (ht : t ^ 2 = -1)
    (cs : CScalars Sc) (μ : X) (i : I) (r : ℕ) :
    HEq (psiWordDouble (sy := sy) (hc := hc) t ht cs μ μ rfl (left_ud μ i)
      (cl D Sc μ [] [up i, dn i] (dcupL i r)))
      (cl D Sc μ [] [up i, dn i] (dcupL i r)) := by
  have H := psiWordDouble_heq (sy := sy) (hc := hc) t ht cs μ μ rfl (left_ud μ i)
    (cl_mem_homPar (sChain_dcupL i r) (parsum_dcupL i r))
  refine H.trans (heq_of_eq ?_)
  rw [psiDCup_parameter_double]
  have hp : psiParity (sy := sy) (hc := hc) (psiWordAt (Sc := Sc) μ μ [up i, dn i] (left_ud μ i)) =
      ipar D i μ := by simp [psiParity, psiWordAt, ob, wd]
  rw [hp]
  change sign k (ipar D i μ * (D.parity i * r + (ipar D i μ + 0)) +
    (ipar D i μ + (D.parity i * r + (ipar D i μ + 0))) * 0 + 0) •
    (sign k (ipar D i μ * (r * D.parity i + 1)) • _) = _
  have he : ipar D i μ * (D.parity i * r + (ipar D i μ + 0)) +
      (ipar D i μ + (D.parity i * r + (ipar D i μ + 0))) * 0 + 0 =
      ipar D i μ * (r * D.parity i + 1) := by
    simp only [add_zero, mul_zero, mul_add, zmod2_mul_self', mul_one]
    ring
  rw [he, smul_smul, sign_mul_self, one_smul]

/-- Diamond caps return after the actual Π conjugation, including all zero ranges. -/
theorem psiDCap_parameter_roundtrip (t : k) (ht : t ^ 2 = -1)
    (cs : CScalars Sc) (μ : X) (i : I) (r : ℕ) :
    HEq (psiWordDouble (sy := sy) (hc := hc) t ht cs μ μ (left_du μ i) rfl
      (cl D Sc μ [dn i, up i] [] (dcapL i r)))
      (cl D Sc μ [dn i, up i] [] (dcapL i r)) := by
  have H := psiWordDouble_heq (sy := sy) (hc := hc) t ht cs μ μ (left_du μ i) rfl
    (cl_mem_homPar (sChain_dcapL i r) (parsum_dcapL i r))
  refine H.trans (heq_of_eq ?_)
  rw [psiDCap_parameter_double]
  have hp : psiParity (sy := sy) (hc := hc) (psiWordAt (Sc := Sc) μ μ [dn i, up i] (left_du μ i)) =
      ipar D i μ := by simpa [psiParity, psiWordAt, ob, wd] using ipar_wt_up (D := D) i μ
  rw [hp]
  change sign k (0 * (D.parity i * r + (0 + ipar D i μ)) +
    (0 + (D.parity i * r + (0 + ipar D i μ))) * ipar D i μ + ipar D i μ) •
    (sign k (ipar D i μ * (r * D.parity i)) • _) = _
  have he : 0 * (D.parity i * r + (0 + ipar D i μ)) +
      (0 + (D.parity i * r + (0 + ipar D i μ))) * ipar D i μ + ipar D i μ =
      ipar D i μ * (r * D.parity i) := by
    simp only [zero_add, zero_mul, add_mul, zmod2_mul_self', add_assoc, zmod2_add_self, add_zero]
    ring
  rw [he, smul_smul, sign_mul_self, one_smul]

private theorem wordParity_ud (ν μ : X) (i : I) (h : wt D μ [up i, dn i] = ν) :
    psiParity (sy := sy) (hc := hc) (psiWordAt (Sc := Sc) ν μ [up i, dn i] h) = ipar D i μ := by
  simp [psiParity, psiWordAt, ob, wd]

private theorem wordParity_du (ν μ : X) (i j : I) (h : wt D μ [dn i, up j] = ν) :
    psiParity (sy := sy) (hc := hc) (psiWordAt (Sc := Sc) ν μ [dn i, up j] h) = ipar D i μ := by
  simpa [psiParity, psiWordAt, ob, wd] using ipar_wt_upj (D := D) i j μ

private theorem wordParity_ud' (ν μ : X) (i j : I) (h : wt D μ [up j, dn i] = ν) :
    psiParity (sy := sy) (hc := hc) (psiWordAt (Sc := Sc) ν μ [up j, dn i] h) = ipar D i μ := by
  simp [psiParity, psiWordAt, ob, wd]

private theorem double_equalParity (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc) (ν μ : X)
    {s r : List (Letter I)} (hs : wt D μ s = ν) (hr : wt D μ r = ν)
    {x : (pres D Sc).obj (ob D μ s) ⟶ (pres D Sc).obj (ob D μ r)} {p : ZMod 2}
    (hx : x ∈ homPar D Sc μ s r p)
    (hp : psiParity (sy := sy) (hc := hc) (psiWordAt (Sc := Sc) ν μ r hr) =
      psiParity (sy := sy) (hc := hc) (psiWordAt (Sc := Sc) ν μ s hs))
    (H : psiWordReverse (sy := sy) (hc := hc) (-t) (psi_neg_sq ht) (psiInverseCScalars t ht cs)
      ν μ hr hs (psiWordReverse (sy := sy) (hc := hc) t ht cs ν μ hs hr x) = x) :
    HEq (psiWordDouble (sy := sy) (hc := hc) t ht cs ν μ hs hr x) x := by
  refine (psiWordDouble_heq t ht cs ν μ hs hr hx).trans (heq_of_eq ?_)
  rw [hp, H]
  have he (b p : ZMod 2) : b * (p + (b + b)) + (b + (p + (b + b))) * b + b = 0 := by
    revert b p
    decide
  rw [he, sign_zero, one_smul]

private theorem cup_word_roundtrip (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc) (μ : X) (i : I) :
    HEq (psiWordDouble (sy := sy) (hc := hc) t ht cs μ μ rfl (left_du μ i)
      (cl D Sc μ [] [dn i, up i] (etaL i 0))) (cl D Sc μ [] [dn i, up i] (etaL i 0)) := by
  unfold psiWordDouble
  rw [wordParity_du]
  exact psiCup_parameter_roundtrip t ht cs μ i

private theorem cap_word_roundtrip (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc) (μ : X) (i : I) :
    HEq (psiWordDouble (sy := sy) (hc := hc) t ht cs μ μ (left_ud μ i) rfl
      (cl D Sc μ [up i, dn i] [] (epsL i 0))) (cl D Sc μ [up i, dn i] [] (epsL i 0)) := by
  unfold psiWordDouble
  rw [wordParity_ud]
  exact psiCap_parameter_roundtrip t ht cs μ i

/-- Every one of the seven presentation generators returns under the two
quotient maps with inverse parameters and the actual Π conjugation.
This is a generator statement, not equality on arbitrary quotient morphisms. -/
theorem psiGenerator_parameter_roundtrip (t : k) (ht : t ^ 2 = -1)
    (cs : CScalars Sc) (ν μ : X) (g : Shape I) (h : wt D μ g.dom = ν) :
    HEq (psiWordDouble (sy := sy) (hc := hc) t ht cs ν μ h
      ((g.wt_dom_eq_wt_cod D μ).symm.trans h) (cl D Sc μ g.dom g.cod [([], g, [])]))
      (cl D Sc μ g.dom g.cod [([], g, [])]) := by
  cases g with
  | dot i =>
    subst ν
    exact double_equalParity t ht cs _ μ rfl rfl
      (cl_mem_homPar (sChain_dotsL [] i [] 1) (parsum_dotsL [] i [] 1)) rfl
      (psiDot_parameter_roundtrip t ht cs μ i)
  | cross i j =>
    exact double_equalParity t ht cs ν μ h _
      (cl_mem_homPar (by simp [SChain]) rfl) rfl
      (psiCross_parameter_roundtrip t ht cs ν μ i j h _)
  | cup i =>
    have hn : ν = μ := h.symm
    cases hn
    exact cup_word_roundtrip t ht cs _ i
  | cap i =>
    have hn : ν = μ := by simpa [Shape.dom, wt, sh] using h.symm
    cases hn
    exact cap_word_roundtrip t ht cs _ i
  | lcross i j =>
    apply double_equalParity t ht cs ν μ h _
      (cl_mem_homPar (sChain_lcrossL i j) (parsum_lcrossL i j))
    · exact (wordParity_ud' (sy := sy) (hc := hc) ν μ i j _).trans
        (wordParity_du (sy := sy) (hc := hc) ν μ i j h).symm
    · exact psiLCross_parameter_roundtrip t ht cs ν μ i j h _
  | dcup i r =>
    have hn : ν = μ := h.symm
    cases hn
    exact psiDCup_parameter_roundtrip t ht cs _ i r
  | dcap i r =>
    have hn : ν = μ := by simpa [Shape.dom, wt, sh] using h.symm
    cases hn
    exact psiDCap_parameter_roundtrip t ht cs _ i r

/-- Reverse order of the two parameter choices, for all seven generators. -/
theorem psiGenerator_parameter_roundtrip_reverse (t : k) (ht : t ^ 2 = -1)
    (cs : CScalars Sc) (ν μ : X) (g : Shape I) (h : wt D μ g.dom = ν) :
    HEq (QPiTwoEnvelope.toHom (SOp.unsop
      (psiPiConjugate
        (psiParity (sy := sy) (hc := hc) (psiWordAt (Sc := Sc) ν μ g.cod ((g.wt_dom_eq_wt_cod D μ).symm.trans h)))
        (psiParity (sy := sy) (hc := hc) (psiWordAt (Sc := Sc) ν μ g.dom h))
        (psiMap₂ (sy := sy) (hc := hc) t ht cs
          (psiWordAt ν μ g.cod ((g.wt_dom_eq_wt_cod D μ).symm.trans h)) (psiWordAt ν μ g.dom h)
          (psiWordReverse (sy := sy) (hc := hc) (-t) (psi_neg_sq ht) (psiInverseCScalars t ht cs)
            ν μ h ((g.wt_dom_eq_wt_cod D μ).symm.trans h) (cl D Sc μ g.dom g.cod [([], g, [])]))))))
      (cl D Sc μ g.dom g.cod [([], g, [])]) := by
  simpa only [psiWordDouble, neg_neg, psiInverseCScalars_involutive] using
    psiGenerator_parameter_roundtrip (sy := sy) (hc := hc) (-t) (psi_neg_sq ht)
      (psiInverseCScalars t ht cs) ν μ g h

end OddMath.SKM
