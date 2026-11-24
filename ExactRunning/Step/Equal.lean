import ExactRunning.Step.Festival

/-!
# Exact collapse at predicted coarse field

Independent of stationary status. Includes off-diagonal blocks with
true left variations also on coarse links. `vibrant_equal`: brings
completed matrix to form handled by Det.Prediction.
-/

set_option linter.unusedSectionVars false
noncomputable section
namespace ExactRunning
open YM Stationary Lattice Laurent Bloch RG
open Function Filter Finset Matrix
open scoped BigOperators ContDiff Topology ComplexConjugate Matrix

open Exterior Wilson Precision
open Tree

namespace BlockTie
variable {G : Gauge} {E I : Pylon G} {m : Side} {X : BlockTie E I}


variable (X)
/-- Predictor derivative. Includes the added-frame part
(`mail`, see `prospectus_eq`). -/
def prospectus (b : Joint G m (X.up m)) := quota (X.S m) (X.choice m) 1 b

def sectors (b : Joint G m (X.up m)) := (X.prospectus b).submatrix id Sum.inl

def kcoin (m : Side) := X.kernel.penalty • (1: Funds (Lines G m 1))

lemma penalty : 0 < X.kernel.penalty := X.kernel.penalty_pos

lemma kcoin_unit : IsUnit (X.kcoin m).det := (fund_det (PosDef.one.smul X.penalty))

variable {b : Joint G m (X.up m)}
abbrev Witness := Teller (X.S m) (X.choice m) E.p E.r 1

open scoped Matrix.Norms.Frobenius in
lemma frame_charge (h : X.Witness b) (y : BaseSites G m) :
    X.prospectus b *ᵥ Sum.elim 0 y = mail (X.Z m b) *ᵥ y := by
  let r := worn (X.S m) (X.choice m) 1 b
  have hy : Sum.elim (0: Link G (X.up m)) y = cash (helmets G m (X.up m)) (0,y) := by
    rw [helmets,halvesC,cash_pocket,cash_pocket]
  rw [hy,prospectus,quota,bill_at,cash_pocket,mailed]
  apply HasDerivAt.unique (Push.side _ (h.wist.differentiableAt (by simp)) (0,y))
  let w (s:ℝ) := X.Z m (atire 1 b (s • (0,y)))
  have hw (s:ℝ) : w s=Lattice.gauge (switchSite (s • y)) (X.Z m b) := by
    let S := X.S m
    have e : atire 1 b (s • (0,y))=wages S 1 (switchSite (s • y)) b := by
      refine Prod.ext ?_ ?_ <;> simp [atire,wages,Stationary.extend,gauge_one]; rfl
    unfold w;rw [e]; exact ribbons _ _ X.branches ..
  unfold worn
  simp only [dress_one,show ribbon (X.S m) (X.choice m) = X.Z m from rfl]

  change HasDerivAt (fun s=> content (w s * (X.Z m b)⁻¹)) _ 0
  simp_rw [hw]
  apply ray_content (by simp [gauge_one]); intro i
  let Y (s:ℝ) := switchSite (s • y)
  let U := X.Z m b
  simp only [Lattice.gauge, Pi.mul_apply,Pi.inv_apply,G.mat_mul,G.mat_inv]
  have hh : ∀ j, HasDerivAt (fun v => G.mat (Y v j)) (G.colorMat (gaugeColor y j)) 0 := ray_power y
  convert! (((hh i.1).mul_const (G.mat (U i))).mul (hh (i.1+Lattice.step i.2)).star).mul_const
    (star (G.mat (U i))) using 1
  rw [show Y 0=1 by simp [Y]]; simp [U,cant_at,G.colorMat_skew,Gauge.conjugate,add_mul, Matrix.mul_assoc]; rfl

lemma prospectus_eq (h : X.Witness b) : X.prospectus b = fromCols (X.sectors b) (mail (X.Z m b)) := by
  ext i (j|j)
  · rfl
  have hh := X.frame_charge h (Pi.single j 1)
  rw [mulVec_single_one,
      show Sum.elim (0:Link G (X.up m)) (Pi.single j (1:ℝ))=Pi.single (.inr j) (1:ℝ) from by
        ext (a|a) <;> simp [Pi.single_apply], mulVec_single_one] at hh
  exact congr_fun hh i

private lemma price_charge (h : X.Witness b) (x y : X.Hall m) :
    iteratedFDeriv ℝ 2 (X.sitting b (X.Z m b)) 0 ![x,y] =
      iteratedFDeriv ℝ 2 (burn E.p E.r b.1) 0 ![x.1.1,y.1.1] +
      X.kernel.penalty * dotProduct (x.2-X.prospectus b *ᵥ cash (helmets _ _ _) x.1) (y.2-X.prospectus b *ᵥ cash (helmets _ _ _) y.1) := by
  let r := worn (X.S m) (X.choice m) 1 b
  let L : X.Hall m→L[ℝ] Link G (X.up m) := (ContinuousLinearMap.fst ℝ _ _).comp
    (ContinuousLinearMap.fst ℝ _ _)
  let Q (z : X.Hall m) := ((z.2,r z.1,0): Link G m × Link G m × Link G m)
  have he : X.sitting b (X.Z m b) =ᶠ[𝓝 0]
      burn E.p E.r b.1 ∘ L + priceless (X.S m) ∘ Q := by
    filter_upwards [(continuous_fst.tendsto (0:X.Hall m)).eventually h.shown] with z hz
    simp only [sitting,J,muster, Pi.add_apply,Function.comp_apply]
    refine _root_.congr_arg (HAdd.hAdd (burn E.p E.r b.1 (L z))) ?_
    unfold Q priceless inure
    change tickets _ _ _ = tickets _ _ (input G m 0 * input G m _)
    rw [input_zero,one_mul]
    have hz : input G m (r z.1)*X.Z m b = X.Z m (Stationary.extend z.1*b) := by
      simpa only [dress_one,atire] using hz
    change tickets _ _ (X.Z m (Stationary.extend z.1*b)) = _
    simp [← hz,tickets]
  have hL : ContDiffAt ℝ ω (burn E.p E.r b.1) (L 0) := by rw [map_zero];exact h.known
  have hp : Q 0=0 := Prod.ext rfl (Prod.ext (worn_zero ..) rfl)
  have hc : ContDiffAt ℝ ω (priceless (X.S m)) (Q 0) := by rw [hp];exact valence _
  have hh : ContDiffAt ℝ ω Q 0 :=
    contDiffAt_snd.prodMk (((show ContDiffAt ℝ ω r (0:X.Hall m).1 from h.wist).comp (f:=Prod.fst) 0 contDiffAt_fst).prodMk contDiffAt_const)
  rw [(he.iteratedFDeriv ℝ 2).self_of_nhds, iteratedFDeriv_add_apply
      ((hL.comp _ L.contDiff.contDiffAt).of_le le_top)
      ((hc.comp (f:=Q) _ hh).of_le le_top),_root_.add_apply,
    wired L hL.analyticAt,map_zero,show L ∘ (![x,y]:Fin 2→ _) =![x.1.1,y.1.1] from by
      funext i;fin_cases i <;> rfl,
    pay_second hc hh,hp,(value_drops _).2.1,(value_drops _).2.2]
  have hd := ((hasFDerivAt_snd (𝕜:=ℝ) (p:=(0:X.Hall m))).prodMk
    ((((show ContDiffAt ℝ ω r (0:X.Hall m).1 from h.wist).differentiableAt
      (by simp)).hasFDerivAt.comp _ (hasFDerivAt_fst (p:=(0:X.Hall m)))).prodMk
      (hasFDerivAt_const (0:Link G m) _))).fderiv
  change fderiv ℝ Q 0= _ at hd
  simp only [hd,_root_.zero_apply,zero_add, ContinuousLinearMap.prod_apply, hectic,
    prospectus,quota,bill_at,cash_pocket];rfl

lemma full_price (h : X.Witness b) :
    let Q := X.prospectus b
    let k := X.kcoin m
    X.full b (X.Z m b) =
    fromBlocks ((rearM G m (X.up m))ᵀ * flare E.p E.r b.1 * rearM _ _ _ + Qᵀ*k*Q)
      (-(Qᵀ*k)) (-(k*Q)) k := by
  apply damage_eq (X.podium m); intro x y
  rw [full,detracts,price_charge X h]
  simp only [podium,halvesC (A:=helmets _ _ _),cash_pocket,Matrix.fromBlocks_mulVec,
    Sum.elim_comp_inl,Sum.elim_comp_inr,halvesP,Matrix.add_mulVec,dotProduct_add]
  have e := detracts (pocket _) (burn E.p E.r b.1) 0 x.1.1 y.1.1
  rw [cash_pocket, cash_pocket] at e
  simp only [neg_mulVec,dotProduct_neg,← mulVec_mulVec,transposes,rear_cost,flare,e,
      kcoin,smul_mulVec,one_mulVec,dotProduct_smul,smul_eq_mul,sub_dotProduct,dotProduct_sub]
  ring

lemma rear_place : rearM G m (X.up m) = fromCols (1:Funds _) 0 := by
  refine bill_eq (helmets _ _ _) (fun x => ?_)
  rw [rear_cost,helmets,halvesC,fromCols_mulVec,cash_pocket,Sum.elim_comp_inl,
    one_mulVec,zero_mulVec, add_zero]

lemma vibrant_equal (h : X.Witness b) :
    X.vibrant b (X.Z m b) =
      Det.predicted (epMat E.p E.r b.1) (X.sectors b) (mail (X.Z m b)) (X.kcoin m) := by
  rw [vibrant,X.full_price h, Det.predicted, ← X.prospectus_eq h, fromBlocks_add,
    settings,rear_place X]
  simp only [transpose_mul,transpose_transpose]

  congr 1 <;> try exact add_zero _
  rw [add_right_comm _ ((X.prospectus b)ᵀ * _ * _),← Matrix.mul_assoc,
    add_right_cancel_iff, Matrix.mul_assoc _ (mail b.1),← Matrix.add_mul,← Matrix.mul_add]
  simp only [transpose_fromCols,transpose_one,transpose_zero,fromRows_mul,Matrix.one_mul,
    Matrix.zero_mul]
  rw [mul_fromCols, Matrix.mul_one, Matrix.mul_zero]
  ext (i|i) (j|j) <;> rfl


lemma witness_lit {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    {b : Y → Joint G m (X.up m)} (h : Thaw b 0) (he : (b 0).1 = 1) :
    ∀ᶠ y in 𝓝 0, X.Witness (b y) :=
  awake (X.choice m) E.paths h he X.branches root_customs

lemma Z_zero : X.Z m 1=1 := ribbon_zero _ _ X.branches

lemma vibrant_zero :
    X.vibrant (m:=m) 1 1 =
      Det.predicted (epMat E.p E.r 1) (X.sectors 1) (mail 1) (X.kcoin m) := by
  have hh := X.vibrant_equal ((X.witness_lit (m:=m) (Thaw.fixed 1 (0:ℝ)) rfl).self_of_nhds)
  rw [X.Z_zero] at hh
  exact hh

end BlockTie
end ExactRunning
