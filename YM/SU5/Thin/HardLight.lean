import SatinFixedContrastNovember4
import YM.SU5.Thin.Futures
import YM.SU5.Six.Night

set_option autoImplicit false
set_option maxHeartbeats 150000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
open Regis.Head Regis.Head.Brecht
namespace Spine
open Aria Casting Six
open Sifter DoseBill PadThin VoucherOp
-- careful: YM.Six (another namespace) in spectral tests.Night. This `Night` imported?
open YM.Six (night night_meas)
open Spectral Boundary Probe OS.Semigroup.Balloon
/-!
# Check against continuing a positive-width family as point operators

(Necessary-step tests motivated by `the construction notes` and `the construction notes`.
Not importing their claims as assumptions.) We have *two* orientations, and
unlike positive-width interpretation the ordered-two-point kernel now prices
at the CENTER-TIME gaps, with the actual continuum spatial interpretation.
Check a Fourier/Laplace criterion. Even at height spending for all ordered
prices the result of our experiment does NOT require any spectral contribution
strictly above zero energy. In fact `zero` PRICE MUST be retained in its measure.
Thus don't pretend to pay extra heat-padding removal via a width continuation,
nor use the spectral/locality conclusions in that setting. (Also don't assume
that by not running into that same obstruction test for this TOTAL signal, it
is now OK to require Minkowski locality, even just for these correlations! The
other essential criteria are not asserted. See the writeup.)
-/
namespace StrongStamp
open Spectral.PVM
variable (X:Hilbert) (S:OS.Semigroup X (3:Axis)) (ω x:X)
local notation "Q"=> S.ℚmeasure
private lemma nightTail (h: (S.ℚmeasure.diagonal x) night=0) : Tendsto (fun i:ℕ=>‖S.E i x‖^2) atTop (𝓝 0):= by
 let f (t:ℕ)(x:E4):= tinct 3 ((t:ℝ≥0)+(t:ℝ≥0)) x
 let u:= S.ℚmeasure.diagonal x
 have hU:IsFiniteMeasure u:= (Q).finite _
 have hv: ∀ᵐ x∂u,0<x (3:Axis):= by
    filter_upwards [S.bright x, (show ∀ᵐ x∂u,x∉night from ae_iff.mpr (by simp [u,h]))] with v p q
    exact lt_of_le_of_ne p (fun u=> q (show YM.time v=0 from u.symm))
 have he: Tendsto (fun i:ℕ=>∫ x,f i x∂u) atTop (𝓝 (∫ _:E4,(0:ℝ)∂u)):= by
    refine tendsto_integral_of_dominated_convergence (fun _=>(1:ℝ)) (fun i=>(OS.Semigroup.Balloon.admitted S _ x).1) (integrable_const _) (fun i=>?_ ) (hv.mono ?_)
    · apply hv.mono; intro z p; rw [Real.norm_of_nonneg (r:=f i z) (Real.exp_pos _).le]; exact OS.Semigroup.Balloon.fuel _ _ p.le
    intro v p; have he: Tendsto (fun i:ℕ=> (i:ℝ)+(i:ℝ)) atTop atTop:= tendsto_natCast_atTop_atTop.atTop_add_atTop tendsto_natCast_atTop_atTop
    have hh:= Real.tendsto_exp_neg_atTop_nhds_zero.comp (he.atTop_mul_const p); refine hh.congr fun i=> ?_
    unfold Function.comp f tinct; push_cast; rfl -- conv
 rw [integral_zero] at he; exact he.congr fun i=> (costp S i x).symm

/-- Forced part of the strict-energy criterion. -/
lemma ownsNight (F:X.Op)(e:ℝ≥0)(v:ℝ)(p:0<v)(q:‖ω‖=1)(h:∀ b:ℝ≥0,e≤b→ dist (sent X S b 0 F ω) ((v:ℂ) • ω) ≤ downDue*v) : (S.ℚmeasure.diagonal (F ω)) night ≠0 := by
  intro hx
  let x:= F ω; obtain ⟨i,c,hx⟩:= (((nightTail X S x hx).eventually (gt_mem_nhds (show 0<(v/2)^2 from pow_pos (half_pos p) _))).and (tendsto_natCast_atTop_atTop.eventually_ge_atTop e)).exists
  have h:=h i hx
  unfold sent at h; rw [S.eZero,ContinuousLinearMap.comp_id,ContinuousLinearMap.comp_apply,dist_eq_norm] at h
  have hc:‖S.E i x‖< v/2 := (sq_lt_sq₀ (norm_nonneg _) (half_pos p).le).mp c
  have hq:=norm_sub_norm_le ((v:ℂ) • ω) (S.E i x)
  rw [norm_smul, q, Complex.norm_real,Real.norm_of_nonneg p.le,norm_sub_rev,mul_one] at hq; change ‖S.E i x - _‖ ≤_ at h; unfold downDue at h; linarith only [h,hq,hc,p]
lemma page_eq (c:OS.Cross (3:Axis)) (z:Vantage)(d:ℝ)(A B F G:X.Op)(g: z 3>0)(p:0<d)(v:d < z 3) (k:F ω=x)(e:G ω=S.U c x)
    (s:∀ t,S.E t ω=ω) (h:A.adjoint=sent X S (d-(0:Vantage) 3).toNNReal ((0:Vantage) 3-(-1)).toNNReal F) (t:B=sent X S (z 3-d).toNNReal (z 3+1-z 3).toNNReal G): inner ℂ ω (A (B ω))=∫ y, Probe.plane y c.val * (↑(tinct 3 (z 3).toNNReal y):ℂ)∂(S.ℚmeasure.diagonal x):=by
 rw [← ContinuousLinearMap.adjoint_inner_left,h,t]; simp only [sent,ContinuousLinearMap.comp_apply,s,k,e]; rw [S.swing,←ContinuousLinearMap.comp_apply (S.E _),← S.time]
 have hp: (d-(0:Vantage) 3).toNNReal+(z 3-d).toNNReal=(z 3).toNNReal:= by
    ext; change ↑(d-0:ℝ).toNNReal + ↑(z 3-d).toNNReal = (↑(z 3).toNNReal:ℝ); simp only [sub_zero,Real.coe_toNNReal _ p.le,Real.coe_toNNReal _ g.le,Real.coe_toNNReal _ (sub_nonneg.mpr v.le)]; ring
 rw [hp]; exact (congrArg (fun u:X.Op=>inner ℂ x (u x)) (S.independent ..)).trans (during S _ c x)
end StrongStamp
open StrongStamp
private lemma warmGone (X:Hilbert)(S:OS.Semigroup X (3:Axis))(A:X.Op)(v:X) (r s:ℕ→ℝ≥0)(p:Tendsto r atTop (𝓝 0))(q:Tendsto s atTop (𝓝 0)) : Tendsto (fun i=>sent X S (r i) (s i) A v) atTop (𝓝 (A v)) := by
  have hv(u:X)(r:ℕ→ℝ≥0)(p:Tendsto r atTop (𝓝 0)): Tendsto (fun i=>S.E (r i) u) atTop (𝓝 u):= by
    have ht:= ((S.continuousE u).tendsto 0).comp p; rw [S.eZero] at ht; exact ht
  exact firmly (fun i=>S.E (r i)) zero_le_one (Eventually.of_forall fun i=> S.shrinks (r i)) (hv (A v) r p) (A.continuous.continuousAt.tendsto.comp (hv v s q))
namespace VoucherOp
variable {P: Spine}{x:P.Spectrum0 3}{n:ℕ}{b:ℕ→ℕ}{Z:Lead.Clan}(A:P.VoucherOp x Z n b)(a:Bool)(z:Vantage)
local notation "ξ"=> P.advocate 3 x 3
local notation "H"=> P.ManyF 3 ξ
local notation "H'"=> P.ColorHil 3 ξ
local notation "ω"=> P.heaven 3 ξ
local notation "ν"=> P.seasons 3 ξ
local notation "W"=> P.wealth 3 ξ
local notation "B"=> A.operator true
local notation "C" p:max=> P.tableau 3 ξ p (A.operator true)
local notation "S"=> (P.seasons 3 ξ).ℚmeasure
abbrev atDayPoint : P.ManyF 3 ξ:= W (A.issue (P.colorZero 3 ξ))
private lemma cartPage : (C z) ω= P.cartage 3 ξ z A.atDayPoint:=
  let T:= P.cartage 3 ξ; let F:= P.enter 3 ξ; let U:= B
  congrArg (fun v:H=> T z (W (U (F v)))) (P.cart_empty 3 ξ (-z)) -- ctor
private lemma identityPage : (C 0) ω=A.atDayPoint:= (A.cartPage (0:Vantage)).trans (congrArg (fun z:(H).Op=> z A.atDayPoint) (P.cart_zero ..))
/-- Test against the strict-frequency criterion. Energy in the projected sector
now, orientation field applied to vacuum ket. Essential qualification:
NOT testing that on the centered field. -/
theorem occupancy (h:Weather P x latch downDue n b): ((S).diagonal ((C 0) ω)) night ≠ 0 := ownsNight H ν ω (C 0) latch (purePrice Z) (purePrice_p Z) (P.stone_norm ..) fun _ u=> A.alongTrue latch downDue h (0:Vantage) u
-- ordered kernel density after DUTO costs. Center notation v₁ = 0, v_right= z; all time and Cartesian spatial center separations from 0
abbrev centerKernel (d:ℝ) : ℂ:= inner ℂ ω (A.reachedPillar false (0:Vantage) (-1) d (A.reachedPillar true z d (z 3+1) ω))
/-- Gap-finished PRICES of the center ordered kernel; λ=0 is attainable in
this Laplace test. The kernel is on actual limiting cost from `page_pass`,
`finished0` etc.; applied to strict-gap smearing as in `field_pass`.
Do not impute this to a centered transition w/a surviving finite shift! -/
theorem spectralPrice (d:ℝ)(h:0<d)(u:d<z 3) : A.centerKernel z d= ∫ y:E4, Probe.plane y (Spine.transverse (3:Axis) (fun i=>z i.val)).val * (↑(tinct 3 (z 3).toNNReal y):ℂ) ∂(S).diagonal ((C 0) ω):=
 let U:= Spine.transverse (3:Axis) fun i=> z i.val
 let X:= A.reachedPillar false (0:Vantage) (-1) d; let Y:= A.reachedPillar true z d (z 3+1); let W':= C z
 have he: W' ω=(ν).U U ((C 0) ω):= (A.cartPage z).trans (((congrArg (fun f:(H).Op=> f (A.atDayPoint)) (P.uses_cart 3 ξ z))).trans (congrArg ((ν).U U) A.identityPage.symm))
 page_eq H ν ω _ U _ _ X Y _ W' (h.trans u) h u rfl he (P.heaven_hot 3 ξ) (A.adjBackward (0:Vantage) (-1) d) (A.reached_unad true z d (z 3+1))
/-- Actual continuing price on projected OPs for positive lo/hi clearance,
now can take LAST heat pads to zero after width passage. Still this says
nothing about contact products, not building them simultaneously with width. -/
theorem landing (s t:ℕ→ℝ≥0)(p:Tendsto s atTop (𝓝 0))(q:Tendsto t atTop (𝓝 0))(v:P.ManyF 3 ξ) : Tendsto (fun i:ℕ=> sent H ν (s i) (t i) (P.tableau 3 ξ z (A.operator a)) v) atTop (𝓝 ((P.tableau 3 ξ z (A.operator a)) v)):= warmGone H ν _ v s t p q
end VoucherOp
#print axioms VoucherOp.occupancy
#print axioms VoucherOp.spectralPrice
#print axioms VoucherOp.landing
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
