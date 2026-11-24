import SatinFixedContrastNovember4
import SatinThinReproofClock
/-! # CP16. At each stencil of the THIN probes. Test the REAL `tableau` operators (gaps), and the hypotheticals for these bodies from the references (even using only Hilbert-space positive-heat costs & ordinary boundaries).

READ qualifications. No statement about general local theories OR distributional hypotheses. Use the matching on sufficiently late center tests; also `CenteredAt`-type prices, not requiring all spatial directions. (See `CenterPays`.) -/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 330000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Casting Six OS.Semigroup OS.Semigroup.Balloon
open MacroGrid SatinNucleus SatinJets DoseTravel Set
open YM.SatinMacro YM.SatinEdge
variable (P:Spine)(x:P.Spectrum0 3)
local notation "ξ"=> P.advocate 3 x 3
local notation "H"=> P.ColorHil 3 ξ
local notation "G"=> P.ManyF 3 ξ
local notation "Ω"=> P.heaven 3 ξ
local notation "ω"=> P.colorZero 3 ξ
local notation "S"=> P.seasons 3 ξ
local notation "π'"=> P.wealth 3 ξ
local notation "E!"=> (S).E
local notation "U!"=> (S).U
local notation "κ"=> (S).unit
local notation "ℒ"=> Lead.Clan
variable (A:P.Apron)(p:Vantage)
def orderedStripe (t:ℝ):ℂ:= P.commonWell 3 x (usher (A.kiss P 3) A) (usher 0 (rollCall p t)) [false,true]
local notation "V" => P.orderedStripe x A p
local notation "w" => A.realWidth P 3
local notation "t!" => (w+w)
variable (Y:P.birthF 3 A.s A.F)
local notation "B" => π' (P.thinOrigin x A Y)
local notation "v" => sameRest p
lemma stripe_price (K:P.Ellis 3 x)(t:ℝ)(q:t ∈ Ioi t!): V t= SatinMacro.kernel (S) (B) (B) v t.toNNReal:=by
 let x':= rollCall p t; have ht : x' 3=t := roll_price_time p t
 unfold orderedStripe; rw [P.thin_kernel x A Y A Y 0 _ K (by rw [roll_price_time]; change 0+(w) < t - (w); linarith only [show w+w<t from q]),Pi.zero_apply,sub_zero,sub_zero, P.roll_uses x p t, roll_price_time]; rfl
lemma stripe_zero (K:P.Ellis 3 x) : CenterPays v V (S) B B 0:= by
 unfold CenterPays; filter_upwards [eventually_gt_atTop t!] with i h; rw [NNReal.coe_zero, add_zero, add_zero]; exact P.stripe_price x A p Y K i h
local notation "w₀" => Real.toNNReal w
abbrev realTable : (G).Op:= P.tableau 3 ξ 0 (A.engine P 3 ξ)
local notation "A!"=> P.realTable x A
local notation "W"=> A! Ω
-- the real tests will be for *same* two labels at this point center using `Mink.Geometry`.
lemma roll_label_pay : W= E! w₀ B := by rw [realTable,P.tableMaps,P.cart_zero,ContinuousLinearMap.id_apply]; exact P.thinCenterEntry x A Y
lemma roll_label_adj : star A! = P.realTable x (A.kiss P 3):=by
 unfold realTable; rw [P.lives_twin,show mirrorΩ 3 (0:Vantage) = 0 from (by funext i; by_cases h:i=3<;> simp [mirrorΩ,h])]
-- use even ALL positive gaps in the actual width 2w interpretation of the two prices.
include Y in
lemma roll_gap_pay (K:P.Ellis 3 x)(t:ℝ)(q:t ∈ Ioi t!): V t= SatinMacro.kernel (S) (W) (W) v ((t-t!).toNNReal):=by
 have hp : (w₀:ℝ)=w:= Real.coe_toNNReal _ (A.real_width_pos P 3).le
 rw [P.stripe_price x A p Y K t q, P.roll_label_pay x A Y]; refine Eq.trans ?_ (cost_both v (S) B B ((t-t!).toNNReal) w₀).symm; congr 1; ext; rw [Real.coe_toNNReal, NNReal.coe_add,NNReal.coe_add,hp,Real.coe_toNNReal _ (sub_nonneg.mpr (LT.lt.le (show _ < _ from q)))]; ring; linarith only [A.real_width_pos P 3,show t!<t from q]
structure MarkRefusal : Prop where
 -- B is center vector WITHOUT conventional extra time damping on top.
 center : CenterPays v V (S) B B 0
 -- nonetheless also gets positive-energy further extension there on vector itself.
 padding : HasPadding (S) B
 dark : (S).orth B = 0
 pay_label(t:ℝ)(q:t ∈ Ioi t!) : V t= SatinMacro.kernel (S) (W) (W) v ((t-t!).toNNReal)
 gap : CenterPays v V (S) (W) (W) w₀
 deep : ∃ᶠ t:ℝ in atTop, V t≠0
 conflict (r:ℝ≥0) : ThinRefusal v V r
 output (a b:ℝ)(q:a<b): ∃ t∈ Ioo a b, inner ℂ Ω ((star A! * (YM.SatinMacro.act (κ) (sameTravel p t) (A!))) Ω) ≠ inner ℂ Ω (((YM.SatinMacro.act (κ) (sameTravel p t) (A!))*star A!) Ω) ∧ ¬ Commute (star A!) (YM.SatinMacro.act (κ) (sameTravel p t) A!)
lemma mark_refuses (K:P.Ellis 3 x)(d:(S).orth B = 0)(u:HasPadding (S) B) (i:ℝ)(p': i ∈ Ioi t!)(v': V i ≠ 0) : P.MarkRefusal x A p Y:=by
 have h(a:ℝ≥0): CenterPays v V (S) (E! a B) (E! a B) a:= by simpa only [zero_add] using (paid_later v V (S) B B 0 a (P.stripe_zero x A p Y K)) -- order
 have g:CenterPays v V (S) (W) (W) w₀:= (P.roll_label_pay x A Y).symm ▸ (h w₀)
 have m:∃ᶠ t:ℝ in atTop, V t ≠ 0:= by
    have hv : 0 < i := lt_trans (add_pos (A.real_width_pos P 3) (A.real_width_pos P 3)) p'
    let l:= fun t:ℝ=> SatinMacro.kernel (S) B B v t.toNNReal
    have ha:AnalyticOnNhd ℝ l (Ioi 0):= by simpa only [add_zero,neg_zero] using real_analytic_shift (S) B B v 0
    have hz:∃ᶠ s:ℝ in atTop,l s ≠ 0:= traveler l 0 ⟨ha,i,hv,(P.stripe_price x A p Y K i p').symm.trans_ne v'⟩
    exact (hz.and_eventually (eventually_gt_atTop t!)).mono fun i h=> (P.stripe_price x A p Y K i h.2).trans_ne h.1
 have f(a:ℝ≥0): ThinRefusal v V a:= padded_price_refuses v V (S) (E! a B) (E! a B) a (h a) m (dark_later (S) B _ d) (padded_later (S) B _ u)
 refine ⟨P.stripe_zero x A p Y K,u,d,P.roll_gap_pay x A p Y K,g,m,f,fun a b q=>?_⟩
 obtain ⟨t,ht,he⟩:= f w₀ G (S) (W) ((star A!) Ω) W ((star A!) Ω) g a b q
 exact ⟨t,ht,fun hh=> he ((swap_iff (κ) (sameTravel p t) _ (P.roll_static x) A! A!).mpr hh),fun hh=> he (swap_of_commute (κ) (sameTravel p t) _ (P.roll_static x) _ _ hh)⟩
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.roll_label_adj
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.mark_refuses
