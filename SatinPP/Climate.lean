import SatinPP.Price
import SatinThinVisit
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry

open TopologicalSpace
namespace Spine
open Lamour.Bridge.Celeste
open Lamour.Bridge.Celeste.Morn
open Py.Rate.LocalLimit.Papal (Weaver household)
open TopologicalSpace Tapestry.Exhibition
variable (P:Spine)(R : P.Register)(j:Axis)
open Papal Regis.Head Gleam
open Clock Clock.Hookah Clock.Hookah.Blaze
open Preparation.Yoke Yoke.Travel Regis.Head.Garland
open QuadClock Again Pressure
variable {s t f r v i k:ℕ}
open CF.Pannier.Chancel CF.Py.Rate.LocalLimit.Preparation.Yoke
open Worth Pays CF.BProof
open Real (log)
open Aria Casting MacroGrid
local notation "W"=>P.calibration
local notation "Q"=>P.par.block
variable (x:P.Spectrum0 3)
local notation "ξ"=>P.advocate 3 x j
local notation "Y"=>P.physicalEnergy j ξ
local notation "L"=>P.par.R.L.val
local notation "Υ"=>timeMesh P.par

def fifth(B e:ℝ):ℝ:= B/e^5
lemma fifth_pos {B e:ℝ}(p:0<B)(h:0<e):0<fifth B e:=div_pos p (pow_pos h _)
variable {A C b B e:ℝ}{g m:ℕ}
local notation "J"=>ℕ×ℕ
local notation "lock"=>P.locket j ξ
local notation "tier"=> P.par.R.L
-- match elected consumption
structure Climate (C:ℝ): Prop where
 night:P.NightCop
 temple:∀ᶠ s:ℕ in atTop,∀ᶠ i:ℕ in atTop,∀ k:ℕ, (P.run.voyage i).kick ≤ k→s≤P.run.uv k→Yoke.ShelterCost C P.run s i k
 aug:15∣P.par.R.L.val
 days:P.par.R.L.val%16=1

variable (Y₀:P.Climate C)
lemma fare_price (p:64<L)(r:ℕ): fareMin tier r ≤ 1:=by
    apply pow_le_one₀ (by positivity)
    rw [inv_pow,←div_eq_mul_inv]
    have hl:(64:ℝ)<L:= by exact_mod_cast p
    exact div_le_one_of_le₀ (hl.le.trans (le_self_pow₀ (by linarith only [hl]) (by decide:4≠0))) (by positivity)
/-- All-scale hypotheses at every large r. -/
structure Weather_LocalFieldBounds (P:Spine)(A C:ℝ)(g s r:ℕ):Prop where
 space:g≤P.pointEra r
 ready:P.pointEra r < r
 after:s ≤ r
 clear:∀ l,P.Clearance (P.pointEra r) (P.pageChoice (P.pointEra r)) (P.rootSpace g (P.pointEra r) l)
 close:∀ v ≥r,P.CloseRates A C (P.pointEra r) r v

include Y₀ R
lemma weather (s g:ℕ)(A:ℝ): ∀ᶠ r in atTop, Weather_LocalFieldBounds P A C g s r:=by
 let a:=P.future_payment
 filter_upwards [P.payment_late, a.eventually_ge_atTop g,eventually_ge_atTop s, a.eventually P.choice_late,
   P.close_rates_late R Y₀.night A C Y₀.temple] with r u h k t v
 exact ⟨h,u.2.1,k,t g,v⟩


omit R
local notation "point! " r:max=> P.pointEra r

lemma price_small (s g r:ℕ)(u:g<s)(p:Weather_LocalFieldBounds P A C g s r)(l:List Axis)
   (e:ℝ)(t:P.menuSize (1/2) r < e):
    ∀ᶠ v:ℕ in atTop,∀ {c a y},Workforce A C g v P c a y →
   roomFee A * |a (g,s)| * ‖lock ((P.basePlay x g v).pivot P l) e e‖ ≤
    8*zoomC P.par.R.L^r:=by
 have ht:P.pageFull (P.pointEra r)≤e:=by rw [←P.page_menu]; exact t.le
 have hu:Odd L:=by have h:=Y₀.days; exact ⟨L/2,by omega⟩
 have h:=P.price_base Y₀.aug Y₀.days
 filter_upwards [eventually_ge_atTop r,P.pose_earned j x _ _ p.space hu l] with v hv z c a y b
 obtain ⟨d,k,m,Z⟩:=z
 have v₀:chargeSpan g v (g,s):=⟨le_rfl,u,p.after.trans hv⟩
 have vl:chargeSpan g v (P.pointEra r,r):=⟨p.space,p.ready,hv⟩
 have q:=P.pose_cost j x Y₀.night (b.plans _ vl) (p.clear _) (p.close _ hv) (P.fare_price h _) Z ht
 have hy:0 <roomFee A:=div_pos (Real.exp_pos _) (by norm_num)
 rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_of_pos hy] at q

 let a':=a (P.pointEra r,r)
 let y:=zoomC P.par.R.L
 have q':|a (g,s)| ≤ 4*y^r*|a'|:= (b.career (g,s) (P.pointEra r,r) v₀ vl p.after).trans 
    (mul_le_mul_of_nonneg_right
     (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (zoomC_p _) (Nat.sub_le _ _)) (by norm_num)) (abs_nonneg _))
 apply le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left q' hy.le) (norm_nonneg _))
 have hy':0≤y:=zero_le_one.trans (zoomC_p _)
 change roomFee A*|a'| * _ ≤ 2 at q
 refine le_trans (le_of_eq ?_) ((mul_le_mul_of_nonneg_left q (by positivity : 0 ≤ 4*y^r)).trans_eq ?_)
 · ring
 unfold y; ring

include R
/-- Eventual on the voters. One constant suffices for all axes,
pivots, and coalitions taken far enough into the tail.
-/
lemma fifth_votes (g s:ℕ)(h:g<s){v:ℕ→ℕ}{a:ℕ→J→ℝ}
   (T:ScoutAnthem P x A C g s b v a):
    ∃ B:ℝ,0<B ∧ ∀ e:ℝ,0<e→e ≤ 1→∀ j:Axis, ∀ l:List Axis,
     ∀ᶠ i in atTop,
       ‖((P.rewardK g s * a i (g,s):ℝ):ℂ) • P.locket j (P.advocate 3 x j)
            ((P.basePlay x g (v i)).pivot P l) e e‖ ≤ fifth B e:=by
 obtain ⟨R',y⟩:=T.station
 obtain ⟨B,d,t⟩:=P.menu_fifth (P.price_base Y₀.aug Y₀.days) (by norm_num : (0:ℝ)<1/2)
    (P.weather R Y₀ s g A)
 let K:=|P.rewardK g s|
 have hu:0<roomFee A:=div_pos (Real.exp_pos _) (by norm_num)
 let u:=roomFee A
 have hu':0<u:=hu
 refine ⟨(K+1)*8*B/u,by unfold K;positivity,?_⟩ 
 intro e g₀ g₁ j l
 obtain ⟨r,w,p,q⟩:=t e g₀ g₁
 filter_upwards [y.fast.tendsto_atTop.eventually (P.price_small j x Y₀ s g r h w l e p)] with i hi
 obtain ⟨c,l,H⟩:=y.cruise i

 specialize hi H
 rw [norm_smul, Complex.norm_real,Real.norm_eq_abs,abs_mul]
 unfold fifth
 rw [div_right_comm _ u]; apply (le_div_iff₀ hu').mpr
 have ht:0≤K:=abs_nonneg _
 have hz:0≤zoomC P.par.R.L:=zero_le_one.trans (zoomC_p _)
 have he:=mul_le_mul_of_nonneg_left q (show (0:ℝ)≤8 from by norm_num)
 refine le_trans (le_of_eq ?_) ((mul_le_mul_of_nonneg_left (le_trans hi he) ht).trans ?_)
 · unfold K u; ring
 rw [_root_.mul_div_assoc]; simp only [←mul_assoc]
 gcongr; linarith

end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.fifth_votes

