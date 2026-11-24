import SatinThinAngle

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
local notation "φ"=> P.groundZero j
local notation "μ"=> P.pillars j
local notation "W"=> P.calibration
local notation "Q"=> P.par.block
local notation "ℓ"=> P.calibration.ℓ
open Papal Regis.Head Gleam
/-! # Price of ensemble-of-trips. Exactly composed on printed test level before estimation. -/
open Clock Clock.Hookah Clock.Hookah.Blaze
open Preparation.Yoke Yoke.Travel Regis.Head.Garland
open QuadClock Again Pressure
variable {s t f r v i k:ℕ}
local notation "Y"=> P.run
local notation "Λ"=> P.par
local notation "L"=> P.par.R.L
local notation "H"=>P.large
local notation "F" s:max=>hat P.par.R.L P.par.x s
local notation "N" s:max i:max => Journey.side P.run i s
/-! # Buy height and travel together. Keep both actual calibration and rank resolution schedule. -/
open CF.Pannier.Chancel CF.Py.Rate.LocalLimit.Preparation.Yoke
open Worth Pays CF.BProof
open Real (log)
abbrev diameterEra (r:ℕ):ℝ:= Real.log (scaleY (F r))
local notation "W" i:max=> P.diameterEra i -- W reused above? 
abbrev decades (r:ℕ):=Nat.ceil (20*P.diameterEra r)
def pointEra (r:ℕ):ℕ:=r-P.decades r
abbrev baseK (f:ℕ):ℕ:=2*P.axleQ 3 (P.thresholdF f)+1
abbrev baseRoot(f:ℕ):Cover:=fun _ => (P.plateau f) 3
abbrev megaK(f r:ℕ):ℕ:=P.par.R.L.val^(r-f)* P.baseK f
abbrev plannedK (r:ℕ):ℕ:= P.megaK (P.pointEra r) r
lemma brand : nodeC (P.baseRoot f)=(fun _=>↑(P.baseK f)):=by ext j; unfold baseK; simp [baseRoot,plateau,nodeC,two_smul,two_mul]
lemma clock_brand(a:Axis): P.clockPlate f r (P.baseRoot f) a=(P.megaK f r:ℤ):=by unfold clockPlate megaK; rw [Pi.smul_apply,P.brand,nsmul_eq_mul]; push_cast; rfl
lemma payment_pos (f:ℕ): 0<P.baseK f:= Nat.succ_pos _
lemma pointK_pos (f r:ℕ):0<P.megaK f r:= mul_pos (pow_pos (L).property _) (P.payment_pos f)
lemma diameter_view (s:ℕ): W s=(Real.log (Real.log (F s)))^2:=by unfold diameterEra; rw [coin_scale,Real.log_exp]
lemma f_here (s:ℕ): 0 < F s:=((Real.exp_pos 1).trans_le P.large).trans_le (Vale.crown ..)
lemma diameter_go : Tendsto P.diameterEra atTop atTop:= Real.tendsto_log_atTop.comp ((summitT 1 zero_lt_one).comp (turnover P.par))
lemma decades_go : Tendsto (fun r:ℕ=> (P.decades r:ℝ)) atTop atTop:= tendsto_atTop_mono (fun x=> Nat.le_ceil (20*W x)) (Filter.Tendsto.const_mul_atTop (by norm_num : (0:ℝ)<20) P.diameter_go)
-- sublinear gap
lemma diameter_fee (c:ℝ) (u:0<c): ∀ᶠ s:ℕ in atTop,P.decades s ≤ c*F s:=by
 filter_upwards [(turnover Λ).eventually (coin_budget (a:=0) (b:=1) (c:=0) (d:=1) (e:=0) (f:=0) (Or.inl zero_lt_one) 21 c u)] with s h
 have h0:0≤W s:=P.diameter_view s ▸ sq_nonneg _; have hz:P.diameterEra s + 1 ≤ scaleY (F s):= (Real.add_one_le_exp _).trans_eq (Real.exp_log (coin_pos ..)); rw [coinY (P.f_here s)] at h
 have hl: (P.decades s:ℝ) ≤ (20:ℝ)*W s+1:= le_of_lt (Nat.ceil_lt_add_one (show 0 ≤ 20*W s from mul_nonneg (by norm_num) h0)); unfold scaleY at hz; linarith only [hl,h,h0,hz]
lemma arc_price:0<billX P.par.R.L:= mul_pos (Gauge.slopeConstant_pos (by exact Thera.yet_one)) (Real.log_pos (by exact_mod_cast (show 1<(L).val by have he:=P.par.V.tallX; omega)))
lemma payment_late : ∀ᶠ r:ℕ in atTop,P.decades r*2 ≤ r ∧ P.pointEra r<r∧r-P.pointEra r=P.decades r:=by
 let v:=billX P.par.R.L; let b:=(4*v)⁻¹; have hv:0<v:=P.arc_price; have he:0<b:=by unfold b; positivity
 filter_upwards [P.diameter_fee b he,eventually_gt_atTop 0, tendsto_natCast_atTop_atTop.eventually_ge_atTop (2*b*P.par.x*2), P.decades_go.eventually_gt_atTop 0] with r t p h q
 have hh: b*(4*v)=1:= inv_mul_cancel₀ (show _ from mul_ne_zero (by norm_num) hv.ne')
 have hn: (P.decades r)*2 ≤ r:=by
   have hq:  (P.decades r:ℝ)*2 ≤ (r:ℝ):=by change (↑(P.decades r):ℝ) ≤ b*(P.par.x + (r:ℝ)*v) at t; have ht: (2:ℝ)*b*P.par.x*2≤ ↑r:=h; linarith only [t,ht, congrArg (· * (r:ℝ)) hh] -- products expand? linarith nonlin
   exact_mod_cast hq
 have h':0<P.decades r:=Nat.cast_pos.mp (show (0:ℝ)< P.decades r from q); unfold pointEra; omega
lemma future_payment : Tendsto P.pointEra atTop atTop:=by
 refine Filter.tendsto_atTop.mpr fun d=>?_ ; filter_upwards [P.payment_late, eventually_ge_atTop (2*d)] with r p h; unfold pointEra; obtain ⟨t,u,v⟩:=p; omega
lemma base_height {r s:ℕ} (h:r ≤ s) : (F r) ≤ (F s):= by unfold hat; gcongr; exact P.arc_price.le
lemma pays_root_mile : ∀ᶠ r:ℕ in atTop, (P.baseK r:ℝ) ≤ scaleY (F r):=by
 have he(r:ℕ): P.thresholdF r= radiusB (F r):=(P.run.meter.boot r).2.1
 have h: Worth.Pays 0 0 6 (fun x:ℝ=> 2*(P.axleQ 3 (radiusB x):ℝ)+1):= plus (Pays.scale 2 (P.width_ledger 3)) (Worth.Pays.merit (constant _) (by norm_num [Worth.Earlier]))
 filter_upwards [(turnover Λ).eventually (leap (w:=0) (p:=1) (q:=0) h (by norm_num [Worth.Earlier]))] with r u; unfold baseK; rw [he,Nat.cast_add_one,Nat.cast_mul,Nat.cast_ofNat]; exact u
lemma root_visit : ∀ᶠ r:ℕ in atTop, (P.baseK (P.pointEra r):ℝ) ≤ scaleY (F r):=by
 let f:=P.pointEra; let Wt:= hat P.par.R.L P.par.x
 filter_upwards [P.future_payment.eventually P.pays_root_mile, (Real.tendsto_log_atTop.comp ((turnover Λ).comp P.future_payment)).eventually_ge_atTop 1] with r h p
 refine h.trans ?_; rw [coin_scale,coin_scale]; let a:= log (Wt (f r)); let b:=log (Wt r); have ht:1≤a:=p; have hv:a≤ b:=Real.log_le_log (P.f_here _) (P.base_height (Nat.sub_le ..)); exact Real.exp_monotone (pow_le_pow_left₀ (Real.log_nonneg ht) (Real.log_le_log (by linarith only [ht]) hv) 2)
abbrev depthCap := 1+20* Real.log P.par.R.L.val
lemma depthCap_pos : 0<P.depthCap:=by
 have hp:1 < (P.par.R.L.val:ℝ):=by exact_mod_cast (timeMesh P.par).Llarge -- nat
 unfold depthCap; linarith [Real.log_pos hp]
lemma height_calc (t:ℝ)(h:0<t)(n:ℕ): t^n= Real.exp ((n:ℝ)*Real.log t):=by rw [Real.exp_nat_mul, Real.exp_log h] -- tune
lemma planned_ceiling : ∀ᶠ r in atTop,(P.plannedK r:ℝ) ≤ P.par.R.L.val* trailℓ P.depthCap (F r):=by
 filter_upwards [P.root_visit,P.payment_late] with r h q
 let y:= P.par.R.L.val; let t:=log (y:ℝ); have ht:0<t:= Real.log_pos (by exact_mod_cast (timeMesh P.par).Llarge); let m:=P.decades r; unfold plannedK megaK; rw [q.2.2,Nat.cast_mul,Nat.cast_pow]
 have hc:(m:ℝ) ≤ 20*W r+1:= le_of_lt (Nat.ceil_lt_add_one (show 0 ≤ 20*W r by rw [P.diameter_view]; positivity)); let k:=F r
 change (y:ℝ)^m * _≤ (y:ℝ)*trailℓ _ k; have hp:=coin_pos (F r) 0 1 0; refine le_trans (mul_le_mul_of_nonneg_left h (pow_nonneg (Nat.cast_nonneg _) _)) ?_
 rw [height_calc (t:=(y:ℝ)) (by exact_mod_cast P.par.R.L.property)]; nth_rw 1 [show scaleY (F r)=Real.exp (W r) from (Real.exp_log hp).symm]; rw [←Real.exp_add]; change Real.exp ((m:ℝ)*t+W r)≤_
 have hz:(y:ℝ)=Real.exp t:=(Real.exp_log (show 0<(y:ℝ) by exact_mod_cast P.par.R.L.property)).symm; rw [show trailℓ P.depthCap k= Real.exp (W r * P.depthCap) from ?_, hz,← Real.exp_add]
 · exact Real.exp_monotone (by change _≤ t+W r*(1+20*t); nlinarith only [mul_le_mul_of_nonneg_right hc ht.le]) -- rw hz changes t inside Real.exp and left? !
 rw [P.diameter_view]; unfold trailℓ BProof.coin; simp [k]
lemma planned_grows : Tendsto (fun r=> (P.plannedK r:ℝ)) atTop atTop:=by
 have he:Tendsto (fun r:ℕ=>r-P.pointEra r) atTop atTop:= (tendsto_natCast_atTop_iff.mp P.decades_go).congr' (P.payment_late.mono fun r h=> h.2.2.symm)
 let t:ℝ:= (L).val; have ht:1<t:=by unfold t; exact_mod_cast (timeMesh P.par).Llarge
 refine tendsto_atTop_mono (f:=fun r:ℕ=> t^(r-P.pointEra r)) (fun r=>?_) ((tendsto_pow_atTop_atTop_of_one_lt ht).comp he)
 unfold plannedK megaK; rw [Nat.cast_mul,Nat.cast_pow]; exact le_mul_of_one_le_right (pow_nonneg (by positivity : (0:ℝ)≤ _) _) (by exact_mod_cast P.payment_pos (P.pointEra r))
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.planned_grows
