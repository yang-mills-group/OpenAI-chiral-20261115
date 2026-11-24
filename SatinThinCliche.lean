import SatinThinArc

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
local notation "δ" s:max=> P.decades s
local notation "h₀" s:max=> P.pointEra s
local notation "ψ" s:max=> log (scaleY (F s))
local notation "Q!" s:max=>slotFee P.par s
local notation "a$$" s:max=> P.tallWorth s
local notation "Kx" s:max => (P.plannedK s:ℝ)
def rewardK (f r:ℕ):ℝ:= (P.megaK f r:ℝ)^4/(P.tallWorth r)
def repeatLoss (r:ℕ):= P.rewardK (P.pointEra r) r * slotFee P.par (P.pointEra r) / (zoomM P.par.R.L)^(r-P.pointEra r)
-- enough for this PPE price with C_f bounded. 
lemma tariff_law (s:ℕ): a$$ s = (Q! s) / ((scaleY (F s))^2):=by
 unfold tallWorth; rw [← thresh_eq (P.f_here s),show (thresh (F s))^2*(F s) = (scaleY (F s))^2 from ?_]; unfold thresh scaleY; rw [coin_pow,coin_pow]; conv_lhs=> rhs; rw [← coinY (P.f_here s)] -- tune replacing t
 rw [coin_mul]; ring_nf
lemma size_honors : ∀ᶠ s:ℕ in atTop, 0 < slotFee P.par s ∧ slotFee P.par s ≤ 2*slotFee P.par (s+1):=by
 filter_upwards [(turnover P.par).eventually (pal_U L (billX L) P.arc_price.le)] with s p; have hp:(F (s+1))=(F s)+billX L:=hat_succ ..; unfold slotFee; rw [hp]; exact ⟨p.1.trans_le p.2.1,p.2.2⟩
lemma reward_positive: ∀ᶠ s in atTop, 0 < P.tallWorth s ∧ ∀ f, 0< P.rewardK f s:=by
 filter_upwards [P.size_honors] with s p; have he:0<P.tallWorth s:=P.tariff_law s ▸ div_pos p.1 (pow_pos (coin_pos ..) _); exact ⟨he,fun f=>div_pos (pow_pos (Nat.cast_pos.mpr (P.pointK_pos ..)) _) he⟩
lemma size_holds : ∀ᶠ f:ℕ in atTop,∀ m:ℕ, Q! f ≤ 2^m * (Q! (f+m)):=by
 obtain ⟨A,t⟩:= eventually_atTop.mp P.size_honors
 filter_upwards [eventually_ge_atTop A] with f h m; induction m with
 | zero=> simp
 | succ m ih=> refine ih.trans ?_; rw [pow_succ,← Nat.add_assoc,mul_assoc]; exact mul_le_mul_of_nonneg_left (t (f+m) (h.trans (Nat.le_add_right ..))).2 (by positivity)
lemma era_upper : ∀ᶠ r:ℕ in atTop,P.repeatLoss r ≤ trailℓ (-1) (F r):=by
 filter_upwards [P.size_honors, P.future_payment.eventually P.size_holds, P.future_payment.eventually P.size_honors,P.root_visit,P.payment_late] with r p e t h q; let u:=h₀ r; let m:= r-u; let w:= scaleY (F r); let b:=P.baseK u; let a₀:=(L).val; have ha:0<(a₀:ℝ):=by exact_mod_cast P.par.R.L.property
 have hp:0<w:= coin_pos ..; have hW:0≤log w:= show 0 ≤ P.diameterEra r from P.diameter_view r ▸ sq_nonneg _; have hR:(Q! u)≤2^m*Q! r:=by have he:=e m; change (Q! u) ≤2^m*(Q! (u+m)) at he; rwa [show u+m=r from Nat.add_sub_of_le q.2.1.le] at he
 let k:ℝ:= (a₀:ℝ)^m; have hk:0<k:=pow_pos ha m; let c:= (Q! u)/(Q! r); have hc:0<c:= div_pos t.1 p.1; have hc': c ≤2^m:= (div_le_iff₀ p.1).mpr hR
 have hL:P.repeatLoss r = (b:ℝ)^4 * w^2 * c / 512^m:=by
    unfold repeatLoss rewardK; rw [P.tariff_law]; change ((P.megaK u r:ℝ)^4/(Q! r/w^2))*Q! u / (512*(a₀:ℝ)^4)^m= _; rw [show (P.megaK u r:ℝ)= k*(b:ℝ) by unfold megaK; rw [Nat.cast_mul,Nat.cast_pow],mul_pow, mul_pow, show ((a₀:ℝ)^4)^m= k^4 by unfold k; rw [←pow_mul,←pow_mul,Nat.mul_comm 4 m]]; change (k^4* (b:ℝ)^4/_ )*_/(512^m * k^4)=_; unfold c; field_simp [hk.ne', hp.ne', p.1.ne']
 rw [hL, show trailℓ (-1) (F r)=w⁻¹ by unfold w scaleY; rw [coin_inv,neg_zero]]; apply le_trans (b:= w^4*w^2*2^m/512^m) ?_ ?_
 · apply div_le_div_of_nonneg_right _ (by positivity); apply mul_le_mul _ hc' hc.le (by positivity); exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) h _) (sq_nonneg _)
 suffices hw:w^7 ≤ 256^m by
    field_simp
    rw [show (512:ℝ)^m=(2:ℝ)^m *256^m by rw [←mul_pow]; norm_num]
    nlinarith only [mul_le_mul_of_nonneg_left hw (show 0 ≤ (2:ℝ)^m by positivity)]
 rw [height_calc w hp 7, height_calc 256 (by norm_num)]; apply Real.exp_monotone
 have hv:(m:ℝ)≥20*log w:=by rw [show m = P.decades r from q.2.2]; exact Nat.le_ceil _
 norm_num
 nlinarith [show 1/2 ≤ log (256:ℝ) from le_trans (Real.log_two_gt_d9.le.trans' (by norm_num)) (Real.log_le_log (by norm_num) (by norm_num)),show 0 ≤ (m:ℝ) by positivity] -- norm_num may err
lemma era_complete : Tendsto P.repeatLoss atTop (𝓝 0):=by
 apply squeeze_zero' _ P.era_upper (shrinkT (P:=P.par) (v:=1) zero_lt_one)
 filter_upwards [P.reward_positive, P.future_payment.eventually P.size_honors] with r p q; exact (div_pos (mul_pos (p.2 _) q.1) (pow_pos (zoomM_p _) _)).le
-- arbitrarily small continuum clearance later. 
open Aria MacroGrid
abbrev flightCap (f:ℕ):ℝ:= (P.baseK f:ℝ) * P.macroStep f / P.sidesPerTick
lemma flight_pos(f:ℕ): 0<P.flightCap f:=div_pos (mul_pos (Nat.cast_pos.mpr (P.payment_pos _)) (P.macroStep_pos _)) (Nat.cast_pos.mpr P.sides_pos)
private lemma shadowed_t (m:Mesh)(b t:ℝ): Tendsto (fun i:ℕ=> (b+(i:ℝ)*t)* (mill m i:ℝ)) atTop (𝓝 0):=by
 let k:ℝ:= (m.base:ℝ); let z:ℝ:=(m.L:ℝ); have hz: (1:ℝ)<z:=by unfold z; exact_mod_cast m.Llarge
 have hu:=vanishes m; have ht:= NNReal.tendsto_coe.mpr hu; let D:= tendsto_pow_const_div_const_pow_of_one_lt 1 hz; have he:Tendsto (fun i:ℕ=>(i:ℝ)/z^i) atTop (𝓝 0):=by simpa only [pow_one] using D
 have hx: Tendsto (fun i:ℕ=> b*(mill m i:ℝ) + k*t*((i:ℝ)/z^i)) atTop (𝓝 0):=by simpa only [NNReal.coe_zero,mul_zero, add_zero] using (ht.const_mul b).add (he.const_mul (k*t))
 refine hx.congr fun i=>?_ ; unfold mill k z; push_cast; ring -- definition of D using let proposition notation?
lemma flight_soon: Tendsto P.flightCap atTop (𝓝 0):=by
 let A:= fun s=>F s * P.macroStep s /P.sidesPerTick; have he: Tendsto A atTop (𝓝 0):=by simpa only [zero_div,A,macroStep,hat] using ((shadowed_t (timeMesh P.par) P.par.x (billX P.par.R.L)).div_const (P.sidesPerTick:ℝ))
 refine squeeze_zero' (Eventually.of_forall (fun i=>(P.flight_pos i).le)) ?_ he
 filter_upwards [P.pays_root_mile,(turnover P.par).eventually (coin_budget (a:=0) (b:=1) (c:=0) (d:=1) (e:=0) (f:=0) (Or.inl zero_lt_one) 1 1 zero_lt_one)] with i h j; rw [coinY (P.f_here i),one_mul,one_mul] at j; exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (h.trans j.le) (P.macroStep_pos _|>.le)) (Nat.cast_nonneg _)
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.era_complete
