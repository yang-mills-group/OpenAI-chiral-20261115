import YM.SU5.May.LunarDials
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.May.Lunar
open Function Filter Finset Lattice Laurent Next.Free Bloch Fir Real Complex MeasureTheory WithLp
open scoped Topology BigOperators ContDiff Matrix InnerProductSpace ENNReal ComplexOrder Classical Matrix.Norms.L2Operator
open Lat Onyx Flare Fock Buffered.Lifted Buffered.Afterglow.Tower Buffered.Afterglow.Tower.Tilted Window.ArchiveK Window.Largo
open SU Tulip Hygrometry Personality Rush Dial Cube Kea Emu Tilted May.Floe
attribute [local instance] opCStarAlgebra
open Rink
variable (N:Side)(P:Ramp)(p q:E4)(i:Title P)(x:Cover)(b:Bool) (v:Ket SpinIdx) (x':ℝ)(a:Slot)
variable {D j:ℕ}(J:Fin D)
local notation "T"=>rimB N
local notation "G" => chord N P i
local notation "ε" => ‖chord N P i‖
local notation "β" => warp b (chord N P i)
local notation "L"=> lengthT P
-- attach functions
noncomputable def encore (P:Ramp)(p:E4)(a:Slot)(v:Ket SpinIdx):Screen:= PiLp.single 2 a (acts (hymnP P p) v)
lemma encore_value(u:p≠0)(e:inner ℝ (tilted P) p=0): ‖encore P p a v‖≤2*‖v‖:=by rw [encore,PiLp.norm_single]; exact hunt P p v e u
lemma cross_n : (warp b (-(chord N P i)))= -(warp b (chord N P i)):=by cases b<;> rfl
lemma adapt : warp b (x' • p)=x' • warp b p:=by cases b; rfl; simp [warp]
noncomputable def envelopeT (P:Ramp)(p:E4)(x:Cover)(b:Bool):ℂ:= Complex.I* (inner ℝ (warp b p) (age x))-(‖p‖*faceN P x:ℝ)
def basisP := encore P (- warp b (chord N P i)) a v
-- order due binder. note basisP likely N P i b v a
noncomputable def approach(N:Side)(P:Ramp)(i:Title P)(b:Bool)(x:Cover)(a:Slot)(v:Ket SpinIdx)(u:ℝ):Screen:= Complex.exp (envelopeT P (chord N P i) x b*u) • basisP N P i b v a
local notation "Y"=> envelopeT P (chord N P i) x b
lemma basis_cost: ‖basisP N P i b v a‖≤ 2*‖v‖:=by apply encore_value P; apply neg_ne_zero.mpr (warp_hired _ _ (duet N P i) (hired N P i) b); rw [inner_neg_right,warp_cross P _ (duet ..) (hired N P i), neg_zero]
lemma downstairs : approach N P i b x a v (-1)=back N P i b x a v:=by
 unfold approach back basisP gramF; apply congrArg (· • encore P (- warp b (chord N P i)) a v); unfold envelopeT coastE poreP; push_cast; rw [←Complex.exp_add]; ring_nf
local notation "j*"=> arenaI P i J j
lemma ascends (u:j∈fling D): approach N P i b x a v (rateD J j)= forward N P (arenaI P i J j) b x a v:=by
 let B:= rateD J j; have h:0<B:=zero_lt_one.trans_le (rate_profit J u); unfold approach forward gramF basisP encore; rw [scaleH N P i J u,askSale,adapt,cross_n,hymnP,hymnP,seam_d P _ (rateD J j) (show 0 < rateD J j from h)]; -- rw hymn at LHS first! 
 rw [real_inner_smul_left,inner_neg_left]; congr 1; unfold envelopeT coastE poreP; push_cast; rw [← Complex.exp_add]; ring_nf
variable (t:Legible P N x)(e:grain P i ≤ (D:ℝ))(d:6≤ D)(w:‖age x‖≤ hazySize D N)
private lemma sBound(y:Cover)(r:‖age y‖≤x') : |faceN P y|≤ x':=by unfold faceN lengthT; apply (abs_real_inner_le_norm ..).trans; rw [rulerL P,one_mul]; exact r
include e d w
private lemma pay : ‖envelopeT P (chord N P i) x b‖≤2*‖chord N P i‖* hazySize D N:=by
 unfold envelopeT; refine (norm_sub_le ..).trans ?_; rw [norm_mul,Complex.norm_I, one_mul,norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs]; let Y':=hazySize D N; rw [abs_mul, abs_of_nonneg (norm_nonneg _)]; have ht: |inner ℝ (warp b (chord N P i)) (age x)| ≤ ‖chord N P i‖*Y':= by refine (abs_real_inner_le_norm ..).trans ?_; rw [warp_size _ (hired N P i)]; gcongr
 exact (add_le_add ht (mul_le_mul_of_nonneg_left (sBound P Y' x w) (norm_nonneg _))).trans_eq (by unfold Y'; ring)
lemma enhance (p:j∈fling D): ‖envelopeT P (chord N P i) x b*(rateD J j:ℂ)‖≤1:=by
 rw [norm_mul,mul_comm,Complex.norm_real]; have hp:0≤rateD J j:=zero_le_one.trans (rate_profit J p); rw [Real.norm_of_nonneg hp]; exact (mul_le_mul_of_nonneg_left (pay N P i x b e d w) hp).trans (temperatureA N P i J e d p)
lemma aspect : ‖envelopeT P (chord N P i) x b‖≤1:=by
 have e':1∈ fling D:= (fling_up _).2 ⟨Nat.zero_lt_one,by omega⟩; let j':Fin D:=⟨0,by omega⟩; let v:= rateD j' 1; have hp:1≤v:= rate_profit _ e'; have he:= (enhance N P i x b j' e d w e'); rw [norm_mul,Complex.norm_real, Real.norm_of_nonneg (zero_le_one.trans hp)] at he; exact le_trans (le_mul_of_one_le_right (norm_nonneg _) hp) he
omit w d e
-- hot limit. Band from nearby interpolation stencil at prices
lemma hot_ticket : ∀ᶠ D:ℕ in atTop,∀ N:Side,(D:ℝ)^10 ≤ rimB N→∀ i:Title P,grain P i ≤ (D:ℝ)→∀ (J:Fin D)(j:ℕ), j∈fling D→ meal ≤ stip P N (arenaI P i J j):=by
 obtain ⟨s,v,u⟩:= Metric.mem_nhds_iff.mp (window_soon P); filter_upwards [ (show Tendsto (fun D:ℕ=>1/(D:ℝ)) atTop (𝓝 (0:ℝ)) from tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop).eventually (gt_mem_nhds v), eventually_ge_atTop (6:ℕ)] with D h d N a i u₀ j x f; let t:=arenaI P i j x; apply meal_to_stip; exact (show 1/2< windowW P (chord N P t) from u (mem_ball_zero_iff.mpr ((tune_head N P i j a u₀ d f).trans_lt h))).le -- tune ball name.
lemma shadow (u:Legible P N x) : ‖back N P i b x a v‖ ≤ 2*Real.exp (grain P i /8)*‖v‖:=by
 unfold back gramF; let C':=Real.exp ((ε) * faceN P x); -- substitute η'
 rw [norm_smul,norm_mul,coast_pay,one_mul,poreP,Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos _).le]; refine (mul_le_mul (Real.exp_monotone ?_) (basis_cost N P i b v a) (norm_nonneg _) (Real.exp_nonneg (grain P i /8))).trans_eq (by ring); rw [←therm N]; exact (mul_le_mul_of_nonneg_left u.major.le (norm_nonneg _)).trans_eq (mul_div_assoc ..).symm -- tune
#print axioms ascends
#print axioms aspect
end YM.CF.May.Lunar
