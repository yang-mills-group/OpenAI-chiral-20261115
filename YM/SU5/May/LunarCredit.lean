import YM.SU5.May.LunarTrail
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
variable {N:Side}{P:Ramp}(p q:E4)(i:Title P)(x:Cover){b:Bool}(v:Ket SpinIdx)(a:Slot)
variable {D j:ℕ} (J:Fin D) {X:Type*} [Fintype X]
local notation "T"=>rimB N
local notation "G" => chord N P i
local notation "η" => ‖chord N P i‖
structure CapeF (P:Ramp)(N:Side)(D:ℕ) : Prop where
 e:tacit ≤ 1 -- optional remove
 t_h: 80 ≤ rimB N
 hot : ∀ (i:Title P), grain P i ≤ (D:ℝ) →∀ J:Fin D,∀ j∈fling D, meal ≤ stip P N (arenaI P i J j)
 t: 6 ≤ D
-- help lemma
noncomputable def tollV (D:ℕ):= Real.exp (-(D:ℝ)/4)
lemma tollVal(D:ℕ):0<tollV D:=Real.exp_pos _
noncomputable def brokerC :ℝ:=200*Rink.flight^2
lemma broker_p:0≤ brokerC:=by unfold brokerC; positivity
lemma chargeLease(D:ℕ): chillD D ^ 2 ≤ tollV D:=by unfold chillD tollV; rw [sq,← Real.exp_add]; apply Real.exp_monotone; have ht:0≤(D:ℝ):= (by positivity); linarith
namespace Trail
variable (F:Trail N P b X)(w: X→ℂ)
local notation "φ" j:max => F.feature j w
local notation "Y" i:max => F.yesterday i w
local notation "σ" i:max=> stip P N i
local notation "η'" i:max=> reelT P N i
local notation "R" d:max=> rime P d
local notation "μ" => ∑ j:X,‖w j‖
local notation "c" => (μ)^2
local notation "V*"=> F.temple w
variable (A:CapeF P N D) (Q:∀ i, ‖age (F.atSlot i)‖ ≤ hazySize D N) (ξ:grain P i ≤ (D:ℝ))
include A Q ξ
private lemma talented_chart : ∃ j∈fling D, ‖Y i‖ ≤4*‖φ (arenaI P i J j)‖+10*Rink.flight*chillD D*(∑ k:X,‖w k‖):=by
 let f(k:X):=envelopeT P (chord N P i) (F.atSlot k) b; let a(k:X):= w k • basisP N P i b (F.vr k) (F.appointment k); let h(k:X):=approach N P i b (F.atSlot k) (F.appointment k) (F.vr k); have hx(x): showers f a x=∑ j:X,w j • h j x := by unfold showers h approach f a; simp_rw [smul_comm _ (w _)]; -- check
 have hl(k:X): ‖basisP N P i b (F.vr k) (F.appointment k)‖≤2:= (basis_cost ..).trans (by have ht:=F.amountC k; linarith)
 obtain ⟨j,p,H⟩:= talented (D:=D) (show 0< (↑(flash D J):ℝ) from Nat.cast_pos.mpr (wage_cash _)) f a (fun x=>aspect _ _ i _ b ξ A.t (Q x)) (fun j z k=> enhance N P i (F.atSlot k) b J ξ A.t (Q k) z) (by have he:=A.t; omega)
 simp_rw [hx, h,downstairs,show ferryD _ j= rateD J j from rfl, ascends _ _ _ _ _ _ _ J p] at H; refine ⟨j,p,H.trans ?_⟩; apply add_le_add_right; rw [show 10*Rink.flight*chillD D= (5*Rink.flight*chillD D)*2 from (by ring),mul_assoc (5*Rink.flight*chillD D)]; refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (mul_nonneg (by positivity) flight_p.le) (chill_pos _).le); rw [mul_sum]; refine sum_le_sum fun k _=>?_ ; rw [show ‖a k‖=‖w k‖* ‖basisP N P i b _ _‖ from norm_smul .., mul_comm (2:ℝ)]; exact mul_le_mul_of_nonneg_left (hl _) (norm_nonneg _)
private lemma talented_square : ∃ j∈fling D, ‖Y i‖^2 ≤ (32/meal)*F.privilege (arenaI P i J j) w + brokerC*(tollV D) *( (∑ i:X,‖w i‖)^2):=by
 obtain ⟨j,u,t⟩:=talented_chart i J F w A Q ξ; let k:=arenaI P i J j; let P1:=32*‖φ k‖^2; let V:= F.privilege k w; let X':ℝ:= μ; let Z:=10*Rink.flight*chillD D*X'; have hm:P1 ≤ 32/meal * V:=by unfold V privilege; rw [←mul_assoc]; unfold P1; refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _); refine le_trans ?_ (mul_le_mul_of_nonneg_left (A.hot i ξ J j u) (div_nonneg (by norm_num) meal_p.le)); exact (div_mul_cancel₀ _ meal_p.ne').symm.le
 have hv: 2*Z^2 ≤ brokerC * tollV D *c:=by apply le_trans _ (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (chargeLease D) broker_p) (sq_nonneg _)); unfold Z brokerC X'; apply Eq.le; ring; -- tune
 refine ⟨j,u,?_⟩; refine (pow_le_pow_left₀ (norm_nonneg _) t 2).trans ?_; refine le_trans ?_ (add_le_add hm hv); change (4*‖φ k‖+Z)^2 ≤ 32*‖φ k‖^2+2*Z^2; nlinarith only [sq_nonneg (4*‖φ k‖-Z)]
private lemma capacity : ‖Y i‖^2 ≤ (32/meal)/(D:ℝ)*(V*) + brokerC*tollV D * ((∑ i:X,‖w i‖)^2):=by
 choose j p h using (fun J:Fin D=> talented_square i J F w A Q ξ); let m(x:Fin D):Title P:=arenaI P i x (j x); let B:= brokerC*tollV D * c; let L':=32/meal
 have hx:(∑ i:Fin D,F.privilege (m i) w) ≤ V*:=by
    refine le_trans ?_ ((F.frontSum w A.t_h).sum_le_tsum (Finset.univ.image m) (fun i _=>F.privilege_p i w)); rw [Finset.sum_image]; unfold m arenaI; intro i _ k _ z; exact aimed j p (cast_inj P _ z) -- orientation
 have ht:0≤32/meal:=by have ht:=meal_p; positivity
 have he:(D:ℝ)*‖Y i‖^2 ≤ L'*(V*)+(D:ℝ)*B:=calc
    _ =∑ _j:Fin D, ‖Y i‖^2:=by simp
    _ ≤∑ j:Fin D, (L'*F.privilege (m j) w+B):=Finset.sum_le_sum fun j _=> h j
    _ ≤_:= by rw [sum_add_distrib, ←Finset.mul_sum, sum_const]; simpa using add_le_add_left (mul_le_mul_of_nonneg_left hx ht) ((D:ℝ)* B) -- applies order? inspect
 have hD:0<(D:ℝ):=by have hp:=A.t; exact_mod_cast (show 0<D by omega)
 apply le_of_mul_le_mul_left _ hD; change (D:ℝ)* ‖Y i‖^2 ≤ _; exact he.trans_eq (by field_simp; ring) -- maybe defeq
private lemma lower_price : F.proration i w ≤ R i * (loanP* ((32/meal)/(D:ℝ)*(V*) +(4+brokerC)*tollV D * ((∑ i:X,‖w i‖)^2))) := by
 let V:ℝ:= (V*); let D':ℝ:= D; let L':=32/meal; let B:= L'/D'*V; let a:= L'/D'*V+(4+brokerC)*tollV D*c; unfold proration; refine (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_abs_self _) (stip_n N P i)) (sq_nonneg _)).trans ?_; let Y':= grain P i
 have h: Real.exp (-(3/4:ℝ)*grain P i) ≤ R i:= by unfold rime; exact Real.exp_monotone (by linarith only [grain_floor P i])
 have hp: ‖Y i‖^2 ≤ a:=by refine (capacity i F w A Q ξ).trans (add_le_add_right ?_ _); exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (show (0:ℝ)≤4 by norm_num)) (tollVal _).le) (sq_nonneg _)
 refine (mul_le_mul ((ceil_back N P i A.t_h).trans (mul_le_mul_of_nonneg_left h loan_p.le)) hp (sq_nonneg _) (mul_nonneg loan_p.le (rime_p P i).le)).trans_eq ?_; unfold a L' V D'; ring
omit ξ
lemma rebate (i:Title P): F.proration i w ≤ R i * (loanP* ((32/meal)/(D:ℝ)*(V*) + (4+brokerC)*tollV D*((∑ i:X,‖w i‖)^2))):=by
 by_cases h:grain P i ≤ (D:ℝ); · exact lower_price i F w A Q h
 let B:= (32/meal)/(D:ℝ)*(V*); have he:0 ≤ B:=by unfold B; have he:= meal_p; have hp:= F.temple_n w; positivity
 refine (le_abs_self _).trans ((F.funding i w A.t_h).trans ?_); let f:= Real.exp (- grain P i/2); let E:=tollV D; have hp: f≤ R i * E:=by unfold rime E f tollV; rw [← Real.exp_add]; apply Real.exp_monotone; linarith
 refine le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (mul_nonneg (by norm_num) loan_p.le)) (sq_nonneg _)) ?_
 rw [show 4*loanP*((R i)*E)*c=R i*(loanP*(4*E*c)) from (by ring)]; apply mul_le_mul_of_nonneg_left _ ((rime_p P i).le); apply mul_le_mul_of_nonneg_left _ loan_p.le; refine le_trans ?_ (le_add_of_nonneg_left he); exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right broker_p) (tollVal _).le) (sq_nonneg _)
noncomputable def remainder (P:Ramp):ℝ:= cessR P * loanP*(4+brokerC)
lemma fond (u:cessR P*loanP*(32/meal)≤ (D:ℝ)): -(remainder P*tollV D*(∑ j:X,‖w j‖)^2) ≤ (N.val:ℝ)^3*(F.yield w).re:=by
 rw [F.entire_h w A.t_h]; let α₀:ℝ:=32/meal; let U:= (4+brokerC)*tollV D*c; let B':=α₀/(D:ℝ)*(V*); let Z1:= V*
 have he: (∑' i,F.proration i w) ≤ Z1+ remainder P*tollV D*c:= by
    refine le_trans (Summable.tsum_le_tsum (rebate F w A Q) (F.backSum w A.t_h) ((rime_sum P).mul_right (loanP*( B'+U)))) ?_; rw [tsum_mul_right]; change cessR P * _ ≤ _; rw [mul_add loanP, mul_add (cessR P)]; apply add_le_add; swap; · unfold remainder; exact Eq.le (by ring)
    rw [show cessR P*(loanP*B')=(cessR P*loanP* (32/meal))/(D:ℝ)*Z1 from (by unfold B' α₀ Z1; ring)]; refine mul_le_of_le_one_left (F.temple_n _) ?_; exact (div_le_one (Nat.cast_pos.mpr (by have ht:=A.t; omega))).mpr u
 linarith only [he] -- potential Z1 def mismatch
#print axioms rebate
#print axioms fond
end Trail
end YM.CF.May.Lunar
