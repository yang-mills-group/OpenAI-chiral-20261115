import YM.SU5.Velvet.Skyline
import YM.SU5.Velvet.Glint
import YM.SU5.FiniteGaugeData.Pannier.PaleFace
/-!
 # Density for tilt. Need to compete with leasePart pressure & altitude.
 Cost checked for actual j M, same normed ν. With flags.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 16000
set_option maxHeartbeats 190000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Velvet
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye Pannier.Chancel Brace
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable {N:Side} {j n w d:ℕ} {u v η ζ δ:ℝ}
namespace Hours
open Fock
variable (j) (z:ℝ)
abbrev sky:LedgerK:= fun _ N _ _=> tickA N
abbrev Tgate:LedgerK:=fun _ N _ _=>gate (tickA N) z
abbrev side:LedgerK:=fun _ _ M x=> spar j M x
def settle: LedgerK:=let H:=Tgate z; let Y:=side j; Y*(H*H)*Y+(1-Y)
def account:LedgerK:=let Q:=side j; let H:=Tgate z; H*Q* (settle j z)⁻¹*(Q*H)
theorem settle_coin (N:Side)(M:Tulip.Male)(x:Pane N)(r:Rails) : settle j z r N M x=hinge (spar j M x) (tickA N) z:=rfl
theorem earns_account(N:Side)(M:Tulip.Male)(x:Pane N)(r:Rails) : account j z r N M x=draft (spar j M x) (tickA N) z:=rfl
abbrev Difference:= settle j z-1
def located:LedgerK:= fun r N M x=>beam (Difference j z r N M x) ↑(r.val:ℝ)
-- direct ℝ density; Rails parameter for kernels only
def nectar:LedgerK:= (fun r N M P=> Real.log z • (sky-side j) r N M P)+(fun r N M P=>(1/2:ℝ) • ((located j z)⁻¹*Difference j z) r N M P)
variable {j z} (Q: Procurement j n δ)
local notation "🎕" => Prudence n δ
section urban
include Q
lemma atBase (z:ℝ) : 🎕 (Tgate z):=by -- parentheses ?
 let p:=Q.insp; exact (Prudence.tick (δ:=δ) (n:=n)).add' ((Prudence.id.sub' Prudence.tick).scalec p (z^2))
lemma inCost (z:ℝ) : 🎕 (settle j z) :=by
 let p:= Prudence.covers Q; let q:= atBase Q z; let u:= Q.insp; exact (((p.mul' (q.mul' q u) u).mul' p u).add' (Prudence.id.sub' p))
lemma settle_price (v:z≤1)(u:0<z): London n δ (1-settle j z) (1-z^4):= fun r N P q t M=> hinge_budget ((Q.audit q).projection _ t) (Kea.cut_t _) u.le v
lemma flowing (u:0<z)(v:z≤1) : 🎕 (account j z):=by
 let p:= Prudence.covers Q; let q:= atBase Q z; let w:= Q.insp
 have h:= (inCost Q z).revere (settle_price Q v u) (sub_lt_self _ (pow_pos u _)) (sub_nonneg.mpr (pow_le_one₀ u.le v)) w
 exact ((q.mul' p w).mul' h w).mul' (p.mul' q w) w
lemma situated (z:ℝ): 🎕 (located j z):=by
 let V:=Difference j z; have h:located j z=1+(fun r N M P=>r.val • V r N M P):=by funext r N M P; change 1+(r.val:ℂ) • (V r N M P)=1+(r.val:ℝ) • _; rw [RCLike.real_smul_eq_coe_smul (K:=ℂ)]; rfl
 rw [h]; exact Prudence.id.add' (((inCost Q z).sub' Prudence.id).scaleL Q.insp _ 1 zero_le_one (fun i=>(abs_of_nonneg i.property.1).trans_le i.property.2))
lemma lightening (p:0<z)(v:z≤1): London n δ (1-located j z) (1-z^4):= by
 intro r N P e h M; let F:= settle j z r N M P; let A:= F-1; let t:ℂ:= r.val; change ‖1-(1+t • A)‖ ≤ _; rw [sub_add_eq_sub_sub,sub_self,zero_sub,norm_neg,norm_smul,show ‖t‖=r.val from (by unfold t; rw [Complex.norm_real, Real.norm_of_nonneg r.property.1]), show ‖A‖=‖1-F‖ from norm_sub_rev ..]; exact (mul_le_of_le_one_left (norm_nonneg _) r.property.2).trans (settle_price Q v p r N P e h M)
lemma worth (p:0<z)(v:z≤1): 🎕 (nectar j z):=by
 let u:= Q.insp; let a:= Prudence.covers Q; let q:= (inCost Q z).sub' Prudence.id; let S: Prudence n δ sky:= Prudence.tick; have h:= (situated Q z).revere (lightening Q p v) (sub_lt_self _ (pow_pos p _)) (sub_nonneg.mpr (pow_le_one₀ p.le v)) u
 exact ((S.sub' a).scalec u (Real.log z)).add' ((h.mul' q u).scalec u (1/2))
end urban
variable (j z)
-- nectar is truly integrand determinant/trades
private def vapor (M:Tulip.Male)(P:Pane N) (r:ℝ):ℂ:= (Real.log z) • (tickA N - spar j M P).trace + (1/2:ℝ) • Fock.slope (hinge (spar j M P) (tickA N) z - 1) r
private lemma vapor_cost (M:Tulip.Male)(P:Pane N)(r:Rails): vapor j z M P r.val= (nectar j z r N M P).trace:=by unfold vapor nectar; simp_rw [Pi.add_apply,Matrix.trace_add, Matrix.trace_smul]; rfl
variable {j z}
include Q
private lemma berth (p:0<z)(v:z≤1)(M:Tulip.Male)(P:Pane N)(g:n≤N.val)(k:Guard P δ) : let A:=hinge (spar j M P) (tickA N) z; ‖A-1‖ < 1 :=by intro A; rw [norm_sub_rev]; exact (settle_price Q v p ⟨0,Set.left_mem_Icc.mpr zero_le_one⟩ N P g k M).trans_lt (sub_lt_self _ (pow_pos p _))
private lemma sunlight (p:0<z)(v:z≤1)(M:Tulip.Male)(P:Pane N)(g:n≤N.val)(k:Guard P δ): IntervalIntegrable (Fock.slope (hinge (spar j M P) (tickA N) z-1)) volume 0 1:=by
 let A:=hinge (spar j M P) (tickA N) z; have h:‖A-1‖<1:= berth Q p v M P g k; exact ContinuousOn.intervalIntegrable (fun i c=> (slope_at (beam_active h i c)).continuousWithinAt)
private lemma vapored (p:0<z)(v:z≤1)(M:Tulip.Male)(P:Pane N)(g:n≤N.val)(k:Guard P δ): IntervalIntegrable (vapor j z M P) volume 0 1:= intervalIntegrable_const.add ((sunlight Q p v M P g k).smul (1/2:ℝ))
lemma revenue (p:0<z)(v:z≤1)(M:Tulip.Male)(P:Pane N)(g:n≤N.val)(k:Guard P δ) : trade (spar j M P) (tickA N) z=(∫ i in (0:ℝ)..1,vapor j z M P i).re:=by
 let A:=hinge (spar j M P) (tickA N) z; let E:=A-1; let t:= invoice E; let w:= slope E; have he: Real.exp t.re=‖A.det‖:= by rw [←Complex.norm_exp,show Complex.exp t= _ from factor E (berth Q p v M P g k),show 1+E=A from (by unfold E; abel)]
 unfold vapor; rw [intervalIntegral.integral_add intervalIntegrable_const (show IntervalIntegrable (fun i=>(1/2:ℝ) • Fock.slope (hinge (spar j M P) (tickA N) z-1) i) volume 0 1 from (sunlight Q p v M P g k).smul (1/2:ℝ)), intervalIntegral.integral_smul (f:=Fock.slope (hinge (spar j M P) (tickA N) z-1)),intervalIntegral.integral_const]; -- names
 simp only [sub_zero,one_smul, Complex.add_re, Complex.smul_re, smul_eq_mul]; unfold trade; change _*Real.log z+Real.log _ / 2= _+(1/2:ℝ)*t.re; rw [←he,Real.log_exp]; ring
-- raw comparison accepts trace ℂ data for each r
lemma net_gain (p:0<z)(v:z≤1)(M:Tulip.Male)(P:Pane N)(g:n≤N.val)(k:Guard P δ) (a:ℝ) (L:∀ r:Rails, ‖(nectar j z r N M P-nectar j z r N M 1).trace‖≤ a): |trade (spar j M P) (tickA N) z - trade (spar j M (1:Pane N)) (tickA N) z| ≤ a:=by
 let hp:= guard0 (N:=More N) Q.insp
 rw [revenue Q p v M P g k,revenue Q p v M 1 g hp,←Complex.sub_re,← intervalIntegral.integral_sub (vapored Q p v M P g k) (vapored Q p v M 1 g hp)]
 apply (Complex.abs_re_le_norm _).trans; let K:=fun i:ℝ=>vapor j z M P i-vapor j z M (1:Pane N) i
 have h(i:ℝ)(p: i∈Set.uIoc 0 1): ‖K i‖ ≤ a:= ?_
 apply (intervalIntegral.norm_integral_le_of_norm_le_const (a:=(0:ℝ)) (b:=1) (C:=a) (f:=K) h).trans_eq; simp -- final goal?
 have ht:=L ⟨i,show i∈Set.Icc (0:ℝ) 1 from (Set.uIcc_of_le (zero_le_one (α:=ℝ))) ▸ (Set.uIoc_subset_uIcc p)⟩; rw [Matrix.trace_sub,←vapor_cost,←vapor_cost] at ht; exact ht
end Hours
end YM.CF.Velvet
#print axioms YM.CF.Velvet.Hours.net_gain
#print axioms YM.CF.Velvet.Hours.worth
