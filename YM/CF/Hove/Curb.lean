import YM.CF.Hove.Script
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Hove
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Stationary Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Fock Tulip Font Spire Nacre Ember Pec
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker MatrixOrder Classical
attribute [local instance] opCStarAlgebra
open Tap Hake Urn Yaw Levier Proa Rill

variable{f:Cover→ℂ}{m:ℕ}{a C:ℝ}(hp:Cp 2 f C)
variable(c:Side)(o:Site c)
lemma leak (x:Cover):tweight m (Lattice.lift (wrap c x)) ≤ tweight m x:=by
 unfold tweight; gcongr; exact sum_le_sum fun i _=> Corona.lap ..
local notation "tr(" x ")"=> (Lattice.lift (wrap c x))
local notation "oxK"=> (fun x:Cover=> tr(x))
variable(F:Cover→ℂ)(hF:∀ x:Cover,‖F x‖≤a*tweight 1 x)
lemma loan_h (a:ℝ)(p:0 < a):∃ C:ℝ,0<C∧∀{f:Cover→ℂ}{V:ℝ}, Width a V f→Cp 2 f (C*V):=by
 let K:=max 1 (2/a); have hk:1 ≤ K:=le_max_left ..; have hx:0<K:=lt_of_lt_of_le zero_lt_one hk; have he:1 ≤ K * (a/2):=by refine (inv_le_iff_one_le_mul₀ (by positivity)).mp ?_; unfold K; rw [inv_div]; exact le_max_right ..
 refine ⟨K^2,by positivity,fun {w v} h=>?_⟩
 let R(x:Cover):=Real.exp (a*(Laurent.size x))*‖w x‖; apply Work.F08.budget_minor (show RG.SumBudget (fun i=>K^2*R i) (K^2*v) from ⟨fun _=>mul_nonneg (sq_nonneg _) (h.1 _), h.2.1.mul_left _,by rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left h.2.2 (sq_nonneg _)⟩) (fun x=>mul_nonneg (tw_pos ..) (norm_nonneg _)); intro x
 unfold R; rw [←mul_assoc]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); let n:ℝ:=Laurent.size x; have hz:0≤n:=Nat.cast_nonneg _; calc
    _ ≤ (K*Real.exp (a*n/2))^2:=by
       apply pow_le_pow_left₀ (show 0 ≤ 1+n by positivity) _ 2
       have hz': n ≤ K*(a*n/2):=(le_mul_of_one_le_left hz he).trans_eq (by ring); exact le_trans (add_le_add hk hz') (by nlinarith [Real.add_one_le_exp (a*n/2)])
    _ =_:=by
              rw [mul_pow,pow_two (Real.exp _)] -- use
              rw [← Real.exp_add, show a*n/2+a*n/2=a*n from (by ring)] -- tune
include hp hF
private lemma pitK (g:ℝ)(p:0 ≤ g)(V:Cover→ℂ)(h:∀ x, ‖V x‖≤g*tweight 2 x): Summable (fun x:Cover=> f x*V x) ∧‖∑' x:Cover,f x*V x‖ ≤ g*C:=by
 let F(x:Cover):= f x*V x; let W(x):=g*(tweight 2 x*‖f x‖); have ht:Summable W:=hp.2.1.mul_left _; have hv(x):‖F x‖ ≤ W x:=by unfold F; rw [norm_mul, mul_comm]; exact (mul_le_mul_of_nonneg_right (h _) (norm_nonneg _)).trans_eq (mul_assoc ..)
 have hx:Summable (fun x:Cover=>‖F x‖):=ht.of_nonneg_of_le (fun _=>norm_nonneg _) hv
 refine ⟨hx.of_norm,(norm_tsum_le_tsum_norm hx).trans ((hx.tsum_le_tsum hv ht).trans ?_)⟩; unfold W; rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left hp.2.2 p
local notation "ζ"=> Rush.wind o
variable {n:ℕ}
def hill_q(x:Cover):=ζ x*ζ (oxK x)*F (oxK x)
local notation "FX"=> hill_q c o F
lemma turfL (p:0 ≤ a)(h:2*n < c.val) : let X:= fun x=>f x * FX x; let Y:=fun x=> f x*F x; Summable X ∧ Summable Y ∧ ‖∑' x,X x‖≤ a * C ∧ ‖(∑' x,X x)-(∑' x,Y x)‖≤ (2*a/(1+(n:ℝ))) * C:=by -- parentheses x
 intro X Y; have hv(x):tweight 1 x≤ tweight 2 x:=pow_le_pow_right₀ (show 1≤1+(Laurent.size x:ℝ) from le_add_of_nonneg_right (Nat.cast_nonneg _)) (by norm_num)
 have ht(x:Cover):‖FX x‖≤ a*tweight 1 x:=by unfold hill_q; rw [norm_mul,norm_mul, show ‖ζ x‖=1 from fee_norm _,show ‖ζ (oxK x)‖=1 from fee_norm _,one_mul,one_mul]; exact (hF _).trans (mul_le_mul_of_nonneg_left (leak ..) p)
 let K:=FX-F; let B:=2*a/(1+(n:ℝ)); have hP(x):‖K x‖≤ B*tweight 2 x:=by
    by_cases e: Laurent.size x≤n
    · have ht: tr(x)=x:= lift_eq_iff.mpr ⟨rfl, fun i=> by have hp:= (show (x i).natAbs ≤ Laurent.size x from single_le_sum (f:=fun a:Axis=> (x a).natAbs) (fun i _=> Nat.zero_le _) (mem_univ i)).trans e; omega⟩
      unfold K; rw [Pi.sub_apply,hill_q,show oxK x=x from ht,show ζ _*_=1 from (show ζ x*ζ x=1 from fee_one _),one_mul,sub_self,norm_zero]; unfold B; exact mul_nonneg (by positivity) (tw_pos ..)
    refine le_trans (le_trans (norm_sub_le _ _) (add_le_add (ht x) (hF x))) ?_; unfold B tweight; let y:ℝ:=Laurent.size x; have h':0 ≤ 1+y:= by unfold y; positivity
    calc
       _ = 2*a*(1+y):=by unfold y; ring
       _ ≤ _:=by
         have hx: (n:ℝ)≤ y:=by unfold y; exact_mod_cast le_of_lt (Nat.lt_of_not_ge e) -- e
         have hp:0 < 1+(n:ℝ):=by positivity
         rw [show (1+(Laurent.size x:ℝ))^2=(1+y)*(1+y) from pow_two _, ← mul_assoc]; refine mul_le_mul_of_nonneg_right ?_ h'
         rw [div_mul_eq_mul_div]; exact (le_div_iff₀ hp).mpr (mul_le_mul_of_nonneg_left (add_le_add (le_refl _) hx) (by positivity))
 obtain ⟨i,h'⟩:= pitK hp F hF a p FX (fun x=>(ht _).trans (mul_le_mul_of_nonneg_left (hv x) p)); obtain ⟨v,s⟩:= pitK hp F hF a p F (fun x=>(hF _).trans (mul_le_mul_of_nonneg_left (hv x) p)); refine ⟨i,v,h',?_⟩
 have hT: X-Y= fun x=>f x*K x:=funext fun x=> (mul_sub ..).symm
 rw [←i.tsum_sub v]; have hz':0 ≤ B:=by unfold B; positivity
 exact le_trans (le_of_eq (congr_arg _ (congr_arg (fun g:Cover→ℂ=>∑' x,g x) hT))) (pitK hp F hF B hz' K hP).2
end YM.CF.Hove
