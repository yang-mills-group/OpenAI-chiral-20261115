import YM.CF.Hove.Pair
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

variable {c f:Side}(G:Ratio c f)(w:Odd G.count.val)(o:Site c)
variable (U V:Op (Single c))(n:ℕ)
abbrev O_o:= Cube.node o
def nook_T (x:Single c):ℝ:= (1+(separation (node o) (node x.1.1):ℝ))^n
local notation "H"=> (node o)
local notation "Y'"=> nook_T o n
include w in
lemma cue_l (x:Single c):nook_T o n x= feeT G n (heel G o) x:=by
 unfold nook_T feeT Tap.streak gum dish place_x; change _=(1+ (separation ((ratio G).parent (node (isle G (o,0)))) _ :ℝ))^n; rw [embed_node G w]; simp only [show (Lattice.lift (0:Site G.count))=0 from (by simp),smul_zero,map_zero,add_zero, Ratio.embed_parent] -- name
lemma nook_l (x:Single c) : 1 ≤ Y' x:=one_le_pow₀ (le_add_of_nonneg_right (Nat.cast_nonneg _))
lemma ζdist (x:Site c):separation (node o) (node x)=2*separation o x:=by unfold node; rw [separation_translate]; exact Laic.emptio (assembly c) _ _
lemma ζ_t (x: Single c) : tweight n (ox o x) ≤ 2^n * Y' x:=by
 let z:= x.1.1; have hp(i:Axis): (Lattice.lift (z-o) i).natAbs≤ separation z o:= component_le ..; have he : Laurent.size (ox o x) ≤ 4 * separation z o:=by
    refine (sum_le_sum (fun i _=>hp i)).trans_eq ?_; simp [Axis]
 rw [separation_comm] at he; have hq : (Laurent.size (ox o x):ℝ) ≤ 4*separation o z:=by exact_mod_cast he
 unfold tweight nook_T; rw [ζdist,← mul_pow]; refine pow_le_pow_left₀ (by positivity) ?_ _; push_cast; linarith
lemma turn_i(x:Single c×Single c):opus n o x≤(2:ℝ)^n* coyF Y' x:=by
 unfold opus coyF; by_cases h:(Laurent.size (ox o x.1):ℝ) ≤ (Laurent.size (ox o x.2):ℝ)
 · rw [max_eq_right h]; exact (ζ_t o n x.2).trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (zero_le_one.trans (nook_l o _ _))) (by positivity))
 rw [max_eq_left (le_of_not_ge h)]; exact (ζ_t o n x.1).trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (zero_le_one.trans (nook_l o _ _))) (by positivity))
lemma march (x:Single c) : nook_T o n x ≤ 2^n * tweight n (ox o x):=by
 unfold nook_T tweight; rw [ζdist, ← mul_pow]; have hx:separation o x.1.1 ≤ Laurent.size (ox o x):=by
    rw [separation_comm,separation]; apply Finset.sup_le; intro y _; exact Finset.single_le_sum (f:=fun i: Axis=> (ox o x i).natAbs) (fun i _=> Nat.zero_le _) (mem_univ _)
 refine pow_le_pow_left₀ (by positivity) ?_ _; push_cast; linarith only [(Nat.cast_le.mpr hx : (separation o x.1.1:ℝ) ≤ _)]
def paid_M:= paidX (coyF (nook_T o n)) (pinF U)
lemma limP :moneyP n o U ≤ 2^n * paid_M o U n:=by unfold moneyP paid_M paidX; rw [mul_sum]; apply sum_le_sum; intro i _; rw [←mul_assoc]; exact mul_le_mul_of_nonneg_right (turn_i o n i) (norm_nonneg _)
lemma walk_p : paid_M o U n ≤ 2^(n+1) * moneyP n o U:=by
 unfold moneyP paid_M paidX; rw [mul_sum]; apply sum_le_sum; intro i _; rw [←mul_assoc]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
 unfold coyF; refine (add_le_add (march o n i.1) (march o n i.2)).trans ?_
 have hx: tweight n (ox o i.1) ≤ opus n o i:=by unfold opus tweight; gcongr; exact le_max_left ..
 have he: tweight n (ox o i.2) ≤ opus n o i:=by unfold opus tweight; gcongr; exact le_max_right ..
 exact (add_le_add (mul_le_mul_of_nonneg_left hx (by positivity)) (mul_le_mul_of_nonneg_left he (by positivity))).trans_eq (by rw [pow_succ]; ring)
lemma paidp_p :0≤ paid_M o U n:= windL _ _ (fun x=> add_nonneg (zero_le_one.trans (nook_l o n x.1)) (zero_le_one.trans (nook_l o n x.2)))
lemma paidp_sum : paid_M o (U+V) n≤ paid_M o U n+paid_M o V n:=by unfold paid_M; rw [show pinF (U+V)=pinF U+pinF V from rfl]; exact Tap.p_sum (show ∀ x, 0 ≤ coyF (nook_T o n) x from fun x=> add_nonneg (zero_le_one.trans (nook_l o n x.1)) (zero_le_one.trans (nook_l o n x.2))) (pinF U) (pinF V)
section
local notation "Sθ"=> Single c
variable {a b d:ℝ}(P Q:Matrix (Single c) Kt ℂ)
local notation "Ω"=> moneyP n o U
lemma pump (v:0≤a)(h:∀ i x j k, ‖P i x‖*‖Q j k‖ ≤ a*opus n o (i,j)) : ‖snapH P Q U‖≤ Haro.ξP * (a * Ω):=by
 apply Haro.ζP; intro i j; change ‖(Pᴴ*U*Q) i j‖≤ _; rw [Matrix.mul_apply]; unfold moneyP paidX; rw [mul_sum]; conv_rhs=> rw [Fintype.sum_prod_type,sum_comm]
 refine (norm_sum_le ..).trans (sum_le_sum fun x _=>?_); rw [Matrix.mul_apply,Finset.sum_mul]; refine (norm_sum_le ..).trans (sum_le_sum fun y _=>?_); change ‖star (P y i)*U y x*Q x j‖≤ _; rw [norm_mul,norm_mul,norm_star]; calc
    _ = (‖P y i‖*‖Q x j‖)*‖U y x‖:=by ring
    _ ≤ _:=((mul_le_mul_of_nonneg_right (h ..) (norm_nonneg _)).trans_eq (mul_assoc ..))
abbrev κP:= Haro.ξP*(m_fee false*m_fee true)* (2:ℝ)^n
local notation "η" b:max=> (m_fee b)
lemma lim_k(v:Bool)(i: Sθ)(s:Kt): ‖rampF v o i s‖≤ η v:=by unfold rampF; rw [Matrix.of_apply,norm_mul,show ‖ζw o i‖=1 from fee_norm _,one_mul]; exact mp_iv ..
lemma limb_k(v:Bool)(i: Sθ)(s:Kt)(a: Axis): ‖spanH v o a i s‖≤ (η v)*(tweight 1 (ox o i)):=by unfold spanH; rw [Matrix.of_apply,norm_mul,show ‖ζw o i‖=1 from fee_norm _,one_mul]; refine (mon_v v _ _ _ a).trans_eq ?_; unfold tweight; rw [pow_one,mul_comm]
lemma ζr : ‖mornC o U‖≤ κP n*paid_M o U n:=by
 have hz:= mpe true; have he:0≤ Haro.ξP:=by unfold Haro.ξP; positivity
 have hp:0≤ (η false)* η true:=mul_nonneg (mpe _) hz; apply (pump o U n (rampF false o) (rampF true o) hp _).trans -- underscore delay
 · refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (limP o U n) hp) he).trans_eq ?_; unfold κP; ring
 intro i x j k; exact (mul_le_mul (lim_k o false i x) (lim_k o true j k) (norm_nonneg _) (mpe _)).trans (le_mul_of_one_le_right hp (show 1 ≤ opus n o (i,j) from by unfold opus; apply one_le_pow₀; simp)) -- tactic goal order
variable (a':Axis)(hN:1≤n)
include hN
lemma opox : ‖partX o U a'‖≤κP n * paid_M o U n:=by
 have hz:= mpe true; have he:0≤ Haro.ξP:=by unfold Haro.ξP; positivity
 have hp:0≤ (η false)* η true:=mul_nonneg (mpe _) hz; apply (pump o U n (spanH false o a') (rampF true o) hp _).trans
 · refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (limP o U n) hp) he).trans_eq ?_; unfold κP; ring
 intro i x j k; have hm:tweight 1 (ox o i) ≤ opus n o (i,j):= by unfold tweight opus; apply le_trans (pow_le_pow_right₀ (show 1 ≤ 1+(Laurent.size (ox o i):ℝ) by simp) hN); gcongr; exact le_max_left ..
 refine (mul_le_mul (limb_k o false i x a') (lim_k o true j k) (norm_nonneg _) (mul_nonneg (mpe _) (tw_pos ..))).trans ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm (mpe false)) hz).trans_eq ?_); ring
lemma opoy : ‖partY o U a'‖≤κP n * paid_M o U n:=by
 have hz:= mpe false; have he:0≤ Haro.ξP:=by unfold Haro.ξP; positivity
 have hp:0≤ (η false)* η true:=mul_nonneg hz (mpe _); apply (pump o U n (rampF false o) (spanH true o a') hp _).trans
 · refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (limP o U n) hp) he).trans_eq ?_; unfold κP; ring
 intro i x j k; have hm:tweight 1 (ox o j) ≤ opus n o (i,j):= by unfold tweight opus; apply le_trans (pow_le_pow_right₀ (show 1 ≤ 1+(Laurent.size (ox o j):ℝ) by simp) hN); gcongr; exact le_max_right ..
 refine (mul_le_mul (lim_k o false i x) (limb_k o true j k a') (norm_nonneg _) (mpe _)).trans ((mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hm (mpe true)) hz).trans_eq ?_); ring
end
end YM.CF.Hove
