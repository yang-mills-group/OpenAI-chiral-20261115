import YM.SU5.May.LunarLongitude
import YM.SU5.May.FloeTwist
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.May.Lunar
open Function Filter Finset Lattice Laurent Next.Free Bloch Fir Real Complex MeasureTheory WithLp
open scoped Topology BigOperators ContDiff Matrix InnerProductSpace ENNReal ComplexOrder Classical Matrix.Norms.L2Operator
open Onyx Fock Buffered.Lifted Buffered.Afterglow.Tower Buffered.Afterglow.Tower.Tilted Window.ArchiveK Window.Largo
attribute [local instance] opCStarAlgebra
variable (N:Side)(P:Ramp)(p:E4)(i:Title P)(b:ℝ)
local notation "a₀"=> P.a
local notation "b₀"=> P.b
local notation "Z"=> tilted P
-- hsinc phase
lemma sinc_neg' (z:ℂ): hsinc (-z)=hsinc z:= by by_cases p:z=0; simp [p]; rw [haway _ (neg_ne_zero.mpr p), haway _ p, Complex.sin_neg, neg_div_neg_eq]
lemma sinc_star' (z:ℂ): star (hsinc z)= hsinc (star z):=by
 by_cases v:z=0; simp [v,hzero]; rw [haway _ v,haway _ (star_ne_zero.mpr v)]; simp [Complex.sin_conj]
lemma leer_under(q:Momentum): leer (-q)= leer q:=by
 unfold leer; simp only [Pi.neg_apply, neg_div, sinc_neg']
lemma leer_mirror : star (leer (shaft p (tilted P) b)) = leer (shaft p (tilted P) (-b)):=by
 unfold leer; rw [star_prod]; refine prod_congr rfl fun a _=>?_ ; rw [sinc_star']; apply congrArg; simp [shaft, brushQ,Fir.tmap]
lemma sector_bend (w:inner ℝ (tilted P) p=0): p P.b = - p P.a:=by
 rw [show inner ℝ (tilted P) p= _ from chopped P _] at w; have he:= (mul_eq_zero.mp w).resolve_left halfLegal.ne'; linarith
lemma backwards (w:inner ℝ (tilted P) p=0): leer (shaft p (tilted P) (-b))= leer (shaft p (tilted P) b):=by
 unfold leer; refine Fintype.prod_equiv P.s.perm _ _ ?_
 intro i; simp only [shaft,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,brushQ,Fir.tmap,ofReal_neg,tilted_at]; let A:= sector_bend P p w
 by_cases u:i=P.a; · subst i; rw [P.sab]; nth_rw 1 [← sinc_neg']; simp [A]; ring_nf
 by_cases v:i=P.b; · subst i; rw [P.sba]; nth_rw 1 [← sinc_neg']; simp [A]; ring_nf
 rw [P.saa u v]; simp [u,v]
noncomputable def walletP (P:Ramp)(z:E4)(b:ℝ):ℝ:= (leer (shaft z (tilted P) b)).re^8
lemma wallet_turn(w:inner ℝ (tilted P) p=0): walletP P p (-b)=walletP P p b:=by unfold walletP; rw [backwards P p b w]
lemma portfolio (w:inner ℝ (tilted P) p=0): lensome p (tilted P) b=(walletP P p b:ℂ):=by
 let L0:= leer (shaft p (tilted P) b); have he: (L0.re:ℂ)= L0:= Complex.conj_eq_iff_re.mp ((leer_mirror P p b).trans (backwards P p b w)); unfold lensome walletP; push_cast; rw [he]
lemma wallet_n : 0 ≤ walletP P p b:=by unfold walletP; positivity
lemma wallet_bound(w:inner ℝ (tilted P) p=0): walletP P p b ≤ Real.exp (20*|b|):=by have he:= (lent p (tilted P) (rulerL P) b).2; rw [portfolio P p b w, Complex.norm_real, Real.norm_of_nonneg (wallet_n P p b)] at he; exact he -- semicolon issue
-- budget continuity. mind dependency
noncomputable def windowW (P:Ramp)(z:E4):ℝ:=walletP P z ‖z‖
lemma fee_one (P:Ramp): windowW P 0=1:=by simp [windowW,walletP,leer,shaft,brushQ,tmap,hzero]
lemma windowC : Continuous (windowW P):=by unfold windowW walletP; have he:= leer_safe; apply Continuous.pow; apply Complex.continuous_re.comp; apply he.comp; unfold shaft; fun_prop
lemma window_soon : ∀ᶠ p:E4 in 𝓝 0,1/2 < walletP P p ‖p‖:= (windowC P).continuousAt.tendsto.eventually (lt_mem_nhds (show (1:ℝ)/2<windowW P 0 by rw [fee_one]; norm_num))
-- centers
variable (x y:Cover)
noncomputable def age (x:Cover):E4:= (1/2:ℝ) • emitX (nodeC x)
lemma age_at(j:Axis): age x j=(1/2:ℝ)+(x j:ℝ):=by simp [age,nodeC,nsmul_eq_mul]; ring
local notation "θ"=> P.plan.flee
lemma reflected_age : age (P.plan.flee x)= age x- (2 * lengthT P (age x)) • tilted P:=by
 have he: nodeC (P.plan.flee x) = P.s.act (nodeC x):= May.Floe.branch_clock P x; apply PiLp.ext; intro j
 rw [chopped]; unfold age; simp only [he, PiLp.sub_apply,PiLp.smul_apply,emit_axis,tilted_at,smul_eq_mul]; have η'(v:ℝ): halfer^2*v=1/2*v:= by rw [halfSquare]
 by_cases p:j=a₀; · subst j; simp only [true_or,ite_true,P.move_a, Int.cast_neg]; linear_combination (((nodeC x a₀:ℤ):ℝ)+ ((nodeC x b₀:ℤ):ℝ)) * halfSquare
 by_cases q:j=b₀; · subst j; simp only [or_true,ite_true,P.move_b,Int.cast_neg]; linear_combination (((nodeC x a₀:ℤ):ℝ)+ ((nodeC x b₀:ℤ):ℝ)) * halfSquare
 rw [P.move_h _ p q]; simp [p,q]
lemma port_age : emitX (P.plan.flee x-y)=age (P.plan.flee x)-age y:=by
 apply PiLp.ext; intro j; simp [age_at]
lemma ptime : lengthT P (emitX (P.plan.flee x-y))= -(lengthT P (age x)+lengthT P (age y)):=by rw [port_age,reflected_age]; unfold lengthT; rw [inner_sub_right,inner_sub_right,real_inner_smul_right,real_inner_self_eq_norm_sq,rulerL]; ring
local notation "I'"=> chord N P i
lemma orbit_time : inner ℝ (chord N P i) (emitX (P.plan.flee x-y))=inner ℝ (chord N P i) (age x) - inner ℝ (chord N P i) (age y):=by rw [port_age, reflected_age]; rw [inner_sub_right,inner_sub_right,real_inner_smul_right,real_inner_comm (tilted P) (I'), duet,mul_zero,sub_zero]
#print axioms portfolio
#print axioms orbit_time
end YM.CF.May.Lunar
