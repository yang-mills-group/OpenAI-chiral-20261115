import YM.SU5.SatinWard.Resolution.CoinIndex
set_option autoImplicit false
noncomputable section
namespace Zephyr.Chern.IndexMag
open YM YM.Lattice YM.CF.Fir YM.CF YM.CF.Jill Silk YM.Laurent Filter Topology MeasureTheory NormedSpace
open YM.Stationary
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator Classical Topology _root_.Pointwise
open GaussianFourier
local notation "η"=> boundsEarth
local notation "pi!"=> Real.pi
local notation "Φ"=> exileE
local notation "T" => MeasureTheory.volume
variable {F:Streams}
def orbitalPay (F:Streams)(n:ℕ):ℂ:= (2:ℂ)⁻¹^n * moment F n
lemma polsum (p:Sphere F) (n:ℕ):orbitalPay F n*(n+2:ℂ)*(n+3:ℂ)= (6:ℂ)* Silk.τ (jac F):=by
 induction n with
 | zero=> simp only [orbitalPay,Nat.cast_zero,moment,pow_zero,one_mul,zero_add]; ring
 | succ n ih=>
    have hz:=p.recur n; unfold orbitalPay at *; push_cast; rw [pow_succ]; rw [← ih]; have h:∀ a b c ℂ' : ℂ, (n+4:ℂ)*b=(2*n+4:ℂ)*a→ (c*b)*(n+1+2)*(n+1+3)*(2:ℂ)⁻¹=c*a*(n+2)*(n+3):=by intro a b c d ht; linear_combination (n+3:ℂ)*c/2*(‹_=_›)
    apply Eq.trans _ (h (moment F n) (moment F (n+1)) _ 0 hz); ring
lemma minting(n:ℕ): (cartWeight:ℂ)*(∫ x:Gaia,toEarth F n x)= (n:ℂ)^2 * orbitalPay F n:= by
 unfold toEarth moveJ; rw [Measure.integral_comp_inv_smul T,show Module.finrank ℝ Gaia=4 from finrank_euclideanSpace_fin,show winSize n^4=(n:ℝ)^2 from (by unfold winSize; rw [show (4:ℕ)=2*2 from rfl,pow_mul,Real.sq_sqrt (by positivity)]),abs_of_nonneg (by positivity:(0:ℝ)≤(n:ℝ)^2),integral_indicator earth_meas]; unfold orbitalPay moment; rw [← Silk.integral, earth_globe]; have hh (x:Gaia): nres n (E (dial x) (F 0))*balljac F x=(2:ℂ)⁻¹^n * (E (dial x) ((1+F 0)^n* jac F)):=by simp only [balljac,nres,map_mul,map_pow,map_add,map_one]; rw [div_eq_mul_inv,mul_pow]; ac_rfl
 simp_rw [hh]; rw [MeasureTheory.integral_const_mul]; rw [Complex.real_smul]; push_cast; ring
lemma orb_limit (p:Sphere F): Tendsto (fun n:ℕ=> (n:ℂ)^2 * orbitalPay F n) atTop (𝓝 ((6:ℂ)* Silk.τ (jac F))):=by
 let R:(ℕ→ ℂ):= fun n=>(((n:ℝ)⁻¹:ℝ):ℂ); have hu: Tendsto R atTop (𝓝 0):=by simpa only [R,Function.comp_def,Complex.ofReal_zero] using Complex.continuous_ofReal.continuousAt.tendsto.comp (show Tendsto (fun x:ℕ=>(x:ℝ)⁻¹) atTop (𝓝 0) from tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop); -- ending
 let V:=(6:ℂ)*Silk.τ (jac F); let h:=(tendsto_const_nhds (x:=V)).div (g:=fun i=> ((1:ℂ)+2*R i)*(1+3*R i)) (((hu.const_mul 2).const_add 1).mul ((hu.const_mul 3).const_add 1)) (by simp); rw [mul_zero,mul_zero,add_zero,mul_one,div_one] at h
 refine h.congr' ?_; filter_upwards [eventually_gt_atTop 0] with i t; have h':(i:ℂ)≠0:=Nat.cast_ne_zero.mpr (ne_of_gt t); simp only [Pi.div_apply]; unfold V R; push_cast; rw [← polsum p i]; have hp:((i:ℂ)+2)≠0:= (by exact_mod_cast (by omega: i+2 ≠0)); have he:(i:ℂ)+3≠0:=(by exact_mod_cast (by omega:i+3≠0)); field_simp <;> ring -- maybe n+a
variable {j:ℕ}{r:Male→Streams}(L:Looming j r)(H:1≤ j)
include L H
lemma topMap (m:Male) : Silk.τ (jac (r m)) = (6*(Real.pi:ℂ)^2)⁻¹:=by
 have q:= (meteringJ L H m).const_mul (cartWeight:ℂ); simp_rw [minting] at q; have i:= tendsto_nhds_unique q (orb_limit (L.round m).1); unfold cartWeight at i; have t:(Real.pi:ℂ)≠0:=(by exact_mod_cast Real.pi_pos.ne'); push_cast at i; field_simp at *; linear_combination - i/16
#print axioms orb_limit
#print axioms topMap
end Zephyr.Chern.IndexMag
