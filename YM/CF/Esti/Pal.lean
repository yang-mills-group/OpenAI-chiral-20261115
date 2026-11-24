import YM.CF.Esti.Teen
import YM.CF.Vol.Celt
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Psalm.Baton
import YM.CF.Palot.End
import YM.CF.Appel.Sat
import YM.Next.FLUCTUATIONS.Grants
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Folio.Wind
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Esti
open Siete
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG PhysicalNext.JointLoad Heir Next.Foundations AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD
open Ac
variable {c f:Side}(S:StepData c f){r v:ℕ}
open CF.Jet
local notation "G"=> SU.group
variable {S}{n:ℕ}{θ a b m x t w K C d:ℝ}
variable {K': Teller G}{A B:Stores S}{T:Tube G S}{V:Config G c}{U:Config G f}{k:S.Choices}{q:Chi}{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][Nonempty E]{x':E}
open AnalyticBridge.Annulus1AD Push.SectorMeasure.Oriented Pressure.Tube
variable {O:Stores S}{F: Forest S.ratio}{Y:LinkArray G (Frozen A x F)}{z:LogArray G (Active A x F)}{β Q γ D L M s:ℝ}{J:ChartRatio G}{P:Patch}
-- nuisance algebra might even grow exp of fixed polyradius. after L and cap.
def plow(x:ℝ):ℝ:=Scales.b x
abbrev Lento(f:ℝ→ℝ):Prop:=∃ K:ℝ,∃ n:ℕ, 0 ≤ K∧∀ᶠ x:ℝ in atTop,|f x| ≤ Real.exp (K*plow x^n)
lemma Lento.sun (i:ℝ):Lento fun _=> i:=⟨|i|,0,abs_nonneg _,Eventually.of_forall fun x=> by rw [pow_zero,mul_one]; linarith [Real.add_one_le_exp |i|]⟩
private lemma poc (x:ℝ):1 ≤ plow x:=Scales.size x
lemma Lento.plus{f g:ℝ→ℝ}(h:Lento f)(p:Lento g):Lento fun x=>f x+g x:=by
 obtain ⟨C,r,hC,h⟩:=h; obtain ⟨D,s,hD,p⟩:=p
 refine ⟨C+D+1,r+s,by positivity,?_⟩; filter_upwards [h,p] with x h p; set z:= (C+D)*(plow x)^(r+s); have hr:=poc x; have hk:1 ≤ plow x^(r+s):=one_le_pow₀ hr; have hh:C*(plow x)^r ≤ z:=by unfold z; gcongr; linarith; exact Nat.le_add_right .. -- tune
 have he:D*(plow x)^s ≤ z:=by unfold z; gcongr; linarith; exact Nat.le_add_left ..
 refine (abs_add_le ..).trans ((add_le_add (h.trans (Real.exp_monotone hh)) (p.trans (Real.exp_monotone he))).trans ?_)
 rw [add_mul, one_mul, Real.exp_add, ← two_mul, mul_comm]; exact mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (plow x^(r+s))]) (Real.exp_pos _).le
lemma Lento.times{f g:ℝ→ℝ}(h:Lento f)(p:Lento g): Lento fun x=>f x*g x:=by
 obtain ⟨C,r,hC,h⟩:=h; obtain ⟨D,s,hD,p⟩:=p
 refine ⟨C+D,r+s,by positivity,?_⟩; filter_upwards [h,p] with x h p; rw [abs_mul,add_mul]; have hr:=poc x; apply (mul_le_mul h p (abs_nonneg _) (Real.exp_pos _).le).trans; rw [← Real.exp_add]; exact Real.exp_monotone (by gcongr <;> omega)
lemma Lento.power{f:ℝ→ℝ}(h:Lento f)(n:ℕ): Lento fun x=> f x^n:=by induction n with| zero=> simpa using Lento.sun 1| succ n ih=>simp_rw [pow_succ]; exact ih.times h
lemma Lento.mono{f g:ℝ→ℝ}(h:Lento f)(p:∀ᶠ x in atTop,|g x| ≤ |f x|):Lento g:=by obtain ⟨C,r,hC,h⟩:=h; refine ⟨C,r,hC,?_⟩; filter_upwards [h,p] with x hx hp; exact hp.trans hx
lemma plow_l:Lento plow:=by
 refine ⟨1,1,zero_le_one,Eventually.of_forall fun x=> ?_⟩; have p:=poc x; rw [pow_one,one_mul,abs_of_nonneg (by linarith)]; linarith [Real.add_one_le_exp (plow x)]
lemma swim: Lento (fun x:ℝ=>x):=by
 refine ⟨1,1,zero_le_one,?_⟩; filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx; rw [one_mul,pow_one,abs_of_pos hx]; conv_lhs=> rw [←Real.exp_log hx]
 apply Real.exp_monotone; unfold plow Scales.b; have h: Real.log x^2 ≤ (radiusB x:ℝ):= Nat.le_ceil _; nlinarith
lemma Lento.yearB(P:Side):Lento (y G P):= swim.plus (sun _)
lemma Lento.tuff(P:Side):Lento fun x=>(fiery G x P)⁻¹ :=by
 refine (yearB P).mono ?_; filter_upwards [(year G P).eventually_ge_atTop 1,(peak G P).eventually_ge_atTop 1,(minute G P).eventually (ge_mem_nhds (show (0:ℝ)<1 by norm_num))] with x hx hp hf; let t:=g G P x; have ht:0< t:=Scales.gauge G P (zero_lt_one.trans_le hx); -- tune hg hx
 have h:fiery G x P=t*Scales.p G P x:=fi ..; have hJ:=yg2 G P (zero_lt_one.trans_le hx); change y G P x*t^2=1 at hJ; rw [abs_of_nonneg (show 0 ≤ (fiery G x P)⁻¹ from inv_nonneg.mpr (Work.E04.temp_nonneg _)), abs_of_pos (zero_lt_one.trans_le hx),h]
 apply le_trans (inv_anti₀ ht (le_mul_of_one_le_right ht.le hp)); rw [inv_le_iff_one_le_mul₀ ht]; change t≤1 at hf; nlinarith
lemma lentA(P:Side) (f:ℝ→ℝ)(h:Lento f)(m:ℕ)(k:ℝ)(p:0<k)(K:ℝ)(u:0 ≤ K): ∀ᶠ x in atTop,∀ r t:ℕ,(t:ℝ) ≤ K*(r:ℝ)*plow x^m→|f x|^t ≤ Real.exp (k*(Scales.p G P x)^2 * r):=by
 obtain ⟨Q,j,g,H⟩:=h; set V:=Q*K; have hV:0 ≤ V:=mul_nonneg g u
 have he:= ((cover_pay G P (m+j) two_pos).const_mul V); rw [mul_zero] at he
 filter_upwards [he.eventually (ge_mem_nhds p),H] with x hx hh r t ht
 simp only [Real.rpow_two] at hx; rw [←mul_div_assoc,div_le_iff₀ (pow_pos (Scales.pos ..) _)] at hx; refine (pow_le_pow_left₀ (abs_nonneg _) hh t).trans ?_
 rw [←Real.exp_nat_mul]; apply Real.exp_monotone; have hg:=poc x; refine (mul_le_mul_of_nonneg_right ht (by positivity)).trans ?_; rw [show K*↑r*plow x^m*(Q*plow x^j)= V*plow x^(m+j)*r from by rw [pow_add]; unfold V; ring]; exact mul_le_mul_of_nonneg_right hx (by positivity)
end YM.CF.Esti
