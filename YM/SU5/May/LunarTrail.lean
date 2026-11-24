import YM.SU5.May.LunarFeatures
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
local notation "β"=> warp b (chord N P i)
structure Trail (N:Side)(P:Ramp)(b:Bool)(X:Type*) where
 atSlot:X→ Cover
 appointment:X→Slot
 vr:X→ Ket SpinIdx
 noted:∀ i, remains b (vr i)
 inK:∀ i,Legible P N (atSlot i)
 amountC:∀ i, ‖vr i‖ ≤1
namespace Trail
variable (F:Trail N P b X)(w: X→ℂ)
noncomputable def lives: Ket (Single N):=∑ i:X, w i • cantor N (F.atSlot i) (F.appointment i) (F.vr i)
noncomputable def stored(i j:X):ℂ:= Solstice N P b (F.atSlot i) (F.atSlot j) (F.vr i) (F.vr j) (F.appointment i) (F.appointment j)
noncomputable def yield :ℂ:=∑ i:X,∑ j:X, star (w i)*w j * F.stored i j
def feature:Screen:= ∑ j:X,w j • forward N P i b (F.atSlot j) (F.appointment j) (F.vr j)
def yesterday:Screen:= ∑ j:X,w j • back N P i b (F.atSlot j) (F.appointment j) (F.vr j)
local notation "μ"=> ∑ i:X,‖w i‖
local notation "σ"=> stip P N i
local notation "η'"=>reelT P N i
lemma sum_season : HasSum (fun i:Title P=> sectionC N P i (F.feature i w) (F.feature i w) (F.yesterday i w) (F.yesterday i w)) (F.yield w):= by
 let f(n:Title P)(j:X):= forward N P n b (F.atSlot j) (F.appointment j) (F.vr j); let g(n:Title P)(j:X):= back N P n b (F.atSlot j) (F.appointment j) (F.vr j)
 let A(x y:X)(i:Title P):= (star (w x)*w y)*sectionC N P i (f i x) (f i y) (g i x) (g i y)
 have h(x y:X):HasSum (A x y) (star (w x)*w y* F.stored x y):= (compass _ _ _ _ b _ _ _ _ (F.inK x) (F.inK y) (F.noted y)).mul_left _
 have he (i:Title P): sectionC N P i (F.feature i w) (F.feature i w) (F.yesterday i w) (F.yesterday i w)= ∑ j:X,∑ k:X,A j k i:=by
    unfold feature yesterday; simp_rw [A,sectionC, sum_inner,inner_sum,inner_smul_left,inner_smul_right,Finset.mul_sum,←Finset.sum_sub_distrib]; simp_rw [Finset.mul_sum]; refine sum_congr rfl fun j _=> sum_congr rfl fun k _=>?_ ; unfold f g; rw [← Complex.star_def]; ring
 simp_rw [he]; exact hasSum_sum (s:=Finset.univ) (f:=fun j n=>∑ k:X,A j k n) fun i _=> hasSum_sum (s:=Finset.univ) fun j _=>h i j
noncomputable def privilege :ℝ:= stip P N i * ‖F.feature i w‖^2
noncomputable def proration :ℝ:= stip P N i * (reelT P N i)*‖F.yesterday i w‖^2
lemma privilege_p : 0≤ F.privilege i w:=mul_nonneg (stip_n N P i) (sq_nonneg _)
lemma charges : HasSum (fun i=>F.privilege i w-F.proration i w) ((N.val:ℝ)^3*(F.yield w).re):= by
 let h' := (F.sum_season w).mapL Complex.reCLM -- need `ReCLM`
 have he(i:Title P): sectionC N P i (F.feature i w) (F.feature i w) (F.yesterday i w) (F.yesterday i w)= ((1/(N.val:ℝ)^3 *(F.privilege i w-F.proration i w):ℝ):ℂ):=by
    unfold sectionC; rw [inner_self_eq_norm_sq_to_K,inner_self_eq_norm_sq_to_K]; unfold privilege proration; push_cast; ring_nf; simp only [sub_eq_add_neg,add_comm]; rfl
 refine (h'.mul_left ((N.val:ℝ)^3)).congr_fun fun i=>?_ ; change _=((N.val:ℝ)^3)*(sectionC ..).re; rw [he, ofReal_re]; field_simp
lemma shadow_read : ‖F.yesterday i w‖≤ 2*Real.exp (grain P i/8)* (∑ j:X,‖w j‖):=by
 let E:= 2*Real.exp (grain P i /8); have e:0≤E:= by unfold E; positivity
 unfold yesterday; apply (norm_sum_le ..).trans; rw [mul_sum]; refine sum_le_sum fun j _=> ?_; rw [norm_smul,mul_comm (2*_ :ℝ)]; exact mul_le_mul_of_nonneg_left ((shadow N P i (F.atSlot j) b _ _ (F.inK j)).trans ((mul_le_mul_of_nonneg_left (F.amountC j) e).trans_eq (mul_one _))) (norm_nonneg _)
-- need $T≥80.$
variable (t:80 ≤ rimB N)
include t
lemma funding : |F.proration i w| ≤ 4*loanP * Real.exp (-grain P i/2)*(∑ j:X,‖w j‖)^2:=by
 let Y:=grain P i; let z:=‖F.yesterday i w‖; let B:ℝ:= ∑ j:X,‖w j‖; unfold proration; rw [abs_mul,abs_mul (stip ..:ℝ),abs_of_nonneg (show (0:ℝ)≤‖F.yesterday i w‖^2 from sq_nonneg _)] -- actually `abs_pow` then
 rw [abs_of_nonneg (stip_n N P i)]; refine (mul_le_mul (ceil_back N P i t) (pow_le_pow_left₀ (show 0≤z from norm_nonneg _) (show z ≤ _ from shadow_read i F w) 2) (sq_nonneg _) (mul_nonneg loan_p.le (Real.exp_nonneg _))).trans_eq ?_
 rw [show Real.exp (-grain P i/2) = Real.exp (-(3/4:ℝ)*grain P i)* (Real.exp (grain P i/8))^2 from (by rw [sq,←Real.exp_add,←Real.exp_add]; ring_nf)]; ring
lemma backSum: Summable (fun i=>F.proration i w):=by
 let C:=4*loanP * (μ)^2; refine Summable.of_norm_bounded ((rime_sum P).mul_left C) (fun i=>?_); rw [Real.norm_eq_abs]; refine ((F.funding i w t)).trans ?_; let c:=cessR P; refine le_trans ?_ (le_of_eq (show 4*loanP*rime P i *(μ)^2=C*rime P i from (by unfold C; ring))); apply mul_le_mul_of_nonneg_right _ (sq_nonneg _); refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (by norm_num) loan_p.le); unfold rime; exact Real.exp_monotone (by linarith only [grain_floor P i])
lemma frontSum: Summable (fun i=> F.privilege i w):=by simpa only [sub_add_cancel] using ((F.charges w).summable.add (F.backSum w t))
noncomputable def temple:= ∑' i,F.privilege i w
omit t in
lemma temple_n :0≤F.temple w:= tsum_nonneg (fun i=>F.privilege_p i w)
lemma entire_h : ((N.val:ℝ)^3*(F.yield w).re)= F.temple w- ∑' i,F.proration i w:=by unfold temple; rw [← (F.frontSum w t).tsum_sub (F.backSum w t)]; exact (F.charges w).tsum_eq.symm
#print axioms funding
#print axioms entire_h
end Trail
end YM.CF.May.Lunar
