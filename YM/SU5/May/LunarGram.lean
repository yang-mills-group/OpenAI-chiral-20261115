import YM.SU5.May.LunarStencil
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
variable (N:Side)(P:Ramp)(p q:E4)(i:Title P)(x y:Cover)(b:Bool) (v w:Ket SpinIdx) (m x':ℝ)
abbrev Screen:= PiLp 2 fun _:Slot=>Ket SpinIdx
variable (a d:Slot)
noncomputable def faceN (x:Cover):= lengthT P (age x)
local notation "J" => tilted P
local notation "Θ"=> P.plan.flee
local notation "G"=> chord N P i
local notation "η" => ‖chord N P i‖
local notation "K"=> warp b (chord N P i)
local notation "C"=>walletP P (chord N P i) ‖chord N P i‖
local notation "δ"=>tagE P i
local notation "T"=>rimB N
def poreP (x:ℝ):ℂ:=Real.exp x
noncomputable def gramF (P:Ramp)(q p:E4)(t:ℝ)(x:Cover)(a:Slot)(v:Ket SpinIdx):Screen:= (coastE (-inner ℝ q (age x))*poreP (t*faceN P x)) • (PiLp.single 2 a (acts (hymnP P p) v):Screen)
abbrev forward := gramF P (warp b (chord N P i)) (warp b (chord N P i)) (- ‖chord N P i‖)
abbrev back := gramF P (warp b (chord N P i)) (-(warp b (chord N P i))) ( ‖chord N P i‖)
noncomputable def stip (P:Ramp)(N:Side)(i:Title P):ℝ:= halfer/2 * windowW P (chord N P i)/earning (rimB N) ‖chord N P i‖ (tagE P i)
-- positive. T not suppressed? combine below
noncomputable def reelT(P:Ramp)(N:Side)(i:Title P):ℝ:= tagE P i*Real.exp (-‖chord N P i‖ *rimB N)
local notation "γ" => stip P N i
def sectionC (Y Z Y' Z':Screen) :ℂ:= (1/(N.val:ℂ)^3:ℂ)*(stip P N i:ℂ)*(inner ℂ Y Z-(reelT P N i:ℂ)*inner ℂ Y' Z') -- Y notation conflict
private lemma grade_age : lengthT P (emitX (gapC P b x y)) = - (faceN P x+ faceN P y):=by cases b; exact ptime P x y; change lengthT _ _= _; unfold faceN; rw [add_comm]; exact ptime P y x
private lemma grade_loc : inner ℝ (chord N P i) (emitX (gapC P b x y))= inner ℝ (warp b (chord N P i)) (age x)- inner ℝ (warp b (chord N P i)) (age y):=by
 cases b
 · exact orbit_time N P i x y
 simp only [warp,gapC,if_true,inner_neg_left, orbit_time]; ring
lemma gram_inner : inner ℂ (gramF P q p m x a v) (gramF P q p m y d w) = (if a=d then coastE (inner ℝ q (age x)-inner ℝ q (age y))*poreP (m*(faceN P x+faceN P y))* inner ℂ (acts (hymnP P p) v) (acts (hymnP P p) w) else 0):= by
 unfold gramF; let X(y:Ket SpinIdx)(a:Slot):Screen:= PiLp.single 2 a y; let V:= X (acts (hymnP P p) v) a; let W:=X (acts (hymnP P p) w) d; have he: inner ℂ V W= (if a=d then inner ℂ (acts (hymnP P p) v) (acts (hymnP P p) w) else 0):=by
    rw [PiLp.inner_apply,Finset.sum_eq_single a]; · unfold V W X; split; rename_i h; rw [h]; simp; rename_i h; simp [PiLp.single_apply,h] -- tune h orientation
    · intro i _ t; simp [V,X,PiLp.single_apply,t]
    · simp
 rw [inner_smul_left,inner_smul_right, ←Complex.star_def, star_mul, coast_inv, neg_neg, show inner ℂ (PiLp.single ..:Screen) (PiLp.single ..:Screen) = _ from he]; unfold poreP; split_ifs <;> simp only [Complex.star_def,Complex.conj_ofReal, sub_eq_add_neg, coast_add, mul_add, Real.exp_add, ofReal_mul, mul_zero] <;> ring
local notation "Φ"=>forward N P i b
local notation "Υ"=>back N P i b
private lemma lumen (e:remains b w): inner ℂ v (acts (chargeAxis P b (Floe.coins N 1 • lash (campaign P i (emitX (gapC P b x y)) N))) w)= sectionC N P i (forward N P i b x a v) (forward N P i b y a w) (back N P i b x a v) (back N P i b y a w):= by
 let r:= gapC P b x y; let Q:=chord N P i; let E:=‖Q‖; let Z':= earning (rimB N) ‖Q‖ δ; let L:= chargeAxis P b; let Hb:= (if b then minA else Aop)
 have hy: acts Hb w=w:= by cases b; exact e; change acts minA w =_; rw [minA,act_sub,act_one,show acts Aop w= 0 from e,sub_zero]
 unfold campaign rays sectionC forward back; simp_rw [lash_s, lash_a,lash_s,charge_s,charge_q,charge_s]; let he:= duet N P i; let h:= hired N P i; rw [ocean_p P _ he h,ocean_n P _ he h]; simp only [act_smul, act_add, act_mul, show acts (if b then minA else Aop) w=w from hy]; simp only [inner_add_right,inner_smul_right]; rw [grade_loc, show inner ℝ (tilted P) _= _ from grade_age P x y b]; unfold errata; rw [portfolio P _ _ he,portfolio P _ _ he,wallet_turn P _ _ he]; simp_rw [gram_inner,if_true]; have ht:= warp_cross P _ he h b; have hh:= warp_hired P _ he h b; rw [horizon P _ _ _ ht hh,horizon P _ _ _ (show inner ℝ (tilted P) (-warp b Q)=0 by rw [inner_neg_right]; rw [ht, neg_zero]) (neg_ne_zero.mpr hh)]
 unfold poreP stip reelT windowW; -- ring spectral expo use sign normalization. diagnostic
 let N':ℂ:= N.val; have h0:E≠0:=(norm_pos_iff.mpr h).ne'; have h0': (‖Q‖:ℂ) ≠0:=by exact_mod_cast h0 -- Q.norm invalid
 have hz:0<Z':= earning_p (rimH N) (norm_pos_iff.mpr h) (tagguard P i).2.1; have hh0:(Z':ℂ)≠0:=by exact_mod_cast hz.ne'
 push_cast; field_simp -- tune
 unfold fareP Floe.coins rimB Q at *; push_cast; field_simp; ring
variable (o:-rimB N+20<lengthT P (emitX (gapC P b x y)))(U:lengthT P (emitX (gapC P b x y))< -20)
#print axioms grade_loc
noncomputable def Solstice (N:Side)(P:Ramp)(B:Bool)(x y:Cover)(v w:Ket SpinIdx)(a d:Slot):ℂ := booth v w a d (chargeAxis P B (headS N (gapC P B x y)))
include o U
lemma accumulation (e: remains b w): HasSum (fun i:Title P=>sectionC N P i (forward N P i b x a v) (forward N P i b y d w) (back N P i b x a v) (back N P i b y d w)) (Solstice N P b x y v w a d):=by
 unfold Solstice booth; split
 next h=> subst d; simp_rw [←lumen N P _ x y b v w a e]; set c:= coins N 1; let f: Peb→+ℂ:= {toFun:= fun A=> inner ℂ v (acts A w), map_zero':=by simp, map_add':=fun i j=>by rw [act_add, inner_add_right]} -- maybe no goals
          have hc: Continuous f:=by change Continuous (fun A:Peb=> inner ℂ v (acts A w)); apply Continuous.inner continuous_const; apply Continuous.clm_apply; exact acts_cont; exact continuous_const
          unfold headS; simp_rw [charge_s]; set x':= gapC P b x y; exact ( ((asker P b).hasSum (interrupt N P x' o U)).const_smul c |>.map f hc)
 next h=> simp only [sectionC,forward,back,gram_inner, if_neg h,mul_zero,sub_self,hasSum_zero] -- dollar
-- simple sufficient
structure Legible (P:Ramp)(N:Side)(x:Cover):Prop where
 minor : 20<faceN P x
 major : faceN P x < rimB N/8
omit o U
lemma compass (f:Legible P N x)(f':Legible P N y) (e: remains b w): HasSum (fun i:Title P=>sectionC N P i (forward N P i b x a v) (forward N P i b y d w) (back N P i b x a v) (back N P i b y d w)) (Solstice N P b x y v w a d):=by
 apply accumulation N P x y b v w a d _ _ e <;> rw [grade_age] <;> linarith [f.minor,f'.minor,f.major,f'.major]
#print axioms compass
end YM.CF.May.Lunar
