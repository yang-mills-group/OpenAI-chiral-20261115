import YM.SU5.FiniteGaugeData.Lycan.Joy
import YM.SU5.FiniteGaugeData.CodaT.Royal
/-! # WP24b: joint P20 estimate and centered covariance. Paths at certain late but then fixed versions. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 410000
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.LyraBill
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Window.Brique
open Reed (Fine)
attribute [local instance] opCStarAlgebra
set_option quotPrecheck false
open Heat Quest Fock.Brique
open Nacre Heat Charm Chrono Journey
open Py Py.Rate LocalLimit Preparation Journey Fiber Vale VolumeCape FullBill
open SalonG
open Quest.Chaperone
open Steam
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l)) {g:ℝ}{u v:ℕ→ℕ}
open Eight YM.SU5.FiniteGaugeData.CodaT YM.SU5.FiniteGaugeData.Cuprite.Spirit YM.SU5.FiniteGaugeData.Cuprite.Spirit.Vapors Fock.Relief Rhythm.Hush Rhythm.CodaT Dial Aria Reduction.Drama.Pack
open Rhythm.Dolores Rhythm.Ergo Hills Gamer Fock.Reduction Turnist Alts Alts.Emblem Window.Presidio.Nigra
namespace Chiffon
open Moorend Rhythm.CodaT
open Reduction.Loyd Reduction.Dijon Reduction.Loyd.Art Reduction.Celeste
namespace Sesame
open Reduction Lycan Niagara Chisel Largo Mirage Cascade Ember PolarF Onyx
open Stationary Mir Royal
-- wires normal at x with i-apex; all species.Matter site support. real normalization.
variable (σ:Window.Family)(x y:Cover)(i n:ℕ)
local notation "r°"=>n+1
abbrev originT(N:ℕ)(x: Cover):Cover:= x+(N+1) • step 3
abbrev oculus(σ:Window.Family)(x:Cover)(n:ℕ):= Royal.berceuse σ (originT n x) (n+1)
def antiPol(X:Grit):Grit:=
 let x:=(Buffered.plane 3 0).flee X.landing; let y:=(Buffered.plane 3 0).flee X.launch
 ⟨X.σ,x,y,Lattice.route (nodeC x) (nodeC y) 1,Lattice.route_end ..,0,2,by decide,by decide⟩
private lemma spin_pin0 (i:SpinIdx): Mir.pin 3 i 0=(if i=2 then 1 else 0) ∧ Mir.pin 3 i 2= (if i=0 then -1 else 0):=by
 fin_cases i <;> norm_num [Mir.pin,gammaOp,grading,Matrix.mul_apply,SpinIdx,Axis, Fin.ext_iff,Fin.sum_univ_succ] -- tune from Melody
 all_goals first| rfl | exact ⟨rfl,rfl⟩ | (simp only [show (2:Fin 4)=Fin.succ (1:Fin 3) from rfl,show (3:Fin 4)=Fin.succ (2:Fin 3) from rfl,show (2:Fin 3)=Fin.succ (1:Fin 2) from rfl,Matrix.cons_val_succ]; norm_num) -- tune
 all_goals rfl
private lemma act0 (N:Side)(p: SU.Slot) : acts (carR 3 0 N).val (basisC N x 0 p)= basisC N ((Buffered.plane 3 0).flee x) 2 p :=by
 rw [acted_basisC]; simp_rw [(spin_pin0 _).1, ite_smul,zero_smul,one_smul]; rw [sum_ite_eq',if_pos (mem_univ _)]
private lemma act2 (N:Side)(p: SU.Slot) : acts (carR 3 0 N).val (basisC N x 2 p)= -(basisC N ((Buffered.plane 3 0).flee x) 0 p) :=by
 rw [acted_basisC]; simp_rw [(spin_pin0 _).2,ite_smul,zero_smul,neg_smul,one_smul]; rw [sum_ite_eq',if_pos (mem_univ _)]
variable {X:Grit}(uu:X.u=0)(d':X.d=2)(N:Side)
local notation "v'"=> carR 3 0 N
local notation "F0"=>theta v'
include uu d'
lemma flips (p:SU.Slot):theta (carR 3 0 N) (Lycan.mark (uEnd id N) (dEnd id N) (X,p) (X,p))= Lycan.mark (uEnd id N) (dEnd id N) (antiPol X,p) (antiPol X,p):=by
 let A:= antiPol X; let V:= v'; let W:=dEnd id N (A,p); let Y:= uEnd id N (A,p)
 have he: acts V.val (uEnd id N (X,p))=W:=by change acts V.val (basisC N X.launch X.u p)=_; rw [uu]; exact act0 X.launch N p
 have hp: acts V.val (dEnd id N (X,p))= -Y:=by change acts V.val (basisC N X.landing X.d p)=_; rw [d']; exact act2 X.landing N p
 rw [Lycan.mark,theta_mul,theta_upV,theta_downV,he,hp,map_neg,smul_neg, Algebra.smul_mul_assoc,mul_neg,Algebra.mul_smul_comm,smul_neg,smul_smul,neg_mul,Complex.I_mul_I]; rw [neg_neg,one_smul,show Fock.remove W*create Y= -(_ ) from duo _ _ (siphon id N (A,p) (A,p)),neg_neg] -- tune neg rw and remove
lemma turf : Auth.turn (ProbeCode.score X) 3 0 N 1= ProbeCode.score (antiPol X) N 1:=by
 have hv:fling 3 0 N 1=1:=by funext i; unfold fling; change Step.read _ _ _=(1:SU.E); simp [Lattice.Step.read]
 let A:= antiPol X; unfold Auth.turn; rw [hv,show ProbeCode.score X N 1= _ from dgreen id N X,show ProbeCode.score (antiPol X) N 1=_ from dgreen id N _]; unfold tribe; rw [theta_sum]; exact sum_congr rfl fun p _=> flips uu d' N p
omit uu d'
abbrev ferris(x y:Cover)(n:ℕ)(b:Bool):Grit:= if b then oculus σ y n else antiPol (oculus σ x n)
abbrev localFee(K:Calibration)(x y:Cover)(n:ℕ)(b:Bool): W K:= if b then bookFee K (oculus σ y n) else fire K 3 0 (bookFee K (oculus σ x n))
abbrev localSite(x y:Cover)(n:ℕ)(b:Bool):Finset Cover:= if b then (oculus σ y n).town else refract 3 0 ((oculus σ x n).town)
abbrev localPaint(x y:Cover)(n:ℕ)(b:Bool):Paint:= if b then ProbeCode.score (oculus σ y n) else Auth.turn (ProbeCode.score (oculus σ x n)) 3 0
lemma localSkin(K:Calibration)(v:Bool):Auth K (localSite σ x y n v) (localFee σ K x y n v) (localPaint σ x y n v):=by
 cases v; · exact Auth.polar (ProbeCode.Country K _) 3 0
 exact ProbeCode.Country K _
lemma scent0 (v:Bool):localPaint σ x y n v N 1=ProbeCode.score (Sesame.ferris σ x y n v) N 1:=by cases v; exact turf (by rfl) (by rfl) N; rfl
local notation "A°"=> ferris σ x y
-- structure.V
abbrev morphK(b:Bool):ℤ:= if b then 1 else -2
abbrev dayb(b a:Bool):ℝ:= ((morphK a+1-morphK b:ℤ):ℝ)
def aSpan(b a:Bool): Gaia:= Window.corner (dayb b a)
private lemma leadK(b:Bool): ((A° n b).launch)=(r°) • (morphK b • step 3) + if b then y else (Buffered.plane 3 0).flee x :=by
 ext i; by_cases p:i=3<;> cases b <;> simp_all [ferris,antiPol,morphK,oculus,Royal.berceuse,originT,step,flee_pos,eq_comm] -- tune
 all_goals ring
private lemma lowerK(b:Bool): ((A° n b).landing)=(r°) • ((morphK b+1) • step 3) + if b then y else (Buffered.plane 3 0).flee x :=by
 ext i; by_cases p:i=3<;> cases b <;> simp_all [ferris,antiPol,morphK,oculus,Royal.berceuse,originT,step,flee_pos,eq_comm]
 all_goals ring
private lemma normage (x:Cover)(t:ℤ): Tendsto (fun n:ℕ=> Onyx.riseX (Royal.fuao n) ((n+1) • (t • step 3)+x)) atTop (𝓝 (Window.corner (t:ℝ))):=by
 let q(n:ℕ):= Royal.fuao n; have he:Tendsto q atTop atTop:=tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
 let F(n:ℕ):= WithLp.ofLp (p:=2) (Onyx.riseX (Royal.fuao n) ((n+1) • (t • step 3)+x)); refine ((PiLp.continuous_toLp 2 _).tendsto (WithLp.ofLp (p:=2) (Window.corner (t:ℝ)))).comp (f:=F) (tendsto_pi_nhds.mpr ?_); intro i
 let U:=Tendsto.const_div_atTop he (x i:ℝ); let y:= Window.corner (t:ℝ); refine (show Tendsto (fun n=> y i+ (x i:ℝ)/q n) atTop (𝓝 (y i)) from (by simpa only [add_zero] using U.const_add (y i))).congr' (Eventually.of_forall fun n=>?_); dsimp only [F]; have h:0< (n:ℝ)+1:=by positivity
 by_cases p:i=3 <;> simp [q,y, Royal.fuao,riseX,moor,p,Window.corner] ; field_simp -- `t` simp unnecessary
lemma cantor : Globe (ferris σ x y) Royal.fuao (fun _=>σ) (fun _=>0) (fun _=>2) aSpan:=by
 refine ⟨fun _=>by unfold fuao; positivity,tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop,fun i b=>?_,fun b a=>?_⟩
 · cases b <;> exact ⟨rfl,rfl,rfl⟩
 let v:= morphK a+1; let w:=morphK b; let Y0(b:Bool):= if b then y else (Buffered.plane 3 0).flee x
 have he(i:ℕ) : ((A° i a).landing)- ((A° i b).launch)=(i+1) • ((v-w) • step 3)+ (Y0 a-Y0 b):=by rw [leadK,lowerK, _root_.sub_smul, _root_.smul_sub]; unfold v w Y0; abel
 refine ⟨fun t=>?_,?_⟩; · have h:=congrArg (fun x:Gaia=>x 3) t; cases a <;> cases b <;> norm_num [aSpan,Window.corner,dayb,morphK,PiLp.zero_apply] at h -- tune
 simp_rw [he]; exact normage _ _
#print axioms cantor
#print axioms turf
end Sesame
end Chiffon
end YM.CF.Buffered.Afterglow.Hierarchy.LyraBill
