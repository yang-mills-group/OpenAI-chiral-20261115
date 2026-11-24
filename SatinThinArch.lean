import SatinThinPiers
set_option autoImplicit false
set_option maxHeartbeats 680000
set_option synthInstance.maxSize 20000
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.CF.QuadClock
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Stationary Rush Cube Scroll SU Drapes Peaks Dial Paige Brace Vault Fock Tulip Font Spire Nacre Ember Pec Levier Skye Scree Hove Haro Tap Moto
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker MatrixOrder Classical
attribute [local instance] opCStarAlgebra
set_option quotPrecheck false
open Ione StressFlux AnalyticBridge.VerifiedReset

variable {n:Side}{c t:Bool}{s:Signed}{U:UNI SpinIdx}(H:JetS s c t U)

lemma paneStep (P:Op (Single n))(p q:Bool)(o:Site n)(i j:Option Axis)(a:Shape)(w:JetS a.s c t U)(g:FinLife P (a.mills n o)):
 snapH (fillOpt (t.xor p) o i) (fillOpt (t.xor q) o j) (sings c (prepU a U (xtra c) n) P)
   = (signOpt a.s i*signOpt a.s j) • sings c (twoU U c) (snapH (fillOpt p (a.mills n o) (portQi a i)) (fillOpt q (a.mills n o) (portQi a j)) P):=by
 let L:=sings c (prepU a U (xtra c) n) P; let A:=fillOpt (t.xor p) o i; let B:=fillOpt (t.xor q) o j; let V:=a.mills n o; let C:=fillOpt p V (portQi a i); let D:=fillOpt q V (portQi a j); let Ψ:=twoU U c
 let s:= signOpt a.s i * signOpt a.s j
 change snapH A B L = s • sings c Ψ (snapH C D P)
 let f(x y:Site n):= star (nose A x)*matPH L x y*nose B y; let k(x y:Site n):=star (nose C x)*matPH P x y*nose D y
 have hs(x y:Site n): f x y = s • sings c Ψ (k (a.mills n x) (a.mills n y)):=by
    let T:= a.mills n; unfold f k; rw [show matPH L x y= (a.payA x*a.payA y) • sings c (twoU U c) (matPH P (T x) (T y)) from payR P x y a c U]; by_cases hp:matPH P (T x) (T y)=0
    · rw [hp]; simp [singT,win_z]
    rw [singT (p:=c) Ψ (star (nose C (a.mills n x))*matPH P (a.mills n x) (a.mills n y)*nose D (a.mills n y)),win_m,win_m,win_s,map_mul,map_mul,map_star]; have he:=g (T x) (T y) hp
    rw [show twist _ (windX _ (nose C (a.mills n x)))=_ from noseV a w p o x i he.1,show twist _ (windX _ (nose D (a.mills n y)))=_ from noseV a w q o y j he.2]; simp only [star_smul,star_trivial,star_mul,a.real_payA];
    let K:=sings c Ψ (matPH P (T x) (T y)); let E:=star (nose A x)*K*nose B y; change star (nose A x) * ((_*a.payA y) • K)* nose B y = s • ( _ * K * _)
    let a₀:=signOpt a.s i; let b₀:=signOpt a.s j; have hz: a₀*a₀=1:=scarOpt_sq ..; have hv: b₀*b₀=1:=scarOpt_sq ..
    simp only [←Complex.coe_smul,Matrix.smul_mul,Matrix.mul_smul,smul_smul]; apply congrArg (fun k:ℂ=> k • E); unfold s; -- tune
    push_cast; change _= ((a₀:ℂ)* (b₀:ℂ))*_; -- use ring combination
    have hf:a.payA o*a.payA o=1:= a.reflex o; have ht:(a₀:ℂ)*(a₀:ℂ)=1:=by exact_mod_cast hz
    have hu:(b₀:ℂ)*(b₀:ℂ)=1:=by exact_mod_cast hv
    let Z:= a.payA x*a.payA y; refine Eq.trans (b:= (a₀:ℂ)*a₀*((b₀:ℂ)*b₀)*(a.payA o*a.payA o)*Z) ?_ ?_
    · rw [ht,hf,hu,one_mul,one_mul,one_mul]
    unfold Z a₀ b₀; ring
 rw [grantF,grantF]; change (∑ x:Site n,∑ y:Site n, f x y)= s • sings c Ψ (∑ x:Site n,∑ y:Site n,k x y);
 rw [singT,win_sum,map_sum, Finset.smul_sum]; simp_rw [win_sum,map_sum,Finset.smul_sum]; exact Fintype.sum_equiv (Tofu a n) _ _ fun x=> Fintype.sum_equiv (Tofu a n) _ _ fun y=> hs x y
lemma starSnap {n:Side}(P:Op (Single n))(S T:Foot n): snapH S T (-star P)= -(star (snapH T S P)):=by
 unfold snapH; change Sᴴ*(-Pᴴ)*T= -((Tᴴ*P*S)ᴴ); simp only [Matrix.mul_neg,Matrix.neg_mul, Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,Matrix.mul_assoc] -- tune

noncomputable def castPal (a b:Bool)(U: UNI SpinIdx) (F: Pal):= Thera.jazz b (sings a (twoU U a) F)
noncomputable def coinArc (s:Signed)(a b:Bool)(U: UNI SpinIdx)(X:Dome) : Dome:= (castPal a b U X.1,fun i=> sign s i • castPal a b U ((if b then X.2.2 else X.2.1) (s.perm i)),fun i=> sign s i • castPal a b U ((if b then X.2.1 else X.2.2) (s.perm i)))
include H
lemma cul_p1 (A:Pal): culm (castPal c t U A)=castPal c t U (culm A):=by
 have hx:=step_Base H false; have hy:=step_Base H true; unfold culm castPal
 cases t; swap
 · simp only [Bool.true_xor,Bool.not_true,Bool.not_false, singT] at hx hy; change _= -star _; simp only [Thera.jazz,singT,ite_true,win_m,map_mul, star_mul, hx, hy, show star (baseF false)=baseF false from φ_a false, show star (baseF true)=baseF true from φ_a true]; simp [mul_assoc]
 change _*sings _ _ _*_=_; unfold Thera.jazz; simp only [Bool.false_eq_true, ite_false,singT,win_m,map_mul]; simp only [singT,Bool.false_xor] at hx hy; rw [hx,hy]
omit H
lemma castDome_step (W:Op (Single n))(o:Site n)(a:Shape)(q:JetS a.s c t U)(u:FinLife W (a.mills n o)):
 jetsL o (Thera.jazz t (sings c (prepU a U (xtra c) n) W))= coinArc a.s c t U (jetsL (a.mills n o) W):=by
 let A:= a.mills n o; let V:=sings c (prepU a U (xtra c) n) W
 let Z(i j:Option Axis):= snapH (fillOpt false A (portQi a i)) (fillOpt true A (portQi a j)) W
 let B(i j:Option Axis):= signOpt a.s i*signOpt a.s j
 let F:=fun i j=> snapH (fillOpt false o i) (fillOpt true o j) (Thera.jazz t V)
 have hp(i j:Option Axis): F i j=B i j • castPal c t U (if t then Z j i else Z i j):=by
    cases t
    · unfold F castPal B Z; unfold V A; simp only [Bool.false_eq_true,ite_false,Thera.jazz];
      have hp:= paneStep W false true o i j a q u; simpa only [Bool.false_xor] using hp
    unfold F castPal B Z; unfold V A; simp only [Thera.jazz,ite_true]
    have hp:=paneStep W false true o j i a q u; simp only [Bool.true_xor,Bool.not_true,Bool.not_false] at hp; rw [starSnap,hp,star_smul,star_trivial, mul_comm (signOpt _ j),smul_neg]
 have hz(i:Option Axis): B none i=signOpt a.s i:=one_mul _; have hx(i:Option Axis):B i none=signOpt a.s i:=mul_one _
 let J:= jetsL (a.mills n o) W; let K:= castPal c t U
 refine Prod.ext (?_: F none none= castPal c t U (Z none none)) (Prod.ext ?_ ?_)
 · rw [hp,hx,ite_self]; exact one_smul ..
 · funext i; change culm (F (some i) none)= sign _ _ • K _; rw [hp,hx,culm,Matrix.mul_smul,Matrix.smul_mul,show (baseF false*castPal _ _ _ _*baseF true)=_ from cul_p1 q _]; cases t<;>rfl
 funext i; change culm (F none (some i))= sign _ _ • K _; rw [hp,hz,culm,Matrix.mul_smul,Matrix.smul_mul,show (baseF false*castPal _ _ _ _*baseF true)=_ from cul_p1 q _]; cases t<;>rfl

noncomputable def costDome(s:Sweep n)(F:Dome):Dome:=coinArc s⁻¹.s s⁻¹.charge (detX s⁻¹.s) (spinU s⁻¹.charge s⁻¹.s) F -- notation s⁻¹.s? Lean parses?
lemma cost_Dome (s:Sweep n)(K:Scree.Hub n)(a b:Site n)(g:Earlier s a b)(y:K.val.1=node a)(Z:InkD n){P:RG.BudgetPoint}{h c:ℝ}(p:PressB P (moveHub s K) Z h c)(w: Nonwrapping (moveHub s K).val.2 (moveHub s K).val.1):
 jetsL a (orbitPH (step_F s Z 1))= costDome s (jetsL b (orbitPH (Z 1))):=by
 let T:= s⁻¹; unfold step_F; simp only [Function.comp_apply,suit_Y,paral,Facet.glacial]
 have hb : (moveHub s K).val.1=node b:=by apply (boxA s).injective; exact ((boxA s).apply_symm_apply _).trans (y.trans g.symm)
 have ht:(castX s⁻¹).mills n a=b:= (earlier_mills ..).mp g.backward; unfold costDome; rw [←ht]; exact castDome_step _ a (castX s⁻¹) (spinZ ..) (ht.symm ▸ (finPartition (moveHub s K) b Z p hb w)) -- tune
end YM.CF.QuadClock
