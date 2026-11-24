import YM.SU5.Silk.Clock.Ramp
import YM.SU5.Silk.Clock.Glide
import YM.CF.Hove.Bird
import YM.CF.Hove.Prune
set_option autoImplicit false
set_option maxHeartbeats 1900000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Ione.Clock
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Stationary Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Fock Tulip Font Spire Nacre Ember Pec
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker MatrixOrder Classical
attribute [local instance] opCStarAlgebra
open Tap Hake Urn Yaw Levier Proa Rill Hove StressFlux Jet Salt Ione Skye
open Stilo Pastry Scree
variable {n:Side}(s:Sweep n)(X:Support (More n))(o:Site n)(U:UNI SpinIdx)(h:Nonwrapping X (node (mPath s o)))(p:JetS s.s false (detX s.s) U)
local notation "C"=> cutM (pitchMask X)
local notation "O"=> mPath s o
local notation "K"=> siteU (castX s) false U n
local notation "W"=> W_fill -- wrong
local notation "H"=> spinQ U (xtra false)
local notation "P"=> s.s
local notation "D"=> cutM (pitchMask (actY s X))
local notation "c"=> (castX s).payA o
lemma pitch_rot : twist K (cutM (pitchMask X))=cutM (pitchMask (actY s X)):=by
 let L:=siteU (castX s) false U n; change twist L _=_; apply Mir.twist_comm; ext i j; rw [cutM,cutM,Matrix.diagonal_mul,Matrix.mul_diagonal]; by_cases t:L.val i j=0
 · rw [t,mul_zero,zero_mul]
 have ht: node j.1.1=(boxA s) (node i.1.1):=(show (boxA s) _=_ from Tye.birth_l i j (castX s) U false t).symm
 have hL:j∈ pitchMask X ↔ i∈ pitchMask (actY s X):=by rw [pitchIn,pitchIn,ht]; unfold actY; rw [Finset.mem_map_equiv]; rfl
 by_cases p:i∈ pitchMask (actY s X); rw [if_pos p, if_pos (hL.mpr p),one_mul,mul_one]; rw [if_neg p, if_neg (mt hL.mp p),mul_zero,zero_mul]
variable(XF:Op (Single n))
lemma pitch_Q (q:cutM (pitchMask X)*XF*cutM (pitchMask X)=XF): D * twist K XF *D= twist K XF:=by
 rw [← pitch_rot, ← map_mul,←map_mul,q]
variable (A B E F:Matrix (Single n) Kt ℂ)
local notation "Y"=> twist K XF
lemma coset_X(q:D*Y*D=Y)(a:D*(K).val*A=c • (D*E*(H).val))(b:D*(K).val*B=c • (D*F*(H).val)): Eᴴ * Y *F= twist H (Aᴴ*XF*B):=by
 let L:= spinQ U (xtra false)
 have hp: ((K).val*A)ᴴ* Y * ((K).val*B)= Aᴴ * XF* B:=by
    rw [Matrix.conjTranspose_mul,Matrix.mul_assoc (_*_) _ _, ←Matrix.mul_assoc Y (K).val,twist_product]
    simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc (K).val.conjTranspose (K).val,show (K).val.conjTranspose*(K).val=1 from (K).property.1,Matrix.one_mul] -- inspect
 have hf(D' C': Matrix (Single n) Kt ℂ): D'ᴴ*Y*C'= (D*D')ᴴ* Y *(D*C'):=by
    symm; rw [Matrix.conjTranspose_mul,show Dᴴ=D from (cutM_idp _).isSelfAdjoint];
    simp only [Matrix.mul_assoc]; rw [←Matrix.mul_assoc _ D C',←Matrix.mul_assoc D (Y*D),show D*(Y*D)=Y from (Matrix.mul_assoc ..).symm.trans q] -- tune
 let Y':= Eᴴ* Y *F
 have ht: Aᴴ*XF*B= L.val.conjTranspose*Y'*L.val:=by
    rw [← hp,hf,←Matrix.mul_assoc D,← Matrix.mul_assoc D (K).val,a,b]; simp only [Matrix.conjTranspose_smul,Matrix.smul_mul,Matrix.mul_smul, smul_smul,(castX s).real_payA,(castX s).reflex,one_smul]; unfold Y'; rw [hf E F, Matrix.conjTranspose_mul (D*E)]; simp only [Matrix.mul_assoc]; rfl
 rw [ht,twist_formula]; change Y'= L.val * (L.val.conjTranspose*Y'* L.val) * L.val.conjTranspose
 simp only [Matrix.mul_assoc]; rw [show L.val*L.val.conjTranspose=1 from L.property.2,Matrix.mul_one,←Matrix.mul_assoc,show L.val*L.val.conjTranspose=1 from L.property.2,Matrix.one_mul]
include h p
lemma poise1(b:Bool): D*(K).val*rampF b O=c • (D*rampF (b.xor (detX P)) o*(H).val):= rail U X s o h 0 (fun _=>baseF b) (fun _=>baseF (b.xor (detX P))) (fun x=>twinned P U p b)
lemma poise2(b:Bool)(i:Axis): D*(K).val*spanH b O ((P).perm i) = c • (D*hush ((P).flip i) (spanH (b.xor (detX P)) o i)* (H).val):=by
 let A':=fun u=>moonB b ((P).perm i) u; let B':=fun u=> hush ((P).flip i) (moonB (b.xor (detX P)) i u); have ht:=rail U X s o h 0 A' B' (fun u=>moon_s P U p u i b);
 rw [show bodyLift o B'=hush ((P).flip i) (spanH (b.xor (detX P)) o i) from ?_] at ht; exact ht; cases w:(P).flip i; simp only [B',w,hush_false]; rfl; ext x j; simp only [B',w,hush_true,bodyLift, spanH, Matrix.of_apply,Matrix.neg_apply,mul_neg]; rfl

omit p h
def zoomL (p:Signed)(U:UNI SpinIdx)(Z:Dome):Dome:= if detX p then ( -star (twist (spinQ U (xtra false)) Z.1),fun i=> -star (hush (p.flip i) (twist (spinQ U (xtra false)) (Z.2.2 (p.perm i)))),fun i=> -star (hush (p.flip i) (twist (spinQ U (xtra false)) (Z.2.1 (p.perm i))))) else (twist (spinQ U (xtra false)) Z.1,fun i=>hush (p.flip i) (twist (spinQ U (xtra false)) (Z.2.1 (p.perm i))),fun i=>hush (p.flip i) (twist (spinQ U (xtra false)) (Z.2.2 (p.perm i))))
lemma zoom_zero(q:Signed): zoomL q U 0=0:=by unfold zoomL; split<;> refine Prod.ext ?_ (Prod.ext (funext fun i=>?_) (funext fun i=>?_))<;> simp [hush,apply_ite]<;>split<;>simp

include h p
lemma tQuantum(q:D*Y*D=Y): jetsL o (Thera.jazz (detX P) Y)= zoomL P U (jetsL O XF):=by
 let V(b:Bool):= b.xor (detX P); have f:= coset_X s X o U XF _ _ _ _ q (poise1 s X o U h p false) (poise1 s X o U h p true)
 let g(i:Axis):= coset_X s X o U XF _ _ _ _ q (poise2 s X o U h p false i) (poise1 s X o U h p true)
 let j(i:Axis):= coset_X s X o U XF _ _ _ _ q (poise1 s X o U h p false) (poise2 s X o U h p true i)
 have A(i:Axis): (spanH (V false) o i)ᴴ*Y*rampF (V true) o=hush ((P).flip i) (twist H (partX O XF ((P).perm i))):=by
    have ht:=g i; cases w:(P).flip i; rw [w,hush_false] at ht; exact ht -- tune
    rw [w,hush_true,Matrix.conjTranspose_neg,Matrix.neg_mul,Matrix.neg_mul] at ht; rw [hush_true]; exact neg_eq_iff_eq_neg.mp ht
 have B(i:Axis): (rampF (V false) o)ᴴ*Y*spanH (V true) o i=hush ((P).flip i) (twist H (partY O XF ((P).perm i))):=by
    have ht:=j i; cases w:(P).flip i; rw [w,hush_false] at ht; exact ht
    rw [w,hush_true,Matrix.mul_neg] at ht; rw [hush_true]; exact neg_eq_iff_eq_neg.mp ht
 unfold V at A B
 unfold zoomL
 cases w:detX P<;> simp only [w,Bool.xor_false, Bool.xor_true] at f A B
 · change jetsL o Y= _
   have hp(Z:Pal)(Q:Bool):culm (hush Q (twist H Z))=hush Q (twist H (culm Z)):=by cases Q<;> simp only [hush_false,hush_true,culm,map_mul,twinned P U p, w,Bool.xor_false, Matrix.neg_mul, Matrix.mul_neg]
   refine Prod.ext f (Prod.ext ?_ ?_)
   · refine funext fun i=> (congrArg culm (A i)).trans (hp _ _)
   exact funext fun i=> (congrArg culm (B i)).trans (hp _ _)
 change jetsL o (-star (Y))=_
 have hZ (X Z: Matrix (Single n) Kt ℂ): Xᴴ*(-star (Y))*Z = -star (Zᴴ*Y*X):=by rw [Matrix.mul_neg, Matrix.neg_mul]; congr 1; change _= (Zᴴ*Y*X)ᴴ; rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]; exact Matrix.mul_assoc ..
 have hj(W':Pal)(b:Bool): culm (-star (hush b (twist H W'))) = -star (hush b (twist H (culm W'))):=by
    let X₀(b):=baseF b; have hh(b):star (X₀ b)=X₀ b:=φ_a _; cases b<;> simp only [culm,hush_false,hush_true,map_mul,twinned P U p,w,star_neg,star_mul,neg_neg]<;> rw [show ∀ b:Bool,star (baseF b)= baseF b from hh, show ∀ b:Bool,star (baseF b)= baseF b from hh] -- tune
    all_goals simp only [Matrix.neg_mul,Matrix.mul_neg,Matrix.mul_assoc]<;>rfl
 refine Prod.ext ((hZ _ _).trans (congrArg (fun i:Pal=> -star i) f)) (Prod.ext (funext fun i=>(congrArg culm ((hZ _ _).trans (congrArg (fun z:Pal=> -star z) (B i)))).trans (hj _ _)) (funext fun i=>(congrArg culm ((hZ _ _).trans (congrArg (fun z:Pal=> -star z) (A i)))).trans (hj _ _)))
end YM.CF.Ione.Clock
