import YM.CF.Pec.Tel
set_option autoImplicit false
noncomputable section
namespace YM.CF.Pec
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Laic
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {n N: Side}{a b:ℝ}
open Mir
def X (f:Equiv.Perm Axis):=Signed.mk f (fun _=>false)
lemma detSwap(i j:Axis)(h:i≠j):detX (X (Equiv.swap i j))=true:=by
 have hA:∃ U:UNI SpinIdx,JetS (X (Equiv.swap i j)) false true U:=by
    let x:=gammaOp i - gammaOp j; let y:= x*grading; let c:= (Real.sqrt 2)⁻¹; have he:Commute y (1:Op SpinIdx):=Commute.one_right _
    have hs:c*c=(1/2:ℝ):=by rw [show c*c=(Real.sqrt 2*Real.sqrt 2)⁻¹ by rw [_root_.mul_inv_rev]]; rw [Real.mul_self_sqrt (by norm_num)]; simp
    have hx:x*x=1+(1:Op SpinIdx):=by unfold x; rw [sub_mul,mul_sub,mul_sub,gammaOne,gammaOne,gammaSwap i j h]; abel
    have hv:star x=x:= by unfold x; rw [star_sub,(gammaAdj i).star_eq,(gammaAdj j).star_eq]
    have hp: y*star y=1+(1:Op SpinIdx):=by unfold y; rw [star_mul,hv,gradingAdj.star_eq,←mul_assoc _ _ x,mul_assoc x, gradingOne,mul_one,hx]
    let U:UNI SpinIdx:=⟨c • y, Matrix.mem_unitaryGroup_iff.mpr (by change _ * star _= _; rw [star_smul,star_trivial, Matrix.smul_mul,Matrix.mul_smul, smul_smul,hp,smul_add,←add_smul,hs]; norm_num)⟩
    have hk(d):y*gammaOp d= -(x*gammaOp d*grading):=by unfold y; rw [mul_assoc,gradingSwap,mul_neg,←mul_assoc]
    refine ⟨U,fun a=>twist_comm _ _ _ ?_,twist_comm _ _ _ ?_,?_⟩
    · change (c • y)*_=gammaOp a * _; rw [show U.val=c • y from rfl, Matrix.smul_mul, Matrix.mul_smul]; congr 1; change y*gammaOp ((Equiv.swap i j) a)= _; rw [hk]; by_cases t:a=i
      · subst a; rw [Equiv.swap_apply_left]; unfold y; rw [← mul_assoc]; unfold x; rw [sub_mul,gammaOne,mul_sub,gammaOne, show gammaOp i * gammaOp j-1= -(1-gammaOp i*gammaOp j) by abel,neg_mul,neg_neg]
      by_cases p:a=j
      · subst a; rw [Equiv.swap_apply_right]; unfold y; rw [←mul_assoc]; unfold x; rw [sub_mul,gammaOne,mul_sub,gammaOne, show 1-gammaOp j*gammaOp i= -(gammaOp j*gammaOp i-1) by abel,neg_mul,neg_neg]
      rw [Equiv.swap_apply_of_ne_of_ne t p]; unfold y; rw [←mul_assoc, show x*gammaOp a= -(gammaOp a*x) by unfold x; rw [sub_mul,mul_sub,gammaSwap i a (Ne.symm t),gammaSwap j a (Ne.symm p)]; abel,neg_mul,neg_neg]
    · change (c • y)*grading= -grading*(c • y); rw [Matrix.smul_mul, Matrix.mul_smul]; congr 1; unfold y; rw [← mul_assoc (-grading), neg_mul]; congr 1; unfold x; rw [sub_mul,mul_sub,gradingSwap,gradingSwap]; abel
    change (c • y)*_=spinJ*cc (c • y); rw [Matrix.smul_mul,cc_rsmul,Matrix.mul_smul]; congr 1; unfold y; rw [mul_assoc x,spinJ_grading,cc_mul,←mul_assoc spinJ,←mul_assoc x]; congr 1; unfold x; rw [sub_mul,cc_sub,mul_sub,spinJ_inter,spinJ_inter]
 exact mono_d _ _ _ hA.choose hA.choose_spec
-- invariant coefficient calculus on TWO copies of skew field
variable {Z:Type}[NormedAddCommGroup Z][InnerProductSpace ℝ Z]
abbrev Hue(Z:Type):=Axis→Axis→Z
def dye(p:Signed)(i:Axis):ℝ:=if p.flip i then -1 else 1
def skew(p:Signed)(f: Hue Z):Hue Z:=fun i j=> (dye p i*dye p j) • f (p.perm i) (p.perm j)
lemma dyeM(p q: Signed)(i:Axis): dye (p*q) i= dye p (q.perm i)*dye q i:=by unfold dye; rw [Signed.mul_flip]; cases h:p.flip (q.perm i)<;>cases k:q.flip i<;> simp
lemma skew_t(p q:Signed)(F:Hue Z): skew q (skew p F)=skew (p*q) F:=by funext i j; unfold skew; rw [dyeM,dyeM,smul_smul]; simp only [Signed.mul_perm_apply]; congr 1; ring
abbrev Case:= PlaqAxes→PlaqAxes→ℂ
def beam(P:Case)(X Y: Hue Z):ℂ:=∑ i:PlaqAxes,∑ j:PlaqAxes, inner ℝ (X i.val.1 i.val.2) (Y j.val.1 j.val.2) • P i j
def hum(P:Case)(X Y:Hue Z):ℂ:= (Fintype.card Signed:ℝ)⁻¹ •∑ p: Signed, pays p (beam P (skew p X) (skew p Y))
lemma humid(s:Signed)(P:Case)(X Y:Hue Z): hum P (skew s X) (skew s Y)=pays s (hum P X Y):=by
 unfold hum; rw [map_smul,map_sum]; simp_rw [skew_t]; congr 1; conv_rhs => rw [←Equiv.sum_comp (Equiv.mulLeft s)] 
 apply sum_congr rfl; intro i _; change pays i _= pays s (pays (s*i) _); simp only [complX,sign_seq,det_p]; cases h:detX s<;> cases v:detX i<;> simp
lemma pays_v(s:Signed)(z:ℂ):(pays s z).re=z.re∧ (pays s z).im=(if detX s then -z.im else z.im):=by rw [complX]; cases h:detX s<;> simp [cSignX]
def ask (i j l m:Axis):ℝ:= (if i=l∧ j=m then 1 else 0)-(if j=l ∧ i=m then 1 else 0)
lemma ask_basis (F: Hue Z)(p:∀ i j,F i j= -F j i)(x y): F x y=∑ i:PlaqAxes, ask i.val.1 i.val.2 x y • F i.val.1 i.val.2:=by
 rcases lt_trichotomy x y with h|h|h
 · let v:PlaqAxes:=⟨(x,y),h⟩; rw [sum_eq_single v]; swap; intro b _ hx; have hp: ask b.val.1 b.val.2 x y=0:=by
       unfold ask; have ht:=b.property; rw [if_neg (fun t=> hx (Subtype.ext (Prod.ext t.1 t.2))),if_neg (fun v=>by rcases v with ⟨v,w⟩; exact lt_asymm (v ▸ w ▸ ht) h),sub_self]
   rw [hp,zero_smul]; -- indent
   swap; simp
   unfold v; simp [ask,(ne_of_lt h),Ne.symm]
 · subst y; have ht:F x x=0:=by
      have hh:F x x+F x x=0:=eq_neg_iff_add_eq_zero.mp (p x x); rw [←two_smul ℝ] at hh; exact (smul_eq_zero_iff_right (by norm_num:(2:ℝ)≠0)).mp hh
   rw [ht]; simp [ask,and_comm]
 let v:PlaqAxes:=⟨(y,x),h⟩; rw [sum_eq_single v]; swap; intro b _ hx; have hp: ask b.val.1 b.val.2 x y=0:=by
    unfold ask; have ht:=b.property; rw [if_neg (fun v=>by rcases v with ⟨v,w⟩; exact lt_asymm (v ▸ w ▸ ht) h),if_neg (fun v=>hx (Subtype.ext (Prod.ext v.2 v.1))),sub_self]
 rw [hp,zero_smul]
 swap; simp
 unfold v; simp [ask,(Ne.symm (ne_of_lt h)),ne_of_lt h,p x y]
def crest(i j:Axis)(z:Z):Hue Z :=fun k l=> ask i j k l • z
def gems (s:Signed)(i j k l:Axis):ℝ:= dye s k * dye s l * ask i j (s.perm k) (s.perm l)
def crystalC(P:Case)(i j k l:Axis):ℂ:=hum P (crest i j (1:ℝ)) (crest k l 1)
lemma lineB(P:Case)(i j k l:Axis)(u v:Z): hum P (crest i j u) (crest k l v)=inner ℝ u v • crystalC P i j k l:=by
 unfold crystalC hum; rw [smul_comm (inner ℝ u v) ,Finset.smul_sum (r:=(inner ℝ u v))]; congr 1; refine Finset.sum_congr rfl fun s _=>?_ ; rw [←map_smul]; unfold beam; simp_rw [Finset.smul_sum]; apply congr_arg (pays s); refine Finset.sum_congr rfl fun x _=> ?_; refine Finset.sum_congr rfl fun y _=>?_ ; simp only [skew,crest,real_inner_smul_left,real_inner_smul_right, smul_smul,real_inner_self_eq_norm_sq, norm_one,one_pow,mul_one]; congr 1; ring
lemma stretch(P:Case)(f g:Hue Z)(p:∀ i j,f i j= -f j i)(q:∀ i j,g i j= -g j i):hum P f g= ∑ i:PlaqAxes, ∑ j:PlaqAxes, inner ℝ (f i.val.1 i.val.2) (g j.val.1 j.val.2) • crystalC P i.val.1 i.val.2 j.val.1 j.val.2:=by
 have ht (f: Hue Z)(e:∀ i j,f i j= -f j i): f=∑ v:PlaqAxes,crest v.val.1 v.val.2 (f v.val.1 v.val.2):=by funext i j; simp_rw [Finset.sum_apply]; exact ask_basis f e i j
 let l:=PlaqAxes
 have ha(f g h:Hue Z):hum P (f+g) h=hum P f h+hum P g h ∧ hum P f (g+h)=hum P f g+hum P f h:=by unfold hum; constructor <;> simp only [beam,skew,Pi.add_apply,smul_add, inner_add_left,inner_add_right,add_smul,sum_add_distrib,map_add,smul_add]
 have he(s: Finset PlaqAxes)(f:PlaqAxes→Hue Z)(g:Hue Z): hum P (∑ i∈s,f i) g=∑ i∈s,hum P (f i) g ∧hum P g (∑ i∈s,f i)=∑ i∈s, hum P g (f i):=by induction s using Finset.induction_on with
 | empty => simp [hum,beam,skew]
 | @insert i s h ih=> simp only [sum_insert h,(ha ..).1,(ha ..).2,ih]; trivial -- `simp only [ih]`
 conv_lhs => rw [ht f p]
 rw [(he ..).1]; apply Finset.sum_congr rfl; intro i _; conv_lhs => rw [ht g q]
 rw [(he ..).2]; exact Finset.sum_congr rfl fun j _=> lineB .. -- type
end YM.CF.Pec
