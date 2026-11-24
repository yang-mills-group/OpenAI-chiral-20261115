import YM.CF.Spire.Lane
set_option autoImplicit false
noncomputable section
namespace YM.CF.Spire
open Function Filter Matrix NormedSpace Finset Fock Lat Lattice Rush Cube Scroll Mir
open scoped Matrix.Norms.L2Operator Matrix Topology MatrixOrder BigOperators InnerProductSpace
attribute [local instance] opCStarAlgebra
-- spin implementations
lemma jet_add (b r t:Bool)(a c:Signed)(U V:UNI SpinIdx)(h: JetS a b r U)(p:JetS c false t V): JetS (a*c) b (r.xor t) (V*U):=by
 refine ⟨fun i=>?_,?_,?_⟩
 · rw [Signed.mul_perm_apply,singT,twin,←singT,h.cliff,Signed.mul_flip]; cases q:a.flip (c.perm i); rw [Bool.false_xor]; exact p.cliff i
   rw [hush_true,map_neg,show twist V (gammaOp (c.perm i)) = hush (c.flip i) _ from p.cliff i]; exact hush_comp true (c.flip i) _
 · rw [singT,twin,←singT,h.grade]; cases r; rw [Bool.false_xor]; exact p.grade; rw [hush_true,map_neg,show twist V grading=hush t grading from p.grade]; exact hush_comp true t _
 change V.val*U.val*_=spinJ*cc (V.val*U.val); rw [mul_assoc,h.justice,←mul_assoc,p.justice,mul_assoc,cc_mul]
lemma combo_one (b:Signed):∃ U:UNI SpinIdx,∃ r:Bool,JetS b false r U:=by
 let Z: Signed→ Prop:=fun b=>∃ U:UNI SpinIdx,∃ r,JetS b false r U
 have he: Z 1:=⟨1,false, calmSX⟩
 have ht(a v): Z a → Z v→ Z (a*v):=by rintro ⟨U,r,h⟩ ⟨V,s,p⟩; exact ⟨_,_,jet_add false r s a v U V h p⟩
 let X := fun (f: Equiv.Perm Axis) => Signed.mk f (fun _=>false)
 have hP(i j:Axis)(h:i≠j): Z (X (Equiv.swap i j)):=by
    let x:=gammaOp i - gammaOp j; let y:= x*grading; let c:= (Real.sqrt 2)⁻¹; have he:Commute y (1:Op SpinIdx):=Commute.one_right _
    have hs:c*c=(1/2:ℝ):=by rw [show c*c=(Real.sqrt 2*Real.sqrt 2)⁻¹ by rw [_root_.mul_inv_rev]]; rw [Real.mul_self_sqrt (by norm_num)]; simp
    have hx:x*x=1+(1:Op SpinIdx):=by unfold x; rw [sub_mul,mul_sub,mul_sub,gammaOne,gammaOne,gammaSwap i j h]; abel
    have hv:star x=x:= by unfold x; rw [star_sub,(gammaAdj i).star_eq,(gammaAdj j).star_eq]
    have hp: y*star y=1+(1:Op SpinIdx):=by unfold y; rw [star_mul,hv,gradingAdj.star_eq,←mul_assoc _ _ x,mul_assoc x, gradingOne,mul_one,hx]
    let U:UNI SpinIdx:=⟨c • y, Matrix.mem_unitaryGroup_iff.mpr (by change _ * star _= _; rw [star_smul,star_trivial, Matrix.smul_mul,Matrix.mul_smul, smul_smul,hp,smul_add,←add_smul,hs]; norm_num)⟩
    have hk(d):y*gammaOp d= -(x*gammaOp d*grading):=by unfold y; rw [mul_assoc,gradingSwap,mul_neg,←mul_assoc]
    refine ⟨U,true,fun a=>twist_comm _ _ _ ?_,twist_comm _ _ _ ?_,?_⟩
    · change (c • y)*_=gammaOp a * _; rw [show U.val=c • y from rfl, Matrix.smul_mul, Matrix.mul_smul]; congr 1; change y*gammaOp ((Equiv.swap i j) a)= _; rw [hk]; by_cases t:a=i
      · subst a; rw [Equiv.swap_apply_left]; unfold y; rw [← mul_assoc]; unfold x; rw [sub_mul,gammaOne,mul_sub,gammaOne, show gammaOp i * gammaOp j-1= -(1-gammaOp i*gammaOp j) by abel,neg_mul,neg_neg]
      by_cases p:a=j
      · subst a; rw [Equiv.swap_apply_right]; unfold y; rw [←mul_assoc]; unfold x; rw [sub_mul,gammaOne,mul_sub,gammaOne, show 1-gammaOp j*gammaOp i= -(gammaOp j*gammaOp i-1) by abel,neg_mul,neg_neg]
      rw [Equiv.swap_apply_of_ne_of_ne t p]; unfold y; rw [←mul_assoc, show x*gammaOp a= -(gammaOp a*x) by unfold x; rw [sub_mul,mul_sub,gammaSwap i a (Ne.symm t),gammaSwap j a (Ne.symm p)]; abel,neg_mul,neg_neg]
    · change (c • y)*grading= -grading*(c • y); rw [Matrix.smul_mul, Matrix.mul_smul]; congr 1; unfold y; rw [← mul_assoc (-grading), neg_mul]; congr 1; unfold x; rw [sub_mul,mul_sub,gradingSwap,gradingSwap]; abel
    change (c • y)*_=spinJ*cc (c • y); rw [Matrix.smul_mul,cc_rsmul,Matrix.mul_smul]; congr 1; unfold y; rw [mul_assoc x,spinJ_grading,cc_mul,←mul_assoc spinJ,←mul_assoc x]; congr 1; unfold x; rw [sub_mul,cc_sub,mul_sub,spinJ_inter,spinJ_inter]
 have hX(f: Equiv.Perm Axis): Z (X f):=by
   refine Equiv.Perm.swap_induction_on f he ?_ -- tune motive
   intro S i j g k; have hp:X (Equiv.swap i j * S)=X (Equiv.swap i j) * X S := rfl; rw [hp]; exact ht _ _ (hP i j g) k
 let T(s:Finset Axis):Signed:=⟨Equiv.refl _,fun i=>decide (i∈s)⟩
 have hT(s:Finset Axis): Z (T s):=by
   induction s using Finset.induction_on with
   | empty=> rw [show T ∅=1 by unfold T; congr!<;> ext<;>simp]; exact he -- tune
   | @insert i s e ih=>
       rw [show T (insert i s)=Signed.mirror i*T s by refine Signed.ext rfl ?_; funext b; by_cases h:b=i <;> simp [T,Signed.mirror,h,e,Ne.symm]]
       exact ht _ _ ⟨_,_,mirrorX i⟩ ih
 let A:=univ.filter fun x:Axis=> b.flip x
 have hk:X b.perm*T A=b:=by
   apply Signed.ext; ext; simp [X,T]
   funext i; cases h:b.flip i<;>simp [X,T,A,h]
 rw [←hk]; exact ht _ _ (hX _) (hT _)
lemma mono_s (s:Signed)(b p q:Bool)(U V:UNI SpinIdx)(h: JetS s b p U)(k: JetS s b q V):p=q:=by
 have hr(i):sings b U (gammaOp i)=sings b V (gammaOp i):=by obtain ⟨i,rfl⟩:=s.perm.surjective i; rw [h.cliff,k.cliff]
 have he:b=b:=rfl; have ht:hush p grading=hush q grading:=by rw [← h.grade,← k.grade,grading_rule]; simp only [singT,win_m,map_mul]; simp_rw [show ∀ i,twist U (windX b (gammaOp i))=twist V (windX b (gammaOp i)) from hr]
 have hx:= Matrix.ext_iff.mpr ht 0 0; cases p<;>cases q; rfl; change (1:ℂ)= -1 at hx; norm_num at hx; change -(1:ℂ)=1 at hx; norm_num at hx; rfl
def detX (s: Signed):Bool:= (combo_one s).choose_spec.choose
lemma det_sub (b:Bool)(s:Signed):∃ U:UNI SpinIdx,JetS s b (detX s) U:=by cases b; exact ⟨_,(combo_one s).choose_spec.choose_spec⟩; refine ⟨(combo_one s).choose * ⟨spinJ,spinJ_unitary⟩,?_⟩; simpa only [one_mul,Bool.false_xor] using jet_add true false (detX s) 1 s _ _ cloneSX (combo_one s).choose_spec.choose_spec -- tune
lemma mono_d(s:Signed)(b p:Bool)(U: UNI SpinIdx)(h: JetS s b p U): detX s=p:= mono_s s b _ p _ U (det_sub b s).choose_spec h
lemma det_i: detX 1=false:= mono_d _ false _ _ calmSX
lemma det_t(i:Axis):detX (Signed.mirror i)=true:=mono_d _ false _ _ (mirrorX i)
lemma det_p (s t:Signed):detX (s*t)=(detX s).xor (detX t):=mono_d _ false _ _ (jet_add false _ _ _ _ _ _ (det_sub false s).choose_spec (det_sub false t).choose_spec)
end YM.CF.Spire
