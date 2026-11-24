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
variable {n:Side}(P:Signed)(U:UNI SpinIdx)(t:JetS P false (detX P) U)
local notation "W"=> spinQ U (xtra false)
include t
lemma twinned(b:Bool):twist W (baseF b)=baseF (b.xor (detX P)):=by
 rw [← binA,←binA]; have h:=Scroll.wingK U (xtra false) (binV b) 1; change _=twist U (binV b)⊗ₖ twist 1 (1:Op Slot) at h
 apply h.trans; rw [binV,map_sub,map_one,show twist U (angle b)= _ from angleX t b,one_des,Bool.xor_comm (detX P) b]; rfl
lemma halo_d(i:Axis): twist W (Tap.boom (P.perm i))=hush (detX P) (hush (P.flip i) (Tap.boom i)):=by
 let Z:= gammaOp (P.perm i)
 have hv(i:Axis): zen (step i)=Complex.I • gammaOp i:= by unfold Fir.zen; rw [sum_eq_single i]; simp; intro _ _ h; simp [h]; simp
 unfold Tap.boom; rw [show twist _ (_⊗ₖ _)= twist U (taxi (P.perm i)) ⊗ₖ (1:Op Slot) from ?_]; swap
 · have he:= Scroll.wingK U (xtra false) (taxi (P.perm i)) (1:Op Slot); change _=twist U _ ⊗ₖ twist 1 _ at he; rw [one_des] at he; exact he
 rw [Tap.taxi,twist_scalar,map_mul,hv,twist_scalar,show twist U grading= _ from t.grade,show twist U (gammaOp (P.perm i))= _ from t.cliff i]; cases detX P <;> cases P.flip i <;> simp [Tap.taxi,hv,op_kron_neg]
lemma leg_twist(i:Axis)(b:Bool): twist W (ditF b (P.perm i))=hush (P.flip i) (ditF (b.xor (detX P)) i):=by
 unfold ditF; split <;> first| rw [twist_scalar,map_neg]|rw [twist_scalar]
 all_goals rename_i h; rw [halo_d P U t]; cases b<;> cases detX P <;> cases P.flip i <;> simp_all
lemma moon_s(z:Cover)(i:Axis)(b:Bool): twist W (moonB b (P.perm i) (P.act z))=hush (P.flip i) (moonB (b.xor (detX P)) i z):=by
 unfold moonB; rw [map_add,twist_scalar,P.act_at,twinned P U t,leg_twist P U t]; cases h:P.flip i<;>simp [h,add_comm]
omit t

-- Masks of rows which will pay. Lean hides apron when applied to broader marks: mask only on Wire price.
variable (X: Support (More n))
abbrev pitchMask (X: Support (More n)) : Finset (Single n):= univ.filter fun i=> node i.1.1∈X
lemma pitchIn (x:Single n): x∈ pitchMask X↔ node x.1.1∈X:=by simp [pitchMask]
lemma nearer (q:Sweep n)(o u:Site n)(h:Nonwrapping X (node (mPath q o)))(v:node u∈ actY q X):10*separation u o < n.val:=by
 have he:(boxA q) (node u)∈X:=Finset.mem_map_equiv.mp v; have ht:= h _ he; rw [nodeA] at ht -- stray
 rw [sitT,Hove.ζdist] at ht; change 10*(2*_)<(n.val*2) at ht; omega
lemma liftingV(q: Sweep n)(o u:Site n)(h:Nonwrapping X (node (mPath q o)))(v:node u∈ actY q X): Lattice.lift (mPath q u-mPath q o)= q.s.act (Lattice.lift (u-o)):=by
 have hx:=nearer X q o u h v; let s:= castX q
 apply lift_eq_iff.mpr
 refine ⟨?_,fun i=> ?_⟩
 · rw [←wrap_signed,wrap_lift]; change s.mills n u-s.mills n o=s.s.act _; unfold Shape.mills affine; rw [s.s.act_sub]; abel
 obtain ⟨j,rfl⟩:=q.s.perm.surjective i
 have h:= component_le (u-o) j; unfold separation at hx; rw [Signed.act_at]; split<;>omega
lemma motion_w(q:Sweep n)(o x: Site n)(h:Nonwrapping X (node (mPath q o)))(v:node x∈ actY q X): let a:=castX q; let S:=mPath q; a.payA x*Rush.wind (S o) (Lattice.lift (S x-S o))=a.payA o*Rush.wind o (Lattice.lift (x-o)):=by
 intro a S; rw [liftingV X q o x h v]; let z:=Lattice.lift (x-o); let w:=Rush.wind o z; let p:=a.payA o; let u:=a.payA x; change u* Rush.wind (a.mills n o) (a.s.act z)=p*w
 apply mul_left_cancel₀ (a:=p) (fun e=> one_ne_zero (by have H:p*p=1:=a.reflex o; rw [e,zero_mul] at H; exact H.symm)); rw [mul_left_comm,footFee,show o+wrap n z=x from (by rw [wrap_lift]; abel)] -- explicit order
 rw [mul_left_comm u,←mul_assoc p,show p*p=1 from a.reflex o,show u*a.payA x= 1 from a.reflex x]; simp; rfl

abbrev bodyLift(o:Site n)(F:Cover→ Op Kt): Matrix (Single n) Kt ℂ:=Matrix.of fun i j=>Rush.wind o (Lattice.lift (i.1.1-o))* F (Lattice.lift (i.1.1-o)) (Hove.portB i) j
lemma rail (q:Sweep n)(o:Site n)(h:Nonwrapping X (node (mPath q o)))(Y:Op (Single n) -- unused
 )(A B:Cover→Op Kt)(t:∀ u:Cover,twist (spinQ U (xtra false)) (A (q.s.act u))= B u):
 cutM (pitchMask (actY q X))*(siteU (castX q) false U n).val * bodyLift (mPath q o) A=(castX q).payA o • (cutM (pitchMask (actY q X))*bodyLift o B* (spinQ U (xtra false)).val):=by
 let a:=castX q; let S:=mPath q; ext ⟨⟨x,i⟩,u⟩ j; let E(v: Site n):= (milU a U (xtra false) v).val; let C:= pitchMask (actY q X); let H:= spinQ U (xtra false); let O:=Lattice.lift (x-o); let y:Single n:=((x,i),u); change (cutM C*(siteU (castX q) false U n).val*bodyLift (S o) A) y j=((a.payA o) • (cutM C* bodyLift o B * H.val)) y j; rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.smul_apply]; simp only [cutM,Matrix.diagonal_mul]; by_cases p:y∈ C; swap
 · simp only [if_neg p, zero_mul,smul_zero]
 let K:=siteU a false U n; have hx:= (pitchIn _ y).1 p
 simp only [if_pos p,one_mul]; change (K.val * bodyLift (S o) A) y j= a.payA o * _; rw [Matrix.mul_apply,Fintype.sum_prod_type] -- nested prod
 -- unfold Tofu only once. collapse outer x'
 rw [Fintype.sum_prod_type]; rw [sum_eq_single (S x)] -- tune matrix RHS sum order
 · have he(i' u'): K.val y ((S x,i'),u')= a.payA x * H.val (i,u) (i',u'):=by change jump S E (x,i,u) (S x,i',u')= _; rw [jump_apply,if_pos rfl]; rfl
   simp_rw [he]; let L:= A (q.s.act O); let N:= B O; have hf : H.val*L=N*H.val:=(twist_product H _).symm.trans (congrArg (fun i=> i*H.val) (t _)); let w:= (a.payA o * Rush.wind o O);
   calc
    _ = w * (H.val*L) (i,u) j:=by
       rw [Matrix.mul_apply,Fintype.sum_prod_type,mul_sum]; apply sum_congr rfl; intro i' _; rw [mul_sum]; apply sum_congr rfl; intro u' _; change _*(Rush.wind (S o) (Lattice.lift (S x-S o)) * A _ _ _) = _; rw [show Lattice.lift (S x-S o)= _ from liftingV X q o x h hx]; -- specify lift
       have ht:=motion_w X q o x h hx; dsimp only at ht; rw [liftingV X q o x h hx] at ht; rw [show w= _ from ht.symm]; unfold L; ring -- may need portB
    _ = _ :=by
       rw [hf,Matrix.mul_apply,Matrix.mul_apply]; unfold w; simp only [Matrix.of_apply,bodyLift]; simp_rw [mul_sum]; apply sum_congr rfl; intro z _; unfold N; ring
 · intro b _ pv; refine sum_eq_zero (fun i' _=>sum_eq_zero (fun u' _=>?_)); change jump S E (x,i,u) (b,i',u') * _= _; rw [jump_apply,if_neg pv.symm,zero_mul]
 simp
end YM.CF.Ione.Clock
