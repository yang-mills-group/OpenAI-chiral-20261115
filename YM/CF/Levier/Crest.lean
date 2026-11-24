import YM.CF.Levier.Isle
set_option maxHeartbeats 350000
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Levier
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Spire Nacre
-- analytic profiles under affine pullback incl sail seams
variable {N:Side}(b:Bool)(a:Shape)
open Urn
variable {n:Type*}[LinearOrder n][Fintype n](t:Bool)
def spinU (s:Signed):UNI SpinIdx := (det_sub b s).choose
lemma spinZ(s:Signed): JetS s b (detX s) (spinU b s):=(det_sub b s).choose_spec
abbrev whiten(U:UNI n):UNI n:=if b then ccU U else U
lemma glint (U:UNI n): (whiten b U).val= windX b U.val:=by cases b <;> rfl -- accidental abbrev lemma
lemma wake_r(X:Op n)(U V: UNI n): sings t V (sings b U X)= sings (b.xor t) (V*whiten t U) X:=by
 have ht: windX t (windX b X)=windX (b.xor t) X:=by cases t <;> cases b; rfl; rfl; rfl; exact cc_cc _
 rw [singT t,singT b,singT]; simp only [twist_formula,win_m,win_s, Submonoid.coe_mul, glint, ht,star_mul]; simp only [mul_assoc]
lemma shineU(t:Bool)(U:UNI SpinIdx)(V:UNI SpinIdx)(c:Signed)(h:JetS a.s b (detX a.s) U)(p:JetS c t (detX c) V):JetS (a.s*c) (b.xor t) (detX (a.s*c)) (V*whiten t U):=by
 refine ⟨fun i=>?_,?_,?_⟩
 · rw [←wake_r,Signed.mul_perm_apply,h.cliff,Signed.mul_flip]; cases u:a.s.flip (c.perm i) <;>simp only [hush_true,hush_false,singT,win_n,map_neg,Bool.false_xor]; -- tune
   exact p.cliff i; rw [←singT,p.cliff]; exact hush_comp true (c.flip i) (gammaOp i)
 · rw [← wake_r, h.grade, det_p]; cases q:detX a.s; rw [Bool.false_xor]; exact p.grade; rw [hush_true,singT,win_n,map_neg,←singT,p.grade]; exact hush_comp true (detX c) grading
 change V.val*(whiten t U).val*_= spinJ*cc (V.val*(whiten t U).val); rw [mul_assoc,show (whiten t U).val*spinJ=spinJ*cc (whiten t U).val from ?_, ←mul_assoc,p.justice,mul_assoc,cc_mul]; cases t; exact h.justice; rw [glint]; change cc U.val*_= _; nth_rw 1 [←spinJ_real]; rw [←cc_mul,h.justice,cc_mul,spinJ_real]; rfl
lemma kitsX (s:Signed)(U V:UNI SpinIdx)(h: JetS s b (detX s) U)(p: JetS s b (detX s) V):∃ z:ℂ,U.val=z • V.val∧ z*star z=1:=by
 cases b; exact kits s U V h p
 let W:UNI SpinIdx:=⟨spinJ,spinJ_unitary⟩; let S:= Shape.mk 1 0
 have he (A:UNI SpinIdx)(h:JetS s true (detX s) A): JetS s false (detX s) (A*whiten true W):=by
    have hx:= shineU true S true W A s (show JetS S.s true (detX S.s) W from det_i.symm ▸ cloneSX) h; simp only [S, one_mul] at hx; exact hx
 let B:= (whiten true W); obtain ⟨z,hp,q⟩:=kits s (U*B) (V*B) (he U h) (he V p)
 refine ⟨z,?_,q⟩; change U.val*B.val=z • (V.val*B.val) at hp; rw [show U.val= U.val*B.val*star B.val by rw [mul_assoc, B.property.2,mul_one],hp, Matrix.smul_mul,mul_assoc,B.property.2,mul_one]
end YM.CF.Levier
