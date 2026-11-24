import YM.CF.BProof.Wick.Soar
import YM.CF.BProof.Align.Gust
/-! Log segments one common torus & argument. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Wick
open Function Filter NormedSpace Fock Finset Branch Align Double MeasureTheory
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {I:Type}[Fintype I][LinearOrder I][Nonempty I] {P Q A C T:Op I}{x:Wave I} {c e:ℝ}
variable (u:ℝ)
lemma gust_slope (g:Gust A T): HasDerivAt (slit A T) (T*slit A T u) u:=by
 have he:T*slit A T u=T:=by rw [g.rise,mul_add,g.2.1,Algebra.mul_smul_comm,g.square,smul_zero,add_zero]
 rw [he,funext (g.rise)]; let f:= fun t:ℝ=> t • T; simpa using (((hasDerivAt_id' u).smul_const T).const_add A) -- tune
def powder (A P Q:Op I)(u:ℝ) : Op I := (space P Q+(2*u) • Q)* wedgeP A P + Q*wedgeQ A P
def shutter (A P Q:Op I)(u:ℝ):= powder A P Q u* send A (house A P Q u)
lemma walk_der (p:‖u‖≤1)(b:Board A P Q c) : HasDerivAt (house A P Q) (shutter A P Q u * house A P Q u) u:=by
 let F:= powder A P Q u; have he:F*A=F:= by unfold F powder; rw [add_mul,mul_assoc _ (wedgeP A P) A,mul_assoc _ (wedgeQ A P) A,b.sailP,b.sailQ]
 rw [shutter,mul_assoc,(b.houseFit u p).lays,he]; unfold F powder house; let L:=space P Q; let V:=wedgeP A P; let W:= wedgeQ A P
 have h(x: Op I) : HasDerivAt (fun v:ℝ=>v • x) x u:= by simpa using (hasDerivAt_id' u).smul_const x
 have hf: HasDerivAt (fun t:ℝ=>t^2 • Q) ((2*u) • Q) u:=by simpa using ((hasDerivAt_pow 2 u).smul_const Q)
 -- inferred
 exact ((((h L).const_add P).add hf).mul_const V).add (((h Q).const_add L).mul_const W)
abbrev linestretch(A T C:Op I):ℂ:= poses (fun _=>C) (fun u=>land A (slit A T u)) (fun _=>T) 0 1
abbrev expire (A T:Op I)(x:Wave I):= acts (quant (slit A T 1)) x
lemma sustain (t:Task A x)(g:Gust A T): acts (exp (dg T)) x=expire A T x:=by rw [tallied T g.square]; unfold expire slit Align.bend; rw [quant_mul,one_smul, act_mul,t.enters]
def spentDown(A C P Q:Op I):ℂ:=poses (fun _=>C) (floorH A P Q) (shutter A P Q) 0 1
lemma liveline (g:Gust A T)(s:Task A x)(h:∀ u∈Set.Icc (0:ℝ) 1,Shelf (land A (slit A T u)) C e)(L:ContinuousOn (fun i=>(salary (land A (slit A T i)) T C).trace) (Set.Icc (0:ℝ) 1)): overlap C (expire A T x)=Complex.exp (linestretch A T C)* overlap C x:=by
 let f(t:ℝ):=acts (quant (slit A T t)) x; have hf:f 0=x:=by unfold f slit Align.bend; rw [zero_smul,add_zero,one_mul,s.enters]
 exact (coast (v:=f) zero_le_one _ (fun _=>T) e C h (fun u _=>s.quantS (g.fit u)) (fun i _=> drift_der (gust_slope i g) x) L).trans (congrArg _ (congrArg (overlap C) hf)) -- congr λ
lemma chordEnd (b:Board A P Q c)(s:Task A x)(h:∀ u∈Set.Icc (0:ℝ) 1,Shelf (floorH A P Q u) C e)(L:ContinuousOn (fun i=>(salary (floorH A P Q i) (shutter A P Q i) C).trace) (Set.Icc (0:ℝ) 1)): overlap C (acts (quant (house A P Q 0)) x)=Complex.exp (-(spentDown A C P Q))*overlap C x := by
 let f(t:ℝ):=acts (quant (house A P Q t)) x; have hf:f 1=x:=by unfold f; rw [b.hitOne]; exact s.enters
 have hu(u:ℝ)(h:u∈Set.Icc (0:ℝ) 1): ‖u‖≤1:=by rw [Real.norm_of_nonneg h.1]; exact h.2
 have hz:= coast (v:=f) zero_le_one _ _ _ C h (fun i e=>s.quantS (b.houseFit i (hu i e))) (fun i e=>drift_der (walk_der i (hu i e) b) x) L; rw [hf] at hz; rw [hz,←mul_assoc,← Complex.exp_add]; change _= Complex.exp (-spentDown A C P Q+spentDown A C P Q)*_; rw [neg_add_cancel,Complex.exp_zero,one_mul]
end YM.CF.BProof.Wick
