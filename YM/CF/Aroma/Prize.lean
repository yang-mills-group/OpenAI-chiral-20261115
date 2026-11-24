import YM.CF.Aroma.Kits
set_option autoImplicit false
noncomputable section
namespace YM.CF.Aroma
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Ember Rush Cube MeasureTheory
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
variable {n:Type*}[Fintype n][DecidableEq n]{N:Side}
def amber(q:Momentum): Air N :=fun x=> (dialH q x).re
def zinnia(q:Momentum): Air N :=fun x=> (dialH q x).im
def firstH(J:InJ n N)(q:Momentum): Cab n N:= JD J (amber q)+ Complex.I • JD J (zinnia q)
def secondH(J:InJ n N)(q:Momentum): Cab n N:= JG J (amber q) (amber q)+JG J (zinnia q) (zinnia q)
section tide
variable {q:Momentum}(F:Tide N q)
include F
lemma plaid(t:Cover): let x:=mode q (2 • t); rake t (amber q:Air N)=x.re • amber q-x.im • zinnia q ∧ rake t (zinnia q:Air N)= x.im • amber q+x.re • zinnia q:=by
 intro x; constructor <;> ext i
 · change (dialH q (i+wrap _ (2 • t))).re= x.re* _ -x.im*_ ; rw [F.plusT]; unfold x amber zinnia; rw [mul_comm]; rfl
 change (dialH q (i+wrap _ (2 • t))).im= x.im* _+x.re*_ ; rw [F.plusT]; unfold x amber zinnia; rw [Complex.mul_im]; ring
variable (J:InJ n N)(h:ContDiffAt ℝ ω J 0)(p:CurveH J)
include h p
lemma coneA1:Lurch q (firstH J q):=by
 intro t; let a: Air N:= amber q; let b:Air N:= zinnia q; let f:=JD J; let x:=mode q (2 • t)
 have hg(c:Air N): twist (clime t) (f c)= f (rake t c):= (honk t J h p c).symm
 unfold firstH; rw [map_add]; have hv(U:Cab n N): twist (clime t) (Complex.I • U)= Complex.I • twist (clime t) U:=by simp only [twist_formula,Matrix.mul_smul,Matrix.smul_mul]
 rw [hv]; change twist _ (f a)+ Complex.I • twist _ (f b)= x • (f a+ _); rw [hg,hg]
 change f (rake t (amber q))+Complex.I • f (rake t (zinnia q))= _; rw [(plaid F t).1,(plaid F t).2]
 simp only [map_add,map_sub,map_smul,RCLike.real_smul_eq_coe_smul (K:=ℂ)]; change ((x.re:ℂ) • f a- (x.im:ℂ) • f b)+(Complex.I • ((x.im:ℂ) • f a+(x.re:ℂ) • f b))= x • (f a+ Complex.I • f b)
 conv_rhs=> lhs; rw [← Complex.re_add_im x]
 rw [smul_add, add_smul (x.re:ℂ), smul_add, smul_add,smul_smul (↑x.im * Complex.I)]; rw [mul_assoc,Complex.I_mul_I]; module
lemma coneB1:Lurch 0 (secondH J q):=by
 intro t; let a:=amber q (N:=N); let b:=zinnia q (N:=N); let f:=JG J; let x:=mode q (2 • t); let r:=x.re; let s:=x.im
 have hf: ‖x‖=1:=mode_real _ _ F.phys
 have hx:= Complex.sq_norm_sub_sq_re x; -- name
 have hk: r*r+s*s=1:=by have hg := Complex.sq_norm x; rw [hf,one_pow] at hg; exact hg.symm
 have hp:rake t a=r • a-s • b:= (plaid F t).1; have hu:rake t b=s • a+r • b:= (plaid F t).2
 have he(x y): twist (clime t) (f x y)=f (rake t x) (rake t y):=(homes t J h p x y).symm
 rw [show mode 0 (2 • t)=1 by simp [mode],one_smul]; change twist _ (f a a+f b b)= _; rw [map_add,he,he,hp,hu]; change _+_=f a a+f b b
 simp only [map_add,map_sub,map_smul,ContinuousLinearMap.add_apply,ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply]
 calc
  _ = (r*r+s*s) • (f a a+f b b):=by module
  _ = _:=by rw [hk,one_smul]
end tide

def spur(x:Site (More N)): Air N:= Pi.single x 1
lemma spur_sum(x:Air N): ∑ i:Site (More N), x i • spur i=x:=by ext i; simp [spur,Pi.single_apply, mul_ite]
lemma merit1 (f:Air N→L[ℝ]Cab n N)(x:Air N): f x= ∑ i:Site (More N),x i • f (spur i):=by conv_lhs=> rw [← spur_sum x]; simp
lemma merit2 (f:Air N→L[ℝ] Air N→L[ℝ] Cab n N)(x y:Air N): f x y=∑ i:Site (More N),∑ j: Site (More N),(x i*y j) • f (spur i) (spur j):=by
 conv_lhs=> rw [← spur_sum x,map_sum,ContinuousLinearMap.sum_apply]
 refine sum_congr rfl ?_; intro i _; rw [map_smul,ContinuousLinearMap.smul_apply,merit1 (f (spur i)) y, Finset.smul_sum]; apply sum_congr rfl; intro _ _; rw [smul_smul]
lemma stem_w(J:InJ n N)(q): firstH J q = ∑ i:Site (More N),dialH q i • JD J (spur i):=by
 rw [firstH,merit1,merit1 (JD J) (zinnia q), Finset.smul_sum,← sum_add_distrib]; refine sum_congr rfl ?_; intro i _; unfold amber zinnia; rw [RCLike.real_smul_eq_coe_smul (K:=ℂ),RCLike.real_smul_eq_coe_smul (K:=ℂ),smul_smul,mul_comm Complex.I,← add_smul]; exact congrArg (fun x :ℂ=> x • JD J (spur i)) (Complex.re_add_im (dialH q i))
def logA (q:Momentum)(x:Cover):ℂ:=(mode q x+mode (-q) x)/2
lemma logA_real(q:Momentum)(F:Tide N q)(i j:Site (More N)):logA q (lift i-lift j)= ((amber q i*amber q j+zinnia q i*zinnia q j:ℝ):ℂ):=by
 have h:= F.phys; unfold amber zinnia; rw [F.fresh,F.fresh]; let x:=lift i-lift j
 have he : mode q x=mode q (lift i)*star (mode q (lift j)):=by
    unfold x; rw [sub_eq_add_neg,mode_shift]; congr 1; rw [← mode_adjoint,h]
 change (mode q x+mode (-q) x)/2=_; rw [mode_negate _ h, he]; apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring -- tune
lemma pine_w (J:InJ n N)(q)(F:Tide N q): secondH J q=∑ i:Site (More N),∑ j: Site (More N), logA q (lift i-lift j) • JG J (spur i) (spur j):=by
 rw [secondH,merit2,merit2 (JG J) (zinnia q),←sum_add_distrib]; refine sum_congr rfl ?_; intro i _; rw [← sum_add_distrib]; refine sum_congr rfl ?_; intro j _; rw [←add_smul,logA_real _ F,RCLike.real_smul_eq_coe_smul (K:=ℂ)]; rfl
end YM.CF.Aroma
