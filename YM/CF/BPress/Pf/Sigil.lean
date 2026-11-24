import YM.CF.BPress.Pf.Resolve
/-! Fock symbols. Both spaces in the letter ordering create/annihilate v,w. `bar` on Euclidean kets used explicitly; τ bilinear. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Pf
open Function Filter NormedSpace Finset Fock Spin Spin.Quad Spin.Cellar Spin.Cellar.Pass
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
variable {I:Type}[Fintype I][LinearOrder I][Nonempty I]{P Q A T L C:Op I}{c d r:ℝ}
abbrev echo (x:Ket I):Ket I:= WithLp.toLp 2 (fun i=> star (x.ofLp i)) -- cc
@[simp] lemma echo_at (x:Ket I)(i:I): (echo x).ofLp i=star (x.ofLp i):=rfl
lemma echo_s(X:Op I)(v:Ket I): echo (acts X v)=acts (cc X) (echo v):=by apply PiLp.ext; intro i; simp only [echo_at,act_at,Matrix.mulVec,dotProduct,star_sum,star_mul,cc_apply, mul_comm]
lemma echo_eq (v:Ket I): echo (echo v)=v:=by ext; simp
lemma echo_sum (x y:Ket I): echo (x+y)=echo x+echo y:=by ext; simp
lemma echo_mul (x:Ket I)(c:ℂ): echo (c • x)=star c • echo x:=by ext; simp [mul_comm]
@[simp] lemma echo_zero: echo (0:Ket I)=0:=by ext; simp
@[simp] lemma echo_b (i:I): echo (basisKet i)=basisKet i:=by apply PiLp.ext; intro j; by_cases e:j=i <;> simp [e]

def letterV (v w:Ket I): FC I:= create v + remove (echo w)
lemma l_add (u v w x:Ket I):letterV (u+v) (w+x)=letterV u w+letterV v x:=by unfold letterV remove; rw [echo_sum,map_add,map_add,star_add]; abel
@[simp] lemma l_zero: letterV (0:Ket I) 0=0:=by simp [letterV,remove]
lemma l_scale (v w:Ket I)(c:ℂ): letterV (c • v) (c • w)= c • letterV v w:=by simp only [letterV,echo_mul,remove,map_smul,star_smul,star_star,smul_add]
lemma l_sub (u v w x:Ket I):letterV (u-v) (w-x)= letterV u w-letterV v x:=by
 rw [eq_sub_iff_add_eq] -- tune eq_sub orientation
 have ht:= (l_add (u-v) v (w-x) x).symm; rw [sub_add_cancel,sub_add_cancel] at ht; exact ht
lemma l_basis(u v:Op I)(i:I): letterV (acts u (basisKet i)) (acts v (basisKet i))= prong put u i+prong takeF v i:=by rw [letterV, echo_s,echo_b, create_def,remove_def]; simp only [basis_act,cc_apply,star_star]; rfl
def τpair (u v w x:Ket I):ℂ:= inner ℂ (echo w) v + inner ℂ (echo x) u -- order x creator? convention arg u,v = creators first of x? design adjust
lemma l_CAR (u v w x:Ket I): letterV u w * letterV v x+letterV v x*letterV u w= τpair u v w x • 1:=by
 let f:= remove (echo w); let g:= remove (echo x); unfold τpair; rw [add_smul,← car, ← car];
 have ht:f*g+g*f=0:=by have ht:=congrArg star (car_create (echo x) (echo w)); rwa [star_add,star_mul,star_mul,star_zero] at ht
 unfold letterV; calc
   _ = f*create v+create v*f + (g*create u+create u*g)+(create u*create v+create v*create u)+(f*g+g*f):=by simp only [mul_add,add_mul]; unfold f g; abel
   _ = _:=by rw [ht,car_create,add_zero,add_zero] -- tune

-- bar from basis frames (anticut inside P estimate only)
variable {u: Wave I}{v w:Ket I}
namespace Top
lemma veto (p:Top P u)(v:Ket I)(h:acts P v=v): acts (create v) u=0:=by
 obtain ⟨U,s,c,rfl,f,rfl⟩:= p.usable; rw [map_smul,←quant_column]; let x:=acts (Star.star U.val) v; let S:=quant U.val
 have ht: acts U.val x=v:=act_starUnit ..; have hp: acts (cutM s) x=x:=by rw [twist_formula,act_mul,act_mul] at h; unfold x; nth_rw 2 [←h]; exact (act_unit U _).symm -- tune local unfold
 have he : acts (create x) (basisKet s)=0:=by
    rw [create_def,act_sum]; apply sum_eq_zero; intro i _; rw [act_smul,put_act]; by_cases h:i∈s; simp [h]; rw [show x.ofLp i=0 by nth_rw 1 [←hp]; rw [cut_apply,if_neg h],zero_smul]
 rw [←act_mul, show create v*S= S*create x from by rw [quant_create,ht],act_mul,he,map_zero,smul_zero]
lemma noon (p:Top P u)(v:Ket I)(h:acts P v=0): acts (remove v) u=0:=by nth_rw 1 [←p.occupies]; rw [←act_mul,quant_ann,p.star.isSelfAdjoint,h,remove,map_zero,star_zero,mul_zero,act_zero]
lemma strike (p:Top P u)(h:acts P v=v)(g:acts (cc P) w=0): acts (letterV v w) u=0:=by
 rw [letterV,act_add, p.veto _ h,p.noon]; simp
 rw [show P=cc (cc P) from (cc_cc _).symm, ←echo_s,g,echo_zero]
end Top

lemma pair_all (p:Cᵀ= -C)(v:Ket I):acts (remove v) (pairWave C) = -acts (create (acts C (echo v))) (pairWave C):=by
 -- move rows into prong. sum identity up to action
 rw [remove_def,act_sum]; simp_rw [act_smul,pull p]; -- care simp changes
 have he: ∑ i, star (v.ofLp i) • coupleRow C i= -create (acts C (echo v)):=by
    rw [create_def,←sum_neg_distrib]; simp_rw [coupleRow, Finset.smul_sum]; rw [sum_comm]; refine sum_congr rfl fun i _=>?_ ; rw [act_at,Matrix.mulVec,dotProduct,sum_smul,←sum_neg_distrib]; exact sum_congr rfl fun k _=>by rw [smul_smul, show C k i= -C i k from Matrix.ext_iff.mpr p i k,mul_neg,neg_smul,mul_comm] -- tune
 simp_rw [←act_smul]; rw [←act_sum _ _ (pairWave C)]; -- needs act_smul rev first tune
 rw [he,act_neg]
lemma left_ann (p:Cᵀ= -C)(v:Ket I) : acts (star (letterV v (acts (cc C) v))) (pairWave C)=0:=by unfold letterV remove; rw [star_add, star_star,act_add,pair_all p, echo_s,cc_cc]; exact neg_add_cancel ..
end YM.CF.BPress.Pf
