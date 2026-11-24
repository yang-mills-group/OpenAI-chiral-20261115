import GaugeFieldConstruction.Flan
/-! Our variant of (56) uses s-dependent polynomial excursion avoiding the matrix logarithm. -/
set_option autoImplicit false
set_option maxHeartbeats 20000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Fock.Flux
open Finset Function Filter Lattice NormedSpace Set TopologicalSpace
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator Topology BigOperators InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {I:Type*} [LinearOrder I][Fintype I] {P: Op I}
variable {J:Type*}[DecidableEq J]{L W:FC I}{z:ℝ}
def one_guard (x: Wave I) : FC I→ₗ[ℂ]Wave I:=⟨⟨fun v=>acts v x, fun v w=>act_add v w x⟩,fun c v=>act_smul c v x⟩ -- type Def
set_option maxHeartbeats 120000 in
lemma sec_dev (f:ℝ→FC I)(k:HasDerivAt f L z) (x:Wave I): HasDerivAt (fun t=>acts (f t) x) (acts L x) z:=by
 let V:=((one_guard x).toContinuousLinearMap).restrictScalars ℝ
 have h:HasDerivAt (V ∘ f) (V L) z:= by
    let h:= V.hasFDerivAt (x:=f z)
    exact h.comp_hasDerivAt z k
 change HasDerivAt (V ∘ f) (V L) z
 exact h
lemma k_change (h:IsStarProjection P)(y:ℝ) : HasDerivAt (fun x:ℝ=> knight P (1-x)) (-(Flux.excite P*knight P (1-y))) y:= by
 have he:HasDerivAt (fun t:ℝ=>1-t) (-1) y:=by simpa using! ((hasDerivAt_const y (1:ℝ)).sub (hasDerivAt_id' y)); -- tune spaces
 let A:= excite P; have hh: HasDerivAt (fun x:ℝ=> exp ((1-x) • A)) ((-1:ℝ) • (A*exp ((1-y) • A))) y:= (hasDerivAt_exp_smul_const' A (1-y:ℝ)).scomp y he
 simpa only [A,k_card h,neg_smul,one_smul] using hh
-- Q propagation with current weights moving multiplicatively. Q_t(X)=I+y T. Commuting. DO not move exc through prop before costs.
abbrev tidef (T:J → FC I) (y:ℝ)(j:J): FC I:=1+y • T j
def flowing (T:J→ FC I) (s:List J)(x:ℝ):= rollC (tidef T x) s
lemma commute_series (F H:J→FC I)(L:FC I)(s: List J)(h:∀ i∈s,Commute L (F i)): Commute L (rollC F s):=by induction s with| nil=>exact Commute.one_right _| cons i s ih=>exact (h i List.mem_cons_self).mul_right (ih fun j v=>h j (List.mem_cons_of_mem i v)) -- tune
lemma tide_cast (T:J→FC I)(q:List J)(h:q.Nodup)(t:∀ i∈q, ∀ j∈q,Commute (T i) (T j))(x:ℝ)(i:J)(g:i∈q): flowing T q x=tidef T x i * flowing T (q.erase i) x:= by
 induction q with
 | nil=> exact False.elim (List.not_mem_nil g) -- tune
 | cons j q ih=>
   obtain ⟨e,p⟩:=List.nodup_cons.mp h; by_cases b:j=i; · subst i; rw [List.erase_cons_head]; rfl
   have hp:i∈q:=(List.mem_cons.mp g).resolve_left (Ne.symm b); have hu:Commute (tidef T x i) (tidef T x j):= by
      apply Commute.add_left (Commute.one_left _); apply Commute.add_right (Commute.one_right _); exact ((t i g j List.mem_cons_self).smul_left x).smul_right x
   rw [show (j::q).erase i=j::q.erase i from List.erase_cons_tail (show ¬(j == i) by simpa using b)]; change _*flowing T q x=tidef T x i*(tidef T x j*flowing T (q.erase i) x); rw [ih p (fun i v j p=>t i (List.mem_cons_of_mem _ v) j (List.mem_cons_of_mem _ p)) hp,←mul_assoc,← hu.eq,mul_assoc]
lemma tide_der (T:J→ FC I)(q:List J)(h:q.Nodup)(t:∀ i∈q,∀ j∈q,Commute (T i) (T j))(x:ℝ): HasDerivAt (flowing T q) (∑ i∈q.toFinset,T i*flowing T (q.erase i) x) x:=by
 induction q with
 | nil=> unfold flowing rollC; simp only [List.map_nil,List.prod_nil,List.toFinset_nil,sum_empty]; exact hasDerivAt_const ..
 | cons i q ih=>
    obtain ⟨e,p⟩:=List.nodup_cons.mp h; let C:=flowing T q; let Q:= q.toFinset; let V(y):= tidef T y i
    have hv:HasDerivAt V (T i) x:=by
       simpa only [V,tidef,one_smul] using (((hasDerivAt_id' (𝕜:=ℝ) x).smul_const (T i)).const_add 1)
    have hw:= ih p (fun i v j p=>t i (List.mem_cons_of_mem _ v) j (List.mem_cons_of_mem _ p)); have ht:= hv.mul hw; apply ht.congr_deriv; rw [List.toFinset_cons,sum_insert (show i∉ q.toFinset by simpa using e),List.erase_cons_head]; rw [Finset.mul_sum]; apply congrArg; apply sum_congr rfl; intro j f; have hp: j∈q:= List.mem_toFinset.mp f; have he: i ≠ j:= fun h=>e (h.symm ▸ hp)
    have hV:Commute (V x) (T j):= by apply Commute.add_left (Commute.one_left _); exact (t i List.mem_cons_self j (List.mem_cons_of_mem _ hp)).smul_left x
    rw [List.erase_cons_tail (show ¬(i == j) by simpa using he)]; change V x*_ = T j*(V x*_); rw [←mul_assoc,hV.eq,mul_assoc]; rfl -- maybe need change q length
lemma tide_k (T:J→ FC I)(p:IsStarProjection P)(q:List J)(h:q.Nodup)(t:∀ i∈q,∀ j∈q,Commute (T i) (T j))(x:ℝ)(u:Wave I): let f(y:ℝ):= acts (knight P (1-y)*flowing T q y) u
  HasDerivAt f ( -(acts (excite P) (f x)) + ∑ i∈q.toFinset, acts (knight P (1-x)*T i * flowing T (q.erase i) x) u) x:=by
 intro f; let k:=tide_der T q h t x; apply (sec_dev _ ((k_change p x).fun_mul k) u).congr_deriv
 let v:=knight P (1-x); let w:=flowing T q x; let Q':=q.toFinset; change acts ((-(excite P*v))*w+v*_ ) u=_
 rw [act_add,neg_mul,act_neg,mul_assoc (excite P),act_mul,Finset.mul_sum, act_sum]; apply congrArg; apply sum_congr rfl; intro i _; rw [mul_assoc]
-- Budget envelope at translated 1-y
abbrev tradeKm (P:Op I)(T:J→FC I)(x:ℝ) (j:J) := knight P (1-x)*T j* knight P (-(1-x))
local notation "O"=> Set.Icc (0:ℝ) 1
lemma sliding (q:List J)(h:q.Nodup)(v:Wave I)(p:IsStarProjection P)(T:J→FC I)(t:∀ i∈q,∀ j∈q,Commute (T i) (T j))(x:ℝ)(i:J)(u:i∈q): let k:= knight P (1-x)
 let Y:= tradeKm P T x i; let Z:= flowing T (q.erase i) x; let X:= acts (k*Z) v
 acts (k*flowing T q x) v=X+x • (acts Y X)∧ acts (k*T i* Z) v=acts Y X:=by
 intro k Y Z X; have he:Y*k=k*T i:=by
    let V:= knight P (-(1-x)); rw [show Y=k*T i*V from rfl,mul_assoc,show V*k=1 from (by unfold k V; rw [knight_seg p,neg_add_cancel, knight_start]),mul_one]
 have hh: acts Y X=acts (k*T i*Z) v:= by rw [show X=acts (k*Z) v from rfl,←act_mul,←mul_assoc,he]
 rw [hh]; refine ⟨?_,rfl⟩; rw [tide_cast _ q h t x i u];
 change acts (k*((1+x • T i)*Z)) _=_; have hc(a b c:FC I):a*((1+x • b)*c)=a*c+x • (a*b*c):=by rw [add_mul,one_mul,Matrix.smul_mul,mul_add,Matrix.mul_smul,mul_assoc]
 rw [hc k,act_add, ←Complex.coe_smul x,act_smul,Complex.coe_smul] -- tune ←mul_assoc applies weird
end YM.CF.Fock.Flux
end
