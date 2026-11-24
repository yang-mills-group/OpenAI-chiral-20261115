import YM.CF.Sedge.Aurum
/-! Graph transmission, square-free plus determinant ratio definition. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Fock
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology
open Finset NormedSpace Filter
attribute [local instance] opCStarAlgebra
section core
variable {n:Type*}[DecidableEq n][Fintype n]
structure Clad (P Q W V K:Op n):Prop where
  proj : IsStarProjection P
  helm : IsStarProjection Q
  balance : star V * W=1
  left : K*(Q*W*P)=P
  right : Q*W*P*K=Q
  tray : P*K=K
  stem : K*Q=K
abbrev throat (P Q W:Op n):=Q*W*P
def laneP (Q W K:Op n):=(1-Q)*W*K
namespace Clad
variable {P Q W V K:Op n}(h:Clad P Q W V K)
include h
lemma slag : W*star V=1:=mul_eq_one_comm.mp h.balance
lemma rain : star W * V=1:=by rw [←star_star V,←star_mul,h.balance,star_one]
lemma lengthT : Q.trace=P.trace:=by nth_rw 1 [←h.right]; rw [Matrix.trace_mul_comm,h.left]
lemma chest : laneP Q W K*Q=laneP Q W K:=by unfold laneP; rw [mul_assoc,h.stem]
lemma bare : Q*laneP Q W K=0:=by unfold laneP; rw [←mul_assoc,←mul_assoc,Porth h.helm,zero_mul,zero_mul]
lemma quotaW : Q*W*K=Q:=by have he:=h.right; rwa [mul_assoc,h.tray] at he
lemma stave : (1+laneP Q W K)*throat P Q W=W*P:=by
  let H:=throat P Q W;
  unfold laneP; rw [add_mul,one_mul,mul_assoc,h.left]; unfold throat; rw [sub_mul,sub_mul,one_mul]; abel
lemma reef : laneP Q W K*laneP Q W K=0:=by nth_rw 1 [←h.chest]; rw [mul_assoc,h.bare,mul_zero]
lemma flick : (1+laneP Q W K)*(1-laneP Q W K)=1:=by rw [mul_sub,mul_one,add_mul,h.reef,one_mul]; abel
lemma cave : Q*(1+star (laneP Q W K))*V*P=star K:=by
  let M:= laneP Q W K; let B:= Q*(1+star M)*V*P
  have hp:star P=P:=h.proj.2; have hq:star Q=Q:=h.helm.2
  have hT: Q * B=B:=by unfold B; rw [←mul_assoc,←mul_assoc,←mul_assoc,h.helm.isIdempotentElem.eq]
  have hv:=congrArg star h.stave
  let N:=throat P Q W
  change star ((1+M)*N)=_ at hv; rw [star_mul,star_add,star_mul W P,hp,star_one] at hv -- tunes star_mul at *?
  have he: Q*N=N:=by unfold N throat; rw [←mul_assoc,←mul_assoc,h.helm.isIdempotentElem.eq]
  have hx:star N * Q= star N:=by nth_rw 1 [←hq]; rw [←star_mul,he]
  have hr:star N * B=P:=by unfold B; rw [←mul_assoc,←mul_assoc,←mul_assoc,hx,hv,mul_assoc _ (star W),h.rain,mul_one,h.proj.isIdempotentElem.eq]
  change B=star K; rw [←hT,show Q=star K * star N from ?_,mul_assoc,hr,← hp, ←star_mul,h.tray]
  rw [←star_mul,h.right,hq]
lemma sprint {Y:Op n} (g: Clad (1-P) (1-Q) V W Y) : (1-Q)*(1-laneP Q W K)*W*(1-P)=star Y:=by -- show comp negative star equivalence
  let N:=1-P; let T:=1-Q; let H:=laneP Q W K
  let B:= T*(1-H)*W*N; let R:= throat N T V
  have hT:star T=T:=g.helm.2; have hn:star N=N:=g.proj.2
  have he:T*B=B:=by unfold B; rw [←mul_assoc,←mul_assoc,←mul_assoc,g.helm.isIdempotentElem.eq]
  have ht:T*R=R:=by unfold R throat; rw [←mul_assoc,←mul_assoc,g.helm.isIdempotentElem.eq]
  have hm:star R*T=star R:=by nth_rw 1 [←hT]; rw [←star_mul,ht]
  have hu:star R=N*star V*T:=by unfold R throat; rw [star_mul,star_mul,hT,hn,mul_assoc]
  have hy:N*W=W ∨ N*K=0:= Or.inr (by unfold N; rw [sub_mul,one_mul,h.tray,sub_self])
  have hN:N*K=0:=by unfold N; rw [sub_mul,one_mul,h.tray,sub_self]
  have hc:star R*H= -(N*star V*Q):=by
    rw [←hm]; change _*( (1-Q)*W*K)=_; -- hm at first? `star R*T`
    rw [hm,hu,mul_assoc,show T*((1-Q)*W*K)=(1-Q)*W*K by rw [←mul_assoc,←mul_assoc,g.helm.isIdempotentElem.eq]]
    rw [show (1-Q)*W*K=W*K-Q from (by rw [sub_mul,sub_mul,one_mul,h.quotaW]),mul_sub,←mul_assoc _ W,mul_assoc N (star V),h.balance,mul_one,hN,zero_sub]; -- quotaW reassoc
  have hz:star R*(1-H)=N*star V:=by rw [mul_sub,hc,mul_one, sub_neg_eq_add,hu]; unfold T; rw [mul_sub,mul_one]; abel
  have hw:star R*B=N:=by unfold B; rw [←mul_assoc,←mul_assoc,←mul_assoc,hm,hz,mul_assoc N (star V),h.balance,mul_one,g.proj.isIdempotentElem.eq]
  change B=star Y; rw [←he,show T=star Y*star R from ?_,mul_assoc, hw,←hn, ←star_mul,g.tray]
  rw [←star_mul,g.right,hT]
end Clad
end core
variable {n:Type*}[LinearOrder n][Fintype n]
variable {P Q W V K : Op n} (h:Clad P Q W V K)
include h
lemma near_c : lineOp Q*quant (throat P Q W)=quant (throat P Q W) * lineOp P := by -- ∗ typo
  let N:=throat P Q W; let M:=quant N
  have he:N*P=N:=by unfold N throat; rw [mul_assoc,h.proj.isIdempotentElem.eq]
  have hy: Q*N=N:=by unfold N throat; rw [←mul_assoc,←mul_assoc,h.helm.isIdempotentElem.eq]
  let f (i:ℕ):=chooseK (Fintype.card n) i P.trace • selector n i
  change lineOp Q * M=M * lineOp P
  rw [lineOp,lineOp,h.lengthT]; change quant Q*(∑ i∈_,f i)*M=_; rw [mul_assoc];
  have hp : (∑ i ∈ range (Fintype.card n+1), f i)*M=M*(∑ i∈range (Fintype.card n+1),f i):= by
    unfold f M; simp_rw [mul_sum,sum_mul, Algebra.mul_smul_comm, Algebra.smul_mul_assoc,selector_quant];
  change quant Q*(_*M)=M*(quant P*(∑ i∈_,f i))
  rw [hp,←mul_assoc, ←mul_assoc M, show quant Q*M=M by unfold M; rw [←quant_mul,hy], show M*quant P=M by unfold M; rw [←quant_mul,he]]
lemma shownF {p:Wave n}(g:Sea P p): acts (quant (throat P Q W)) p ≠0:=by
  intro hz; have he:= congrArg (acts (quant K)) hz; rw [←act_mul,←quant_mul,h.left,map_zero] at he
  have hv : acts (quant P) p=p:=by nth_rw 1 [←g.1]; rw [←act_mul,line_quant h.proj,g.1];
  rw [hv] at he; apply one_ne_zero (g.2.symm.trans (by rw [he,norm_zero]):(1:ℝ)=0)
def skyGlow (q:Wave n)(W:Op n)(p:Wave n):=inner ℂ q (acts (quant W) p)
lemma beam_plan (p q:Wave n) (g:Sea P p)(e:Sea Q q): acts (quant (throat P Q W)) p=skyGlow q W p • q:=by
  have hv := congrArg (fun a:FC n=>acts a p) (near_c h); rw [act_mul,act_mul,g.1] at hv
  have hp : acts (quant P) p=p:=by nth_rw 1 [←g.1]; rw [←act_mul,line_quant h.proj,g.1];
  rw [←hv]; nth_rw 1 [throat]; rw [quant_mul,quant_mul,act_mul,hp,act_mul,←act_mul (lineOp _),quant_line h.helm,Sea.scalar h.helm e]
  rfl
lemma shines (p q:Wave n)(g:Sea P p)(e:Sea Q q): skyGlow q W p≠0:=fun w=> shownF h g (by rw [beam_plan h p q g e,w,zero_smul])
lemma broomstick (p q:Wave n)(g:Sea P p)(e:Sea Q q):acts (quant W) p=skyGlow q W p • acts (exp (dg (laneP Q W K))) q:=by
  rw [←map_smul,←beam_plan h p q g e,←act_mul, tallied _ h.reef, ←quant_mul,h.stave,quant_mul,act_mul]; congr 1
  symm;  nth_rw 1 [←g.1]; rw [←act_mul,line_quant h.proj,g.1]
lemma boom (C: Op n) : acts (quant (throat P Q W)) (filled P C)=filled Q (throat P Q W*C*(throat P Q W)ᵀ):=by rw [filled,←act_mul,←near_c h,act_mul,pair_cov]; rfl
end YM.CF.Fock
