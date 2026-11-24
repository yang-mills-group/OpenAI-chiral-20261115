import YM.CF.Sedge.Grail
/-! Charts have bounded Wick evaluation kernels from the two compressed inverses. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Fock
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology
open Finset NormedSpace Filter Function
attribute [local instance] opCStarAlgebra
variable {n:Type*}[LinearOrder n][Fintype n]
lemma tarp {P:Op n}{p:Wave n}{v:Ket n}(h:IsStarProjection P)(g:acts (lineOp P) p=p)(hb:acts P v=v): acts (create v) p=0:=by
  obtain ⟨U,s,rfl⟩:=spot_projection P h; let V:= U.val; let H:=quant U.val
  have he: acts (star V) v=acts (cutM s) (acts (star V) v):=by nth_rw 1 [←hb]; rw [twist_formula,act_mul,act_mul,act_unit]
  let x:=acts (star V) v
  have ht: acts (create x) (basisKet s)=0:=by
    rw [create_def,act_sum]; apply sum_eq_zero; intro i _; rw [act_smul,put_act]; by_cases hy:i∈s
    · rw [if_pos hy,smul_zero]
    have H:x.ofLp i=0:=by unfold x; nth_rw 1 [he]; rw [cut_apply,if_neg hy]
    rw [H,zero_smul]
  have he': p= inner ℂ (wedge V s) p • acts H (basisKet s):=by rw [← show (wedge V s)=acts H _ from (quant_column ..).symm]; rw [←act_twistLine U s p]; exact g.symm
  have hz:create v*H=H*create x:=by unfold H; rw [quant_create,show acts U.val x=v from act_starUnit ..]
  rw [he',map_smul,←act_mul,hz,act_mul,ht,map_zero,smul_zero]
lemma tars {P:Op n}{p:Wave n}{v:Ket n}(h:IsStarProjection P)(g:acts (lineOp P) p=p)(hb:acts P v=0): acts (remove v) p=0:=by
  have he: remove v*quant P=0:=by rw [quant_ann,h.isSelfAdjoint,hb,show remove (0:Ket n)=0 from by simp [remove],mul_zero]
  nth_rw 1 [←g]; rw [←act_mul,lineOp,←mul_assoc,he,zero_mul,act_zero]
-- input excitation
abbrev Cod (n:Type*) := Bool × n
def cry (P:Op n)(i: Cod n): FC n:=if i.1 then hideF P i.2 else seekF P i.2
def collar (P Q W V K:Op n)(b:Bool): Op n:=if b then (1+star (laneP Q W K))*V*P else (1-laneP Q W K)*W*(1-P)
def creed (b: Bool)(v:Ket n):FC n:=if b then remove v else create v
lemma creed_a (b:Bool)(v w:Ket n):creed b (v+w)=creed b v+creed b w:=by cases b<;> simp [creed,remove]
def cravat (P Q W V K:Op n)(i:Cod n):=creed i.1 (acts (collar P Q W V K i.1) (basisKet i.2))
def rone (K T:Op n)(i:Cod n): Op n:= if i.1 then K else T
def detail (K Y:Op n)(i:Cod n): FC n:=creed i.1 (acts (star (rone K Y i)) (basisKet i.2))
def dull (P Q W V K:Op n)(i:Cod n): Op n:= (if i.1 then 1-Q else Q) * collar P Q W V K i.1
def draw (P Q W V K:Op n)(i:Cod n): FC n:=creed i.1 (acts (dull P Q W V K i) (basisKet i.2))
variable {P Q W V K Y:Op n}(h:Clad P Q W V K)(D:Clad (1-P) (1-Q) V W Y)
include h D
lemma cloth(i:Cod n): cravat P Q W V K i=detail K Y i+draw P Q W V K i:=by
  unfold cravat detail draw; rw [←creed_a, ←act_add]; congr 3
  rcases i with ⟨b,x⟩; cases b
  · simp only [dull,rone,ite_false,Bool.false_eq_true]; rw [←h.sprint D,collar]; change (1-laneP Q W K)*W*(1-P)=_ + Q*_;
    simp only [mul_assoc,Bool.false_eq_true,ite_false]; simp [sub_mul]
  · simp only [dull,rone,ite_true]; rw [←h.cave,collar]; change (1+star (laneP Q W K))*V*P=_+(1-Q)*_;
    simp only [mul_assoc,ite_true]; rw [sub_mul]; simp
lemma slump (q:Wave n)(p:Sea Q q)(i:Cod n): acts (draw P Q W V K i) q=0:=by
  rcases i with ⟨b,x⟩; cases b
  · apply tarp h.helm p.1; rw [←act_mul]; unfold dull; dsimp only; rw [if_neg (show false≠true by decide),←mul_assoc,h.helm.isIdempotentElem.eq]
  apply tars h.helm p.1; rw [←act_mul]; unfold dull; dsimp only; rw [if_pos rfl,←mul_assoc,Porth h.helm,zero_mul,act_zero]
lemma stateB (i:n): acts Q (acts (star K) (basisKet i))=acts (star K) (basisKet i):=by rw [←act_mul, show Q*star K=star K by nth_rw 1 [←h.helm.isSelfAdjoint]; rw [←star_mul,h.stem]]
lemma stayB (i:n): acts Q (acts (star Y) (basisKet i))=0:=by
  rw [←act_mul];
  have ht:(1-Q)*star Y=star Y:=by nth_rw 1 [←D.helm.isSelfAdjoint]; rw [←star_mul,D.stem]
  rw [show Q*star Y=0 by nth_rw 1 [←ht]; rw [←mul_assoc, Porth h.helm,zero_mul],act_zero]
def costC (A B:Op n)(i j:n):ℂ:=(star A * B) i j
def chordP (P Q W V K Y:Op n) (i j:Cod n):ℂ:=if i.1=j.1 then 0 else if i.1 then costC (dull P Q W V K i) (star Y) i.2 j.2 else costC (star K) (dull P Q W V K i) j.2 i.2
omit h D
lemma tout (A B:Op n)(i j:n):inner ℂ (acts A (basisKet i)) (acts B (basisKet j))=costC A B i j:=by rw [twin_inner,← act_mul,basis_inner, basis_act]; rfl
lemma car_rem (x y: Ket n): antiB (remove x) (remove y)=0:=by rw [antiB_comm]; unfold remove antiB; rw [←star_mul,←star_mul,←star_add,car_create,star_zero]
lemma contr (P Q W V K Y:Op n)(i j:Cod n): antiB (draw P Q W V K i) (detail K Y j)=chordP P Q W V K Y i j • 1:=by
  unfold draw detail; cases b:i.1<;> cases c:j.1
  · rw [creed,creed]; rw [if_neg (show false≠true by decide), if_neg (show false≠true by decide),show chordP P Q W V K Y i j=0 by simp [chordP,b,c],zero_smul,antiB, car_create]
  · unfold chordP; rw [antiB_comm,show creed true _=remove _ from rfl,show creed false _=create _ from rfl,antiB,car,tout]; simp [b,c, rone]
  · unfold chordP; rw [show creed true _=remove _ from rfl,show creed false _=create _ from rfl,antiB,car,tout]; simp [b,c, rone]
  rw [show creed true _=remove _ from rfl,show creed true _=remove _ from rfl,car_rem,show chordP P Q W V K Y i j=0 by simp [chordP,b,c],zero_smul] -- tune
include h in
lemma hangs (i:Cod n): let T:=quant (1-laneP Q W K)*quant W; T*cry P i=cravat P Q W V K i*T:=by
  intro T; unfold T cry cravat creed collar; split_ifs with g -- both
  · -- both take with inverse
    let A:=1-laneP Q W K; let B:=1+laneP Q W K
    have he: A*B=1:=mul_eq_one_comm.mp h.flick
    have hy : star (A*W)*(star B*V*P)=P:=by -- adjoint orientation incorrect? after T pulls inverse dagger = star B * V; star A * star B yes BA
      rw [star_mul, ←mul_assoc,←mul_assoc, mul_assoc (star W) (star A),←star_mul,h.flick,star_one, mul_one, h.rain,one_mul]
    rw [hideF,prong_t]; change _=remove (acts ((1+star (laneP Q W K))*V*P) _)*(quant A * quant W);
    rw [show 1+star _=star B by unfold B; rw [star_add,star_one],←quant_mul,quant_ann,←act_mul,hy]
  rw [seekF,prong_p,←quant_mul, quant_create,←act_mul]
end YM.CF.Fock
