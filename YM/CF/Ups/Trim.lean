import YM.CF.Ups.Seam
set_option autoImplicit false
set_option maxHeartbeats 630000
noncomputable section
namespace YM.CF.Reed
open Function Filter Metric Cube Finset Fock Lattice Emu Skye
open scoped Topology ContDiff BigOperators InnerProductSpace NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
variable {I:Type}[Fintype I][LinearOrder I]
lemma zest_A (A:Finset I)(J:Finset I):∃ (α:Bool)(L:FC I), Fine A univ α L ∧ acts (star L) (basisKet A)=basisKet J:=by
 have he(X:Finset I): X⊆A →∃ (α:Bool)(L:FC I), Fine A univ α L ∧ acts (star L) (basisKet A)=basisKet (A\X):=by
    induction X using Finset.induction_on with
    |empty=> intro _; refine ⟨false,1,Fine.one,?_⟩; rw [star_one,act_one,sdiff_empty]
    |@insert i X p ih=>
       intro h; have hv:i∈A:=h (mem_insert_self ..); obtain ⟨a,C,s,v⟩:=ih (fun i b=>h (mem_insert_of_mem b)); let K:=parity i (A\X); have ht:= Fine.seed (s:=A) i (mem_univ _); rw [show (think A).term i=put i from if_pos hv] at ht
       refine ⟨_,K • (C*put i),(s.grow ht).scale _,?_⟩; rw [star_smul,star_mul,act_smul,act_mul,v]; change star K • acts (takeF i) (basisKet _) =_; rw [take_act,if_pos (mem_sdiff.mpr ⟨hv,p⟩),show star K=K from parity_star ..,smul_smul,show K*K=1 from parity_sq ..,one_smul]; congr 1; grind -- Finset tune
 let D:= A\(A\J); have hg:D⊆ A:=sdiff_subset; obtain ⟨a,C,s,t⟩:=he (A\J) sdiff_subset
 have hk(X:Finset I): Disjoint X A → ∃ (p:Bool)(C:FC I), Fine A univ p C ∧ acts (star C) (basisKet A)=basisKet (D∪X):=by
    induction X using Finset.induction_on with
    | empty=> intro _; rw [union_empty]; exact ⟨a,C,s,t⟩
    | @insert i X p ih=>
       intro h; have hx:i∉A:= Finset.disjoint_left.mp h (mem_insert_self ..); obtain ⟨j,V,v,f⟩:=ih (Disjoint.mono_left (subset_insert ..) h); let K:= parity i (D∪X); have ht:= Fine.seed (s:=A) i (mem_univ _); rw [show (think A).term i= -(takeF i) from if_neg hx] at ht; have hs:Fine A univ true (takeF i):=by simpa using ht.scale (-1)
       refine ⟨_,K •(V*takeF i),(v.grow hs).scale _,?_⟩; rw [star_smul,star_mul,act_smul,act_mul,f,show star (takeF i)=put i from star_star _, put_act,if_neg (notMem_union.mpr ⟨fun k=>hx (hg k),p⟩), show star K=K from parity_star ..,smul_smul,show K*K=1 from parity_sq ..,one_smul]; congr 1; grind
 obtain ⟨p,L,h,H⟩:=hk (J\A) (Finset.sdiff_disjoint); exact ⟨p,L,h,(show D∪(J\A)=J from (by unfold D; grind)) ▸ H⟩
private theorem phone (A:Finset I)(α:Bool)(x:FC I)(k:Fine A univ α x)(h:acts (star x) (basisKet A)=0): x=0:=by
 have he:star x=0:=op_columns fun i=>by
    obtain ⟨v,C,pV,v'⟩:=zest_A A i; rw [← v', ←act_mul,act_zero, ←star_mul, pV.sign_com k,star_smul,act_smul,star_mul,act_mul,h,map_zero,smul_zero]
 rw [←star_star x,he,star_zero]
lemma contrast_K(A:Finset I)(p:Wave I)(h:Sea (cutM A) p): let c:= p.ofLp A; p=c • basisKet A∧ c≠0:=by
 intro c; have he:=h.1; rw [cutLine,cut_oneAct] at he; refine ⟨he.symm,fun v=>?_⟩; have hv: 0 < ‖p‖ := zero_lt_one.trans_le h.2.symm.le; rw [←he, (show p.ofLp A=0 from v),zero_smul,norm_zero] at hv; exact lt_irrefl _ hv
lemma zeros_Q (A:Finset I)(x y:FC I)(p:Fine A univ true x)(v:Fine A univ false y)(q:Wave I)(g:Sea (cutM A) q)(h:∀ V:Wave I, inner ℂ q (acts (x+y) V)=0):x=0∧y=0:=by
 let Y:=basisKet A; have he:= contrast_K A q g; have hc:acts (star (x+y)) Y=0:=ext_inner_left ℂ fun i=>by
    rw [inner_zero_right]; apply (starRingEnd ℂ).injective; rw [map_zero, inner_conj_symm]; let z:=p; have hf:= h i; rw [he.1,inner_smul_left] at hf; rw [act_inner]; exact (mul_eq_zero.mp hf).resolve_left (star_ne_zero.mpr he.2)
 rw [star_add,act_add] at hc; let U:UNI I:= phaseU (-1) (by simp); let K:=quantU U; have hs(W:FC I)(a:Bool)(v:Fock.Sector univ a W): twist K (star W)=(if a then (-1:ℂ) else 1) • star W:= (v.contr.grade_diag)
 let u:=((-1:ℂ)^A.card); have hk:acts K.val Y=u • Y:=by
    have he:U.val=Matrix.diagonal fun _=> -1:=by change (-1:ℂ) • (1:Op I)=_; ext i j; by_cases g:i=j<;>simp [g]
    change acts (quant U.val) (basisKet A)=_; rw [he, quant_diag]; apply PiLp.ext; intro j; by_cases h:j=A
    · rw [h,basis_act]; simp [Y,u]
    rw [basis_act, Matrix.diagonal_apply_ne _ h]; simp [Y,basis_apply, h]
 let M:= acts (star x) Y; let N:=acts (star y) Y; have hz:M+N=0:=hc
 have hh:-u • M+u • N=0:=by
    have hh:= congrArg (fun i:Wave I=> acts K.val i) hc; rw [map_add,map_zero,Fock.swivel,Fock.swivel,hk,hs _ _ p.sector,hs _ _ v.sector,if_pos rfl,if_neg (by decide:¬(false=true)), act_smul,one_smul,map_smul,map_smul] at hh; simp only [neg_one_smul] at hh; simpa [M,N] using hh
 have ht:-M+N=0:=by rw [neg_smul, ←smul_neg,← smul_add] at hh; exact (smul_eq_zero.mp hh).resolve_left ((pow_ne_zero _ (by norm_num)))
 have hw: N=0:=by
    have htU: (2:ℂ) • N=0:=by rw [two_smul]; exact (show N+N= (M+N)+(-M+N) by abel).trans (by rw [hz,ht,zero_add])
    exact (smul_eq_zero.mp htU).resolve_left (by norm_num)
 exact ⟨phone _ _ x p (by change M=_; rw [hw,add_zero] at hz; exact hz),phone _ _ y v hw⟩
end YM.CF.Reed
