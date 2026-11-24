import YM.CF.Thera.Hang
import YM.CF.BProof.Align.Table

/-! Fock Wick / Slater quantities. One Fock over all Single modes. Do NOT square
phase. First we prove the exact transport through `house u` & real-part cost. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Wick
open Function Filter NormedSpace Fock Thera Finset Branch Align
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {I:Type*}[Fintype I][LinearOrder I] {P S:Op I}{U:Wave I}
structure Task (P : Op I)(U:Wave I): Prop where
 home : IsStarProjection P
 nonzero : U≠0
 wage : acts (lineOp P) U=U
namespace Task
lemma sea (h:IsStarProjection P)(k:Sea P U):Task P U:=⟨h,norm_pos_iff.mp (by rw [k.2]; exact one_pos),k.1⟩
variable (h:Task P U)
include h
lemma enters : acts (quant P) U=U:= by nth_rw 1 [←h.wage]; rw [←act_mul,line_quant h.home,h.wage]
lemma quantS (p:Fit P S) : Task (land P S) (acts (quant S) U):=by
 let X:=land P S; have he:X*S*P=S:=by rw [show X*S=S from p.keeps,p.crop]
 refine ⟨p.landed,fun t=>?_,?_⟩
 · apply h.nonzero; rw [←h.enters,←p.lays,quant_mul,act_mul,t,map_zero]
 have hx:= line_near p.landed h.home p.trace S; change lineOp X*quant (X*S*P)=quant (X*S*P)*lineOp P at hx; rw [he] at hx; rw [←act_mul (lineOp _),show land P S=X from rfl, hx,act_mul,h.wage]
lemma rebase : ∃ a:ℂ,∃ v:Wave I,Sea P v ∧ a≠0∧ U=a • v:=by
 obtain ⟨V,x,v⟩:= spot_projection P h.home
 let Q:=wedge V.val x; have he: U=inner ℂ Q U • Q:=by have he:=h.wage; rw [v,act_twistLine] at he; exact he.symm
 let a:=inner ℂ Q U; have hp: ‖Q‖=1:=wedge_norm ..
 have hh: a≠0:=fun e=>h.nonzero ((he.trans <| by change a • Q=0; rw [e,zero_smul]))
 refine ⟨a,Q,⟨?_,hp⟩,hh,he⟩; rw [v,act_twistLine]; change inner ℂ Q Q •Q=Q; rw [inner_self_eq_norm_sq_to_K,hp]; simp -- tune
lemma sitting (X:Op I)(hp:Commute P X) : acts (quant X) U=(hutch X P).det • U:=by
 obtain ⟨c,t,p,g,e⟩:= h.rebase; subst U; rw [map_smul,smul_comm]; congr 1; rw [show (hutch X P).det=inner ℂ t (acts (quant X) t) from (meadow h.home t p X).symm,← Sea.scalar h.home p]; nth_rw 1 [←p.1]; rw [←act_mul,line_quant_comm hp.symm.eq,act_mul] -- direction
lemma town (q: Fit P S) : ‖acts (quant S) U‖^2= ‖U‖^2*‖(entered P S).det‖:=by
 obtain ⟨c,v,g,x,e⟩:=h.rebase; rw [e,map_smul,norm_smul,norm_smul,g.2,mul_one,mul_pow]; congr 1
 have he:hutch (star S*S) P=entered P S:=by rw [hutch,entered,←mul_assoc P,q.leftS,mul_assoc,q.crop]
 rw [← he,hutch,← show inner ℂ v (acts (quant (star S*S)) v)=_ from meadow q.proj v g (star S*S),quant_mul,quant_star,act_mul]
 let X:= quant S; rw [← act_inner,star_star,inner_self_eq_norm_sq_to_K,norm_pow]; simp
end Task
end YM.CF.BProof.Wick
