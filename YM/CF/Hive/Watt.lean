import YM.CF.Hive.Leto
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Hive
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Urn Hake Levier Spire Scree Stilo
attribute [local instance] opCStarAlgebra
variable {n:Type*}[LinearOrder n][Fintype n](b r t c:Bool)(U V:UNI n)
lemma gearL {z:ℂ}(h:U.val=z • V.val)(p:z^2=1)(u:star z=z)(A:FC n)(hp:Keys A):lotB b r U A=lotB b r V A:=by
 refine kin _ _ z p ?_ _ (lot_s b r U) (lot_s b r V) _ hp
 rintro ⟨x,i⟩; rw [mile,mile]; unfold sound; rw [Finset.smul_sum]; refine sum_congr rfl fun j _=>?_ ; rw [show (crib U r x).val=z • (crib V r x).val from ?_]; rw [smul_smul, Matrix.smul_apply,smul_eq_mul]; cases x <;> cases r<;> simp only [crib, Pastry.thread] <;> simp [filmG,ccU,h,cc_smul,u,smul_comm z]
open Nacre
lemma king(s:Signed) (U V:UNI SpinIdx)(h:JetS s b (detX s) U)(p:JetS s b (detX s) V):∃ z:ℂ,U.val=z • V.val ∧ z^2=1 ∧ star z=z:=by
 obtain ⟨z,v,l⟩:= kitsX b s U V h p; have he:= h.justice; rw [v,Matrix.smul_mul,p.justice,cc_smul, Matrix.mul_smul] at he
 let T:=V.val*spinJ; have ht:z • T=star z • T:=by rw [show T=_ from p.justice]; exact he
 have hx:T*star T=1:= (V*(⟨spinJ,spinJ_unitary⟩:UNI SpinIdx)).property.2
 have hp:z= star z:=by
    have hh:z • (1:Op SpinIdx)=star z • 1:=by rw [←hx,← Matrix.smul_mul,ht,Matrix.smul_mul]
    simpa using Matrix.ext_iff.mpr hh 0 0
 exact ⟨z,v,by rw [hp,pow_two]; nth_rw 1 [← hp]; exact l,hp.symm⟩ -- rw loops
lemma stag_s {N:Side}(s:Shape)(U V:UNI SpinIdx)(X:FC (Single N))(g:Keys X)(h:JetS s.s b (detX s.s) U)(p:JetS s.s b (detX s.s) V): lotB b (detX s.s) (siteU s b U N) X=lotB b (detX s.s) (siteU s b V N) X:=by obtain ⟨z,t,u,k⟩:= king b _ U V h p; exact gearL b _ _ _ (Ygs _ _ _ t) u k X g
abbrev yodel {N:Side}(b:Bool)(a:Shape): FC (Single N)→+*FC (Single N):=lotB b (detX a.s) (siteU a b (spinU b a.s) N)
variable {N:Side}
lemma hanks(a d:Shape)(X:FC (Single N))(p:Keys X): yodel c d (yodel b a X)= yodel (b.xor c) (joinX a d) X:=by
 let U:=spinU b a.s; let V:=spinU c d.s; let Q:= V*whiten c U; unfold yodel; rw [hilly b _ _ c _ _ X p,Levier.turns, ←det_p]; exact stag_s (b.xor c) _ _ _ X p (shineU b a c U V _ (spinZ ..) (spinZ ..)) (spinZ ..)
lemma hono (Y:Shape)(X:FC (Single N))(p:Keys X): yodel (N:=N) b (castX (Levier.ray (N:=N) b Y)) X= yodel b Y X:=by
 let t:=wrap N Y.t; let z:= fee (Rush.periods N (lift t)-Rush.periods N Y.t); refine gearL b (detX Y.s) _ _ (z:=z) (utu N b (spinU b Y.s) Y.s (Lattice.lift t) Y.t (wrap_lift _)) ?_ (fee_real _) X p; exact (pow_two _).trans (fee_one _)
abbrev teen(s:Sweep N):=yodel (N:=N) s.charge (castX s)
lemma yetL(s t:Sweep N)(X:FC (Single N))(p:Keys X):teen t (teen s X)=teen (s*t) X:=by
 unfold teen; rw [hanks _ _ _ _ X p]; let a:=castX s; let v:= castX t; rw [show (s*t).charge=s.charge.xor t.charge from rfl]; have ht : s*t=Levier.ray (s.charge.xor t.charge) (joinX a v):=by rw [← ray_join,show ray s.charge a=_ from ray_i s,show ray t.charge v=_ from ray_i t]; -- tune
 rw [ht,hono _ _ _ p]
end YM.CF.Hive
