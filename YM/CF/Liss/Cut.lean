import YM.CF.Swell.VitaK
import YM.CF.Swell.Vote
import YM.CF.Swell.Chill
import YM.CF.Swell.Beam
import YM.CF.Swell.Hush
import YM.CF.Swell.Harp
import YM.CF.Swell.Lawn
import YM.CF.Swell.Bark
import YM.CF.Swell.Tap
import YM.CF.Swell.Fist
import YM.CF.Mew.Tube
import YM.CF.Pso.Pick
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 700000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Liss
open Mew Function Filter NormedSpace Finset MeasureTheory Fock
open scoped Topology Classical BigOperators Matrix.Norms.L2Operator
variable {N I E:Type*}[Fintype N][LinearOrder N][Fintype I][LinearOrder I][NormedAddCommGroup E][NormedSpace ℂ E]
variable (U:Finset N)(Q P:Op N)
lemma cop(i j k l:N)(v:j≠k)(t:l≠i): Commute (put i*takeF j) (put k*takeF l):=by
 let a:=put i; let b:=takeF j; let c:= put k; let d:= takeF l; have h:b*c= -(c*b):=eq_neg_of_add_eq_zero_left ((mixed j k).trans (if_neg v)); have he:d*a= -(a*d):=eq_neg_of_add_eq_zero_left ((mixed l i).trans (if_neg t)); have ha:a*c= -(c*a):=eq_neg_of_add_eq_zero_left (put_put ..); have hk:b*d= -(d*b):=eq_neg_of_add_eq_zero_left (take_take ..)
 change a*b*(c*d)= c*d*(a*b); calc
    _=a*(b*c)*d:=by noncomm_ring
    _= -(a*c*(b*d)):= by rw [h]; noncomm_ring
    _= c*(d*a)*b:=by rw [ha,hk,he]; noncomm_ring
    _=_:=by noncomm_ring
abbrev gradingXp(P:Op N):=∀ i j:N,P i j≠0→ i∈U ∧ j∉U
lemma pop (h:gradingXp U Q)(v:gradingXp U P): Commute (dg Q) (dg P):=by
 unfold dg dyad; refine Commute.sum_left _ _ _ (fun i _=>Commute.sum_left _ _ _ (fun j _=>?_)); refine Commute.sum_right _ _ _ (fun k _=> Commute.sum_right _ _ _ fun l _=>?_)
 by_cases p:Q i j=0; · rw [p,zero_smul]; exact Commute.zero_left _
 by_cases q:P k l=0; · rw [q,zero_smul]; exact Commute.zero_right _
 exact ((cop i j k l (fun z=>(h i j p).2 (z.symm ▸ (v k l q).1)) (fun z=>(v k l q).2 (z.symm ▸ (h i j p).1))).smul_left (Q i j)).smul_right _
abbrev waveΦ (C:I→FC N)(z:Key I):FC N:=∑ i,z i • C i
variable (Z:I→ FC N)
abbrev κtag (z:Key I):= exp (waveΦ Z z)
lemma penX (i:I)(v:Key I)(z:ℂ): waveΦ Z (update v i z)= z • Z i+ waveΦ Z (update v i 0):=by
 unfold waveΦ; rw [←add_sum_erase _ _ (mem_univ i), ←add_sum_erase _ (fun j=> update v i (0:ℂ) j • Z j) (mem_univ i),update_self,update_self,zero_smul,zero_add]; apply congrArg; exact sum_congr rfl (fun j u=> by rw [update_of_ne (ne_of_mem_erase u),update_of_ne (ne_of_mem_erase u)])
include Z
variable(h:∀ i j,Commute (Z i) (Z j))
include h
lemma ηvek (i:I)(x:Key I)(p:ℂ): κtag Z (update x i p) = exp (p • Z i)* κtag Z (update x i 0):=by
 letI : NormedAlgebra ℚ (FC N):= NormedAlgebra.restrictScalars ℚ ℝ _; unfold κtag; rw [penX, exp_add_of_commute ((Commute.sum_right _ _ _ (fun j _=>(h i j).smul_right (update x i 0 j))).smul_left p)]
lemma hx_H : River (κtag Z):=by
 letI : NormedAlgebra ℚ (FC N):= NormedAlgebra.restrictScalars ℚ ℝ _
 refine ⟨(Continuous.comp exp_continuous (continuous_finsetSum _ (fun i _=> (continuous_apply i).smul continuous_const))).continuousOn,fun x u i y p=>?_⟩
 rw [show (fun w:ℂ=> _)=_ from (funext (ηvek Z h i x))]; exact ((hasDerivAt_exp_smul_const (Z i) y).mul_const _).differentiableAt
lemma σknee (i:I)(v:Key I)(p:v∈hill I): cutI (κtag Z) i v= Z i*κtag Z (update v i 0):=by
 apply Eq.trans (mitt (hx_H Z h) p i).deriv.symm
 rw [show (fun w:ℂ=>_)=_ from (funext (ηvek Z h i v))]; exact ((hasDerivAt_exp_smul_const (Z i) (0:ℂ)).mul_const (κtag Z (update v i 0))).deriv.trans (by simp only [zero_smul,exp_zero,one_mul])
lemma ΘXtip (l:List I)(p:l.Nodup): Mew.tipI (κtag Z) l=(l.map Z).prod:=by
 induction l with
 | nil=> change exp (∑ i, (0:ℂ) • Z i)=(1:FC N); simp
 | cons i l ih=>
    obtain ⟨v,p⟩:= List.nodup_cons.mp p; let L:=ContinuousLinearMap.mul ℂ (FC N) (Z i); let F:=κtag Z ∘ dune i
    calc _ = tipI (L ∘ F) l := lace_C _ (fun _ u=>σknee Z h _ _ u) roots
         _ = Z i*tipI F l:= (sim_H ((hx_H Z h).stay i) L l roots)
         _ = _ :=by unfold F; rw [tip_V _ _ v,ih p]; rfl
end YM.CF.Liss
#print axioms YM.CF.Liss.ΘXtip
