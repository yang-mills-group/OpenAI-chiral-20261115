import YM.CF.Mew.Lace
import CellQ.First
set_option autoImplicit false
set_option linter.flexible false
noncomputable section
namespace YM.CF.Drift
namespace Grain
open Function Finset Mew Metric
open scoped BigOperators Topology
variable {I E:Type}[Fintype I][LinearOrder I][AddCommGroup E][Module ℂ E]
local notation "nT" => (Fintype.card (PairKey I)+1)
local notation "K"=> Key (PairKey I)
attribute [-instance] instDecidableEqLex
variable {V:Type}[NormedAddCommGroup V][NormedSpace ℂ V][CompleteSpace V]
variable {f:Mew.Key I→ V}{s:ℂ}
abbrev dilate (s:ℂ)(x:Mew.Key I):=s • x
lemma edit (s:ℂ)(x:Mew.Key I)(i:I)(z:ℂ): dilate s (update x i z)= update (dilate s x) i (s*z):=by
 funext j; by_cases p:j=i; · subst j; unfold dilate; rw [Pi.smul_apply,update_self,update_self,smul_eq_mul]
 unfold dilate; rw [update_of_ne p,Pi.smul_apply,Pi.smul_apply,update_of_ne p]
variable (v:‖s‖≤1)
include v
lemma dilates{x:Mew.Key I}(h:x∈hill I):dilate s x∈hill I:=by
 rw [mem_closedBall_zero_iff] at *; unfold dilate; rw [norm_smul]; exact (mul_le_mul v h (norm_nonneg _) zero_le_one).trans (by norm_num)
lemma River_house (p:River f) : River (fun x=>f (dilate s x)):=by
 refine ⟨p.shore.comp (continuousOn_id.const_smul s) (fun _ => dilates v),fun z h i x hp=> ?_⟩; simp_rw [edit]; have hx: s*x∈rim:=Metric.mem_ball.mpr (by rw [dist_zero_right,norm_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) v) (show ‖x‖<1 from (by simpa [rim,Metric.mem_ball] using hp)))
 exact (p.slope _ (dilates v h) i _ hx).comp x (differentiableAt_const (c:=s)|>.mul differentiableAt_id)
lemma slice_dilate (p:River f) (i:I): Set.EqOn (cutI (fun x=>f (dilate s x)) i) (fun x=> s • cutI f i (dilate s x)) (hill I):=by
 intro x hx; rw [←(mitt (River_house v p) hx i).deriv]; simp_rw [edit]
 have he:= (mitt p (dilates v hx) i); have hl:HasDerivAt (fun z:ℂ=>s*z) s 0:= by convert! (hasDerivAt_id' (0:ℂ)).const_mul s using 1 <;> simp
 have hm:HasDerivAt (fun w=> f (update (dilate s x) i w)) (cutI f i (dilate s x)) (s*(0:ℂ)):=by rwa [mul_zero]
 exact (HasDerivAt.scomp (𝕜:=ℂ) (x:=0) hm hl).deriv -- parameters
lemma lance_dilate (p:River f)(t:List I): Set.EqOn (lance (fun x=> f (dilate s x)) t) (fun x=> (s^t.length) • lance f t (dilate s x)) (hill I):=by
 induction t generalizing f with
 | nil=> intro x _; simp [lance]
 | cons i t ih=>
   apply (lace_C t (slice_dilate v p i)).trans
   intro x h
   let g(y):=cutI f i (dilate s y)
   have hz:River g:=River_house v (p.flow i)
   rw [show lance (fun x=>s • cutI f i (dilate s x)) t x=s • lance g t x from (sim_H hz (s • ContinuousLinearMap.id ℂ V) t h), (show lance g t x=(s^t.length) • _ from ih (p.flow i) h), smul_smul,List.length_cons,pow_succ']
   rfl
lemma tip_dial (p:River f) (t:List I) : tipI (fun x=> f (dilate s x)) t=(s^t.length) • tipI f t:=by
 simpa only [dilate,smul_zero] using (lance_dilate v p t (Mew.roots (I:=I)))
end Grain
end YM.CF.Drift
