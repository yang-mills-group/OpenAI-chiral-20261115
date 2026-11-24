import Velour.Crepe.Glow
/-!
# Heated tableaus still costing at most an exponential in log-scale
Algebra for extending cap certificates through finite-jet operations.
-/
set_option autoImplicit false
set_option maxRecDepth 2000
noncomputable section
namespace YM.Velour
open Filter
open scoped Topology 

def Costly (H:Hilbert) (F:ℕ→ℕ→H.Op):Prop:=
  ∃ B D:ℝ,1≤B ∧ 1≤D ∧ ∀ k i, ‖F k i‖≤B*D^k

namespace Costly
variable {H:Hilbert}{F G:ℕ→ℕ→H.Op}

lemma smaller (h:Costly H F)(p:∀k i, ‖G k i‖≤‖F k i‖):Costly H G:=by
 obtain ⟨B,D,r,t,u⟩:=h
 exact ⟨B,D,r,t,fun k i=>(p k i).trans (u k i)⟩
lemma agree (h:Costly H F)(p:∀k i,F k i=G k i):Costly H G:=
 h.smaller fun k i=>le_of_eq (congrArg _ (p k i).symm)

lemma bdd (c:ℝ)(h:∀k i, ‖F k i‖≤c):Costly H F:=by
 refine ⟨max c 1,1,le_max_right ..,le_rfl, fun k i=>?_⟩
 simpa only [one_pow,mul_one] using (h k i).trans (le_max_left c 1)

lemma add (g:Costly H F)(h:Costly H G) :
    Costly H (fun d i=>F d i + G d i):=by
 obtain ⟨B,D,s,t,b⟩:=g; obtain ⟨C,E,u,v,c⟩:=h
 have hs:=zero_le_one.trans s; have hu:=zero_le_one.trans u; have ht:=zero_le_one.trans t; have hv:=zero_le_one.trans v
 refine ⟨ B+C,max D E,(s.trans (le_add_of_nonneg_right hu)),t.trans (le_max_left ..),
        fun k i=>le_trans (norm_add_le ..) ?_⟩
 rw [add_mul]
 exact add_le_add ((b k i).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht (le_max_left ..) _) hs))
    ((c k i).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hv (le_max_right ..) _) hu))

lemma smul (g:Costly H F)(z:ℂ):
   Costly H (fun d i=> z • F d i):=by
 obtain ⟨B,D,s,t,b⟩:=g
 let Z:=‖z‖
 refine ⟨ Z*B+1,D,?_,t,
        fun k i=>le_trans (norm_smul_le ..) ?_⟩
 · exact le_add_of_nonneg_left (mul_nonneg (norm_nonneg _) (zero_le_one.trans s))

 refine (mul_le_mul_of_nonneg_left (b k i) (norm_nonneg _)).trans ((le_of_eq (mul_assoc ..).symm).trans ?_)
 exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (pow_nonneg (zero_le_one.trans t) _)

lemma sub (g:Costly H F)(h:Costly H G) :
    Costly H (fun d i=>F d i - G d i):=by
 have h':=g.add (h.smul (-1))
 simpa only [neg_one_smul,←sub_eq_add_neg] using h'

lemma mul (g:Costly H F)(h:Costly H G):
   Costly H (fun d i=> F d i * G d i):=by
 obtain ⟨B,D,s,t,b⟩:=g; obtain ⟨C,E,u,v,c⟩:=h
 refine ⟨ B*C,D*E,one_le_mul_of_one_le_of_one_le s u,one_le_mul_of_one_le_of_one_le t v,
        fun k i=>le_trans (norm_mul_le ..) ?_⟩
 exact (mul_le_mul (b k i) (c k i) (norm_nonneg _) ((norm_nonneg _).trans (b k i))).trans_eq (by rw [mul_pow]; ring)


lemma shift (g:Costly H F):Costly H (fun k i=>F (k+1) i):=by
 obtain ⟨B,D,s,t,b⟩:=g
 exact ⟨B*D,D,one_le_mul_of_one_le_of_one_le s t,t,
   fun k i=>(b (k+1) i).trans_eq (by rw [pow_succ,mul_comm _ D,mul_assoc])⟩

open Finset
lemma sum {ι:Type*}{F:ι→ℕ→ℕ→H.Op}
   (s:Finset ι)(p:∀i∈s,Costly H (F i)):
    Costly H (fun d n=>∑i∈s,F i d n):=by
 classical
 induction s using Finset.induction with
 | empty=> simp only [sum_empty]; exact bdd 1 (by simp)
 | insert i s u q=>
   simp only [sum_insert u]
   exact (p i (mem_insert_self ..)).add (q fun j h=>p j (mem_insert_of_mem h))

end Costly
end YM.Velour

