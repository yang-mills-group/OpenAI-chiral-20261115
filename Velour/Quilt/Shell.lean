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

structure Pays (H:Hilbert) (τ:ℕ→ℝ)(F:ℝ→ℕ→H.Op)(X:ℝ→H.Op):Prop where
 see : ∀ d:ℝ,0<d→ Gleams H (F d) (X d)
 bill : ∃ B D:ℝ,1≤B ∧ 1≤D ∧ ∀ᶠ k:ℕ in atTop,∀ᶠ i:ℕ in atTop, ‖F (τ k) i‖≤B*D^k

namespace Pays
variable {H:Hilbert}{τ:ℕ→ℝ}
variable {F G:ℝ→ℕ→H.Op}{X Y:ℝ→H.Op}

lemma agree (g:Pays H τ F X)(p:∀k,0<τ k)(a:∀ d:ℝ,0<d→F d=ᶠ[atTop] G d)
    (e:∀d:ℝ,0<d→X d=Y d):
   Pays H τ G Y:=by
 obtain ⟨B,D,r,v,b⟩:=g.bill
 refine ⟨fun d t=> ?_,B,D,r,v,b.mono fun k y=>(y.and (a (τ k) (p k))).mono ?_⟩
 · rw [←e d t]; exact (g.see d t).agree (a d t)
 intro i q; exact q.2 ▸ q.1

lemma add (g:Pays H τ F X)(h:Pays H τ G Y) :
    Pays H τ (fun d i=>F d i + G d i) (fun d=>X d + Y d):=by
 obtain ⟨B,D,s,t,b⟩:=g.bill; obtain ⟨C,E,u,v,c⟩:=h.bill
 have hs:=zero_le_one.trans s; have hu:=zero_le_one.trans u; have ht:=zero_le_one.trans t; have hv:=zero_le_one.trans v
 refine ⟨fun d y=>(g.see d y).add (h.see d y), B+C,max D E,(s.trans (le_add_of_nonneg_right hu)),t.trans (le_max_left ..),
        (b.and c).mono fun k w=>(w.1.and w.2).mono fun i z=>le_trans (norm_add_le ..) ?_⟩
 rw [add_mul]
 exact add_le_add (z.1.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht (le_max_left ..) _) hs))
    (z.2.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hv (le_max_right ..) _) hu))

lemma smul (g:Pays H τ F X)(z:ℂ):
   Pays H τ (fun d i=> z • F d i) (fun d=>z • X d):=by
 obtain ⟨B,D,s,t,b⟩:=g.bill
 let Z:=‖z‖
 refine ⟨fun d y=>(g.see d y).smul tendsto_const_nhds, Z*B+1,D,?_,t,
        b.mono fun k w=>w.mono fun i y=>le_trans (norm_smul_le ..) ?_⟩
 · exact le_add_of_nonneg_left (mul_nonneg (norm_nonneg _) (zero_le_one.trans s))

 refine (mul_le_mul_of_nonneg_left y (norm_nonneg _)).trans ((le_of_eq (mul_assoc ..).symm).trans ?_)
 exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (pow_nonneg (zero_le_one.trans t) _)

lemma sub (g:Pays H τ F X)(h:Pays H τ G Y) :
    Pays H τ (fun d i=>F d i - G d i) (fun d=>X d - Y d):=by
 have h':=g.add (h.smul (-1))
 simpa only [neg_one_smul,←sub_eq_add_neg] using h'

lemma mul (g:Pays H τ F X)(h:Pays H τ G Y):
   Pays H τ (fun d i=> F d i * G d i) (fun d=>X d * Y d):=by
 obtain ⟨B,D,s,t,b⟩:=g.bill; obtain ⟨C,E,u,v,c⟩:=h.bill
 refine ⟨fun d y=>(g.see d y).mul (h.see d y), B*C,D*E,one_le_mul_of_one_le_of_one_le s u,one_le_mul_of_one_le_of_one_le t v,
        (b.and c).mono fun k w=>(w.1.and w.2).mono fun i z=>le_trans (norm_mul_le ..) ?_⟩
 exact (mul_le_mul z.1 z.2 (norm_nonneg _) ((norm_nonneg _).trans z.1)).trans_eq (by rw [mul_pow]; ring)

lemma one (X:ℝ→H.Op)(t:∀k,‖X (τ k)‖≤1):
   Pays H τ (fun d _=> X d) X:=by
 refine ⟨fun d _=>Gleams.const _,1,1,le_rfl,le_rfl,
    Eventually.of_forall fun k=>Eventually.of_forall fun i=>?_⟩
 simpa using t k


open Finset
lemma sum {ι:Type*}{F:ι→ℝ→ℕ→H.Op}{X:ι→ℝ→H.Op}
   (s:Finset ι)(p:∀i∈s,Pays H τ (F i) (X i)):
    Pays H τ (fun d n=>∑i∈s,F i d n) (fun d=>∑i∈s,X i d):=by
 classical
 induction s using Finset.induction with
 | empty=> simp only [sum_empty]; exact one (fun _=>0) (by simp)
 | insert i s u q=>
   simp only [sum_insert u]
   exact (p i (mem_insert_self ..)).add (q fun j h=>p j (mem_insert_of_mem h))

end Pays
end YM.Velour
