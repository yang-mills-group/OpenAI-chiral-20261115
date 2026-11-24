import Weft.Fiber
import YM.CF.Roots.Mara
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Mew
open Set Filter Metric MeasureTheory Function Finset
open scoped Classical
-- split project tips across multiplicative character birth at known rate.
variable{I:Type*}[Fintype I][LinearOrder I]
def abrupt(c:I→ℂ)(z:Key I):=Complex.exp (∑ i:I,z i*c i)
lemma charge_h (c:I→ℂ)(i:I)(z:Key I)(d:ℂ): (∑ j:I,(update z i d j)*c j) = (∑ j:I,(dune i z j)*c j)+d*c i:=by
 let A:=Finset.univ.erase i
 rw [←Finset.add_sum_erase _ _ (mem_univ i),←Finset.add_sum_erase _ (fun j=> _ * c j) (mem_univ i),update_self,show dune i z i=0 from update_self ..,zero_mul,zero_add,add_comm (d*c i)]
 refine congrArg₂ (·+·) ?_ rfl; exact sum_congr rfl fun j p=> congrArg (·*c j) ((update_of_ne (mem_erase.mp p).1 ..).trans ((update_of_ne (mem_erase.mp p).1 ..).symm))
lemma spell_deriv (c:I→ℂ)(z:Key I)(i:I)(d:ℂ): HasDerivAt (fun x:ℂ=>abrupt c (update z i x)) (c i* abrupt c (update z i d)) d:=by
 unfold abrupt
 rw [charge_h]
 conv => arg 1; intro x; rw [charge_h]
 let u:ℂ:=∑ j:I,(dune i z j)*c j
 let F(x:ℂ):=u+x*c i
 have he:HasDerivAt F (c i) d:=by
   have h:HasDerivAt (fun x:ℂ=> x*c i) (1*c i) d:=(hasDerivAt_id' d).mul_const _
   rw [one_mul] at h; exact h.const_add u
 have ht:= he.cexp; rw [mul_comm] at ht; exact ht
lemma stampR (c:I→ℂ):River (abrupt c):=by
 refine ⟨?_ ,fun z _ t x _=> (spell_deriv c _ _ _).differentiableAt⟩; unfold abrupt; exact (Complex.continuous_exp.comp (by fun_prop)).continuousOn
lemma stamp1 (c:I→ℂ)(i:I):Set.EqOn (cutI (abrupt c) i) (fun z=> c i * abrupt c (dune i z)) (hill I):=fun z hz=> (mitt (stampR c) hz i).deriv.symm.trans (spell_deriv c z i 0).deriv
-- pack as sum with explicit function. for integral+stove expansion of velocities.Avoid naming birth trace if x.-/ 
def divide {E:Type*}[AddCommGroup E][Module ℂ E] (c:I→ℂ)(l:List I)(k:List I→E):E :=match l with
  |[]=>k []
  |t::l=> c t • divide c l k+ divide c l (fun l=>k (t::l))
lemma tip_abrupt (c:I→ℂ)(q:Key I→ℂ)(hq:River q)(l:List I)(p:l.Nodup): tipI (abrupt c * q) l = divide c l (tipI q):=by
 induction l generalizing q with
 | nil=> simp [tipI,lance,abrupt,divide]
 | cons i l ih=>
    obtain ⟨h,p⟩:= List.nodup_cons.mp p; rw [tip_mul (stampR _) hq]; unfold divide; apply congrArg₂ (·+·)
    · -- first term cutB * q ∘ dune i. use stamp1 and tip_V
      have ht:= lace_C l (f:= (cutI (abrupt c) i)* (q ∘ dune i)) (g:=fun z=>c i • (abrupt c * q) (dune i z)) (by intro z hz; change cutI (abrupt c) i z * q (dune i z)=c i*(abrupt c (dune i z)*q (dune i z)); rw [stamp1 c i hz,mul_assoc]) roots
      refine ht.trans ((tip_C (f:= (abrupt c*q)∘dune i) ((River.mul_T (stampR c) hq).stay _) (c i) l).trans ?_)
      rw [tip_V i l h, ih q hq p]
    · -- apply palate or lace change compositions. cutI q i doesn't see i. tip of right = tip of abrupt*c cutI q uncensored.
      have hx(z:Key I):cutI q i (dune i z)=cutI q i z:=by unfold cutI dune; simp_rw [update_idem]
      rw [show (abrupt c ∘ dune i)*cutI q i=(abrupt c*cutI q i)∘dune i from funext fun x=> congrArg (abrupt c (dune i x)* ·) (hx x).symm,tip_V i l h, ih _ (hq.flow i) p]; rfl
#print axioms tip_abrupt
#check Complex.continuous_exp
end YM.CF.Mew
end
