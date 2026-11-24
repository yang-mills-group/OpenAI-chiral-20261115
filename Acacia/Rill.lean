import Mathlib
set_option autoImplicit false
set_option synthInstance.maxSize 18000
set_option maxHeartbeats 210000
noncomputable section
namespace Acacia
open Filter Function Finset Set
open scoped Topology NNReal BigOperators Classical ComplexConjugate
variable {X:Type*}[NormedAddCommGroup X][NormedSpace ℝ X]
def delta (h:ℝ)(k:ℕ)(f:ℝ→X)(t:ℝ):X:=Nat.rec f (fun _ (g:ℝ→X) t=> h⁻¹ • (g (t+h)-g t)) k t
lemma delta_s (h:ℝ)(k:ℕ)(f:ℝ→X)(t:ℝ):delta h (k+1) f t=h⁻¹ • (delta h k f (t+h)-delta h k f t):=rfl
lemma delta_conf {h:ℝ}{k:ℕ}{f g:ℝ→X}(t:ℝ)(p:∀ i:ℕ,i ≤ k→ f (t+i*h)=g (t+i*h)):delta h k f t=delta h k g t:=by
 induction k generalizing t with
 | zero=> exact (show f t=g t from (by simpa using p 0 le_rfl))
 | succ k ih=>
    have he :delta h k f (t+h)=delta h k g (t+h):=by
       apply ih; intro j g'; have hz:=p (j+1) (Nat.succ_le_succ g'); push_cast at hz; rw [show t+h+(j:ℝ)*h=t+(j+1:ℝ)*h from (by ring)]; exact hz
    have ht: delta h k f t=delta h k g t:=ih t fun i p'=> p i (p'.trans (Nat.le_succ ..))
    rw [delta_s,delta_s,he,ht]
lemma delta_clm {Y:Type*}[NormedAddCommGroup Y][NormedSpace ℝ Y](h:ℝ)(k:ℕ)(L:X→L[ℝ] Y)(f:ℝ→X): delta h k (L ∘ f)=L ∘ delta h k f:=by
 induction k with
 | zero=>rfl
 | succ k ih=>
   ext1 t; rw [delta_s,ih]; change _= L (delta h (_+1) f t); rw [delta_s,map_smul,map_sub]; rfl
lemma delta_price{h:ℝ}(p:0<h)(k:ℕ){f:ℝ→X}(t:ℝ)(c:ℝ)(u:∀i:ℕ,i≤k→‖f (t+i*h)‖ ≤ c): ‖delta h k f t‖ ≤ c*(2/h)^k:=by
 induction k generalizing t with
 | zero=>rw [pow_zero,mul_one]; exact (show ‖f t‖ ≤ _ from (by simpa using u 0 le_rfl))
 | succ k ih=>
    have he:‖delta h k f (t+h)‖ ≤ c*(2/h)^k:=ih _ fun i g=> by rw [show t+h+ (i:ℝ)*h=t+(i+1:ℕ)*h from (by push_cast; ring)]; exact u _ (Nat.succ_le_succ g)
    have hu:= ih t fun i h=> u i (h.trans (Nat.le_succ _))
    rw [delta_s,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr p)]
    calc _≤ h⁻¹*(c*(2/h)^k+c*(2/h)^k):= mul_le_mul_of_nonneg_left ((norm_sub_le ..).trans (add_le_add he hu)) (inv_pos.mpr p).le
         _= _:=by rw [pow_succ]; field
lemma growthU{V:Set ℂ}(F:ℂ→ℝ→ℂ)(k:ℕ)(h:ℝ)(hk:∀ j:ℕ,j ≤k→ DifferentiableOn ℂ (fun z:ℂ=> F z ((j:ℝ)*h)) V): DifferentiableOn ℂ (fun z=>delta h k (F z) 0) V:=by
 exact (hi V F k h 0 (fun j p=>by simpa using hk j p))
where
 hi(V:Set ℂ)(F:ℂ→ℝ→ℂ)(k:ℕ)(h t:ℝ)(hk:∀ j:ℕ,j ≤k→ DifferentiableOn ℂ (fun z=> F z (t+(j:ℝ)*h)) V):DifferentiableOn ℂ (fun z=>delta h k (F z) t) V:=by
    induction k generalizing t with
    | zero=> change DifferentiableOn _ (fun z=> F z t) _; simpa only [Nat.cast_zero,zero_mul,add_zero] using hk 0 le_rfl
    | succ k ih=>
       have hg:DifferentiableOn ℂ (fun z=>delta h k (F z) (t+h)) V:=by
          refine ih _ fun j q=> ?_; rw [show t+h+(j:ℝ)*h=t+(j+1:ℕ)*h from (by push_cast; ring)]; exact hk _ (Nat.succ_le_succ q)
       have ht:DifferentiableOn ℂ (fun z=>delta h k (F z) t) V:= ih t fun j q=>hk j (q.trans (Nat.le_succ _))
       exact (hg.sub ht).const_smul h⁻¹ -- Diff Complex real smul likely works
#check DifferentiableOn.const_smul
#print axioms growthU
end Acacia
