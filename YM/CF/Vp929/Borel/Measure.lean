import YM.CF.Vp929.Paint.Ticket
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
set_option autoImplicit false
set_option maxHeartbeats 560000
noncomputable section
namespace YM.CF.VolumeCape
open Finset Function Paint MeasureTheory ProbabilityTheory
open scoped Classical ENNReal NNReal
variable {I:Type*}[Fintype I]
namespace Ticket
variable [MeasurableSpace I]
def scale(p:Ticket I):ℤ:=∑i,p.bill i
local notation "Φ"=> fun x:ℤ=> ENNReal.ofReal (x:ℝ)
variable (p:Ticket I)
def Law: Measure I:= (Φ (p.scale))⁻¹ • ∑i:I,(Φ (p.bill i)) • Measure.dirac i
lemma highT :Φ p.scale≠0:= (ENNReal.ofReal_pos.mpr (show 0< (p.scale:ℝ) from Int.cast_pos.mpr p.pos)).ne'
private lemma sum_cast(f:I→ℤ)(v:∀ i,0≤ f i): ∑ i:I, Φ (f i)= Φ (∑ i:I,f i):=by dsimp; rw [Int.cast_sum, ENNReal.ofReal_sum_of_nonneg]; exact fun i _=>Int.cast_nonneg (v i)
variable [MeasurableSingletonClass I]
lemma lawPay (U:Set I):p.Law U=(Φ p.scale)⁻¹ * Φ (∑x,p.bill x * Cr (x∈U)):=by
 have h(i:I):0≤ p.bill i*Cr (i∈U):=by unfold Cr; split; simpa using p.nn _; simp
 unfold Law; rw [← Ticket.sum_cast (f:=fun x:I=>p.bill x*Cr (x∈U)) h, Measure.smul_apply, Measure.finset_sum_apply]; refine congrArg ((Φ p.scale)⁻¹ * ·) ?_; apply Finset.sum_congr rfl; intro i _; rw [Measure.smul_apply,Measure.dirac_apply]; by_cases h:i∈ U <;> simp [Set.indicator,h]
lemma mulCast(f g:ℤ)(h:0 ≤ f)(v:0 ≤ g): (Φ f)*(Φ g)=Φ (f*g):=by dsimp; rw [Int.cast_mul,ENNReal.ofReal_mul (Int.cast_nonneg h)]
instance: IsProbabilityMeasure p.Law:= ⟨ by rw [p.lawPay]; simp only [Set.mem_univ,Cr_pos,mul_one]; change (Φ p.scale)⁻¹ * (Φ p.scale) = _; exact ENNReal.inv_mul_cancel p.highT ENNReal.ofReal_ne_top ⟩
lemma cost(e:Equiv.Perm I)(v:∀ i,p.bill (e i)=p.bill i):MeasurePreserving e p.Law p.Law:=⟨measurable_of_countable _, Measure.ext fun s hs=>by rw [Measure.map_apply (measurable_of_countable _) hs,p.lawPay,p.lawPay]; congr 2; exact Fintype.sum_equiv e _ _ fun x=> by rw [v x]; rfl⟩
lemma cashInd {X Y:Type*}[MeasurableSpace X][MeasurableSpace Y]{x:I→X}{y:I→Y}(h:p.Indep x y):IndepFun x y p.Law:=by
 apply indepFun_iff_measure_inter_preimage_eq_mul.mpr; intro s t hs ht; rw [p.lawPay,p.lawPay,p.lawPay]; simp_rw [Set.mem_inter_iff,Set.mem_preimage,Cr_imp]; let k:=Φ p.scale; have v:=h (fun i=>Cr (i∈s)) (fun i=>Cr (i∈t)); unfold both at v; dsimp only [comp_apply] at v
 have u(T:Set I): 0≤ ∑x,p.bill x*Cr (x∈T):= by
    apply sum_nonneg; intro i _; by_cases h:i∈T; · simpa [h] using p.nn i
    simp [h]
 let X:ℤ:= ∑i,p.bill i* Cr (x i∈ s); let Y:= ∑i,p.bill i* Cr (y i∈t); let Z:= ∑i,p.bill i*(Cr (x i∈s)*Cr (y i∈ t)); have H:X*Y= Z*p.scale:=v.symm
 have W:0≤ Z:= by simpa only [Set.mem_inter_iff, Set.mem_preimage,Cr_imp] using u ((x ⁻¹' s) ∩ (y ⁻¹' t))
 change k⁻¹*Φ Z=k⁻¹*Φ X*(k⁻¹*Φ Y); rw [mul_mul_mul_comm, mulCast X Y (u (x ⁻¹' s)) (u (y ⁻¹' t)),H, ← mulCast Z p.scale W p.pos.le]; rw [mul_mul_mul_comm k⁻¹ k⁻¹, ENNReal.inv_mul_cancel p.highT ENNReal.ofReal_ne_top,mul_one]
end Ticket
end YM.CF.VolumeCape
