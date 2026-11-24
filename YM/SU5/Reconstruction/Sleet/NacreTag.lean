import YM.SU5.Reconstruction.Sleet.Snowcap
import Mathlib.Analysis.Normed.Module.HahnBanach
/-! # Transfer test. Does not assume symmetry along any ray, just finite compatibility. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConePrice.Storm
open Filter Set Function Complex Sail CF.Floral
open scoped Topology NNReal Real Classical BoundedContinuousFunction BigOperators ComplexConjugate
variable {X:Type*}(μ:X→ℝ)
variable (F:X→ℂ)(Q:ℝ)
local notation "Pe"=> ℝ≥0 →ᵇ ℂ

def Voucher : Prop:= ∀ (c:X→ℂ)(S:Finset X)(C:ℝ), (∀ p:ℝ,0≤ p → ‖∑ i∈ S, c i*↑(Real.exp (-(μ i)*p))‖ ≤ C) → ‖∑ i∈ S,c i*F i‖≤ Q*C
lemma Voucher.rename {F G:X→ℂ}(p:F=G)(h:Voucher μ F Q): Voucher μ G Q:= p ▸ h
lemma Voucher.reflected(h:Voucher μ F Q): Voucher μ (fun x=>conj (F x)) Q:= by
 intro c S C u
 specialize h (fun x=>conj (c x)) S C (fun p z=> show _ from ?_)
 · simp_rw [show ∀ i:X,conj (c i)*↑(Real.exp (-(μ i)*p))= conj (c i*↑(Real.exp (-(μ i)*p))) from fun i=> by rw [map_mul,conj_ofReal], ←map_sum (conj), norm_conj]; exact u p z
 · simp_rw [show ∀ i:X,conj (c i)*F i = conj (c i*conj (F i)) from (fun i=>by simp), ← map_sum, Complex.norm_conj] at h; exact h
lemma Voucher.safe (h:Voucher μ F Q): 0≤Q:=by
 have t:= h 0 ∅ 1 (by simp); simpa using t
private def surveyP:= Finsupp.linearCombination ℂ (fun i=>monsoon ↑(μ i))
private def cost:=Finsupp.linearCombination ℂ F
variable (h:Voucher μ F Q) (p:∀ i,0<μ i)
local notation "U"=>surveyP μ
local notation "V"=>cost F
include h p
private lemma power_survey(c:X→₀ℂ): ‖V c‖≤ Q*‖U c‖:=by
 unfold cost; simp_rw [Finsupp.linearCombination_apply, Finsupp.sum, smul_eq_mul]; apply h; intro u t
 let x:ℝ≥0:= ⟨u,t⟩; have ht(i): monsoon (μ i) x=(Real.exp (-μ i*u):ℂ):=monsoon_stamp (μ i) (p i) x
 refine le_trans (le_of_eq (congr_arg norm ?_)) ((U c).norm_coe_le_norm x)
 unfold surveyP; simp_rw [Finsupp.linearCombination_apply, Finsupp.sum, BoundedContinuousFunction.sum_apply,BoundedContinuousFunction.smul_apply,smul_eq_mul,ht]

private lemma priceChart: ∃ L: StrongDual ℂ Pe, (∀ i,L (monsoon (μ i)) = F i) ∧ ‖L‖≤Q:=by
 have C₀:= Voucher.safe μ F Q h
 let W:= (surveyP μ).range -- field? 
 have hG(c b:X→₀ℂ)(z: U c = U b): V c= V b:=by
   have ht:= power_survey μ F Q h p (c-b); rw [map_sub,map_sub,z,sub_self,norm_zero,mul_zero, norm_le_zero_iff,sub_eq_zero] at ht; exact ht
 choose r hr using (fun v:W=> (show ∃ c:X→₀ℂ,U c=v.val from LinearMap.mem_range.mp v.property))
 let K: W→ₗ[ℂ] ℂ:={
   toFun v:= V (r v)
   map_add' x y:=by rw [← map_add]; apply hG; rw [hr,map_add,hr,hr]; rfl
   map_smul' c v:=by change V (r _) = c • V (r v); rw [← map_smul]; apply hG; rw [hr,map_smul,hr]; rfl }
 have hM(x:W):‖K x‖≤ Q*‖x‖:=by have ht:= power_survey μ F Q h p (r x); rw [hr] at ht; exact ht
 let D:= K.mkContinuous Q hM
 have hd(x:X→₀ℂ)(b:W)(p:b.val=U x): D b=V x:= hG _ _ ((hr b).trans p)
 obtain ⟨L,H,S⟩:= exists_extension_norm_eq W D
 refine ⟨L,fun x=>?_, S.trans_le (ContinuousLinearMap.opNorm_le_bound _ C₀ hM)⟩
 let c:= Finsupp.single x (1:ℂ); let v:W:= (surveyP μ).rangeRestrict c
 have he:= hd c v rfl; have hh : (v:Pe)=monsoon (μ x):= by change U c= monsoon _; simp [surveyP,c]
 rw [← hh,H,he]; simp [cost,c]

def Kite (C:ℝ)(f:ℂ→ℂ): Prop:= AnalyticOnNhd ℂ f optimistic ∧ ∀ z∈optimistic, ‖f z‖ ≤ C
lemma Voucher.wear : ∃ f:ℂ→ℂ,Kite Q f ∧ ∀ x:X,f (μ x)=F x :=by
 obtain ⟨L,H,W⟩:= priceChart μ F Q h p
 refine ⟨L∘ monsoon, ⟨?_,?_⟩,H⟩
 · exact fun z Z=> (ContinuousLinearMap.analyticAt L _).comp (monsoon_curve z Z) -- sig
 intro z Z; refine (L.le_opNorm (monsoon z)).trans (le_trans (mul_le_mul_of_nonneg_left (monsoon_budget z Z) (by positivity)) ?_); rwa [mul_one]
end YM.ConePrice.Storm
