import YM.SU5.Reconstruction.Quartz.AuroraGlow
import YM.SU5.Reconstruction.Quartz.Swoop
/-! # Tunneling across a thermal GAP. Finish at both Honesty contours here.

Dollar Gaussian tails & unnormalized even Plan. States in two-clock coordinates. Wirings in plot curvature.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Quartz.Waltz
open Function Filter Set MeasureTheory Measure Metric Topology
open scoped Topology NNReal ENNReal Complex InnerProductSpace Interval
open Complex Ravin
variable (b s t d γ B:ℝ) (p:0<b)(w:0≤d)(e:|s|≤3)(k:0≤B)
-- L after operand (time-real); R before operand (time−id)
noncomputable def Board(R d:ℝ):Set ℂ:= Icc (-R) R ×ℂ Icc (-d) 0
noncomputable def FloorBoard(R d:ℝ): Set ℂ:= Ioo (-R) R ×ℂ Ioo (-d) 0
structure Tunneler (R d B:ℝ)(L M:ℝ→ℂ):Prop where
 may:∃ F:ℂ→ℂ,(∀ x∈Icc (-R) R, F x=L x∧ F ((x:ℂ)-(d:ℂ)*I)=M x)∧(∀ z∈ Board R d,‖F z‖≤B) ∧ ContinuousOn F (Board R d)∧ DifferentiableOn ℂ F (FloorBoard R d)
noncomputable def surge (b γ:ℝ):ℝ:=Real.exp (-b*γ)
local notation "R"=> scud d γ
local notation "χ" => surge b γ
include p e w k
lemma skyman {L M:ℝ→ℂ}(h:Tunneler R d B L M):
    ‖(∫ u:ℝ in -R..R,fillet b s t ((u:ℂ)+(d:ℂ)*I)*L u)-(∫ u:ℝ in -R..R,fillet b s t u*M u)‖≤ 2*(χ*B*d):= by
 obtain ⟨F,r,W,a,c⟩:=h.may; let G(z:ℂ):= fillet b s t (z+(d:ℂ)*I)* F z; let hi:Differentiable ℂ (fun z:ℂ=> fillet b s t (z+(d:ℂ)*I)):= by fun_prop
 have hR:= (scud_favorable d γ).le; have hs:-R ≤ R:= neg_le_self hR; have hx(x:ℝ)(y:ℝ) : G ((x:ℂ)+ y*I)=fillet b s t ((x:ℂ)+(y+d)*I)*F ((x:ℂ)+y*I):= by unfold G; rw [add_mul, add_assoc] -- tune casts
 have q(x:ℝ) (u: x=R ∨ x = -R): ‖I • (∫ y:ℝ in -d..0,G ((x:ℂ)+y*I))‖≤ χ*B*d:=by
   rw [norm_smul,norm_I,one_mul]; have hr:|x|=R:= by rcases u with h|h<;>simp [h,hR];
   apply (intervalIntegral.norm_integral_le_of_norm_le_const (C:=χ*B) ?_).trans_eq (by rw[zero_sub,neg_neg,abs_of_nonneg w])
   rintro y (hy: y∈ Set.uIoc (-d) 0); rw [uIoc_of_le (neg_nonpos.mpr w)] at hy; rw [hx, norm_mul, ← ofReal_add]; refine mul_le_mul (cap_edge b s γ d t x (y+d) p e ?_ (Or.inr hr.ge)) (W _ ?_) (norm_nonneg _) (Real.exp_pos _).le
   · exact abs_le.mpr (by constructor<;> linarith [hy.1,hy.2])
   unfold Board; simp only [mem_reProdIm, add_re,add_im,mul_I_re,ofReal_im,neg_zero,add_zero,ofReal_re,mul_I_im,zero_add]; exact ⟨abs_le.mp hr.le,Ioc_subset_Icc_self hy⟩
 have pe:= hor (-R) R (-d) 0 hs (neg_nonpos.mpr w) (hi.continuous.continuousOn.mul a) (hi.differentiableOn.mul c)
 let a':=∫ x:ℝ in -d..0,G ((↑R:ℂ)+x*I); let b':=∫ x:ℝ in -d..0,G ((↑(-R):ℂ)+x*I)
 have h₁: (∫ x:ℝ in -R..R,G (x+(↑(-d):ℂ)*I)) = ∫ x:ℝ in -R..R,fillet b s t x * M x:=by
    refine intervalIntegral.integral_congr (fun x hx=>?_); rw [uIcc_of_le hs] at hx; unfold G; rw [Complex.ofReal_neg,neg_mul,← sub_eq_add_neg,sub_add_cancel,(r x hx).2]
 have h₂: (∫ x:ℝ in -R..R,G (x+(↑(0:ℝ):ℂ)*I)) = ∫ x:ℝ in -R..R,fillet b s t ((x:ℂ)+d*I)*L x:=by
    refine intervalIntegral.integral_congr (fun x hx=>?_); rw[uIcc_of_le hs] at hx; unfold G; rw [Complex.ofReal_zero,zero_mul, add_zero,(r x hx).1]
 -- change template at pe (functions not G after approx)
 change (∫ x:ℝ in -R..R,G (x+(↑(-d):ℂ)*I))-(∫ x:ℝ in -R..R,G (x+(↑(0:ℝ):ℂ)*I)) + I • a'-I • b'=0 at pe
 rw [← h₁,← h₂,show (∫ x:ℝ in -R..R,G (x+(↑(0:ℝ):ℂ)*I))-(∫ x:ℝ in -R..R,G (x+(↑(-d):ℂ)*I))= I • a'-I • b' from ?_]; apply (norm_sub_le ..).trans ((add_le_add (q _ (Or.inl rfl)) (q _ (Or.inr rfl))).trans_eq (by ring))
 linear_combination -pe
-- build tail payments. outside full square
noncomputable def Field (d₁ γ₁:ℝ): Set Du:= let R₁:=scud d₁ γ₁; Set.Ioc (-R₁) R₁ ×ˢ Set.Ioc (-R₁) R₁
omit p e w k in
lemma Field_is(d γ:ℝ):MeasurableSet (Field d γ):= measurableSet_Ioc.prod measurableSet_Ioc
noncomputable def lop (b s d:ℝ)(f:Du→ℂ) : Du→ℂ := (fun x=> Blaze b (Largo x-petal s d) *f x) ∘ hike s
lemma outside {F:Du→ℂ}(m:AEStronglyMeasurable F volume)(a:∀t,‖F t‖≤B)(y:ℝ)(u: |y|≤d):‖∫ v in (Field d γ)ᶜ,lop b s y F v‖≤ 2 * χ *B*Real.pi:= by
 let C:=2* χ* B; have hC :0≤C:=by unfold C surge; positivity
 let f:=lop b s y F; let g: Du→ℝ := wallRate (b/2) ∘ hike s
 let S:=(Field d γ)ᶜ; have hf:Integrable f := (hike_integrable ..).mpr (vat_score b _ p F B k m a).1; have hg:Integrable g:=(hike_integrable ..).mpr (fullWarm _ (half_pos p)); have ht(v:Du): ‖f v‖≤ ‖Blaze b (Largo (hike s v)-petal s y)‖*B:= by unfold f lop comp; rw [norm_mul]; gcongr; exact a _ -- rfl `_` fails!
 have h(x): 0≤g x:= (rate_pos _ _ (half_pos p)).le
 calc
  _ ≤ ∫ v in S, ‖f v‖:= norm_integral_le_integral_norm _
  _ ≤ ∫ v in S,C*g v:= setIntegral_mono_on (hf.norm.integrableOn) ((hg.const_mul _).integrableOn) (Field_is d γ).compl (fun x v=>?_)
  _ ≤ ∫ v:Du,C*g v:= setIntegral_le_integral (hg.const_mul _) (ae_of_all _ (fun v=> mul_nonneg hC (h v)))
  _ = _:= by unfold g comp; rw [integral_const_mul,hike_integral,costs _ (half_pos p)] -- g unfold tune
 obtain ⟨x,z⟩:=x
 apply (ht (x,z)).trans; rw [←harmonic]; refine (mul_le_mul_of_nonneg_right (cap_mist b s γ d x z y p e u ?_) k).trans ?_
 swap
 · let i: Real.exp (-b*(γ+1)) ≤ χ:= Real.exp_le_exp.mpr (by nlinarith)
   unfold g C; simp only[comp_apply]; rw [mul_right_comm _ _ B]; gcongr
   exact (rate_pos _ _ (half_pos p)).le
 by_contra! z'; exact v ⟨Ioo_subset_Ioc_self (abs_lt.mp z'.1),Ioo_subset_Ioc_self (abs_lt.mp z'.2)⟩
end YM.Quartz.Waltz
