import YM.SU5.FiniteGaugeData.Brique.Quince
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 620000
set_option synthInstance.maxSize 22000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Quest
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra
open Heat Brique Window.Brique Journey Py Py.Rate LocalLimit Preparation FullBill Steam Vale
open scoped Classical
variable {Λ: Preparation}{l u:ℕ}{Y:Course Λ (VolumeCape.Dream.Nimbus l)} {h:Real.exp 1 ≤ Λ.x} {C ε:ℝ}
section
variable (Λ Y h) (g:ℝ)
private theorem mpor : ∃ c:ℝ,0<c∧c<1∧∃ n':ℕ,∀ Λ:Preparation,Mac Λ c n':=by obtain ⟨c,t,x,N,G⟩:= firm_price 4 (by omega); exact ⟨c,t,x,N,fun Λ=> ⟨t,x,Λ.kJ.symm ▸ G⟩⟩
def sheenB:= Classical.choose mpor
def pitchV := mpor.choose_spec.2.2.choose
lemma shineP :0 < sheenB:= mpor.choose_spec.1
lemma sheenMac : Mac Λ sheenB pitchV := mpor.choose_spec.2.2.choose_spec _
private theorem cap_d (c C:ℝ)(h:0<c):∃ d:ℕ,2*tailCost c C d ≤ sheenB/2:=by
 have t:Tendsto (fun w:ℕ=>2*tailCost c C w) atTop (𝓝 0):=by simpa using (tailCloud c C h).const_mul 2
 exact (t.eventually (ge_mem_nhds (half_pos shineP))).exists
def stampB (c C:ℝ)(h:0<c) := (cap_d c C h).choose
lemma quantP(c C:ℝ)(h:0<c) : 2*tailCost c C (stampB c C h) ≤ sheenB/2:= (cap_d c C h).choose_spec
abbrev aged (Λ:Preparation):= (storeH Λ.V).c
abbrev pace :ℕ:= stampB (aged Λ) (storeH Λ.V).C ((storeH Λ.V).posse.level)
local notation "Κ" => storeH Λ.V
-- R chosen by marker creator. Bound needed only for D+addgap K for s FINITE. Choose inner m after support radius w chosen (itself after α).
abbrev allotL (d:ℕ):ℕ:=100*(d+1)
abbrev oven (d:ℕ) : ℝ:= (4*(allotL d:ℝ))^4
def alphaL (d:ℕ)(ξ:ℝ):ℝ:=2*(Real.log (1+(sheenB/2)⁻¹)+ |ξ| *oven d+2)
local notation "ζ" => zen (slopeF Λ.W g) (Κ).C
lemma alpha_g(d:ℕ) (g:ℝ) : 0≤alphaL d g:=by
 have h:0≤Real.log (1+(sheenB/2)⁻¹):=Real.log_nonneg (le_add_of_nonneg_right (inv_nonneg.mpr (half_pos shineP).le)); unfold alphaL oven; positivity -- power _
def thresholdH (d:ℕ) (g:ℝ):=Real.exp (alphaL d g)+1
abbrev photoB (Λ:Preparation)(g:ℝ):= alphaL (pace Λ) (zen (slopeF Λ.W g) (storeH Λ.V).C)
-- late bound `α−` for geometric support density: D+(K addgap) price as requested. use no ratio t chosen at cutoff. `reflections` supported area price
variable {D n:ℕ}
local notation "W" => pace Λ
lemma heightCost (P: D+addgap (tent Y h)≤ allotL (pace Λ)*n)(k:0<n)(u:0≤g): lighting (n^4) (photoB Λ g) (per sheenB (n^4))*Real.exp (zen (slopeF Λ.W g) (storeH Λ.V).C*((4:ℝ)*(D+addgap (tent Y h):ℕ))^4)<1/4:=by
 let d:= D+addgap (tent Y h); let n₁:=n^4; have hn:0 < n₁:=pow_pos k _; have hv:(n₁:ℝ)≥1:=Nat.one_le_cast.mpr hn; have hz:0 ≤ ζ:=zen_pos _ _ (by unfold slopeF; positivity) (Κ).posse.value.le
 let x:ℝ:=1+(sheenB/2)⁻¹; have hx:0<x:= add_pos_of_pos_of_nonneg one_pos (inv_pos.mpr (half_pos shineP)).le
 let z:= photoB Λ g; have ht: z/2=Real.log x + ζ * oven W+2:=by unfold z photoB alphaL; rw [abs_of_nonneg hz,mul_div_cancel_left₀ _ (by norm_num : (2:ℝ)≠0)]; -- tune α shape
 have hp: (4*(d:ℝ))^4 ≤ oven W*(n₁:ℝ):=by
    unfold oven n₁; push_cast; rw [←mul_pow]; apply pow_le_pow_left₀ (by positivity); have hP: (↑d:ℝ)≤↑(allotL W)*(n:ℝ):=by exact_mod_cast P
    push_cast at hP; linarith
 have hk(α:ℝ): lighting n₁ α (per sheenB n₁) = Real.exp (((Real.log x)-α/2)*n₁):=by unfold lighting per; change Real.exp (-α/2*n₁)*x^n₁= _; rw [show (Real.log x-α/2)*n₁= (-α/2*n₁)+(n₁:ℝ)*Real.log x from ?_, Real.exp_add,Real.exp_nat_mul,Real.exp_log hx]; ring
 change lighting n₁ z (per sheenB n₁)*Real.exp (ζ* (4*(d:ℝ))^4)<_; rw [hk, ←Real.exp_add]; refine lt_of_le_of_lt (Real.exp_monotone (show _ ≤ -(2:ℝ) from ?_)) ?_; rw [ht]; nlinarith only [hv,mul_le_mul_of_nonneg_left hp hz]
 have he:4<Real.exp 2:=by rw [show (2:ℝ)=1+1 from (by norm_num),Real.exp_add]; nlinarith only [Real.exp_one_gt_d9]
 rw [Real.exp_neg,←one_div]; exact one_div_lt_one_div_of_lt (by norm_num) he
lemma probe_receipts (U:thresholdH (pace Λ) ζ ≤ Λ.h): ∃ w t ε, Vast Λ (photoB Λ g) sheenB pitchV (pace Λ) w t ε:=by
 let ε:=Real.exp (-(photoB Λ g))/2; have hv:0<ε:=half_pos (Real.exp_pos _); let b:=(sheenB/2)⁻¹; let C:= (Κ).C; let t:= ε/(2*C); have hc:0<C:=(Κ).posse.value; have ht:0<t:=div_pos hv (by positivity); have htc:t*C=ε/2:=by unfold t; field_simp
 let F:= tailCost (Κ).c C; have he:Tendsto (fun i:ℕ=> F i*b+2*F i+F i) atTop (𝓝 0):=by have h:Tendsto F atTop (𝓝 0):=tailCloud _ _ (Κ).posse.level; simpa using (((h.mul_const b).add (h.const_mul 2)).add h)
 obtain ⟨w,h,u⟩:= ((show ∀ᶠ i:ℕ in atTop, F i*b+2*F i+F i ≤ ε/2 from he.eventually (ge_mem_nhds (half_pos hv))).and ((tailCloud (Κ).c C (Κ).posse.level).eventually (ge_mem_nhds hv))).exists
 refine ⟨w,t,ε,⟨alpha_g ..,U, show ε + F w ≤ _ from ?_,hv.le⟩,sheenMac Λ,ht, quantP (aged Λ) _ _, show F w*b+(2*F w+t*C)≤_ from ?_⟩
 · change F w ≤ ε at u; unfold ε at *; linarith
 change F w*b+(2*F w+t*C)≤ ε-F w; linarith
-- elect + extra. Discovery descriptor from WP2 after choosing all weights. α_wanted no ζ ret.
def scionNeed (F: Discovery) : Discovery where
 fee K L R V b d U W₁ M J l w:=
  max (F.fee K L R V b d U W₁ M J l w) (thresholdH (stampB (storeH V).c (storeH V).C (storeH V).posse.level) (zen (slopeF W₁ w) (storeH V).C))
-- `diamond` hierarchy chosen at once later, can add conclusion.
end
end YM.CF.Buffered.Afterglow.Hierarchy.Quest
