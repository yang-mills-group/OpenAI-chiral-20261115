import YM.SU5.Selected.Hill.Inner
/-! Outer cost. Loss accounted by counting tiles. -/
set_option autoImplicit false
noncomputable section
namespace YM.Hill.Box
open Function Filter Metric Finset Lattice Tree Wilson RG Pressure Exterior Work.F03 Precision MeasureTheory Chene Trunk FreeResolvent Matrix Chene.Tail Melody SectorNext.Vacuum.FlatTree Calculus Next.Rank.Axial Chene.Perks
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius MatrixOrder Matrix InnerProductSpace Kronecker
open Next.SectorChange Luge SectorTools.PhysicalGaussianSwitch
open CF.Graph
variable {G:Gauge}{n:Side}{r:Side}{S:Lots n}{B' B R m:ℕ}
variable {P:BudgetPoint}{W:PathData G}{C:Clip}{σ X D θ a τ e b μ A:ℝ}
variable (Z:ChartRatio G)(L: Next.Rank.Spindle.Rules G)(p:LocalRatio Z) (h:W.Bounds C σ X D)
variable (κ:ℝ)(s:0<b)(F:B+2*R+4≤B')(v:m+2≤ B)(f:2*R+3 ≤ B)(w:7≤ B)
variable (g:4*r.val*P.threshold ≤ e)(j:e ≤ L.c)(U:2*e<Z.radius)(o:0<θ)(u:θ<1)
variable (k:2≤ P.threshold * Real.exp ((m:ℝ) / C.relaxation))(t:∀ x:G.Color, ‖x‖≤ 2*e→ Z.J x ≤ Real.exp τ)
include p s F v f w g j U o u k t
lemma cater (d:(race r S B' B R h θ).PosDef):
 (∫ x:(columbia r n).Slice G,pours W C P b κ S ((columbia r n).drape x)∂(columbia r n).order G) ≤ fee₃ Z r S B' (fee₂ S C L b X D θ e σ P.threshold κ R) τ b (race r S B' B R h θ).det:=by
 let A:= Board r S B'; let M:= piHaar G (seat_set r S B'); let N:=piHaar G (outside r S B'); let V:=(columbia r n); let f₀(x:V.Slice G):= pours W C P b κ S (V.drape x); let e':= divide (G:=G) V (fun i=> i∈ A); let g':= f₀ ∘ e'.symm; let Q:= fee₃ Z r S B' (fee₂ S C L b X D θ e σ P.threshold κ R) τ b (race r S B' B R h θ).det
 have hg: Envelope f₀:= by obtain ⟨m₀,h,A'⟩:= pours_env W C P b κ h S; exact ⟨m₀.comp (V.continuous_drape.measurable),h,fun _=> A' _⟩
 have hx:MeasurePreserving e' (V.order G) (M.prod N):=by
    let cold (i:V.Free): Prop:=i ∈ A
    let hT:Fintype (Held V cold):= Subtype.fintype cold; let h₁:Fintype (Regular V cold):= Subtype.fintype (fun i=>¬ cold i); suffices hc:∀ (v:Fintype (Held V cold))(t:Fintype (Regular V cold)), MeasurePreserving (⇑e') (V.order G) ((@piHaar G _ v).prod (@piHaar G _ t)) from hc _ _
    have hc:MeasurePreserving e' (V.order G) ((@piHaar G _ hT).prod (@piHaar G _ h₁)):= divided V (fun i=> i ∈ A) -- mismatch again
    intro v t; rw [Subsingleton.elim v hT,Subsingleton.elim t h₁]; exact hc

 have hv:= hx.symm.integrable_comp_of_integrable (hg.integrable (V.order G)); have hu:= hv.integral_prod_right
 have hN : IsProbabilityMeasure N:= by unfold N; infer_instance
 change (∫ x,f₀ x∂ V.order G) ≤ Q; rw [← hx.symm.integral_comp' f₀]; change (∫ x,g' x∂ M.prod N) ≤ _; rw [integral_prod_symm g' hv]; apply (integral_mono hu (integrable_const Q) (fun x=> purchased Z L p h κ s F v f w g j U o u k t d x)).trans; simp -- tune
omit p s F v f w g j U o u k t
abbrev glazeB (Z:ChartRatio G)(b A:ℝ):= atoms0 G*dollar A/2-Real.log (spare Z b)
abbrev nearF (G:Gauge)(θ τ:ℝ):= τ-3*atoms0 G*Real.log (1-θ)/2
abbrev fee₄ (Z:ChartRatio G)(r:Side)(S:Lots n)(B':ℕ)(a τ θ b A:ℝ):= a+(Board r S B').card*nearF G θ τ+(Fintype.card (outside r S B'):ℝ)*glazeB Z b A
private lemma law_log (u v b K r θ σ:ℝ)(t h e z:ℕ)(hp:0<v)(h₀:0<b)(h₁:0<K)(w:0<θ)(p:t+h=e)(g:K^z ≤ Real.exp ((h:ℝ)*z*r)/((θ^3)^(t*z))*v):
 Real.exp (u+t*σ)* b^t / Real.sqrt v ≤ Real.exp (u+ t*(σ-3*z*Real.log θ/2)+h*((z:ℝ)*r/2-Real.log b)+(e*Real.log b-(z:ℝ)/2 * Real.log K)):=by
 let A:=Real.exp (u+t*σ)* b^t / Real.sqrt v; have hA:0<A:= by unfold A; positivity
 have hx:= Real.log_le_log (pow_pos h₁ z) g; change A≤_; nth_rw 1 [← Real.exp_log hA]; apply Real.exp_monotone; unfold A; rw [Real.log_mul (by positivity) hp.ne',Real.log_div (by positivity) (by positivity),Real.log_exp,Real.log_pow,Real.log_pow,Real.log_pow] at hx; rw [Real.log_div (by positivity) (by positivity),Real.log_mul (by positivity) (by positivity),Real.log_exp,Real.log_pow, Real.log_sqrt hp.le]
 rw [← p]; push_cast at hx ⊢; linarith only [hx]
variable {H:Bed}
variable (ν:0<μ)(l:1<n.val)(η:Attached H W)(ε: Floor H C n μ A)(φ:rate_ell σ X R / C.direct ≤ θ^2)
include h s ν F v f w g j U o u k t p l η ε φ
lemma inner_price (S:Lots n) : (∫ x:(columbia r n).Slice G,pours W C P b κ S ((columbia r n).drape x)∂(columbia r n).order G) ≤ Real.exp (fee₄ Z r S B' (fee₂ S C L b X D θ e σ P.threshold κ R) τ θ b A+schedule Z n H b):=by
 obtain ⟨hz,hR⟩:= cusp_corner h η ε r S l o.le u F ν φ; apply (cater Z L p h κ s F v f w g j U o u k t hz).trans; unfold fee₃; apply law_log _ _ _ _ _ (1-θ) _ _ _ _ _ hz.det_pos (spare_pos Z p s) (sky_ok H l _ ν ⟨fun x=>(ε.uniform.1 x).1⟩ ε.symmetric.1) (sub_pos.mpr u) (count_even r S B') -- adjust
 change Trunk.Chene _ _ _ ^ _ ≤ _; unfold Pens seat_set at hR; rw [Fintype.card_prod,Fintype.card_prod,Fintype.card_coe,Nat.cast_mul] at hR; exact hR
-- sum glazeB menu
lemma peak : (∫ x:Config G n,service W C P b κ x∂prior G n) ≤ ∑ S:Lots n,Real.exp (fee₄ Z r S B' (fee₂ S C L b X D θ e σ P.threshold κ R) τ θ b A+ schedule Z n H b) := (all_at W C P b κ h r).trans (sum_le_sum (fun i _=> inner_price Z L p h κ s F v f w g j U o u k t ν l η ε φ i))
end YM.Hill.Box
#print axioms YM.Hill.Box.peak
