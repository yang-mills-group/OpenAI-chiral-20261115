import YM.Next.RANK.Ray
import YM.SU5.FiniteGaugeData.Drachma.TauM
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Counting
/-! # LocalRatio chart pricing adapter. Use only real positive Haar. Need integrabilities against unchanged priors.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 20000
set_option linter.flexible false
noncomputable section
namespace YM.SU5.FiniteGaugeData.Galope
open Function Finset Filter MeasureTheory Matrix Lattice Wilson RG Precision Drachma
open Next.SectorChange Next.SectorChange.Gaussian Metric
open scoped Topology InnerProductSpace Matrix ContDiff BigOperators Classical Kronecker Matrix.Norms.Frobenius
variable {X I:Type}[Fintype I][DecidableEq I]{G:Gauge} {J:ChartRatio G}{c β:ℝ}[MeasurableSpace X]
namespace Rally
-- integral g∈exp chart (no mark directions); price c counts rates αβ(1-ε).
def doll(P:sp I)(x:coin I)(β:ℝ):= Real.exp (-β/2 * dotProduct x (P*ᵥ x))
abbrev holdK(P:sp I)(β:ℝ):= coat ((β•P)⁻¹)
lemma spdC{P:sp I} (h:P.PosDef)(hp:0<β): ((β•P)⁻¹).PosDef:= (h.smul hp).inv
lemma lensP{P:sp I} (h:P.PosDef)(hp:0<β):0<holdK P β:= coat_pos (spdC h hp)
omit [DecidableEq I] in
lemma doll_p(P:sp I)(x:coin I)(β:ℝ):0≤ doll P x β:= (Real.exp_pos _).le
lemma filmZ(P:sp I)(h:P.PosDef)(u:coin I)(hp:0<β) : Integrable (fun x:coin I=> doll P (x+u) β) ∧ (∫ x:coin I,doll P (x+u) β) = holdK P β:=by
 let Z:sp I:= β • P; have hZ:Z.PosDef:= h.smul hp; let S:= Z⁻¹; have hh(x:coin I): force S x = β*dotProduct x (P *ᵥ x):=by unfold force S; rw [nonsing_inv_nonsing_inv _ (Matrix.isUnit_iff_isUnit_det _|>.mp hZ.isUnit)]; change dotProduct x ((β • P)*ᵥ x)=_; rw [smul_mulVec,dotProduct_smul]; rfl
 let f:=fun x=> doll P x β; have he:= under_cloud hZ.inv f; let y(x:coin I):= Real.exp (force S x/2) • f x; have hz: y=(fun _=> (1:ℝ)):=by funext i; unfold y f doll; rw [hh,smul_eq_mul, ←Real.exp_add]; rw [show (β*dotProduct i (P *ᵥ i))/2 + _=0 by ring]; exact Real.exp_zero
 change (Integrable f↔ Integrable y (cloud S)) ∧ (∫ x,f x)=holdK P β*(∫ x,y x ∂cloud S) at he; rw [hz] at he; obtain ⟨p,e⟩:=he; have hs: Integrable f:= p.2 (integrable_const 1); have hμ : MeasurePreserving (MeasurableEquiv.addRight u) volume (volume: Measure (coin I)):= measurePreserving_add_right volume u
 exact ⟨hμ.integrable_comp_of_integrable hs,(hμ.integral_comp' f).trans (by rw [e]; simp)⟩
lemma crest_bill(P:sp I)(h:P.PosDef)(hp:0<β) : Real.log (holdK P β) = (Fintype.card I:ℝ) * (Real.log (Real.sqrt (2 * Real.pi)) - Real.log β/2) - Real.log P.det/2:=by
 let S:= (β•P)⁻¹; unfold holdK coat Gaussian.dome; rw [Real.log_mul (by have h:=Real.pi_pos; positivity) (by have he:0<S.det:=(spdC h hp).det_pos; exact (Real.sqrt_pos.mpr he).ne'), Real.log_sqrt (spdC h hp|>.det_pos.le), Matrix.det_nonsing_inv, Ring.inverse_eq_inv, Real.log_inv,det_smul,Real.log_mul (pow_pos hp _).ne' h.det_pos.ne']; simp only [Real.log_pow]; ring
lemma sea_chart(P:sp (I×G.ColorIndex))(h:P.PosDef)(u:Prices G I)(hp:0<β): let f(x:LogArray G I):= doll P (tape.symm x+u) β; Integrable f ∧ (∫ x,f x)=holdK P β:=by
 intro f; obtain ⟨Q,Z⟩:= filmZ P h u hp; let t:= tape (G:=G) (ι:=I); exact ⟨tape_volume.symm.integrable_comp_of_integrable Q,(tape_volume.symm.integral_comp' _).trans Z⟩ -- tune

-- given chart l1 comparator bound ON function f$ (NN). If f ≠0 then ALL coordinates small and identified with assigned values. No measurable plog assumption.
structure Lucent(J:ChartRatio G)(c C:ℝ):Prop where
 chart : LocalRatio J
 guard_l:c < J.radius
 bound_l: ∀ x:G.Color, ‖x‖≤c→ J.J x ≤ C
lemma marginM (h:LocalRatio J) (p:1<c):∃ δ>0, ∀ d:ℝ,d≤δ→ Lucent J d c:=by
 have he:∀ᶠ x:G.Color in 𝓝 0,J.J x ≤ c:= (h.germ 0 (mem_ball_self h.patch)).continuousAt.tendsto.eventually (ge_mem_nhds (by rw [h.anchored]; exact p))
 obtain ⟨v,p,hv⟩:= Metric.nhds_basis_closedBall.eventually_iff.mp he; have hp:= h.patch; refine ⟨min v (J.radius/2),lt_min p (half_pos hp),fun d t=> ⟨h,(t.trans (min_le_right ..)).trans_lt (half_lt_self hp),fun x he=>?_⟩⟩ -- p duplicate
 exact hv (mem_closedBall.mpr ((dist_zero_right x) ▸ he.trans (t.trans (min_le_left ..))))
omit [DecidableEq I] in
lemma cameo {C:ℝ} (O:Lucent J c C)(hC:0≤C)(x:LogArray G I)(v:∀ i, ‖x i‖≤ c) : Next.SectorChange.pay J x ≤ (J.scale*C)^Fintype.card I:=by
 have ht(i:I): x i∈ ball 0 J.radius:= mem_ball.mpr (by rw [dist_zero_right]; exact (v i).trans_lt O.guard_l)
 unfold pay; exact (prod_le_prod (g:=fun _=>J.scale*C) (fun i _=> mul_nonneg O.chart.scale.le (O.chart.pos _ (ht _)).le) (fun i _=> mul_le_mul_of_nonneg_left (O.bound_l _ (v i)) O.chart.scale.le)).trans_eq (by rw [prod_const,card_univ])
-- f enveloped; price by reading exactly support.
theorem price{C K:ℝ}(L:Lucent J c C)(p:0≤C)  -- dimension tune even empty
 (F:LinkArray G I→ℝ)(hF: Envelope F)(A:sp (I×G.ColorIndex))(hA:A.PosDef)(ht:0<β)(hK:0≤K)(y:coin (I×G.ColorIndex)) (budget:∀ v:LinkArray G I,F v≠0 → ∃ x: LogArray G I, release 1 x=v ∧ (∀ i,‖x i‖≤c) ∧ F v≤K*doll A (tape.symm x+y) β) :
 (∫ v,F v ∂piHaar G I) ≤ ((J.scale*C)^Fintype.card I*K)*holdK A β :=by
 have he(v:LinkArray G I)(hx: v∉ covered J (1:LinkArray G I)) : F v=0:=by
    by_contra hP; obtain ⟨x,r,t,b⟩:=budget _ hP; apply hx; rw [←release_image]; exact ⟨x,fun i _=> mem_ball.mpr (by rw [dist_zero_right]; exact (t i).trans_lt L.guard_l),r⟩
 let f(x:LogArray G I):= doll A (tape.symm x+y) β; let P:=(J.scale*C)^Fintype.card I; let v : LogArray G I→ℝ:= (mouth J).indicator (fun y=>Next.SectorChange.pay J y * F (release (1:LinkArray G I) y))
 obtain ⟨V,hi⟩:=release_integral L.chart (1:LinkArray G I) F hF.meas.stronglyMeasurable he; obtain ⟨hr,hx⟩:= sea_chart A hA y ht; let q : Integrable v:= V.mp (hF.integrable _)
 have hv:0≤P:= pow_nonneg (mul_nonneg L.chart.scale.le p) _
 have h0(x:LogArray G I): 0 ≤ P*K*f x:= mul_nonneg (mul_nonneg hv hK) (doll_p ..)
 have h1: ∀ x:LogArray G I, v x≤ P*K*f x :=by
    intro x; unfold v; by_cases h: x∈ mouth J; swap; · rw [Set.indicator_of_notMem h]; exact h0 x
    rw [Set.indicator_of_mem h]; by_cases r:F (release 1 x)=0; · rw [r,mul_zero]; exact h0 x
    obtain ⟨g,hp,A₀,q⟩:= budget (release 1 x) r; have hu:g=x:= release_injOn L.chart 1 (fun i _=>mem_ball.mpr (by rw [dist_zero_right]; exact (A₀ i).trans_lt L.guard_l)) h hp; subst g
    rw [mul_assoc]; let k:=Next.SectorChange.pay J x; exact ((_root_.mul_le_mul_of_nonneg_left q (show 0≤k from prod_nonneg fun i _=> mul_nonneg L.chart.scale.le (L.chart.pos _ (h i (Set.mem_univ _))).le)).trans (_root_.mul_le_mul_of_nonneg_right (cameo L p x A₀) (mul_nonneg hK (doll_p ..)))) -- tune
 rw [hi,← hx, ← integral_const_mul]; exact integral_mono q (hr.const_mul _) h1 -- tune
end Rally
end YM.SU5.FiniteGaugeData.Galope
