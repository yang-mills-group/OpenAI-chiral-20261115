/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.SU5.Selected.Hill.Epice
import YM.Push.SECTOR_MEASURE.Presented
import Mathlib.Analysis.Convex.Jensen
/-! From whole action to principal under Jensen and with penalty. Split over actual support, on actual periods. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Hill.Box
open Function Filter Finset Lattice Tree Wilson RG Pressure MeasureTheory Work.F05 Push.SectorMeasure
open scoped Topology BigOperators Classical
variable {G:Gauge}{n:Side}{t σ E D a v b:ℝ}{C:Clip}{P:BudgetPoint}{U:Config G n}
def quota (t:ℝ)(U:Config G n):ℝ:= (menu U t).card
variable (t)
lemma quota_price (U:Config G n): quota t U=∑ i:Plane n, if t<G.chord (faceValue U i) then 1 else 0:=by unfold quota menu; rw [←sum_filter,sum_const,nsmul_eq_mul,mul_one]
lemma quota_env(t:ℝ) : Envelope (quota (G:=G) (n:=n) t):=by
 simp_rw [funext (fun U=>quota_price (G:=G) (n:=n) t U)]; refine Envelope.sum _ _ fun i=> Envelope.piece ?_ (Envelope.const 1) (Envelope.const 0); exact (isOpen_lt continuous_const (G.continuous_chord.comp (continuous_travel ..))).measurableSet
private def view_s(s:Signed)(n:Side): Plane n ≃ Plane n:= Equiv.ofBijective (Face.send s 0) (Finite.injective_iff_bijective.mp (Face.injective_send ..))
lemma quota_pull (U:Config G n)(s:Signed) : quota t (pull s 0 U)= quota t U:=by
 rw [quota_price,quota_price]; simp_rw [Face.send_price U _ _ _ G.chord G.chord_inv (fun i v=> G.chord_conj ..)]; exact Equiv.sum_comp (view_s s n) (fun x=> if t<G.chord (faceValue U x) then (1:ℝ) else 0) -- explicit?
lemma quota_test(S:Lots n)(t:ℝ): MeasurableSet {x:Config G n|menu x t=S}:=by
 have hx(i:Plane n):MeasurableSet {x:Config G n| i∈menu x t}:=by simp only [menu, mem_filter, mem_univ, true_and]; exact (isOpen_lt continuous_const (G.continuous_chord.comp (continuous_travel _ i.1))).measurableSet
 simp_rw [Finset.ext_iff, Set.setOf_forall]; refine MeasurableSet.iInter fun i=> ?_; by_cases h:i∈S; simpa [h] using hx i; simp only [h, iff_false]; exact (hx i).compl
variable (W:PathData G)(C:Clip)(P:BudgetPoint)(v κ:ℝ)
def service (x:Config G n):= Real.exp (-W.inChannels C P v x+ κ*quota P.threshold x)
def dish (x:Config G n):= Real.exp (-W.principal C P v x+ κ*quota P.threshold x)
def pours(S:Lots n) (x:Config G n):= if menu x P.threshold=S then dish W C P v κ x else 0
lemma stock (x:Config G n) : dish W C P v κ x=∑ i:Lots n,pours W C P v κ i x:=by simp [pours]
variable (h:W.Bounds C σ E D)
include h
lemma dish_env : Envelope (dish (n:=n) W C P v κ) := (((PathData.principal_env h P v).neg.add ((Envelope.const κ).mul (quota_env _))).exp)
lemma service_env : Envelope (service (n:=n) W C P v κ) := (((PathData.channels_env h P v).neg.add ((Envelope.const κ).mul (quota_env _))).exp)
lemma pours_env(S: Lots n): Envelope (pours W C P v κ S):= Envelope.piece (quota_test ..) (dish_env W C P v κ h) (Envelope.const _)
omit h in
private lemma mask_stamp (x:Support n) {f:Config G n→ℝ}(p:GaugeInvariant f): GaugeInvariant (masked t x f):=by
 intro k V; unfold masked; simp only [Set.indicator,Set.mem_setOf_eq,Healthy,gauge_flags,p k V]; congr!
lemma service_d(S:Lots n): GaugeInvariant (pours W C P v κ S):=by
 intro k U; have he:menu (gauge k U) P.threshold=menu U P.threshold:=by unfold menu; simp_rw [face_gauge,Gauge.chord_conj]
 unfold pours dish quota; rw [he]
 have hp (i:Plane n): W.baseTerm C P (gauge k U) i=W.baseTerm C P U i:=by simp only [PathData.baseTerm,PathData.kept, face_gauge,Gauge.chord_conj,ell_gauge h, G.norm_adjoint]; congr!
 have hk{l:ℕ} (H:ℕ→ Atom G l)(g:∀ i,(H i).Invariant)(x:Site n): PathData.atomSeries H P (gauge k U) x=PathData.atomSeries H P U x:=by
    refine tsum_congr fun i=> mask_stamp (G:=G) _ _ ?_ k U; intro m U; unfold Atom.unmasked; simp_rw [slot_gauge]; exact g i ..
 simp_rw [PathData.principal,hp,hk W.cubic (fun i=>(h.invariant i).2.1),hk W.quartic (fun i=>(h.invariant i).2.2),hk W.loop (fun i=>(h.invariant i).1)] -- tune
abbrev π_s:ℝ:=(Fintype.card Signed:ℝ)⁻¹
lemma almost_l(U:Config G n): service W C P v κ U ≤ ∑ s:Signed,π_s*dish W C P v κ (pull s 0 U):=by
 unfold service dish; simp_rw [quota_pull]; unfold PathData.inChannels; let f(s:Signed):=W.principal C P v (pull s 0 U); let a:=κ * quota P.threshold U
 have he:∑ i:Signed,π_s=1:=by rw [sum_const,card_univ,nsmul_eq_mul]; exact mul_inv_cancel₀ (by positivity)
 have ht: ∑ i:Signed, π_s • (- f i+a)= -(π_s*∑ i,f i)+a:=by simp_rw [smul_eq_mul,mul_add,sum_add_distrib,mul_neg,sum_neg_distrib,← mul_sum (a:=π_s) (f:=f),←sum_mul,he,one_mul] -- may mul_sum greedily
 rw [← ht]; exact ConvexOn.map_sum_le (f:=Real.exp) convexOn_exp (fun _ _=>show 0≤π_s from by unfold π_s; positivity) he (fun _ _=> Set.mem_univ _)
theorem all_at (r:Side): (∫ x:Config G n,service W C P v κ x∂ prior G n) ≤ ∑ i:Lots n, ∫ x:(columbia r n).Slice G,pours W C P v κ i ((columbia r n).drape x)∂(columbia r n).order G:=by
 let μ:= prior G n; let P₀: Config G n→ℝ:= dish W C P v κ; let L(k:Signed):= fun x=> π_s*P₀ (pull k 0 x)
 have ht(k):MeasurePreserving (pull k 0) μ μ:=prior_pull _ _; have hP:= (dish_env W C P v κ h).integrable μ; have hx(k):Integrable (L k) μ:= ((ht k).integrable_comp_of_integrable hP).const_mul _
 have hT : ∀ k, (∫ x,L k x ∂μ)= π_s*∫ x,P₀ x ∂μ:=by 
    intro k; rw [show L k= _ from rfl]; unfold L; rw [integral_const_mul]; refine congrArg (π_s * ·) ?_
    -- beta local
    have hp:= (ht k).map_eq; exact ((integral_map (ht k).aemeasurable (f:=P₀) (hp.symm ▸ (show AEStronglyMeasurable P₀ μ from hP.aestronglyMeasurable))).symm.trans (by rw [hp])) -- tune
 have he:∑ i:Signed, π_s * (∫ x,P₀ x∂μ)=(∫ x,P₀ x ∂μ):=by unfold π_s; simp
 calc
 _ ≤ ∫ x, (∑ i,L i x)∂μ:= integral_mono ((service_env W C P v κ h).integrable μ) (integrable_finsetSum _ (fun i _=>hx i)) (fun x=> almost_l W C P v κ h x)
 _ = ∫ x,P₀ x∂μ:=by rw [integral_finsetSum _ (fun i _=>hx i)]; simp_rw [hT]; rw [he]
 _ = _:=by
    unfold P₀; simp_rw [stock]; rw [integral_finsetSum]; apply sum_congr rfl; intro i _; exact (columbia r n).pack _ ((pours_env W C P v κ h i).integrable μ) (fun t _ x=> service_d W C P v κ h i t x) -- tune
    exact fun i _=> (pours_env W C P v κ h i).integrable μ
end YM.Hill.Box
#print axioms YM.Hill.Box.all_at
