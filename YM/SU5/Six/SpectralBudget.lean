import YM.SU5.Six.Elected

set_option autoImplicit false
open scoped Topology
noncomputable section
namespace MeasureTheory.FiniteMeasure
open Filter Set Metric
open scoped ENNReal NNReal Topology BoundedContinuousFunction
variable {X:Type*}[MetricSpace X][ProperSpace X][MeasurableSpace X][BorelSpace X]
variable {μ : ℕ→FiniteMeasure X}{ν:FiniteMeasure X}

-- Choose one compact ball to pay the family of all sufficiently late measures.
private lemma eventually_tight [Nonempty X](h:Tendsto μ atTop (𝓝 ν)){ε:ℝ}(u:0<ε) :
    ∃ A:Set X, IsCompact A ∧ ∀ᶠ i:ℕ in atTop, ((μ i:Measure X)).real Aᶜ < ε := by
  let o:=Classical.arbitrary X
  let B(n:ℕ):=ball o n
  let U(n:ℕ):= (B n)ᶜ
  have he: ⋂ n:ℕ,U n=∅ := by
    ext x; simp only [mem_iInter, notMem_empty, iff_false]; intro p
    obtain ⟨n,w⟩:= exists_nat_gt (dist x o)
    exact p n (mem_ball.mpr w)
  have ht : Tendsto (fun n:ℕ=> (ν:Measure X) (U n)) atTop (𝓝 0):= by
    have hv : Antitone U:=fun m n p=> Set.compl_subset_compl.mpr (ball_subset_ball (by exact_mod_cast p))
    have hk:= tendsto_measure_iInter_atTop (μ:=(ν:Measure X)) (fun i:ℕ=> (show MeasurableSet (U i) from (isOpen_ball (x:=o) (ε:=(i:ℝ))).measurableSet.compl).nullMeasurableSet) hv (show ∃ i, (ν:Measure X) (U i)≠⊤ from ⟨0,measure_ne_top _ _⟩)
    rwa [he,measure_empty] at hk
  obtain ⟨i,p⟩ := (ht.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr u))).exists
  let A := Metric.closedBall o (i:ℝ)
  have hw:= FiniteMeasure.limsup_measure_closed_le_of_tendsto h (show IsClosed (U i) from isOpen_ball.isClosed_compl)
  refine ⟨A,isCompact_closedBall ..,?_⟩
  filter_upwards [eventually_lt_of_limsup_lt (hw.trans_lt p)] with n k
  exact ENNReal.toReal_lt_of_lt_ofReal ((measure_mono (Set.compl_subset_compl.mpr ball_subset_closedBall)).trans_lt k)

/-!
The variant in l:zoommat with varying, not necessarily continuous,
uniformly bounded tests. (Of course take them measurable. The limit test
must still be bounded continuous.)
-/
lemma bounded_borel_weak [Nonempty X](h:Tendsto μ atTop (𝓝 ν))
    (g:ℕ→X→ℂ)(p:∀ i, Measurable (g i)) (f:BoundedContinuousFunction X ℂ)
    (M:ℝ) (b:∀ i:ℕ,∀ x:X,‖g i x‖ ≤ M)
    (H:∀ A:Set X,IsCompact A → TendstoUniformlyOn g f atTop A) :
    Tendsto (fun i=> ∫ x, g i x ∂(μ i:Measure X)) atTop (𝓝 (∫ x, f x ∂(ν:Measure X))):= by
  let V(i):= g i-(f:X→ℂ)
  have he(i j:ℕ):Integrable (g i) (μ j:Measure X):=
    (integrable_const M).mono' (p i).aestronglyMeasurable (ae_of_all _ (b i))
  have hx : Tendsto (fun i=> ∫ x, V i x ∂(μ i:Measure X)) atTop (𝓝 0):= by
    rw [Metric.tendsto_nhds]
    intro ε e
    let C:=M+‖f‖+1
    have hM:0≤M:= le_trans (norm_nonneg _) (b 0 (Classical.arbitrary _))
    have hc:0<C:=by unfold C; positivity
    let t:ℝ:= ε/3
    have ht:0<t:=by unfold t; positivity
    obtain ⟨A,u,r⟩:=eventually_tight h (show 0<t/C from by positivity)
    let D:ℝ:= (ν.mass:ℝ)+1
    have hD:0<D:=by unfold D; positivity
    have hf:Tendsto (fun i=> ((μ i).mass:ℝ)) atTop (𝓝 (ν.mass:ℝ)):=tendsto_subtype_rng.mp h.mass
    filter_upwards [r,hf.eventually (ge_mem_nhds (lt_add_one _)),Metric.tendstoUniformlyOn_iff.mp (H A u) (t/D) (by positivity)] with i w s l
    have h₁: ‖∫ x in A,V i x ∂(μ i:Measure X)‖≤ t:= by
      have he: ((μ i:Measure X)).real A ≤ D:= le_trans (measureReal_mono (μ:=(μ i:Measure X)) (Set.subset_univ _)) s
      apply le_trans (norm_setIntegral_le_of_norm_le_const (measure_lt_top _ _) (f:=V i) (C:=t/D) ?_) ?_
      · intro x k
        change ‖g i x-f x‖≤ _
        simpa [← dist_eq_norm,dist_comm] using (l x k).le
      calc _ ≤ (t/D)*D := by gcongr
           _ = t:=by field_simp
    have h₂: ‖∫ x in Aᶜ,V i x ∂(μ i:Measure X)‖≤ t:= by
      apply le_trans (norm_setIntegral_le_of_norm_le_const (measure_lt_top _ _) (f:=V i) (C:=C) ?_) ?_
      · intro x k
        exact ((norm_sub_le (g i x) (f x)).trans (add_le_add (b i x) (f.norm_coe_le_norm x))).trans ((lt_add_one _).le)
      calc _ ≤ C*(t/C) := by gcongr
           _ = t:=by field_simp
    rw [dist_zero_right,←integral_add_compl u.measurableSet ((he i i).sub (f.integrable _))];
    apply (norm_add_le ..).trans_lt
    unfold t at *; linarith
  have ht:= hx.add ((FiniteMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp h f)
  rw [zero_add] at ht
  exact ht.congr fun i=>by
    rw [show (∫ x,V i x ∂(μ i:Measure X))=_ from integral_sub' (he i i) (f.integrable (μ i:Measure X))]; rw [sub_add_cancel]
end MeasureTheory.FiniteMeasure
set_option autoImplicit false
set_option maxHeartbeats 480000
set_option synthInstance.maxSize 28000
set_option linter.unusedSectionVars false
set_option maxRecDepth 3000
set_option quotPrecheck false
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia) -- tune
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
open Regis.Head Regis.Head.Brecht
namespace Spine
open scoped BoundedContinuousFunction
open Set
-- `crossCost` on functions on the halfspace. Still use positive measures
-- (Narrow) plus polarization, avoiding auxiliary choices of complex measure.
def crossCost (M:SixCoefficients→Cheer.Narrow)(f:↥TimeHalf→ℂ)(Z W:Lead.Clan) :=
  polar (fun z=>∫ w, f (clampTime w) ∂(M z:Measure E4)) Z W
variable (P:Spine)(x:P.Spectrum0 3) (c r:ℕ→ℕ)
lemma zoom_borel_budget
    (h:∀ z:SixCoefficients,Tendsto (fun i=> P.zoomMatrix x (c i) (r i) z) atTop (𝓝 (diagonalLimit z)))
    (Z W:Lead.Clan)(f:ℕ→↥TimeHalf→ℂ) (g:↥TimeHalf→ᵇ ℂ) (M:ℝ)
    (u:∀ i, Measurable (f i)) (q:∀ i p,‖f i p‖ ≤ M) (v:∀ T:Set ↥TimeHalf, IsCompact T → TendstoUniformlyOn f g atTop T):
    Tendsto (fun i=>crossCost (P.zoomMatrix x (c i) (r i)) (f i) Z W) atTop (𝓝 (if Z=W then ∫ w,onHalf g w ∂(promenade Z:Measure E4) else 0)):= by
  have he(T:Set E4)(h:IsCompact T) : TendstoUniformlyOn (fun i => f i ∘ clampTime) (onHalf g) atTop T:= by
    rw [Metric.tendstoUniformlyOn_iff]
    intro δ p
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp (v _ (h.image clampTime.continuous)) δ p] with n h
    exact fun x t=> h _ ⟨x,t,rfl⟩
  let V(z):=∫ w,onHalf g w ∂(diagonalLimit z: Measure E4)
  let L(i:ℕ)(z:SixCoefficients):=∫ w,f i (clampTime w) ∂(P.zoomMatrix x (c i) (r i) z:Measure E4)
  have p(z:SixCoefficients):Tendsto (fun i=>L i z) atTop (𝓝 (V z)):=FiniteMeasure.bounded_borel_weak (h z) (fun i=> f i ∘ clampTime) (fun i=> (u i).comp clampTime.continuous.measurable) _ M (fun i p=> q i _) he
  rw [← diagonal_only]
  exact ((((p _|>.sub (p _)).sub ((p _).const_mul _)).add ((p _).const_mul _)).div_const 4)
#print axioms zoom_borel_budget
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
