import YM.CF.Continuum.DockSmooth
import YM.CF.Continuum.CanYo
set_option autoImplicit false
noncomputable section
namespace YM.CF.Window
open Function Filter NormedSpace Lattice Wilson Laurent MeasureTheory RG Lat Cube RP Push.GridApprox Topology Scree Skye Fock Spire Scroll Tulip Girt Finset
open scoped Topology BigOperators Classical Matrix MatrixOrder Matrix.Norms.L2Operator Kronecker ENNReal
attribute [local instance] opCStarAlgebra
set_option maxHeartbeats 900000
set_option synthInstance.maxSize 24000
variable {n m B:Side}{P:Patch}{s:Axis}
local notation "G₅"=>SU.group
local notation "Γ"=>Config SU.group (More n)
lemma supportApprox (X:Pane n→ℂ)(u:ξTape s P n X): ∃ (c:ℝ)(F:ℕ→Pane n→ℂ),0<c ∧(∀ i,ξTape s P n (F i)∧ Continuous (F i)∧ ∀ x, ‖F i x‖≤c)∧ ∀ᵐ x∂prior G₅ (More n), Tendsto (fun i=> F i x) atTop (𝓝 (X x)):=by
 let K:= Tenant.leaks (buffered s P n); obtain ⟨k,g⟩:=u.cost; let v:=max 1 k; have hz:0<v:=zero_lt_one.trans_le (le_max_left ..); let y(i:ℕ):=(1/2:ℝ)^i; have htX:RG.Envelope X:=⟨u.borel,u.cost⟩; let μ:=prior G₅ (More n)
 have ht:Evenly.knows K X:=fun i j h=> u.localSites i j fun i p q=> h i (mem_filter.mpr ⟨mem_univ _,p,q⟩); choose H hc hm hg hw f using fun i:ℕ=>Evenly.fund_Y K ht u.gauge htX _ hz (fun i=>(g i).trans (le_max_right ..)) (y i) (pow_pos (by norm_num) _)
 have he:Tendsto (fun i=>eLpNorm (H i-X) 1 μ) atTop (𝓝 0) :=by
    let W(i:ℕ):= H i-X
    have hv:Tendsto (fun i=> ∫ x,‖W i x‖∂ μ) atTop (𝓝 0):= squeeze_zero (fun i=>integral_nonneg (fun x=>norm_nonneg _)) (g:=y) (fun i=> by change (∫ x,‖H i x-X x‖∂ μ)≤_; simp_rw [norm_sub_rev (H i _)]; exact f i) (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
    apply Tendsto.congr' _ (show Tendsto (fun i=>ENNReal.ofReal (∫ x,‖W i x‖ ∂ μ)) atTop (𝓝 0) from (by simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hv))
    apply Eventually.of_forall; intro i; change ENNReal.ofReal _= eLpNorm (W i) 1 μ; rw [eLpNorm_one_eq_lintegral_enorm]; exact ofReal_integral_norm_eq_lintegral_enorm (f:=W i) (((Envelope.compactC (hc i)).subC htX).integrableC μ)
 obtain ⟨f',_,d⟩:= (tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero (fun i=>(hc i).aestronglyMeasurable) u.borel.aestronglyMeasurable he).exists_seq_tendsto_ae
 refine ⟨v,H ∘ f',hz,fun i=>⟨⟨hg _,(hc _).measurable, fun a b e=>?_ , ⟨v,hw _⟩⟩,hc _,hw _⟩,d⟩; exact hm _ _ _ (fun t h=> e t (mem_filter.mp h).2.1 (mem_filter.mp h).2.2)
variable (Y: Orbit n → Phys n)(e:Integrable Y (city _))(A B':ℕ→Pane n→ℂ)(a b: Pane n→ℂ)(v:ℝ)(ha:0<v)(hk:∀ j, Envelope (A j))(hl:∀ j, Envelope (B' j))(g:∀ j x,‖A j x‖≤v)(h:∀ j x,‖B' j x‖≤v)
variable (vp: ∀ᵐ x∂prior SU.group (More n), Tendsto (fun i=> A i x) atTop (𝓝 (a x))) (vq: ∀ᵐ x∂prior SU.group (More n), Tendsto (fun i=> B' i x) atTop (𝓝 (b x)))
include hk hl g h e vp vq ha
lemma chipPass (s:Axis): Tendsto (fun j=>moment Y (bosonic n ((θBack s (A j))*B' j))) atTop (𝓝 (moment Y (bosonic n ((θBack s a)*b)))):=by
 let p:= fun i:Orbit n=> beamL _ (Y i); have hz:Integrable p (city _):=(beamL _).integrable_comp e; let f(x:Orbit n):= pull (Signed.mirror s) 0 x.1; let u:= (show MeasurePreserving Prod.fst (city n) (prior G₅ (More n)) from measurePreserving_fst); have hp:MeasurePreserving f (city n) (prior G₅ (More n)):= (prior_pull (Signed.mirror s) 0).comp u
 simp_rw [boseMoment]
 apply tendsto_integral_filter_of_dominated_convergence (fun x=>‖p x‖*(v*v)) _ _ (hz.norm.mul_const _) _
 · refine Eventually.of_forall fun i=>?_ ; let AΞ: Pane n→ℂ:= θBack s (A i)*B' i; have he:Envelope AΞ:=(θ_back_env s (hk i)).mulC (hl i); exact hz.aestronglyMeasurable.mul (he.meas.comp measurable_fst).aestronglyMeasurable
 · refine Eventually.of_forall fun i=> Eventually.of_forall fun x=>?_ ; rw [norm_mul]; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); rw [Pi.mul_apply,norm_mul]; exact mul_le_mul (by unfold θBack; simp only [comp_apply,norm_star]; apply g) (h i _) (norm_nonneg _) ha.le
 filter_upwards [u.quasiMeasurePreserving.ae vq,hp.quasiMeasurePreserving.ae vp] with x q k; exact tendsto_const_nhds.mul (k.star.mul q) -- annotation?
end YM.CF.Window
