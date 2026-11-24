import YM.CF.Sods.Pail
/-! # Almost-sure escape from discriminants. Does not need coordinates for Haar. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 440000
noncomputable section
namespace YM.CF.Strata
open Function Filter Finset MeasureTheory Metric SU Sods Kea
open scoped Topology ComplexOrder Matrix Matrix.Norms.L2Operator BigOperators
attribute [local instance] opCStarAlgebra
local notation "μ"=> SU.group.probHaar
section
variable(f: ℝ → ℂ)
lemma singer(h: AnalyticOnNhd ℝ f Set.univ)(p:∃ x,f x≠0):∀ᵐ i:ℝ, f i≠0:=by
 let S: Set ℝ:= {i| f i=0}; obtain ⟨x,hx⟩:=p
 haveI:DiscreteTopology S:= discreteTopology_subtype_iff.mpr (fun y hy=>by
    refine disjoint_iff.mp (disjoint_principal_right.mpr (show Sᶜ ∈ 𝓝[≠] y from ?_)); exact not_frequently.mp (fun k=> hx (congrFun (h.eq_of_frequently_eq (g:=fun _=>0) analyticOnNhd_const (z₀:=y) k) x))) -- tune
 have p:= Set.Countable.measure_zero (s:=S) (TopologicalSpace.separableSpace_iff_countable.1 inferInstance) volume; exact ae_iff.mpr (by simpa only [not_not] using p)
end
section
-- one direction parameter chosen separately for every needed neighbourhood
variable(f:E → ℂ)(h:Continuous f)(P:∀ U:E, ∃ g:ℝ→E,Continuous g ∧ g 0=1 ∧ (∀ U, AnalyticOnNhd ℝ (fun x=>f (U*g x)) Set.univ) ∧ f (U*g 1) ≠ 0)
include h P
lemma haze (U:E) : ∃ S:Set E,S∈𝓝 U∧ ∀ᵐ W∂μ,W∈S→ f W≠0:=by
 obtain ⟨g,v,p,k,t⟩:= P U
 let T: Set E:= {t|f (t*g 1)≠0}; have ht:IsOpen T:= isOpen_ne_fun (by fun_prop) continuous_const -- tune redex
 have hm:MeasurableSet {z:E ×ℝ| z.1∈T→ f (z.1*g z.2)≠0}:=by
    simp_rw [imp_iff_not_or]; exact (measurable_fst ht.measurableSet.compl).union (isOpen_ne_fun (by fun_prop) continuous_const).measurableSet
 obtain ⟨r,g₁,d⟩:= Metric.eventually_nhds_iff.mp (show ∀ᶠ y:E ×ℝ in 𝓝 (U,0), y.1*(g y.2)⁻¹ ∈ T from (show Continuous (fun y:E× ℝ=> y.1*(g y.2)⁻¹) from by fun_prop).continuousAt.eventually (ht.mem_nhds (by dsimp only; rw [p,inv_one,mul_one]; exact t))) -- tune
 have he:∀ᵐ y:ℝ,∀ᵐ x∂μ,x∈ T→ f (x*g y)≠0:=Measure.ae_ae_comm hm |>.mp (Eventually.of_forall (fun x=> by by_cases p:x∈T; exact (singer _ (k x) ⟨1,p⟩).mono (fun x p _=>p); exact Eventually.of_forall fun _ h=>False.elim (p h)))
 obtain ⟨y,W,H⟩:= ((frequently_ae_mem_iff.mpr (isOpen_ball.measure_pos volume ⟨(0:ℝ),mem_ball_self g₁⟩).ne').and_eventually he).exists
 let φ(x:E):= x*(g y)⁻¹; refine ⟨Metric.ball U r,ball_mem_nhds U g₁, ((measurePreserving_mul_right (μ) ((g y)⁻¹)).quasiMeasurePreserving.ae H).mono fun x hx u=>?_⟩; have he: f (φ x*g y)≠0:=hx (d (y:=(x,y)) (by rw [Prod.dist_eq]; exact max_lt (Metric.mem_ball.mp u) (Metric.mem_ball.mp W))); unfold φ at he; rwa [inv_mul_cancel_right] at he
lemma payout : ∀ᵐ x∂μ,f x≠0:=by
 choose S ht e using haze f h P; obtain ⟨I,t,p⟩:=isCompact_univ.elim_nhds_subcover S fun i _=> ht i; filter_upwards [(eventually_all_finset I).mpr fun i p=> e i] with x hx; obtain ⟨j,g,t⟩:= Set.mem_iUnion₂.mp (p (Set.mem_univ x)); exact hx j g t
end
lemma distant(x y:E):dist x y= ‖fund x-fund y‖:= dist_eq_norm (fund x) (fund y)
def chargeW(x:TF)(t:ℝ):TF:= ⟨t • x.val,by simp_rw [Pi.smul_apply,← smul_sum, x.property, smul_zero]⟩
def fly(x:TF)(W:E)(t:ℝ):E:= W*waveG (chargeW x t)*W⁻¹
lemma pay0(x:TF)(W:E): fly x W 0=1:=by rw [fly,show waveG _=1 from ?_,mul_one,mul_inv_cancel]; apply SU.group.mat_injective; change Matrix.diagonal _= (1:Op SU.F); simp [chargeW,Kea.phase_z]
lemma payN(x:TF)(W:E): fund (fly x W 1)=twist W.val (Matrix.diagonal (pw∘x.val)):=by rw [fly,fund_mul,fund_mul,wave_id,show chargeW x 1=x from Subtype.ext (one_smul _ _),twist_formula]; rfl
lemma salute (x:TF)(W:E) : Continuous (fly x W):=by
 have he: Continuous fun t:ℝ=>waveG (chargeW x t):= continuous_induced_rng.mpr (continuous_induced_rng.mpr ?_); swap
 · change Continuous fun t:ℝ=> Matrix.diagonal (fun i=> pw (t*x.val i)); apply continuous_matrix; intro i j; by_cases p:i=j; · subst j; unfold pw BZ.phase; simp only [Matrix.diagonal_apply_eq]; fun_prop
   simp_rw [Matrix.diagonal_apply_ne _ p]; exact continuous_const
 unfold fly; fun_prop
variable(f:E → ℂ)(h:Continuous f)(T:∀ x:TF,∀ W U:E, AnalyticOnNhd ℝ (fun z=> f (U*fly x W z)) Set.univ)
open scoped Classical
-- We actually have arbitrarily-good density of flight endpoints. no use topological path connected SU.
lemma nimbus (U:E) (S:Set E)(hr:S∈𝓝 U):∃ x:TF,∃ W:E, fly x W 1∈S:=by
 obtain ⟨ε,v,z⟩:= Metric.mem_nhds_iff.mp hr
 obtain ⟨r,A,b,g,t,u,e⟩:= accord (E:=SU.F) (I:=Bool)
 let k:=min 1 ((ε/2)/A); have hx: 0<k:=lt_min one_pos (by positivity); let φ(_:Bool):= U.val; obtain ⟨y,p,Q⟩:= e k hx (min_le_left ..) φ (fun _=>U.property) (fun _ _=>by unfold Switch φ; rw [sub_self,norm_zero]; positivity); obtain ⟨D,d,h,H⟩:= Q true; let x:TF:=⟨D,d⟩; let W:E:= ⟨y,p⟩; refine ⟨x,W,z (Metric.mem_ball.mpr ?_)⟩; rw [dist_comm,distant,payN]; exact H.trans_lt (lt_of_le_of_lt (mul_le_mul_of_nonneg_left (min_le_right ..) t.le) (by rw [mul_div_cancel₀ _ t.ne']; exact half_lt_self v))
include h T
lemma tent (k:∃ x,f x≠0):∀ᵐ x∂μ,f x≠0:=by
 obtain ⟨x,p⟩:= k; apply payout f h; intro U; let y:=U⁻¹*x; obtain ⟨t,W,L⟩:= nimbus y {z|f (U*z)≠0} ((isOpen_ne_fun (by fun_prop) continuous_const).mem_nhds (by change f (U*y)≠0; unfold y; rwa [mul_inv_cancel_left])); exact ⟨fly t W,salute t W,pay0 t W,T t W,L⟩
#print axioms tent
end YM.CF.Strata
