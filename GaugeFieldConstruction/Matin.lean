import GaugeFieldConstruction.Canter
/- Cost continued across cap. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 60000
noncomputable section
namespace YM.CF.XGarden
open Function Filter Metric Lattice Wilson Precision Finset MeasureTheory Gauge RG WilsonStartup Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.Frobenius Classical
open Buffered.Region FlightFlux Work Tensor
open Fock Tulip Lat Spire Phase Cube
open Jet
variable {E W F:Type} [NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F][NormedAddCommGroup W][NormedSpace ℝ W] {K d v t r u c:ℝ}{j k:ℕ}{n:Side}{G:Gauge}{p:BudgetPoint}
namespace Shield
open F03
-- universal supply from local support receipts. signs via Prism.
section
variable (o: Seat n)(U:Pane n) {X:Support (More n)}{V:Pane n→ E}
open Prism
local notation "GS"=> SU.group
open TableF.Lenten.Housing
open TableF
private lemma ω_pi(Y:Seat n)(p:BudgetPoint)(e:Edge (Seat n)):let g:ℝ:=(1+(separation e.1 Y:ℝ))^p.power
 1≤g := one_le_pow₀ (le_add_of_nonneg_right (Nat.cast_nonneg _))
private abbrev easeW (x:Seat n)(p:BudgetPoint)(e:Edge (Seat n)):ℝ:= p.threshold*(1+(separation e.1 x:ℝ))^p.power
lemma easeB (p:BudgetPoint)(i:tangD n)(e:Edge (Seat n)): trunk p o i e=easeW o p e • i e:=rfl
lemma easeC (p:BudgetPoint)(i:tangD n)(e:Edge (Seat n)): silo p o i e=(easeW o p e)⁻¹ • i e:=rfl
lemma milk_X (h: Signs p o (V∘ increment U) c): Allows p.order (V ∘ solo p.threshold U) 0 c:=by
 let H:=V∘solo p.threshold U; let Q:tangD n →L[ℝ] tangD n:= (silo p o) ∘L (p.threshold • ContinuousLinearMap.id ℝ (tangD n))
 have hp:‖Q‖ ≤1:=by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one; intro i; rw [one_mul]; apply (pi_norm_le_iff_of_nonneg (norm_nonneg i)).mpr; intro e; change ‖silo p o (p.threshold • i) e‖≤_; rw [easeC,Pi.smul_apply,norm_smul,norm_smul]; have hh:=p.threshold_pos; have ht:=ω_pi o p e; let w:= easeW o p e; have he:p.threshold≤easeW o p e:=by unfold easeW; exact le_mul_of_one_le_right hh.le ht
    rw [Real.norm_of_nonneg hh.le, Real.norm_of_nonneg (inv_pos.mpr (hh.trans_le he)).le, inv_mul_le_iff₀ (hh.trans_le he)]; exact mul_le_mul he (norm_le_pi_norm i e) (norm_nonneg _) (hh.trans_le he).le
 refine (comps Q (f:=(V ∘ increment U) ∘ trunk p o) ?_ hp).germ (Eventually.of_forall (fun i=>?_))
 · rw [map_zero]; exact skin h
 change V (increment U (trunk p o (silo p o (p.threshold • i))))= _; rw [trench]; rfl
lemma halo_price (V₀:LocalOn X V) (s:Allows p.order (V ∘ solo p.threshold U) 0 c)(u:X ⊆ halo j ({o}:Support (More n))): Signs p o (V ∘ increment U) (c*((1+(j:ℝ))^p.power)^p.order):=by
 let t:= p.threshold; have ht:=p.threshold_pos; let Q:=V∘ solo t U; let R:= Keeper GS X; let T:= trunk p o; let L:tangD n→L[ℝ]tangD n:= t⁻¹ • R ∘L T; let C:ℝ:=(1+(j:ℝ))^p.power
 have hc:1≤C:=one_le_pow₀ (le_add_of_nonneg_right (Nat.cast_nonneg _))
 have hL:‖L‖≤C:=by
    apply ContinuousLinearMap.opNorm_le_bound _ (zero_le_one.trans hc); intro i; change ‖t⁻¹ • R (T i)‖ ≤_; rw [norm_smul,Real.norm_of_nonneg (inv_pos.mpr ht).le,inv_mul_le_iff₀ ht]; have he:0≤ t*(C*‖i‖):=mul_nonneg ht.le (mul_nonneg (zero_le_one.trans hc) (norm_nonneg _)); apply keeper_buy he _; intro e w; change ‖trunk p o i e‖ ≤_; have hh:separation e.1 o≤j:=by obtain ⟨z,q,h⟩:= halo_spec.mp (u w.1); rw [mem_singleton.mp q,separation_comm] at h; exact h
    rw [easeB,norm_smul]; unfold easeW; rw [Real.norm_of_nonneg (by positivity),mul_assoc]; apply mul_le_mul_of_nonneg_left _ ht.le; exact mul_le_mul (pow_le_pow_left₀ (by positivity) (add_le_add_right (by exact_mod_cast hh) _) _) (norm_le_pi_norm _ _) (norm_nonneg _) (zero_le_one.trans hc)
 have he:(V∘ increment U) ∘ trunk p o=Q ∘ L:=funext fun i=>by
    change V (increment U (T i))=V (increment U (t • (t⁻¹ • R (T i)))); rw [smul_inv_smul₀ p.threshold_pos.ne']; exact (stays (U:=U) V₀ (T i)).symm
 apply Prism.skills; rw [he]; refine ⟨((show ContDiffAt ℝ p.order Q (L 0) from (map_zero L).symm ▸ s.smooth).comp _ L.contDiff.contDiffAt),fun i w=> ?_⟩
 rw [Next.Foundations.jets_linear L (s.smooth.of_le (Nat.cast_le.mpr w))]; apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le ..).trans; rw [Finset.prod_const,card_univ,Fintype.card_fin]; exact mul_le_mul (s.norm_le i w) ((pow_le_pow_left₀ (norm_nonneg _) hL _).trans (pow_le_pow_right₀ hc w)) (pow_nonneg (norm_nonneg _) _) s.nonneg
omit U
lemma milk_H (h:Haw p o X V c)(u:Pane n)(p':pingS p.threshold X u): Allows p.order (V ∘ solo p.threshold u) 0 c:= milk_X o u (h.rends u p')
lemma milk_turn (u:LocalOn X V)(t:Continuous V)(p':∀ U: Pane n,pingS p.threshold X U →Allows p.order (V ∘ solo p.threshold U) 0 c)(z:X⊆Lenten.Pax o): Haw p o X V (c*((1+(24:ℝ))^p.power)^p.order):=⟨u,t,fun i h=>halo_price o i u (p' i h) z⟩
end
open Next.SectorChange.Motion
lemma hueGauge(U:Config G n)(g:Site n→G.El)(V:Config G n→ E)(p: GaugeInvariant V)(h:∀ U, ContDiffAt ℝ ω (V ∘ increment U) 0): hue_T V (gauge g U) ∘L swing g=hue_T V U:=by
 let A: Config G n:=Lattice.gauge g U; let M:=V ∘ increment A; let L:=swing (G:=G) g; have hp:M ∘ L=V ∘ increment U:=funext fun i=>by change V (increment A (L i))=_; rw [show increment A (L i)=_ from swing_increment g U i]; apply p
 change fderiv ℝ M 0 ∘L L=fderiv ℝ (V∘ increment U) 0; rw [←hp,fderiv_comp _ (by rw [L.map_zero]; exact (h _).differentiableAt (by simp)) (L.differentiableAt), L.fderiv,L.map_zero]
lemma hue_loc{A: Support n}(V:Config G n→ E)(p:LocalOn A V): LocalOn A (hue_T V):=by
 intro i j t; unfold hue_T; rw [show V ∘ increment i=V ∘ increment j from funext fun v=>p _ _ fun e u v'=> congrArg (fun y=> G.lieExp (v e)* y) (t e u v')]
end Shield
end YM.CF.XGarden
end
