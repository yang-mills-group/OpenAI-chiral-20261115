import YM.CF.BPress.Port.Skin
import YM.CF.BPress.Weave.Astute
/-! Round trip prep. row-cap for travel, reach and frozen legs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Port
open Function Filter MeasureTheory LocalH Lattice Wilson RG Precision Grid Cube Bands Pressure Wealth Finset Weave Branch
open scoped Topology BigOperators Classical Matrix Matrix.Norms.Frobenius InnerProductSpace ENNReal
open SU Gauge Next.SectorChange
attribute [local instance] Gauge.frobInner
variable {s:Side}{B:BandWidth}(X:Bands s B)(D:ℕ)(F:Fare X)
lemma point_cost {I:Type*}[Fintype I](x:EuclideanSpace ℝ I)(i:I): |x i|≤ ‖x‖:=by
 apply (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mp; rw [EuclideanSpace.norm_sq_eq]; exact single_le_sum (f:=fun i=>‖x i‖^2) (fun i _=> sq_nonneg _) (mem_univ i)
def faith (D:ℕ): ℝ:=n_ang D+1
lemma pack_limit (x:Pack D){C:ℝ}(p:0≤ C)(h:∀ i, |x i|≤ C): ‖x‖≤ faith D*C:=by
 apply (sq_le_sq₀ (norm_nonneg _) (by unfold faith; positivity)).mp; rw [EuclideanSpace.norm_sq_eq]; refine le_trans (sum_le_sum (fun i (l:i∈ (univ:Finset (Stack D)))=> pow_le_pow_left₀ (norm_nonneg _) (h i) 2)) ?_; rw [sum_const,nsmul_eq_mul,card_univ,ticket_stack]; unfold faith; rw [mul_pow]; gcongr; nlinarith
-- maximal budget independent of interact tail, h hypothesis only where A transfers possibly nonzero from j.
variable {X F}
lemma ray_mobile (A:BEnd X)(w:RaySpace X) (x:X.Hcols) (t C:ℝ)(h:∀ i,∑ j, |rowM X A i j| ≤ C)(H:∀ i:Axon X,zSite X i=x→ ∀ j, rowM X A i j ≠ 0 → |w j| ≤ t)(p:0≤t)(u:0≤C) : ‖offer X (A w) x‖ ≤ faith B.D*(C*t):=by
 apply pack_limit B.D _ (by positivity); intro j; let i: Axon X:= ((x,j.1.1,j.1.2),j.2); rw [show offer X (A w) x j=_ from offer_hit X _ i, entry1]; refine (abs_sum_le_sum_abs ..).trans ((sum_le_sum (g:=fun j=> |rowM X A i j| * t) (fun j _=>?_)).trans ?_); rw [abs_mul]; by_cases h:rowM X A i j=0; rw [h]; simp; exact mul_le_mul_of_nonneg_left (H i rfl j h) (abs_nonneg _); rw [←sum_mul]; exact mul_le_mul_of_nonneg_right (h i) p
-- for inverse bound simply apply theorem to w MASK soft. Blink lines.
def wjson (F : BEnd X)(v:Fills X): Fills X:=offer X (F ((offer X).symm v))
lemma wjson_meas (F:BEnd X) : Measurable (wjson F):= (offer X).measurable.comp (F.continuous.measurable.comp (offer X).symm.measurable)
lemma wjson_r (F:BEnd X)(v:RaySpace X) : wjson F (offer X v)=offer X (F v):=by rw [wjson,MeasurableEquiv.symm_apply_apply]
lemma whole_he {S}(A:BEnd X)(p:Whole X S A 1)(v:RaySpace X)(i:X.Hcols)(u:i∈ S): offer X (A v) i=offer X v i:=by
 have he:= p.reads v; rw [one_smul] at he; rw [← if_pos (t:=offer X (A v) i) (e:=0) u,← ray_part,he,ray_part,if_pos u]
-- row_read w stash
lemma see_run {r:ℕ}(p:Connect X F r)(A B :Seal X.Hcols)(x:X.Hcols)(e:state (columnBall X x r) A B)(v w:Fills X)(u:∀ i∈columnBall X x r,v i=w i): wjson (F A) v x=wjson (F B) w x:=by
 ext j; let i : Axon X:=((x,j.1),j.2); change offer X _ x j=offer X _ x j; rw [show offer X (F A ((offer X).symm v)) x j= _ from offer_hit X _ i, show offer X _ x j= _ from offer_hit X (F B ((offer X).symm w)) i, entry1,entry1]; apply sum_congr rfl; intro j _; rw [p.sees A B i e j]; by_cases h:zSite X j∈ columnBall X x r; rw [offer_symm,offer_symm,u _ h]; rw [p.reaches B i j h,zero_mul,zero_mul]
lemma hue_small (p:Weave.Budget)(F:Fare X)(t y:ℝ)(u:Summer X F p.upper (p.low y) (p.reach y) (p.chunks y))(i:Seal X.Hcols)(v:Fills X)(b:X.Hcols)(hc:0≤t)(h:∀ j∈columnBall X b (p.reach y), ‖v j‖ ≤ t) : ‖wjson (F i) v b‖ ≤ faith B.D * (p.fore y B.D * t):= by
 refine ray_mobile (F i) _ b t _ (u.turnU_cap i) (fun j q l e=>?_ ) hc (show 0 ≤ _ from (mul_nonneg (grain_nn ..) u.hp.le)); rw [offer_symm]; exact (point_cost ..).trans (h (zSite X l) (q ▸ not_not.mp (fun f=> e (u.seen.reaches i j l f)))) -- tune dependent
end YM.CF.BPress.Port
