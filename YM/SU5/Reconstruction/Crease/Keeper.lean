import YM.SU5.Reconstruction.Crease.Autumn
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option quotPrecheck false
noncomputable section
namespace YM.BridgeClub.Club
open Function Set Filter MeasureTheory Spectral Analysis Metric ContinuousLinearMap Anvil Picket CrossedFrame Opera Moth
open scoped BigOperators Topology InnerProductSpace ComplexOrder NNReal ENNReal Complex Classical
variable {H K D: Hilbert}(C:Clasp K H D)
local notation "L"=> C.Left
local notation "R"=> (1-C.angle)
local notation "P"=> C.angle
local notation "U"=>C.Cabin
noncomputable def backfill (x:H.Op):= C.Left.conjStarAlgEquiv.symm x
local notation "Φ"=> backfill C
lemma surplus (x:H.Op)(v:K): x (L v)= L (Φ x v):= by
 rw [← show (L).conjStarAlgEquiv (Φ x)=x from (L).conjStarAlgEquiv.apply_symm_apply x]; rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, LinearIsometryEquiv.symm_apply_apply, show (Φ ((L).conjStarAlgEquiv (Φ x)))=Φ x from (L).conjStarAlgEquiv.symm_apply_apply _]
lemma pearlA (x:K): C.plume (L x)= L (P x)∧ C.shadow (L x)=L (R x):=by
 rw [Clasp.shadow,sub_apply,C.portAngle,LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,LinearIsometryEquiv.symm_apply_apply]; exact ⟨rfl,(map_sub (L) x (P x)).symm⟩
noncomputable def pond (t:ℝ)(A:H.Op) : H.Op:= C.cLeft t * A * C.cLeft (-t)
lemma cBill (t:ℝ)(x:H):‖C.cLeft t x‖=‖x‖:=by rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ,_root_.YM.CrossedFrame.Pays.ordinary (C.left_credentials t).2.2]
lemma pondCost (A:H.Op)(t:ℝ)(x y:H): ‖inner ℂ x (pond C t A y)‖ ≤ ‖x‖*(‖A‖*‖y‖):= by
 unfold pond; rw [mul_apply_eq_comp, mul_apply_eq_comp]; apply le_trans (norm_inner_le_norm ..); rw [cBill]; exact mul_le_mul_of_nonneg_left (by simpa only [cBill C (-t) y] using A.le_opNorm (C.cLeft (-t) y)) (norm_nonneg x) -- simp loop!
lemma algae (t:ℝ)(A:H.Op)(x y:H): inner ℂ x (pond C t A y)=inner ℂ (C.cLeft (-t) x) (A (C.cLeft (-t) y)):= by unfold pond; rw [mul_apply_eq_comp,mul_apply_eq_comp,← adjoint_inner_left, show adjoint (C.cLeft t)=C.cLeft (-t) from (C.left_credentials t).2.1]
@[fun_prop] lemma pondPaddle (A:H.Op)(x y:H): Continuous fun t=> inner ℂ x (pond C t A y):= by simp_rw [algae]; exact ((C.scheduleLeft x).comp continuous_neg).inner (A.continuous.comp ((C.scheduleLeft y).comp continuous_neg))
variable (θ:ℝ)(p:θ∈ twilight)
include p
lemma lake (A:H.Op)(x y:H): Integrable (fun t=> cup θ t * inner ℂ x (pond C t A y)):= cup_prices _ p _ (pondPaddle ..) _ fun t=> pondCost C _ _ _ _
-- statement continuity via sequence limit. precisely conjugator.
lemma brook (A:H.Op){x y:H}{u v: ℕ→H}(h:Tendsto u atTop (𝓝 x))(k:Tendsto v atTop (𝓝 y)) : Tendsto (fun n=> ∫ t:ℝ,cup θ t*inner ℂ (u n) (pond C t A (v n))) atTop (𝓝 (∫ t:ℝ,cup θ t*inner ℂ x (pond C t A y))):= by
 obtain ⟨M,a⟩:= h.norm.bddAbove_range; obtain ⟨N,b⟩:=k.norm.bddAbove_range; have he(i:ℕ):‖u i‖≤ M:= a (mem_range_self i); have hv(i:ℕ):‖v i‖≤N:= b (mem_range_self i); have hx:0≤M:= le_trans (norm_nonneg _) (he 0)
 apply tendsto_integral_of_dominated_convergence (fun t=> M*(‖A‖*N)*‖cup θ t‖) (fun i=> (lake C θ p A _ _).1) ((redeem θ p).norm.const_mul _) (fun n=> Eventually.of_forall (fun r=>?_)) (Eventually.of_forall (fun t=>tendsto_const_nhds.mul (h.inner ((pond C t A).continuous.continuousAt.tendsto.comp k))))
 rw [norm_mul,mul_comm ‖cup θ r‖]; refine mul_le_mul_of_nonneg_right ((pondCost ..).trans ?_) (norm_nonneg _); gcongr; exact he _; exact hv _
variable {C}{M:Net H}{Ω:H}{Γ:Set H.Op}{J:Flash H}(h:Club C J M Ω Γ)
-- bicomm stage later
lemma bankDense : DenseRange (BasePort C):= by
  apply DenseRange.comp (g:=C.plume) (polar_dense C.plume_self C.plume_inj) (polar_dense C.shadow_self C.shadow_inj) C.plume.continuous
include h
lemma brush {A B:H.Op}(t:A∈M.commutant)(u:B∈M)(v:WPort C Ω (Opera.spin θ) A B)(x y:H) :
 (∫ r:ℝ,cup θ r * inner ℂ x (pond C r A y))= inner ℂ x (J.shade (star B) y):= by
 let Y:=J.shade (star B); have hp(p' q:K):inner ℂ (P (R p')) (Φ A (P (R q)))=inner ℂ (R (R p')) (Φ Y (P (P q))) +Opera.spin θ*inner ℂ (P (P p')) (Φ Y (R (R q))):=by
     have he:= h.torque t u v (L p') (L q); simp only [(pearlA C _).1,(pearlA C _).2, surplus C A,surplus C (J.shade _), LinearIsometryEquiv.inner_map_map] at he; exact he
 have hv (p' q:H): (∫ r:ℝ,cup θ r * inner ℂ (BasePort C p') (pond C r A (BasePort C q)))=inner ℂ (BasePort C p') (Y (BasePort C q)):= by
   obtain ⟨x,rfl⟩:= C.Left.surjective p'; obtain ⟨y,rfl⟩:=C.Left.surjective q; unfold BasePort; simp only [mul_apply_eq_comp,(pearlA C _).1,(pearlA C _).2];
   have hx(r:ℝ):Φ (pond C r A)=C.Cabin r* Φ A * C.Cabin (-r):=by unfold pond Clasp.cLeft backfill; rw [map_mul,map_mul,StarAlgEquiv.symm_apply_apply, StarAlgEquiv.symm_apply_apply]
   simp_rw [surplus C, hx, LinearIsometryEquiv.inner_map_map]; exact transit C θ p (Φ Y) x y hp
 obtain ⟨X,c,d⟩:= mem_closure_iff_seq_limit.mp (bankDense θ p (C:=C) x); obtain ⟨Z,a,e⟩:= mem_closure_iff_seq_limit.mp (bankDense θ p (C:=C) y); choose Ff hF using c; choose FF hh using a; exact tendsto_nhds_unique_of_eventuallyEq (brook C θ p A d e) (d.inner (Y.continuous.continuousAt.tendsto.comp e)) (Eventually.of_forall fun i=> by change (∫ r:ℝ,cup θ r * inner ℂ (X i) (pond C r A (Z i)))=inner ℂ (X i) (Y (Z i)); rw [←hh i, ← hF i]; exact hv (Ff i) (FF i))
end YM.BridgeClub.Club
