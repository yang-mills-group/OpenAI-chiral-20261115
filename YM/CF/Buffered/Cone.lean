import YM.CF.Buffered.LastMile

/-!
# Rate in the cone

Derive `pc-low` CapP side (stop 0) actually uniformly on m⁵≤n, with the
two inputs and no further compatibility requirements as n increases. And
give uniform transfer even on the moving cone's sup unit ball of Borel
marks at level zero. (Not a boundedness/compactness statement, not
asserting limits for varying tests.) Again, donor lower not proved here.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 540000
noncomputable section
namespace YM.CF.Buffered
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory Mesa ProbabilityTheory Peaks Drapes Rush Precision Tree Push.SectorMeasure Next.SectorChange Tulip Jet Tap Laic Dial Paige Vault Pec Skye Pastry Cascade Phase Brace Scree RG Spark RP Gloss Branch Reflect Window Vale Girt
open Py (Vestal Cape)
open Reed (Fine)
open Advance Heat Burn
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
namespace Burn
private lemma boundP (b r : ℕ) : ∀ᶠ n in atTop, ∀ m:ℕ, m^5≤n → r*m^4 ≤ depth b n := by
  filter_upwards [eventually_ge_atTop ((4*b+8):ℕ),tend_depth b|>.eventually (eventually_ge_atTop (r*(4*r)^4)),tend_stage.eventually (eventually_ge_atTop 2)] with n p u h
  intro m t; by_cases a:m≤4*r
  · exact le_trans (by gcongr) u
  have he : 2*stage n ≤ n := by
    apply Nat.le_trans _ ((stage_iff ..).1 le_rfl); exact le_trans (b:=stage n ^ 2) (by nlinarith) (pow_le_pow_right₀ (by omega) (by omega))
  have hp : 4*(r*m^4) ≤ n:= le_trans (by rw [pow_succ m]; nlinarith only [Nat.mul_le_mul_left (m^4) (le_of_lt (Nat.lt_of_not_ge a))]) t
  unfold depth; omega
lemma uniform (b : ℕ) (M : ℝ) {z : ℝ} (u : 0<z) : ∀ᶠ n in atTop, ∀ m:ℕ, m^5≤n → bill m n b M ≤ z := by
  have h:0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨r,p⟩:= exists_nat_ge (4*M/Real.log 2)
  have hp:= (div_le_iff₀ h).1 p
  let T := fun n => Real.exp (-(Real.log 2/4*(depth b n :ℝ)))
  have ht : Tendsto T atTop (𝓝 0) := Real.tendsto_exp_atBot.comp <| tendsto_neg_atTop_atBot.comp <| ((tendsto_natCast_atTop_atTop (R:=ℝ)).comp (tend_depth b)).const_mul_atTop (by positivity : 0<Real.log 2/4)
  filter_upwards [ht.eventually (gt_mem_nhds u), boundP b r] with n t w
  intro m k; have he : (r:ℝ) * (m:ℝ)^4 ≤ depth b n := by exact_mod_cast (w m k)
  refine le_trans ?_ t.le; unfold bill T; rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2),← Real.exp_add]; apply Real.exp_le_exp.mpr
  nlinarith only [mul_le_mul_of_nonneg_right hp (by positivity :(0:ℝ) ≤ (m:ℝ)^4),mul_le_mul_of_nonneg_left he h.le]
lemma bill_div (n m b : ℕ) (M C : ℝ) : bill m n b M / presrec m C = bill m n b (M+C) := by unfold bill presrec; rw [mul_div_assoc,←Real.exp_sub]; ring_nf
end Burn
variable {K : Calibration} (P : Histories K)
/-- comparison of pressures using the given hint, uniform over included
**prescribed** torus list entries with stopping height in the cone. -/
lemma pc_low : ∀ᶠ n in atTop, ∀ m : Side, K.Allowed m n → presrec m.val P.c' /2 ≤ ‖vac0 K.P (P.sharp m n 0) (P.loom m 0)‖ := by
 filter_upwards [P.paid,eventually_gt_atTop 0,Burn.uniform K.b₀ (P.m'+P.c') (by norm_num:(0:ℝ)<1/2)] with n t H w
 intro m a; obtain ⟨s,d,l⟩:= t m a; let h:=s.atComparison H d l _ _ rfl rfl
 apply transfer_lower K.P _ _ _ (Granted.paid s.cap_grant 0 H).2 (Granted.paid s.cap_grant 0 H).1 (Granted.paid s.warm_grant 0 H).1 d _ l
 have he:= w m.val a.2.2; rw [←bill_div,div_le_iff₀ (show 0<presrec m.val P.c' from Real.exp_pos _)] at he; linarith

-- even if studying changing tests: no claim of positivity in the sharp on such a sequence; this also yields differences shrink at fixed support by just the cost b.
lemma cone_ratio {v : ℝ} (u : 0 < v) : ∀ᶠ n in atTop, ∀ m : Side, K.Allowed m n → ∀ F : Mark (K.c m), Envelope F → ∀ b:ℝ, (∀ i, ‖F i‖ ≤ b) → ‖P.cap n F - atZero K.P (P.warm m n) (P.loom m) F‖ ≤ v*b := by
 filter_upwards [P.paid,eventually_gt_atTop 0,Burn.uniform K.b₀ (P.m'+P.c') (by norm_num:(0:ℝ)<1/2),Burn.uniform K.b₀ (P.m'+P.c') (by linarith :0<v/3),Burn.uniform K.b₀ ((P.m'+P.c') + (Burn.trial₀ K + P.c')) (by linarith :0<v/3)] with n t H w g G
 intro m a F f b θ
 obtain ⟨s,d,l⟩:= t m a
 obtain ⟨e,tz⟩:= Granted.paid s.cap_grant 0 H
 let x := num0 K.P (P.sharp m n 0) (P.loom m 0) F; let L := vac0 K.P (P.sharp m n 0) (P.loom m 0)
 let S:= Burn.trial₀ K * (m.val:ℝ)^4; let Z:= presrec m.val P.c'
 let K' := bill m.val n K.b₀ P.m'
 have h : 0<Z := Real.exp_pos _
 have hp := w m.val a.2.2; rw [←bill_div] at hp; have hx := (div_le_iff₀ h).1 hp
 have hh:K' ≤ Z/2:= le_trans hx (by rw [one_div_mul_eq_div ..])
 have hr:= (Granted.paid s.warm_grant 0 H).1; have hL:Z/2 ≤ ‖L‖:= transfer_lower _ _ _ _ tz e hr d Z l hh
 have hz : 0 ≤ b:= (norm_nonneg (F (1,1))).trans (θ _)
 have hz' : ‖x/L‖ ≤ b*(2*Real.exp S/Z):=by
   have he': ‖x‖ ≤ b*Real.exp S := by unfold x num0 markedRead; apply le_trans (norm_integral_le_of_norm_le_const (C:=b*Real.exp S) (Eventually.of_forall fun i=> (mark_bound ..).trans (mul_le_mul (θ _) (Burn.sharp_extensive s i) (norm_nonneg _) hz))) (by simp)
   rw [norm_div]; refine le_trans (div_le_div₀ (by positivity) he' (half_pos h) hL) ?_; apply le_of_eq; ring
 unfold Histories.cap atZero; rw [←same_ratio, ←same_ratio]
 apply (transfer_ratio K.P _ _ _ tz e hr d h l hh F f θ hz').trans
 let C := K'/Z; have ht:C=bill m.val n K.b₀ (P.m'+P.c'):=bill_div ..
 have hQ : C≤v/3:= ht ▸ g m.val a.2.2
 have hs: Real.exp S/Z*C ≤ v/3:= by
    rw [ht]; apply (G m.val a.2.2).trans'; apply le_of_eq; unfold Burn.bill Z presrec S; rw [←Real.exp_sub]; rw [mul_left_comm,←Real.exp_add]; ring_nf
 change (b+b*(2*Real.exp S/Z))*K'/Z ≤ _; calc
    _ = b*C+2*b*(Real.exp S/Z*C) := by unfold C; ring
    _ ≤ b*(v/3) + 2*b*(v/3) := add_le_add (by gcongr) (mul_le_mul_of_nonneg_left hs (by positivity))
    _ = _ := by ring

lemma all_ratio_fixed {m : Side} (h : K.takes m) (F : Mark (K.c m)) (hp : Envelope F) :
 Tendsto (fun n=> P.cap n F - atZero K.P (P.warm m n) (P.loom m) F) atTop (𝓝 0) := by
 obtain ⟨b,L⟩:=hp.cost; let v := |b|+1; have hu:0<v:=by unfold v; positivity
 refine Metric.tendsto_nhds.mpr fun ε t=> ?_
 filter_upwards [cone_ratio P (show 0< ε/2/v by positivity),K.eventually_allowed h] with n a p
 rw [dist_zero_right]; exact lt_of_le_of_lt (a m p F hp v (fun i=> (L i).trans ((le_abs_self _).trans (le_add_of_nonneg_right zero_le_one)))) (show _ < ε by rw [div_mul_cancel₀ _ hu.ne']; linarith)
end YM.CF.Buffered
#print axioms YM.CF.Buffered.all_ratio_fixed
