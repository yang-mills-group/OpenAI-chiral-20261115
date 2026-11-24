import YM.SU5.FiniteGaugeData.ArchiveK.Oak
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Window.ArchiveK
open Function Filter Lattice Metric Complex Finset Laurent Next.Free Bloch Fir Lat MeasureTheory Fock Rush Largo WithLp
open scoped Topology BigOperators Pointwise ENNReal Matrix Matrix.Norms.L2Operator MatrixOrder InnerProductSpace ComplexOrder Kronecker
attribute [local instance] opCStarAlgebra
set_option linter.unusedSimpArgs false
set_option quotPrecheck false
attribute [local instance] μFin
open MeasureTheory.Measure
variable {A:Momentum→Op SpinIdx}{c C:ℝ} (p:0<c) (h: Ream A c C)
def rollK (A:Momentum→Op SpinIdx) :E4→Op SpinIdx:=fun x=> ∑' i:Cover,mode (brushQ x) i • tub A i
def bail (A:Momentum→Op SpinIdx)(d:ℕ):E4→Op SpinIdx:=fun x=> ∑ i∈Lattice.box d,mode (brushQ x) i • tub A i
section F
include h p
lemma rollKeep : Continuous (rollK A):= continuous_tsum (u:=fun i=>‖tub A i‖) (fun i=> (song_in i).smul continuous_const) (h.reserve.unweighted p.le).2.1 (fun i x=>by simp [norm_smul,surfK]) -- tune order
lemma rollPa(x:E4): rollK A x= A (brushQ x) ∨ x∉stair:= by
 by_cases t:x∈ stair; swap; · exact Or.inr t
 refine Or.inl ?_; let Qp:=tub A; let P:= brushQ x; have hg:Summable (fun i=> ‖mode P i • Qp i‖):= by simp_rw [norm_smul,show ∀ i,‖mode P i‖=1 from (by intro i; unfold P; rw [surfK,coast_pay]),one_mul]; exact (h.reserve.unweighted p.le).2.1
 ext i j; let f: Op SpinIdx→L[ℂ]ℂ:= LinearMap.toContinuousLinearMap ({ toFun:=fun A=> A i j,map_add':=by intros;rfl,map_smul':=by intros;rfl}:Op SpinIdx→ₗ[ℂ]ℂ);
 let T:= h.foe; change f (rollK A x)=(A _ i j); unfold rollK; unfold P Qp at hg; rw [f.map_tsum hg.of_norm]; exact T.readK _ (stair_body t) i j -- tune
lemma rollC(x:E4) : ‖rollK A x‖ ≤ C:= h.reserve.estimate (brushQ x) (fun i=>by rw [show (brushQ x i).im=0 from rfl, abs_zero]; exact p.le) -- tune
lemma bailC (x:E4)(d:ℕ) : ‖bail A d x‖ ≤ C:= (norm_sum_le ..).trans (by simp_rw [norm_smul,surfK,coast_pay,one_mul]; exact ((h.reserve.unweighted p.le).2.1.sum_le_tsum (Lattice.box d) (fun i _=> norm_nonneg _)).trans (h.reserve.unweighted p.le).2.2)
omit h p in
@[fun_prop] lemma bail_safe(A:Momentum→Op SpinIdx)(d:ℕ): Continuous (bail A d):= by unfold bail; fun_prop
lemma arriving(x:E4)(d:ℕ): ‖bail A d x - rollK A x‖ ≤ C * Real.exp (-c*d):=by
 let S:= Lattice.box d; let f(i:Cover):= mode (brushQ x) i • tub A i; let U(i:Cover):=Real.exp (c*Laurent.size i)*‖tub A i‖; have he(i:Cover): ‖f i‖=‖tub A i‖:=by unfold f; rw [norm_smul,surfK,coast_pay,one_mul]
 let T:= {i:Cover// i∉ S}; have ht:Summable (fun i:Cover=>‖f i‖):=by simp_rw [he]; exact (h.reserve.unweighted p.le).2.1; -- precedence
 let R:=Real.exp (-c*d); have hv(j:T) : ‖tub A j.val‖ ≤ R*U j.val:=by
    unfold U; rw [←mul_assoc]; apply le_mul_of_one_le_left (norm_nonneg _); unfold R; rw [← Real.exp_add]; apply Real.one_le_exp; have he:d≤ Laurent.size j.val:= le_of_not_gt fun t=> j.property (Lattice.box_test.mpr (have hr(a:Axis): (j.val a).natAbs < d:= lt_of_le_of_lt (Finset.single_le_sum (f:=fun a:Axis=>(j.val a).natAbs) (fun _ _=>by positivity) (mem_univ a)) t; ⟨fun i=>by specialize hr i; omega,fun i=>by specialize hr i; omega⟩)); nlinarith only [mul_le_mul_of_nonneg_left (show (d:ℝ) ≤ Laurent.size j.val from Nat.cast_le.mpr he) p.le]
 let K:= (ht.subtype (fun i=>i∉S)); rw [norm_sub_rev]; change ‖(∑' i,f i)-∑ i∈ S,f i‖ ≤ C*R; rw [← ht.of_norm.sum_add_tsum_subtype_compl S, add_comm,add_sub_cancel_right]; let W:=(norm_tsum_le_tsum_norm K); simp_rw [he] at W; have hq:Summable U:= h.reserve.2.1; refine W.trans ((Summable.tsum_le_tsum hv (K.congr fun i:T=>he i.val) ((hq.subtype _).mul_left R)).trans ?_); rw [tsum_mul_left,mul_comm C]; exact mul_le_mul_of_nonneg_left ((Summable.tsum_subtype_le U _ h.reserve.1 hq).trans h.reserve.2.2) (Real.exp_pos _).le
lemma stationPay {X:Type*}[NormedAddCommGroup X][NormedSpace ℝ X][NormedSpace ℂ X][IsScalarTower ℝ ℂ X]{f:E4→X}(p:Integrable f μF)(a:Cover) : ‖scout f a‖ ≤ gain⁻¹ *∫ p:E4,‖f p‖∂μF:= by unfold scout; rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr gain_h.le)]; exact mul_le_mul_of_nonneg_left ((norm_integral_le_integral_norm _).trans_eq (integral_congr_ae (ae_of_all _ fun i=> by dsimp only; rw [norm_smul,surfK,coast_pay,one_mul]))) (inv_nonneg.mpr gain_h.le)
omit h p in
lemma truncateL(d:ℕ)(A:Momentum→Op SpinIdx)(x:Cover) : scout (fun y=> bail A d y*voteS y) x=∑ i∈Lattice.box d,tub A i*fpS (x+i):=by
 let U(i:Cover):= tub A i; let f(i:Cover)(y: E4):= mode (brushQ y) i • ((U i)*voteS y); let T:= voteS; have h(i:Cover) : Integrable (fun x=> (U i)*T x) μF:= ((mulLs (U i)).restrictScalars ℝ).integrable_comp vote_I; rw [show (fun y=>bail A d y*voteS y)=(fun y=>∑ i∈Lattice.box d,f i y) from (by ext1 y; unfold bail; simp_rw [Matrix.sum_mul,Matrix.smul_mul]; rfl),scout_sum _ f (fun i _=>sing_in (h i) i)]; apply Finset.sum_congr rfl; intro i _; unfold f; rw [scout_more]; change scout (mulLs (U i) ∘ voteS) (x+i)=(mulLs (U i)) (fpS (x+i)); rw [scout_we _ vote_I, vote_Q]
-- C>0 variant μ.Now while comparing M∞ × vote.
lemma roll_I : Integrable (fun x=> rollK A x*voteS x) μF:= (vote_I.norm.const_mul C).mono' ((rollKeep p h).aestronglyMeasurable.mul vote_I.1) (ae_of_all _ fun i=> (norm_mul_le ..).trans (mul_le_mul_of_nonneg_right (rollC p h _) (norm_nonneg _)))
lemma bail_I(d:ℕ): Integrable (fun x=> bail A d x*voteS x) μF:= (vote_I.norm.const_mul C).mono' ((bail_safe A d).aestronglyMeasurable.mul vote_I.1) (ae_of_all _ fun i=> (norm_mul_le ..).trans (mul_le_mul_of_nonneg_right (bailC p h i d) (norm_nonneg _)))
lemma baile_me (d:ℕ)(x:Cover) : ‖(∑ i∈ Lattice.box d,tub A i *fpS (x+i))- scout (fun y=> rollK A y*voteS y) x‖ ≤ Real.exp (-c*d)*(C*gain⁻¹ *∫ p:E4, ‖voteS p‖∂μF):=by
 let g(y):=rollK A y*voteS y; let f(y):= bail A d y * voteS y-g y; have hf:Integrable f μF:= (bail_I p h d).sub (roll_I p h); let s:=Real.exp (-c*d); have he: scout f x+scout g x=scout (fun y=>bail A d y*voteS y) x:=by rw [←scout_add hf (roll_I p h) x]; simp_rw [f,g,sub_add_cancel];
 rw [← truncateL,← he]; change ‖(scout f x+scout g x)-scout g x‖ ≤ _; rw [add_sub_cancel_right]; refine (stationPay p h hf x).trans ?_; refine le_trans (mul_le_mul_of_nonneg_left (integral_mono (g:=fun y=> (C*s)*‖voteS y‖) hf.norm (vote_I.norm.const_mul _) (fun y=>?_)) (inv_nonneg.mpr gain_h.le)) (le_of_eq ?_); -- tune uses Station order
 · unfold f g; rw [←sub_mul]; exact (norm_mul_le ..).trans (mul_le_mul_of_nonneg_right (arriving p h y d) (norm_nonneg _))
 rw [integral_const_mul]; unfold s; ring
#print axioms baile_me
end F
section
variable {X:Type*}{J:Filter X} [J.NeBot][J.IsCountablyGenerated] (M:X→Tulip.Male) (u:Tendsto (fun x=>(M x).val.val) J atTop) (w:∀ i, Ream (bar 4 (M i).val) c C)
include p u w
lemma pulseI(z:Cover): Tendsto (fun i => scout (fun y=>rollK (bar 4 (M i).val) y*voteS y) z) J (𝓝 0):= by
 let T(i):=bar 4 (M i).val; let f(i)(x:E4):= mode (brushQ x) z • (rollK (T i) x*voteS x); let U(x:E4):=C*‖voteS x‖; have hb: Tendsto (fun i=> ∫ x, f i x ∂μF) J (𝓝 (∫ x:E4,(0:Op SpinIdx)∂μF)):=by
    apply tendsto_integral_filter_of_dominated_convergence U (Eventually.of_forall fun i=> ((sing_in (roll_I p (w i)) z)).1) ?_ (vote_I.norm.const_mul C) ?_
    · apply Eventually.of_forall fun i=> Eventually.of_forall fun x=>?_ ; unfold U; rw [norm_smul,surfK,coast_pay,one_mul]; exact (norm_mul_le ..).trans (mul_le_mul_of_nonneg_right (rollC p (w i) x) (norm_nonneg _))
    filter_upwards [stargaze] with x t; have h0:=(tendsto_const_nhds (x:=mode (brushQ x) z)).smul (receives u t.2.2.2 t.1 t.2.2.1); rw [smul_zero] at h0; refine h0.congr' (Eventually.of_forall ?_)
    intro i; dsimp only; rw [Or.resolve_right (rollPa p (w i) x) (not_not.mpr t.2.2.2)]; -- tune
 rw [integral_zero] at hb; have hp:=(tendsto_const_nhds (x:=gain⁻¹)).smul hb; rw [smul_zero] at hp; exact hp
abbrev pride(C:ℝ):ℝ:= C*gain⁻¹ * (∫ p:E4,‖voteS p‖∂μF)+1
omit u w M p in
lemma pride_p(C:ℝ)(t:0≤C): 0< pride C:= add_pos_of_nonneg_of_pos (by have h:=gain_h; have hh:0 ≤ ∫ p:E4,‖voteS p‖∂μF:= integral_nonneg (fun _=>norm_nonneg _); positivity) zero_lt_one
-- local receipt. for all but finitely low µ. use instead using contradiction choose counterexamples.
lemma arriveM (d:ℕ)(x:Cover) : ∀ᶠ i in J,‖∑ l∈ Lattice.box d,tub (bar 4 (M i).val) l*fpS (x+l)‖ ≤ Real.exp (-c*d)*pride C:=by
 let B(i):= bar 4 (M i).val; let T(i):= ∑ a∈Lattice.box d,tub (B i) a*fpS (x+a); let U(i):= scout (fun y=>rollK (B i) y*voteS y) x; have he(i):‖T i-U i‖ ≤ _:=baile_me p (w i) d x; let F:=Real.exp (-c*d); filter_upwards [(pulseI p M u w x).eventually (closedBall_mem_nhds _ (Real.exp_pos (-c*d)))] with i t
 have hv:‖U i‖≤ F:= mem_closedBall_zero_iff.mp t; unfold pride; rw [mul_add,mul_one]; exact (sub_le_iff_le_add.mp ((norm_sub_norm_le ..).trans (he i))).trans (add_le_add_right hv _) -- tune
#print axioms arriveM
end
variable (a:∀ M:Tulip.Male,Ream (bar 4 M.val) c C)
include p a
lemma earnM (d:ℕ)(K:Finset Cover) : ∃ B:ℕ,∀ M:Tulip.Male,B≤M.val.val→∀ x∈ K, ‖∑ l∈Lattice.box d,tub (bar 4 M.val) l*fpS (x+l)‖ ≤ Real.exp (-c*d)*pride C :=by
 by_contra! k; choose M q X H e using k; have hp:= fun x=> arriveM p M (tendsto_atTop_mono q tendsto_id) (fun i=> a (M i)) d x; obtain ⟨i,hi⟩:= ((eventually_all_finset K).mpr (fun i _=>hp i)).exists; exact (e i).not_ge (hi (X i) (H i))
#print axioms earnM
end YM.CF.Window.ArchiveK
