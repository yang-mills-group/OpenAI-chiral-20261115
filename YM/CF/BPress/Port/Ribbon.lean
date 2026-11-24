import YM.CF.BPress.Port.BayTax
/-! short log term PL local with NPL price. healthy h hypotheses at any y. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Port
open Function Filter MeasureTheory LocalH Lattice Wilson RG Precision Grid Cube Bands Pressure Wealth Finset Weave Branch Metric
open scoped Topology BigOperators Classical Matrix Matrix.Norms.Frobenius InnerProductSpace ENNReal ContDiff
open SU Gauge Next.SectorChange
attribute [local instance] Gauge.frobInner
variable {s:Side}{B:BandWidth}(X:Bands s B)(D:ℕ)(J:ChartRatio group)(F A:Fare X)
def lTerm (y:ℝ)(x:Fills X)(S:Seal X.Hcols)(i:X.Hcols):= if i∈ Sᶜ then logPay B.D J y (wjson (F S) x i) else 0
lemma lterms (S:Seal X.Hcols)(x:Fills X)(y:ℝ) : softLog X J y F S x=∑ i,lTerm X J F y x S i :=by unfold lTerm; rw [←sum_filter]; simp only [filter_mem_eq_inter,univ_inter]; rfl -- tune
lemma l_seen (h:LocalRatio J)(S:Seal X.Hcols)(i:X.Hcols)(y:ℝ): Measurable fun v=>lTerm X J F y v S i:=by unfold lTerm; split; exact (log_meas B.D J y h).comp ((measurable_pi_apply _).comp (wjson_meas _)); exact measurable_const
structure LieTicket (J:ChartRatio group)(a C:ℝ):Prop where
 posQ : 0<C
 posD : 0<a
 localT (x:ink): ‖x‖< a → |Real.log (J.J x)| ≤ C * ‖x‖
lemma TicketM (h:LocalRatio J) : ∃ a C, LieTicket J a C:=by
 obtain ⟨L,S,p,v⟩:= ((h.germ 0 (mem_ball_self h.patch)).log (h.anchored.trans_ne one_ne_zero)).hasStrictFDerivAt (by simp) |>.exists_lipschitzOnWith; obtain ⟨r,hR,V⟩:= Metric.mem_nhds_iff.mp p; refine ⟨r,(L:ℝ)+1,⟨by positivity,hR,fun x t=>?_⟩⟩; have he:= v.dist_le_mul x (V (by simpa using t)) 0 (mem_of_mem_nhds p); rw [h.anchored,Real.log_one,dist_zero_right,dist_zero_right] at he; exact he.trans (by gcongr; exact le_add_of_nonneg_right zero_le_one)
-- push after F
variable (P:Weave.Budget)
def strideCost (u y:ℝ):= g y * (faith D * (P.fore y D * u)) -- pl*t/g ???
def lPay (C y:ℝ):= (D:ℝ)*3*(C*strideCost D P (truncv y) y)
lemma lprice (C:ℝ): NPL fun i=> lPay D P C i:=by
 unfold lPay strideCost; convert (((P.buy_for D).times (npl_drift_g 2 1 zero_lt_one)).const_mul ((D:ℝ)*3*C*faith D)) using 1; ext i; rw [Real.rpow_two,Real.rpow_one]; unfold truncv; ring
lemma stride_pl : NPL fun i=> strideCost D P (truncv i) i:=by convert (((P.buy_for D).times (npl_drift_g 2 1 zero_lt_one)).const_mul (faith D)) using 1; ext i; unfold strideCost truncv; rw [Real.rpow_two, Real.rpow_one]; ring
variable {X F J P}
lemma lTerm_loc {a:ℕ}{y:ℝ}(h: Connect X F a) : smallRead (lTerm X J F y) a:=by
 intro x y A B i L e g; unfold lTerm; have ht:=e i (column_self ..); split_ifs; · rw [see_run h A B i e x y g]
 all_goals simp only [mem_compl] at * <;> tauto
variable {y:ℝ}
lemma stride_s {S:Seal X.Hcols}(p: Summer X F P.upper (P.low y) (P.reach y) (P.chunks y))(t:0<y)(x:Fills X)(i:X.Hcols){T:ℝ}(q:0≤T)(h:∀ j∈columnBall X i (P.reach y), ‖x j‖≤T): ∀ j, ‖hew B.D y (wjson (F S) x i) j‖ ≤ strideCost B.D P T y:=by intro j; refine (c_bound B.D _ _).trans ?_; rw [norm_smul,Real.norm_of_nonneg (g_pos t).le]; exact mul_le_mul_of_nonneg_left (hue_small P F T y p S x i q h) (g_pos t).le
lemma soft_price (p: Summer X F P.upper (P.low y) (P.reach y) (P.chunks y))(t:0<y){a C:ℝ}(e:LieTicket J a C)(u:strideCost B.D P (truncv y) y<a)(S:Seal X.Hcols)(x:Fills X)(i:X.Hcols)(v:Barrel X y x): |lTerm X J F y x S i|≤ lPay B.D P C y:= by
 have he:= stride_s (S:=S) p t x i (zero_le_one.trans (trunc_pos y)) (fun i _=> v i); have hx:=e.posQ; unfold lTerm; split; next h=> unfold logPay; apply (abs_sum_le_sum_abs ..).trans; apply (sum_le_sum (fun j (_:j∈ (univ:Finset (Hub B.D)))=> (e.localT _ ((he j).trans_lt u)).trans (mul_le_mul_of_nonneg_left (he j) hx.le))).trans; rw [sum_const,nsmul_eq_mul,Finset.card_univ,Fintype.card_prod]; simp [lPay,SpatialDir] -- tune
 next h=> rw [abs_zero]; unfold lPay; have ht := le_trans (norm_nonneg _) (he (⟨0,B.D_pos⟩,0)); positivity
end YM.CF.BPress.Port
