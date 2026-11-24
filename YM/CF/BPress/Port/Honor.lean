import YM.CF.BPress.Port.Raw
/-! price log global prefactor includes s^4 pieces exactly. PL per exc severity.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Port
open Function Filter MeasureTheory LocalH Lattice Wilson RG Precision Grid Cube Bands Pressure Wealth Finset Weave Branch
open scoped Topology BigOperators Classical Matrix Matrix.Norms.Frobenius InnerProductSpace ENNReal
open SU Gauge Next.SectorChange
attribute [local instance] Gauge.frobInner
variable {s:Side}{B:BandWidth}(X:Bands s B)(D:ℕ)(J:ChartRatio group)(P:Weave.Budget)(κ y:ℝ)
lemma pl_N_abs (p q:ℝ→ℝ)(C:ℝ)(h:PL fun i=>(p i)⁻¹)(e:∀ᶠ i in atTop, 0<p i ∧ p i≤ q i ∧ q i ≤ C): PL (fun i=> |Real.log (q i)|):=by
 apply (h.add (PL.const C)).mono; filter_upwards [e] with i g; obtain ⟨a,b,k⟩:=g; have he:= a.trans_le b; have hC:=he.trans_le k; rw [abs_abs,abs_of_nonneg (by positivity : 0≤ (p i)⁻¹+C)]; apply abs_le.mpr; constructor; linarith only [Real.neg_inv_le_log he.le, inv_anti₀ a b, (he.trans_le k)]; linarith only [Real.log_le_self he.le,k,inv_pos.mpr a]
lemma pl_log_N : PL (fun i=> |Real.log (N_v D i)|):= pl_N_abs (fun _=>minpay D) _ (maxpay D) (PL.const _) (Eventually.of_forall fun i=> ⟨cage_pos _ _ zero_lt_one,pays D i⟩)
lemma log_job (u:LocalRatio J)(p:0<y) : Real.log (job_m D J y) = Real.log (N_v D y)+Real.log (cH D J) - portDim D*(Real.log y/2):=by
 unfold job_m gH; rw [Real.log_mul (v_pos D y).ne' (gH_pos D J y u p).ne', Real.log_mul (show cH D J≠0 from pow_ne_zero _ u.scale.ne') (pow_pos (g_pos p) _|>.ne'),Real.log_pow]; change _+(_+_*Real.log (Real.sqrt y)⁻¹)=_; rw [Real.log_inv,Real.log_sqrt p.le]; ring
lemma job_p (u:LocalRatio J) : PL (fun i=>|Real.log (job_m D J i)|):=by
 apply (((pl_log_N D).add (PL.const (|Real.log (cH D J)|))).add (((PL.const (portDim D:ℝ)).mul PL.log).mul (PL.const (1/2)))).mono; filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 0,eventually_gt_atTop (0:ℝ)] with i a hi; simp only [abs_abs]; rw [log_job D J i u hi]; refine le_trans ((abs_sub ..).trans (add_le_add (abs_add_le ..) le_rfl)) (le_trans (Eq.le ?_) (le_abs_self _)); rw [abs_of_nonneg (by positivity : 0 ≤ (portDim D:ℝ)*(Real.log i/2))]; ring
lemma trace_pl : PL (fun i=>traceTab (P.low i) P.upper):=(pl_N_abs P.low P.low _ P.ipLow (P.pLow.mono fun i p=> ⟨p.1,le_rfl,p.2⟩)).add (PL.const _)
lemma at_most : Fintype.card X.Hcols ≤ s.val^4:=by change Fintype.card (X.Index × Tri s)≤_; rw [Fintype.card_prod,tri_card,pow_succ' s.val 3,show Fintype.card X.Index=X.Q.val from ZMod.card ..]; apply Nat.mul_le_mul_right; rw [X.size_eq]; exact Nat.le_mul_of_pos_left _ B.full.property
lemma ray_rank : Module.finrank ℝ (RaySpace X) = Fintype.card X.Hcols * portDim B.D:=by rw [finrank_euclideanSpace, Fintype.card_congr (stem X), Fintype.card_prod,ticket_stack]
def rootsCount := Fintype.card (Option Signed × PlaqAxes)
lemma total_roots (s:Side): Fintype.card (Root s) ≤ s.val^4 * rootsCount:= by
 apply le_trans (Fintype.card_le_of_injective _ levyH_inj); rw [Fintype.card_prod]; simp [Site,Four,Axis,Per,ZMod.card,rootsCount]
variable (F:Fare X)(M:ℕ)(d:Clip)(R:PathData group)(p:BudgetPoint)(β:ℝ)
def gvol := Real.exp (-(debtH X M R d p β y))* diceV X J y F
lemma price_tab (v:0<y)(u:LocalRatio J)(H:Summer X F P.upper (P.low y) (P.reach y) (P.chunks y)) : 0 < diceV X J y F ∧ |Real.log (diceV X J y F)| ≤ (s.val:ℝ)^4 * (|Real.log (job_m B.D J y)| + (portDim B.D:ℝ)* traceTab (P.low y) P.upper):=by
 unfold diceV; have hp:=mul_pos (v_pos B.D y) (gH_pos B.D J y u v); have h':0<job_m B.D J y:=hp; have he:= H.root_pos ∅; refine ⟨by positivity,?_⟩; rw [Real.log_mul (pow_pos h' _|>.ne') he.ne',Real.log_pow]; let a:=portDim B.D; let n:= Fintype.card X.Hcols; have ht:(n:ℝ) ≤ (s.val:ℝ)^4:=by exact_mod_cast at_most X
 have hL:= H.price_roots ∅; rw [ray_rank] at hL; apply le_trans (abs_add_le ..); rw [mul_add,abs_mul,abs_of_nonneg (Nat.cast_nonneg _)]; apply add_le_add; exact mul_le_mul_of_nonneg_right ht (abs_nonneg _); apply hL.trans; rw [Nat.cast_mul, ←mul_assoc (↑s.val^4:ℝ)]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ht (Nat.cast_nonneg _)) (by unfold traceTab; positivity : 0≤ traceTab (P.low y) P.upper)
variable {C σ Λ:ℝ}
set_option maxRecDepth 16000 in
lemma pay_max (v:0<y)(W:R.Bounds d σ C Λ)(e:Checks M p d)(b:β∈Set.Icc (y/2) (2*y)): |debtH X M R d p β y|≤(s.val:ℝ)^4*rootsCount*(payC d 2 C*y):=by
 have he:= le_trans (by linarith only [v] : 0≤ y/2) b.1; unfold debtH; have h(x:Root s) : |due M R d p β y x|≤payC d β C:= (merit R d p β M W e he x).1.price _; refine (abs_sum_le_sum_abs ..).trans ((sum_le_sum (fun x _=>h x)).trans ?_); rw [sum_const,nsmul_eq_mul]; have hp:= le_trans (card_le_univ (outer X M)) (total_roots s); refine le_trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hp) (pay_zero d _ he)) ?_; rw [Nat.cast_mul, Nat.cast_pow]; apply mul_le_mul_of_nonneg_left _ (show (0:ℝ) ≤ ↑s.val^4*rootsCount by positivity)
 calc
  _ ≤ payC d (2*y) C:= by unfold payC; have hh:= b.2; gcongr <;> positivity [d.quadratic_pos,d.tail_pos,chPrice_pos]
  _ = _:=by unfold payC; ring -- tune
-- PL per entire |log gvol|/s^4 (K part β not PL) packages
lemma pref_content (v:0<y)(u:LocalRatio J)(H:Summer X F P.upper (P.low y) (P.reach y) (P.chunks y))(W:R.Bounds d σ C Λ)(e:Checks M p d)(b:β∈Set.Icc (y/2) (2*y)): 0<gvol X J y F M d R p β ∧ |Real.log (gvol X J y F M d R p β)| ≤ (s.val:ℝ)^4*((rootsCount*payC d 2 C)*y + |Real.log (job_m B.D J y)| + (portDim B.D:ℝ)*traceTab (P.low y) P.upper):=by
 obtain ⟨a,t⟩:= price_tab X J P y F v u H; unfold gvol; refine ⟨by positivity,?_ ⟩; rw [Real.log_mul (Real.exp_pos _).ne' a.ne',Real.log_exp]; refine le_trans (abs_add_le ..) ?_; rw [abs_neg]; exact (add_le_add (pay_max X y M d R p β v W e b) t).trans (Eq.le (by ring)) -- tune
end YM.CF.BPress.Port
