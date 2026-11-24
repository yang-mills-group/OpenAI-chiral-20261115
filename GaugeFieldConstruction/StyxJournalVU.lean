import GaugeFieldConstruction.SorJournalVU
/-! Continuous expenditures on last inequalities. First comparison anchored R=exp(n) sufficient for Walk at ∀Q; western incomplete pressing leaves opposite-sign window. -/
set_option autoImplicit false
noncomputable section
namespace YM.NSF.Outer
open Function Set Filter MeasureTheory Measure Complex Boundary Probe Table Row Word OS Ward
open scoped Topology ContDiff BigOperators NNReal ENNReal InnerProductSpace Matrix.Norms.Frobenius
variable {G : Gauge} {L : Register G} {S : Table L}
lemma receiptPointVU (V : ∀ i, Chamber S i) (Q:Finset Axis)(i:Axis)(A: Weight L)(δ:ℝ)(a:ℝ) (ht:a≤0) (w:Axis→ℝ)(hw:∀ i∈Q,w i≤0) (f:Grouping)(h:∀ j∈Q, Ends (f j))
    (P:∀ g:Grouping,Colors Finset.univ g→∀ b:ℝ,b<0→ Budget δ (fun n => ∫ p,cost i Q (fuel b n) (mails w g n) p ∂ν (V i) A)):
    (∀ t:ℝ,Integrable (cost i Q (FuelVU a t) (TonalVU f w t)) (ν (V i) A)) ∧
    RealBudgetVU δ (fun t=>∫ p,cost i Q (FuelVU a t) (TonalVU f w t) p ∂ν (V i) A):=by
 let μ:=ν (V i) A; let D t:=cost i Q (FuelVU a t) (TonalVU f w t)
 have hD t:Integrable (D t) μ := cost_int V i A _ (Real.exp_pos _) _ _
 refine ⟨hD,?_⟩
 let W:=Q.erase i
 obtain ⟨g,hG,hM⟩:=totalNormVU W f (fun j v=>h _ (Finset.mem_of_mem_erase v)) w (fun j v=>hw _ (Finset.mem_of_mem_erase v))
 let b:= a-1; have hb:b<0:=by dsimp only [b]; linarith
 let c:= Real.exp (-b); have hc:0<c:=Real.exp_pos _
 apply spanBudgetVU δ _ c hc.le _ (P g hG b hb); intro t ht -- tune
 let j:=⌊t⌋₊; let B:= fuel b j; let E:= FuelVU a t; let F:=mails w g j; let Y:= cost i Q B F
 have he:0<E:=Real.exp_pos _; have hx:0<B:=fuel_pos ..
 have hQ: B ≤ c*E:=by
    have hl:= boundFuelVU b j t (show t≤ j+1 by dsimp only[j]; linarith[Nat.self_sub_floor_lt_one t]) hb.le
    have h:FuelVU b t≤E := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (show b≤a by dsimp [b];linarith) ht)
    refine (le_div_iff₀ (Real.exp_pos b)).2 ?_ |>.trans_eq (show E/Real.exp b=c*E by rw[div_eq_mul_inv, mul_comm]; unfold c; rw [Real.exp_neg])
    rw [mul_comm]; exact hl.trans h
 have hC: 1≤c:=by simpa [c] using Real.exp_le_exp.mpr (show 0≤ -b from neg_nonneg.mpr hb.le)
 have hg j hj: Plus (F j):=bill_plus (hG j hj).2.1 _ _
 have hNN:∀ᵐ p ∂μ,0≤Y p:= (before (V i) A).mono fun p hp=>cost_nn i Q _ _ _ hx hp (fun j _=> hg j (Finset.mem_univ _))
 change ‖integral μ (D t)‖ ≤ c* ‖integral μ Y‖; rw [Real.norm_of_nonneg (integral_nonneg_of_ae hNN),←integral_const_mul]
 have hy:Integrable (fun p=>c*Y p) μ:= (cost_int V i A _ hx Q F).const_mul _
 apply (norm_integral_le_integral_norm (D t)).trans (integral_mono_ae (hD t).norm hy ((before (V i) A).mono fun p ho=>?_))
 dsimp only; unfold D Y cost; rw [norm_mul,Real.norm_of_nonneg (low_nn _ _ _ he ho),←mul_assoc]; refine mul_le_mul ?_ (show ‖crop (Q.erase i) _ _‖ ≤ _ from (hM t ht p)) (norm_nonneg (crop (Q.erase i) (TonalVU f w t) p)) (mul_nonneg hc.le (low_nn _ _ _ hx ho)); unfold low; split_ifs
 · change (p i+E)⁻¹ ≤ c*(p i+B)⁻¹; rw [← one_div, ← div_eq_mul_inv, div_le_div_iff₀ (by linarith) (by linarith),one_mul]; nlinarith
 · simp
-- genuine M2 scales (118) arbitrary. C depends after bandwidth exps. AE payments.
lemma EarnPressVU (V : ∀ i, Chamber S i)(H:S.Hierarchy) (Q:Finset Axis)(i:Axis)(A: Weight L)(e)(hi:i∈Q)(hr:Mixed Q e)(hp:∀ i∈Q, Pressed i A)(he:∀ i∈Q, Own A i (e i))
    (δ:ℝ)(hd:0<δ)(w:Axis→ℝ)(hw:∀ i∈Q,w i≤0)(f:Grouping)(h:∀ j∈Q, Ends (f j)):
    (∀ t:ℝ,Integrable (cost i Q (FuelVU (w i) t) (TonalVU f w t)) (ν (V i) A)) ∧
    RealBudgetVU δ (fun t=>∫ p,cost i Q (FuelVU (w i) t) (TonalVU f w t) p ∂ν (V i) A):=
 receiptPointVU V Q i A δ _ (hw i hi) w hw f h (fun g h b hz=> point_cost V H i A e Q hi hr hp he w hw _ hz g (fun i _=>h _ (Finset.mem_univ i)) _ hd)
lemma EarnTrailVU (V : ∀ i, Chamber S i)(H:S.Hierarchy) (l i:Axis)(A: Weight L)(e)(hr:Mixed (other l) e)(hp:∀ i∈other l, Pressed i A)(he:∀ i, Own A i (e i))
    (δ:ℝ)(hd:0<δ)(w:Axis→ℝ)(hw:∀ i,w i≤0)(f:Grouping)(h:∀ j, Ends (f j)):
    (∀ t:ℝ,Integrable (cost i Finset.univ (FuelVU (w i) t) (TonalVU f w t)) (ν (V i) A)) ∧
    RealBudgetVU (if i=l then δ else -w l+δ) (fun t=>∫ p,cost i Finset.univ (FuelVU (w i) t) (TonalVU f w t) p ∂ν (V i) A):=
 receiptPointVU V Finset.univ i A _ _ (hw i) w (fun i _=> hw i) f (fun j _=>h j) (fun g h b hz=> line_cost V H l e A he hr (mixedAliveVU l e hr) hp i w hw δ b hz hd g h)
-- cone: monotone in W directly. No multiplication of fees at test p_i<=1.Cone integration.
lemma ConeLineVU (V:∀ i,Chamber S i) (H:S.Hierarchy)(J: Stress S)(P:DiffPlan S)(hP:P.Derivatives S)(hS:P.Orientation H.spin)
    (hr:RawTensor H.spin J)(C:Conserved P H.spin J)(i: Axis)(A: Weight L)(he:equalRead S A (pick (J i i)))(ha:Own A i false)(ht:Pressed i A)(w:Axis→ℝ) (a:ℝ)(hp:a≤0)(hw:∀ j,j≠i→ w j≤a)(f:Grouping)(h:∀ j, Ends (f j)) (δ:ℝ)(hd:0<δ):
    (∀ t:ℝ,0≤t→Integrable (coneWeight i (FuelVU a t) (TonalVU f w t)) (ν (V i) A)) ∧
    RealBudgetVU (δ+a*4) (fun t=>∫ p,coneWeight i (FuelVU a t) (TonalVU f w t) p ∂ν (V i) A):=by
 let μ:=ν (V i) A; let D t:=coneWeight i (FuelVU a t) (TonalVU f w t)
 obtain ⟨g,hg,hV⟩:=totalNormVU (other i) f (fun j _=>h j) w (fun j v=>(hw j (Finset.mem_erase.mp v).1).trans hp)
 let Y n:=coneWeight i (fuel a n) (mails w g n)
 obtain ⟨hY,hG⟩:=mass V H J P hP hS hr C i A he ha ht w a hp hw g hg δ hd
 have he n : ∀ᵐ p ∂μ,0≤ Y n p:= (before (V i) A).mono fun p hp=>cone_nn i _ _ (fun j=>bill_plus (hg j (Finset.mem_univ _)).2.1 _ _) p (fuel_pos ..) hp
 have hC (t:ℝ)(u:0≤t): ∀ᵐ p∂μ, ‖D t p‖≤ Y ⌊t⌋₊ p:=by
    let j:=⌊t⌋₊; let B:= fuel a j; let E:= FuelVU a t
    have he:0<E:=Real.exp_pos _; have hx:0<B:=fuel_pos ..
    have hQ:E≤B:=descentVU a j t (Nat.floor_le u) hp
    filter_upwards [before (V i) A] with p hv; unfold D Y coneWeight; split_ifs; swap; · simp
    change ‖p i * E^4 / (p i+E)^4 * crop _ _ _‖ ≤ p i * B^4 / (p i+B)^4 * _
    rw [norm_mul,Real.norm_of_nonneg (by positivity)]; refine mul_le_mul ?_ (hV _ u p) (norm_nonneg _) (by positivity)
    rw [mul_div_assoc,mul_div_assoc, ← div_pow, ← div_pow]
    apply mul_le_mul_of_nonneg_left _ hv
    apply pow_le_pow_left₀ (by positivity); rw [div_le_div_iff₀ (by linarith) (by linarith) ]; nlinarith
 have hD(t:ℝ)(u:0≤t): Integrable (D t) μ:= (hY ⌊t⌋₊).mono' (cone_meas i _ _).aestronglyMeasurable (hC _ u)
 refine ⟨hD, spanBudgetVU _ _ 1 zero_le_one (fun n=> integral μ (Y n)) hG ?_⟩
 intro t u; rw [one_mul,Real.norm_of_nonneg (integral_nonneg_of_ae (he _))]; exact (norm_integral_le_integral_norm (D t)).trans (integral_mono_ae (hD _ u).norm (hY _) (hC _ u))
#print axioms ConeLineVU
#print axioms EarnTrailVU
end YM.NSF.Outer
end
