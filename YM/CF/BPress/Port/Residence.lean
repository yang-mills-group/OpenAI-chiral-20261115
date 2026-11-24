import YM.CF.BPress.Port.Honor
/-! Eq:B-Sbill2: log price for sum-Gaussian charged ``hard bad'', I_p exponent entries packed against exact demand. Costs per severe only. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Port
open Function Filter MeasureTheory LocalH Lattice Wilson RG Precision Grid Cube Bands Pressure Wealth Finset Weave Branch Push.AbsoluteSums
open scoped Topology BigOperators Classical Matrix Matrix.Norms.Frobenius InnerProductSpace ENNReal
open SU Gauge Next.SectorChange
attribute [local instance] Gauge.frobInner
variable {s:Side}{B:BandWidth}(X:Bands s B)(D:ℕ)(J:ChartRatio group)(P:Weave.Budget)(κ y:ℝ)(d:Clip)
def reward :=sever d κ D*(1/4)* drift y^2
lemma sever_pos (κ:ℝ)(q:0<κ)(d:Clip)(D:ℕ)(v:0<D):0 < sever d κ D:=by apply half_pos; apply loss_pos; unfold severeP; positivity
lemma reward_fit (r:LocalRatio J)(u:0<κ)(p:0<D): ∀ᶠ y in atTop, P.jcostB y D + |Real.log (job_m D J y)| ≤ reward D κ y d:=by
 have h:=P.buy_jcost D; let a(i):=P.jcostB i D + |Real.log (job_m D J i)|; have hv:= job_p D J r; let K:= sever d κ D * (1/4); have he := npl_drift 2 zero_lt_two; have hp:0<K:=mul_pos (sever_pos κ u d D p) (by norm_num); have hf:= ((h.add hv).times he).drop; filter_upwards [hf.eventually (ge_mem_nhds hp)] with y t; change a y*_ ≤ K at t; rw [Real.rpow_two] at t; rw [← div_eq_mul_inv] at t; exact (div_le_iff₀ (pow_pos (drift_pos y) _)).mp t
variable {X κ y D}
lemma reward_bound (p:0<y)(u:0<κ)(e:0<D) (β:ℝ)(f:y/2≤ β): 2*reward D κ y d≤ sever d κ D*β*temp y^2:=by
 let C:=sever d κ D; let A:= reward D κ y d; have ht:0<C:=sever_pos κ u d D e; rw [temp_eq y,mul_pow,gscale p.le]; apply le_trans _ (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left f ht.le) (by positivity)); unfold reward; exact Eq.le (by field_simp; ring)
lemma Sbill2 (r:LocalRatio J) (M:ℕ)(R:PathData group)(p:BudgetPoint) (β:ℝ) {Φ:Sheet.Atlas} {σ C Λ ζ D':ℝ}
    (H:R.Bounds d σ C Λ)(g:Poise B Φ d D' κ C ζ y M)(hp:Checks M p d)(e:p.threshold=temp y)(t:β∈Set.Icc (y/2) (2*y))(q:P.jcostB y B.D + |Real.log (job_m B.D J y)|≤reward B.D κ y d)
    (F:Fare X)(S:Seal X.Hcols)(A:Seal X.Hcols→ Tender X)(b:Tender X) (z: Quarters X) {U V:Micro s}(a:aware X κ y F S z)
    (Jp:JacData X F A b (P.jrate y) (P.jcostB y B.D))
    (m:Mission X y (Aback X (bodyBase X y F S z)) V U)(l:ToneNoise y V)
    (i:X.Hcols)(v:i∈S):
    (Wealth.pays X M R d p β y S (perturb Φ X κ y (Aback X (bodyBase X y F S z))) U i + burden X (P.heightClose y) A i S) - Real.log (job_m B.D J y) ≤ -(reward B.D κ y d):=by
 have ht:S=chosen X κ y (Aback X (bodyBase X y F S z)):= (show pick X κ y (bodyBase X y F S z)=S from a).symm; have hv : i ∈ pick X κ y (bodyBase X y F S z):=by rw [show pick X κ y _=S from a]; exact v -- tune
 have hw:=storm_at R d p H g hp e t m l i hv; have hh:= Jp.short_bill (P.heightClose y) i (half_pos (P.gg y)).le S; have hz:=reward_bound d g.dividend.young g.kap B.D_pos β t.1; -- tune ht order
 change Wealth.pays X M R d p β y (chosen X κ y (Aback X (bodyBase X y F S z))) _ U i ≤ _ at hw; generalize hG : bodyBase X y F S z=T at *; rw [← ht] at hw; linarith only [q,hz,hw, (le_abs_self _ |>.trans hh),neg_abs_le (Real.log (job_m B.D J y))] -- tune
end YM.CF.BPress.Port
