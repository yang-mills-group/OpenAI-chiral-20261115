import YM.SU5.Gleam.Innate
import GaugeFieldConstruction.Passage
/-! # Blocking permissions with width-independent thresholds when right width choice made. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option quotPrecheck false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 17000
noncomputable section
namespace YM.Gleam
open Function Lattice MeasureTheory Finset RG Wilson Tree Filter Metric Exterior Precision Next.Rank.Spindle Pressure Work.F03 Next.SectorChange Next.SectorChange.Gaussian
open Fineness Matrix
open scoped Matrix BigOperators Classical ContDiff Topology MatrixOrder ENNReal Kronecker Matrix.Norms.Frobenius
variable {c n : Side}{r:Ratio c n}{T:Forest r}{G:Gauge}{p:BudgetPoint}{q:Clip}{v t η C S w δ β κ ξ Λ:ℝ}{U:Config G n}{A:Support c}{m:ℕ} {R:Rules G} {Z:PathData G}{b:Cell n}{H:Bed}{F:Finset T.Free}{J:ChartRatio G}
lemma whirlwind (s:Signed) (U:Config G n)(κ t :ℝ) : κ*(misdemean t (pull s 0 U)).card=κ*(misdemean t U).card:= by
 let i:Equiv.Perm (Cell n):= Equiv.ofBijective (Face.send s 0) ⟨Face.injective_send s 0,Finite.injective_iff_surjective.mp (Face.injective_send s 0)⟩
 have h(b:Cell n): b∈ misdemean t (pull s 0 U) ↔ i b∈ misdemean t U:=by simp only [misdemean,mem_filter]; rw [Face.send_price U b s 0 G.chord G.chord_inv (fun _ u=> G.chord_conj u _)]; simp; rfl
 rw [← counts_tax,← counts_tax]; exact (sum_congr rfl (s₂:=univ) (g:=fun x=> if i x∈misdemean t U then κ else 0) (fun x _=>by simp only [h] )).trans (Equiv.sum_comp i (fun x=> if x∈misdemean t U then κ else 0))

-- Jensen pointwise port. channel chooses its own tree exponent; if common quantity estimates against each, can now use P2 purchases PER channel, not assuming signed-invariance of tree chart errors.
abbrev apportion :ℝ:= (Fintype.card Signed:ℝ)⁻¹
abbrev segments (Z:PathData G)(q:Clip)(p:BudgetPoint)(β κ k θ:ℝ)(F:Signed → Config G n→ ℝ)(U: Config G n):=
 ∑ s:Signed, apportion * (richBoth Z q p β κ k θ (pull s 0 U)*Real.exp (F s (pull s 0 U)))
variable (F':Signed→ Config G n→ℝ){θ k d:ℝ}
lemma season_average (p':∀ s,d≤ F' s (pull s 0 U)):
  Real.exp ( -(Z.inChannels q p β U)+κ*(misdemean p.threshold U).card+k*(misdemean θ U).card + d) ≤ segments Z q p β κ k θ F' U :=by
 let M:ℝ:= Fintype.card Signed; have hM:0<M:=by unfold M; exact_mod_cast Fintype.card_pos
 have ha:0≤apportion:= (inv_pos.mpr hM).le
 have hw:(∑ _:Signed,apportion) =1:=by rw [sum_const,card_univ,nsmul_eq_mul]; exact mul_inv_cancel₀ hM.ne'
 let L:= κ*(misdemean p.threshold U).card; let L':= k*(misdemean θ U).card; let e(s:Signed):= -(Z.principal q p β (pull s 0 U)) + L + L'+d;
 have he:(∑ s:Signed,apportion • e s)= -(Z.inChannels q p β U)+ L + L' + d :=by
    unfold e; simp only [smul_eq_mul,mul_add,mul_neg,sum_add_distrib,sum_neg_distrib]; rw [← sum_mul, hw, one_mul] -- rw likely mul_sum term first not constant first?
    rw [←sum_mul,hw,one_mul,←sum_mul,hw,one_mul,←mul_sum]; rfl
 apply le_trans _ (show (∑ i:Signed,apportion • Real.exp (e i)) ≤ _ from ?_)
 · rw [← (show ∑ s:Signed,_=_ from he)] -- tune
   exact (convexOn_exp.map_sum_le (w:=fun _ : Signed=>apportion) (fun i _=> ha) hw (fun s _ => Set.mem_univ (e s)))
 apply sum_le_sum; intro i _; apply mul_le_mul_of_nonneg_left _ ha; unfold e L L'
 rw [richBoth,richG,whirlwind,whirlwind, ← Real.exp_add, ←Real.exp_add]
 apply Real.exp_monotone; linarith only [p' i]
lemma wind_purchase (B:Z.Bounds q η C S)(W:Signed→ Config G n→ℝ)(T:Signed→Forest r)(pQ:∀ i,Envelope (W i))(t:ℝ)(pZ:∀ s,(∫ x:Config G n,aggregateA Z p q β κ k θ (T s) (W s) x∂prior G n) ≤ t): let Y:= fun s x=> (W s) (tailored (T s) x); let H:=segments Z q p β κ k θ Y;
 Integrable H (prior G n) ∧ (∫ x,H x∂ prior G n)≤ t:=by
 intro Y HH
 let v:=prior G n; let A(s):=aggregateA Z p q β κ k θ (T s) (W s); let Φ(s:Signed)(x:Config G n):=A s (pull s 0 x);
 have E(s:Signed): Envelope (A s):= aggregateEnv B (pQ s)
 let M:ℝ:= Fintype.card Signed; have hM:0<M:=by unfold M; exact_mod_cast Fintype.card_pos
 have ha:0≤apportion:=(inv_pos.mpr hM).le
 have hw:∑ _:Signed,apportion=1:=by rw [sum_const,card_univ,nsmul_eq_mul]; exact mul_inv_cancel₀ hM.ne'
 have he(i:Signed): Integrable (fun x=>apportion*Φ i x) v:= ((prior_pull (G:=G) (n:=n) i 0).integrable_comp_of_integrable ((E i).integrable v)).const_mul apportion
 refine ⟨integrable_finsetSum _ (fun i _=> he i),?_⟩; change (∫ x, (∑ i:Signed, apportion * Φ i x)∂v) ≤ t; rw [integral_finsetSum _ (fun i _=> he i)]
 have h(i:Signed):(∫ x:Config G n, apportion*Φ i x∂v)=apportion*∫ x,A i x∂v:=by
    rw [integral_const_mul]; refine congrArg (apportion * ·) ?_; let t:=prior_pull (G:=G) (n:=n) i 0; exact Eq.symm (show _ = ∫ x, Φ i x∂v from (by have ht:= integral_map (μ:=prior G n) (f:=A i) t.measurable.aemeasurable (show AEStronglyMeasurable (A i) _ from (E i).meas.stronglyMeasurable.aestronglyMeasurable); rw [t.map_eq] at ht; exact ht))
 simp_rw [h]; refine (sum_le_sum (fun i _=>mul_le_mul_of_nonneg_left (pZ i) ha)).trans_eq ?_; rw [← sum_mul,hw,one_mul]
end YM.Gleam
end
