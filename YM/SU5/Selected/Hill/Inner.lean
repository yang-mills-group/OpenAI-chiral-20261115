import YM.SU5.Selected.Hill.Mast
/-! Inner integration. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Hill.Box
open Function Filter Metric Finset Lattice Tree Wilson RG Pressure Exterior Work.F03 Precision MeasureTheory Chene Trunk FreeResolvent Matrix Chene.Tail Melody SectorNext.Vacuum.FlatTree Calculus Next.Rank.Axial Chene.Perks
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius MatrixOrder Matrix InnerProductSpace Kronecker
open Next.SectorChange Luge SectorTools.PhysicalGaussianSwitch
open CF.Graph
variable {G:Gauge}{n:Side}{r:Side}{S:Lots n}{B' B R m:ℕ}
variable {P:BudgetPoint}{W:PathData G}{C:Clip}{σ X D θ a τ e b:ℝ}
variable (Z:ChartRatio G)(L: Next.Rank.Spindle.Rules G)(p:LocalRatio Z) (h:W.Bounds C σ X D)
variable (κ:ℝ)(s:0<b)(F:B+2*R+4≤B')(v:m+2≤ B)(f:2*R+3 ≤ B)(w:7≤ B)
variable (g:4*r.val*P.threshold ≤ e)(j:e ≤ L.c)(U:2*e<Z.radius)(o:0<θ)(u:θ<1)
variable (k:2≤ P.threshold * Real.exp ((m:ℝ) / C.relaxation))(t:∀ x:G.Color, ‖x‖≤ 2*e→ Z.J x ≤ Real.exp τ)
abbrev fee₂ (S:Lots n)(C:Clip)(L:Next.Rank.Spindle.Rules G)(b X D θ e σ a κ:ℝ)(R:ℕ) := (κ-b*daily C a)* S.card+fee₁ n C L b X D θ e σ a R
abbrev fee₃ (Z:ChartRatio G)(r:Side)(S: Lots n)(B':ℕ)(a τ b d:ℝ):= Real.exp (a+(Board r S B').card*τ)* (spare Z b)^ (Board r S B').card / Real.sqrt d
include p s F v f w g j U o u k t
set_option maxHeartbeats 380000 in
lemma purchased (d:(race r S B' B R h θ).PosDef)(y:Borders r S B' G):
 (∫ x:goods r S B' G,pours W C P b κ S (tones r S B' x y)∂ piHaar G _) ≤ fee₃ Z r S B' (fee₂ S C L b X D θ e σ P.threshold κ R) τ b (race r S B' B R h θ).det:=by
 let G':= Board r S B'; let P₁(x:goods r S B' G):= pours W C P b κ S (tones r S B' x y); let a:=fee₂ S C L b X D θ e σ P.threshold κ R; let P₂(u:LogArray G (seat_set r S B')):= (mouth Z).indicator (fun i=> pay Z i * P₁ (release 1 i)) u; let H:=piHaar G (seat_set r S B'); let M:= race r S B' B R h θ; let e₀:= (1:goods r S B' G)
 have hP:Envelope P₁:=by
    obtain ⟨m₀,A,hA⟩:= pours_env W C P b κ h S; exact ⟨m₀.comp (tones_mb r S B' y),A,fun x=> hA _⟩
 have hp:= p.scale
 have h₁:∀ y∉covered Z e₀,P₁ y=0:=by
    intro x hl; unfold P₁ pours; split; next hx=>
       exfalso; apply hl; intro i _; obtain ⟨A,D⟩:= charts_up Z L y _ (show 1≤B' by omega) hx.symm P.threshold_pos.le g j U i; exact ⟨_,⟨_,mem_ball_zero_iff.mpr (D.trans_lt U), rfl⟩,by rw [A]; change _*1=_; simp ⟩
    rfl
 obtain ⟨hx,hy⟩:= release_integral p e₀ P₁ hP.meas.stronglyMeasurable h₁
 have ht: Integrable P₂:= hx.mp (hP.integrable H); have hE:(∫ x,P₁ x∂H)=∫ y,P₂ y:=hy
 let A:= (Z.scale*Real.exp τ)^G'.card; let Q:=(1-θ) • flare R (lesson r S B) h; let P₃:= keyUp (tones r S B' 1 y)
 have hz:Q.PosSemidef:= (squared _).smul (sub_pos.mpr u).le; let ρ:Pens G G'→ Pens G (EdgeT n):= palace _ S B'; have hg:M=Q.submatrix ρ ρ:=rfl
 obtain ⟨Y,htY⟩:= Luge.Hotels hz ρ hg d P₃
 let u₁(x:Scene G (seat_set r S B')):= Real.exp (-(b)*quad M (x-Y)/2)
 have hη:0≤ A:=by unfold A; positivity
 have hB (x: Scene G G'): P₂ (tape x) ≤ (A*Real.exp a) * u₁ x:=by
    -- order of params test output
    have h := buy Z L p h κ y s F v f w g j U o u k t x
    apply LE.le.trans h; unfold u₁; rw [mul_assoc,← Real.exp_add]; apply mul_le_mul_of_nonneg_left _ hη; apply Real.exp_monotone; apply add_le_add le_rfl ?_ -- tune
    apply div_le_div_of_nonneg_right _ (by norm_num : (0:ℝ)≤2); apply mul_le_mul_of_nonpos_left _ (by linarith only [s]); apply (htY x).trans_eq; unfold Q fare quad; rw [Matrix.smul_mulVec, dotProduct_smul]; rw [smul_eq_mul,flash_ok]; rfl
 let g':=(Real.sqrt (2*Real.pi*(coupling b)^2)); let W':=g'^Fintype.card (Pens G G') / Real.sqrt M.det
 obtain ⟨hp',hv'⟩:= Luge.exp_integral d s Y
 change (∫ x,P₁ x∂H) ≤ fee₃ Z _ _ _ a τ b _; rw [hE,← tape_volume.integral_comp' P₂]; apply (integral_mono ((tape_volume (G:=G)).integrable_comp_of_integrable ht) (hp'.const_mul (A * Real.exp a)) hB).trans_eq;
 change (∫ x:Scene G G',A*Real.exp a*u₁ x)=_; rw [integral_const_mul, show (∫ x:Scene G G', u₁ x)=W' from hv']; have hA:A*W'= Real.exp ((G'.card:ℝ)*τ)*(spare Z b)^G'.card / (Real.sqrt M.det):=by
    unfold A W' g'; simpa only [Fintype.card_coe] using (accounts Z hp (↑G':Type) s (D:= M.det) τ)
 rw [_root_.mul_comm A, mul_assoc,hA]; unfold fee₃; rw [Real.exp_add a (↑(Board r S B').card*τ), ← _root_.mul_div_assoc, ← mul_assoc]
end YM.Hill.Box
#print axioms YM.Hill.Box.purchased
