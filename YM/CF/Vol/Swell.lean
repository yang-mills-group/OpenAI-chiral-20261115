import YM.CF.Vol.Slush
set_option autoImplicit false
noncomputable section
namespace YM.CF.Vol
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric
 AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine Char Newt
open Push.SectorMeasure AnalyticBridge.RelativeLogdet.Ink
open Push Push.Uniform Hors Finset Laurent Bloch
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {P:RG.Patch}{G:Gauge}{c f:Side}{S:StepData c f}{T:Tube G S}{K:Teller G}{F:Forest S.ratio}{X E B:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup B][NormedSpace ℝ B]{t x s D A C Q V r:ℝ}{i n l:ℕ}
open Tube Next.Fluctuations Work.F03 Nacre
open Next.SectorChange AnalyticBridge.GaussianFieldAlignment Oriented Rows
variable {k:S.Choices}{m:ℕ}
def gplot(A:ℕ→ Atom G l)(u:Config G c)(x:Site c):ℝ:=∑' i,(A i).unmasked u x
def batch(A:ℕ→ Atom G l)(t:ℕ):ℕ→ Atom G l:=fun i=> if (A i).length ≤ t then A i else dimA (A i)
lemma barn{A:ℕ→Atom G l}(p:SumBudget (fun i=>(A i).budget s) C)(t:ℕ): SumBudget (fun i=> (batch A t i).budget s) C:= by
 let X(i:ℕ):=(batch A t i).budget s; have hp i:0 ≤ X i:=by unfold X batch; split; exact p.1 i; rw [dimB]
 have hy i:X i ≤ _:=show X i ≤ (A i).budget s from by unfold X batch; split; rfl; rw [dimB]; exact p.1 i
 have hS:Summable X:= Summable.of_nonneg_of_le hp hy p.2.1; exact ⟨hp,hS,(hS.tsum_le_tsum hy p.2.1).trans p.2.2⟩
lemma batch_limit(T:ℕ→ Atom G l)(x:Site c)(t:Bid.Dir G c)(p:SumBudget (fun i=>(T i).budget s) C)(ht:0<s) : Tendsto (fun u:ℝ=> gplot T (represent (u • t)) x/u^l) (𝓝[≠] 0) (𝓝 (∑' i,(T i).poly fun j=> faceCurl (slotFace ((T i).leg j) x) t)):=by
 obtain ⟨B,H,h⟩:= slots_bound t; unfold gplot; simp_rw [← tsum_div_const]; apply tendsto_tsum_of_dominated_convergence (p.2.1.mul_right (B^l)) (fun i=> atom_limit _ _ _) ?_
 filter_upwards [h] with u hu i
 rw [atom_scale (T i),Real.norm_eq_abs]; exact (poly_bound _ _ B fun j=> hu x _).trans (mul_le_mul_of_nonneg_right ((T i).lower_budget s ht) (pow_nonneg H l))
lemma floorZ {g:Ratio c f}{F: Forest g}(T:ℕ→Atom G l)(h:SumBudget (fun i=>(T i).budget s) C)(ht:0<s)(H:PaintSupply G n D)(x:Positions (Joint F G))(hp:‖x‖<1)(σ:Signed)(i:Site f):
 let a:=entryWidth n g.count s
 let f(y):=gplot T (signedFine F y σ) i
 Allows n f x (C*atomCost G D s n l * (1+ townCost G*countCost a)^n):=by
 intro a f; have he:=atom_beacon F σ ht h H x (mem_ball_zero_iff.mpr hp) i; have ha:= width_positive ht n g.count; have hc:=mul_nonneg ((tsum_nonneg h.1).trans h.2.2) (atomCost_nn H ht l)
 refine ⟨label_analytic F T ht h σ H i x (mem_ball_zero_iff.mpr hp),fun j hj=>?_⟩; exact (stall _ _ _ (he j hj) (town F) hc ha).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) (count_pos ha).le)) hj) hc)
lemma asp {T:ℕ→ Atom G l}(p:SumBudget (fun i=>(T i).budget s) C)(ht:0<s)(hp:3 ≤ l)(σ: Signed)(i:Site c):
 let F(y:Bid.Dir G c):=gplot T (pull σ 0 (represent y)) i
 ContDiffAt ℝ ω F 0 ∧ cFoot 3 F:=by
 intro F; have he : ContDiffAt ℝ ω F 0:=by
    let G'(x:Bid.Dir G c):= Bid.pulled x σ
    have hh x : represent (G' x) = pull σ 0 (represent x):=Lift.turned_repr ..
    let g(z) := Work.F02.physical (represent (G' z))
    let L(A:Work.F02.Ambient G c) := ∑' j,Work.F02.atomExt (T j) i A -- tune Pull string ext namespace
    have hb:ContDiffAt ℝ ω g 0:= Work.F02.physical_contDiffAt (A:=fun z=> represent (G' z)) fun i=> by
        simp_rw [hh,ProjectorNext.Equivariance.pull_formula]; split
        · simp_rw [G.mat_inv]; exact ((show G.Mat ≃L[ℝ] G.Mat from starL ℝ).contDiff.comp (represent_smooth _)).contDiffAt
        exact (represent_smooth _).contDiffAt
    rw [show F=Complex.reCLM ∘ (L ∘ g) from funext fun y=> by unfold F L g; simp only [Function.comp_apply,hh]; rw [Work.F02.atomExt_real ht p]; rfl]; exact Complex.reCLM.contDiff.contDiffAt.comp _ (((Work.F02.atomExt_series ht p i _).contDiffAt.restrict_scalars ℝ).comp (f:=g) _ hb)
 refine ⟨he,nextF (he.of_le (show (2:ℕ)≤ω from le_top)) ?_⟩
 intro v; unfold F; simp_rw [Work.F03.represent_pulled σ,smul_eq_mul, inv_mul_eq_div]; exact Extra.Iteration.Jets.drop (show 2<l by omega) (batch_limit T i _ p ht)
end YM.CF.Vol
