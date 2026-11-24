import YM.CF.Slate.Solar
import YM.CF.Slate.Roam
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Slate
open Forge Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Push.Uniform (curve Slope tint partSpace meetVar)
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD AnalyticBridge.SectorAffine Oriented Esti Vol Bloch Exterior Jet
variable {G:Gauge}{c f:Side}{S:StepData c f}{r v l n:ℕ}{w x β d:ℝ}{q:Chi}{T:Tube G S}{F:Forest S.ratio}{E A:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup A][NormedSpace ℝ A]
open AnalyticBridge.GaussianFieldAlignment Orthogonal Tensor
open AnalyticBridge.NonflatCovarianceLocality.Matching
lemma hustle(G:Gauge)(b n:ℕ)(hn:1 ≤ n):∃ C:ℝ,0<C ∧∀ᶠ x:ℝ in atTop, let s:=tideF C x; 0<s∧temp x ≤  s ∧ ∀{c f:Side}(S:StepData c f)(V:Config G c)(A:Stores S)(o:Site c), o∉ A.dome ((b+2)*radiusB x)→ A.flags=RG.flags (temp x) V → (b+b+101)*radiusB x ≤  c.val→∃ R:Directions G c→ Mast G c,∃ z:Site c→ G.El,(‖R 0‖ ≤ 1/2 ∧ Allows n R 0 (1/2))∧∀ᶠ y in 𝓝 (0:Directions G c), AgreeNear id o ((b+1)*radiusB x) (Lattice.gauge z (Vmove x V y)) (facadeX G (s•R y)):=by
 obtain ⟨D,δ,hD,hδ,H⟩:=log_chart_cost G; obtain ⟨ε,t,hε,ht,h⟩:=pass_n G n hn
 let C':ℝ:=16*((b:ℝ)+(b:ℝ)+5)^5*(Fintype.card PlaqAxes:ℝ)+1; have hc:0<C':=by unfold C'; positivity
 let E:=1+D*C'; have he:0<E:=by unfold E; positivity
 let T:=max 1 t; have hT:0<T:=lt_of_lt_of_le zero_lt_one (le_max_left ..)
 let M:= 2*T*E; refine ⟨M,by unfold M; positivity,?_⟩
 filter_upwards [(tide_s C').eventually (ge_mem_nhds hδ),(tide_s E).eventually (ge_mem_nhds hε),Work.E01.radiusB_tendsto.eventually_ge_atTop 1000,eventually_gt_atTop (0:ℝ)] with x hx hp he' hpos
 let B:=radiusB x; let g:=temp x; let t':=tideF E x; have hg:0<g:=by unfold g temp; positivity
 have hB:1 ≤ B:=le_trans (by norm_num) he'; have hv:1 ≤ blockF x:=one_le_pow₀ (show (1:ℝ) ≤ B by exact_mod_cast hB)
 have hh:g  ≤  t':=(le_mul_of_one_le_left hg.le hv).trans (le_mul_of_one_le_left (mul_nonneg (zero_le_one.trans hv) hg.le) (show 1  ≤  E from le_add_of_nonneg_right (by positivity)))
 have hm:0<t':=hg.trans_le hh; intro s; have hz:s=2*T*t':=by unfold s M t' tideF; ring
 have hU:g  ≤  s:=by rw [hz]; apply hh.trans; exact le_mul_of_one_le_left hm.le (by have hT :1 ≤ T:=le_max_left ..; linarith)
 refine ⟨hg.trans_le hU,hU,?_⟩; intro c f S V A o hQ hV hs
 have hOO (i:Site c)(hi:separation o i ≤ (b+2)*B) (j:PlaqAxes): toll V (i,j) ≤ g:=by
  by_contra! hu; have he:i∈A.flags:=by rw [hV]; exact (flags_spec ..).mpr ⟨(i,j),Work.E01.base_touched _,hu⟩
  exact hQ (halo_spec.mpr ⟨i,Finset.mem_union_right _ he,(separation_comm ..).trans_le hi⟩)
 obtain ⟨z,hz'⟩:=Work.E08.axial_patch o V ((b+1)*B) ((b+2)*B) (by simp_rw [Nat.add_mul]; omega) (by unfold B; simp_rw [Nat.add_mul] at *; omega) g hg.le  hOO
 let R:=gauge z V; let u(i):=G.plog (G.mat (R i)); let L(i:Bond c):Prop:=separation o i.1 ≤ (b+1)*B
 have hr(i:Bond c)(hs:L i):G.chord (R i) ≤  tideF C' x:=by
    apply (hz' i hs).trans; have hb:(1:ℝ) ≤ B:=by exact_mod_cast hB
    have hl: 2*(((b+2)*B:ℕ):ℝ)+1 ≤ ((b:ℝ)+(b:ℝ)+5)*B:=by push_cast; linarith
    have ht':=(pow_le_pow_left₀ (show 0 ≤ 2*(((b+2)*B:ℕ):ℝ)+1 by positivity) hl 5)
    have hh:= mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht' (show (0:ℝ) ≤ 16 by norm_num)) (show (0:ℝ) ≤ Fintype.card PlaqAxes by positivity)) hg.le
    apply hh.trans; change _ ≤ C'*((B:ℝ)^5*g); unfold C'; nlinarith only [mul_nonneg (show 0 ≤ (B:ℝ)^5 by positivity) hg.le]
 let f(i:Bond c)(y:Directions G c):=g • G.adjoint (z i.1) (y i)
 have hUr(i:Bond c)(hw:L i): G.lieExp (u i)=R i ∧ ‖u i‖  ≤  t':=by
    have hv:= H (R i) ((hr i hw).trans hx); refine ⟨hv.1,hv.2.trans ((mul_le_mul_of_nonneg_left (hr i hw) hD.le).trans ?_)⟩
    unfold t' tideF; rw [←mul_assoc]; exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (show (0:ℝ) ≤ 1 by norm_num)) (mul_nonneg (zero_le_one.trans (show 1 ≤ blockF x by assumption)) hg.le)
 let A'(y:Directions G c):Directions G c:=fun i=>if L i then mount (f i y,u i) else 0
 have hK (i:Bond c)(he:L i):Allows n (fun y=> A' y i) 0 (T*t') ∧ ∀ᶠ y in 𝓝 0,gauge z (Vmove x V y) i=increment 1 (A' y) i:=by
    obtain ⟨h₁,h₂⟩:= h (f i) 0 t' hm hp ((concur (x:=x) z i).mono hh) (u i) (hUr i he).2
    simp only [increment,A',if_pos he, Pi.one_apply,mul_one]
    refine ⟨h₁.mono (mul_le_mul_of_nonneg_right (le_max_right ..) hm.le),?_⟩
    filter_upwards [h₂] with y hy; rw [hy,shake,(hUr i he).1]
 have hv: Allows n A' 0 (T*t'):=by
    refine allows_pi (mul_nonneg hT.le hm.le) fun i=>?_
    by_cases hi:L i
    · exact (hK i hi).1
    simp_rw [A',if_neg hi]; exact allows_const _ (by rw [norm_zero]; positivity)
 let F'(y):=s⁻¹ • link_r c (A' y); have hS:0<s:=hg.trans_le hU
 have hP:Allows n F' 0 (1/2):=by
    apply (((hv.linear (link_r c) (link_art (G:=G) (c:=c))).smul s⁻¹).mono ?_); rw [one_mul,abs_of_pos (inv_pos.mpr hS),hz]; exact le_of_eq (by field_simp)
 refine ⟨F',z,⟨hP.value,hP⟩,?_⟩
 have h(i:Bond c):∀ᶠ y in 𝓝 0,L i→ gauge z (Vmove x V y) i=increment 1 (A' y) i:=by
    by_cases hi:L i
    · exact ((hK i hi).2).mono fun _ ha _=>ha
    exact Eventually.of_forall fun _ hi'=> (hi hi').elim
 filter_upwards [eventually_all.mpr h] with i hi; intro p he; unfold F' facadeX; rw [smul_inv_smul₀ hS.ne',arte]; exact hi p he
end YM.CF.Slate
