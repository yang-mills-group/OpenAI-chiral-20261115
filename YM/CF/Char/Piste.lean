import YM.CF.Char.Gel
set_option autoImplicit false
noncomputable section
namespace YM.CF.Char
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric Newt Jet
 AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine
 AnalyticBridge.NonflatCovarianceLocality.Matching
open Push.SectorMeasure Next.Fluctuations Next.SectorChange Next.SectorChange.Wisps Next.SectorChange.Schur PhysicalNext.JointLoad PatchReads
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {P:RG.Patch}{G:Gauge}{c f:Side}{S:StepData c f}{T:Tube G S}{A A':Stores S}{F F':Forest S.ratio}{k k':S.Choices} {V W:Config G c}{x C:ℝ}{r l:ℕ}
 {Y: LinkArray G (Frozen A x F)}{Y':LinkArray G (Frozen A' x F')}{o:Site c}
open AnalyticBridge.GaussianFieldAlignment Orthogonal Tensor
variable {n:ℕ}{s d v D:ℝ}
def link_r(S:Side):Directions G S→L[ℝ] Mast G S:= LinearMap.toContinuousLinearMap { toFun:=fun v i=>v (i.1.1,axisEquiv.symm i.1.2) i.2, map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl }
lemma link_art: ‖link_r (G:=G) c‖ ≤ 1:=by
 refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun i=>(pi_norm_le_iff_of_nonneg (by positivity)).mpr fun j=>?_
 rw [one_mul]; exact (PiLp.norm_apply_le ..).trans (norm_le_pi_norm i _)
lemma arte(v:Directions G c):hull G c (link_r c v)=v:=by ext i l; change v (i.1,axisEquiv.symm (coord i.2)) l=_; rw [←Exterior.coord_map,axisEquiv.symm_apply_apply]
abbrev Vmove(x:ℝ)(V: Config G c)(u: Directions G c):=increment V (temp x•u)
lemma concur (z:Site c→G.El)(i:Bond c):Allows n (fun u:Directions G c=>temp x • G.adjoint (z i.1) (u i)) 0 (temp x):=by
 let P:Directions G c→L[ℝ] G.Color:= ContinuousLinearMap.proj i; let H:= Gauges.turn (z i.1)|>.toContinuousLinearMap; let g:= temp x; let p:=H.comp P; have hg:0 ≤ g:= Work.E04.temp_nonneg x
 have ht:‖p‖ ≤ 1:=ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v=>by rw [one_mul]; change ‖G.adjoint _ _‖ ≤ _; rw [G.norm_adjoint]; exact norm_le_pi_norm v i
 exact allows_linear (L:=g•p) (by rw [norm_smul, Real.norm_of_nonneg hg]; exact mul_le_of_le_one_right hg ht) (by rw [map_zero,norm_zero]; exact hg)
lemma shake(z:Site c→G.El)(i:Bond c)(u:Directions G c): gauge z (Vmove x V u) i=G.lieExp (temp x • G.adjoint (z i.1) (u i))*gauge z V i:=by rw [←map_smul,exp_adjoint]; unfold Lattice.gauge Vmove increment; rw [Pi.smul_apply]; group
abbrev blockF (x:ℝ):ℝ:= (radiusB x:ℝ)^5
abbrev tideF(C x:ℝ):ℝ:= C*(blockF x*temp x)
lemma tide_s(C:ℝ): Tendsto (tideF C) atTop (𝓝 0):=by simpa only [mul_zero] using (Work.E09.radiusB_temp 5).const_mul C
abbrev grounded(o:Site c)(A:Stores S)(x:ℝ):Prop:=o∉A.dome (40*radiusB x)
def Fleet(S:StepData c f)(x:ℝ)(V:Config G c)(F:Forest S.ratio)(A:Stores S)(Y:LinkArray G (Frozen A x F))(z:Site c→ G.El)(k:S.Choices)(R:Directions G c→ Mast G c)(o:Site c)(s:ℝ): Prop:=∀ᶠ y in 𝓝 (0:Directions G c), Scan S x o (25*radiusB x) A (bareStores S) F F k k (Lattice.gauge z (Vmove x V y)) (facadeX G (s•R y)) (Gauges.gaugeY z x A F Y) 1
lemma podium(h:grounded o A x)(he:1000  ≤  radiusB x)(hp:AgreeNear id o (25*radiusB x) V W): Scan S x o (25*radiusB x) A (bareStores S) F F k k V W Y 1:=by
 refine ⟨fun i hi=> ?_,fun i _=>rfl,fun i _=>rfl,fun i _=> Iff.rfl,hp,fun i j _ _=>?_⟩
 · have hu:i∉A.place:=fun hp=>h (halo_spec.mpr ⟨i,hp,(separation_comm ..).trans_le (show separation o i  ≤  _ from by omega)⟩)
   rw [iff_false_intro hu,(iff_false_intro (show ¬i∈(bareStores S).place by simp [bareStores,Stores.place]))]
 exact ((notChilled S F x _) j.property).elim
lemma terrain(G:Gauge)(n:ℕ)(hn:1 ≤ n):∃ C:ℝ,0<C ∧∀ᶠ x:ℝ in atTop, let s:=tideF C x; 0<s∧temp x ≤  s ∧ ∀{c f:Side}(S:StepData c f)(V:Config G c)(F:Forest S.ratio)(A:Stores S)(o:Site c), grounded o A x→ A.flags=RG.flags (temp x) V → 100*(1+radiusB x) ≤  c.val→∃ R:Directions G c→ Mast G c,∃ z:Site c→ G.El,(‖R 0‖ ≤ 1/2 ∧ Allows n R 0 (1/2))∧∀(Y k),Fleet S x V F A Y z k R o s:=by
 obtain ⟨D,δ,hD,hδ,H⟩:=log_chart_cost G; obtain ⟨ε,t,hε,ht,h⟩:=pass_n G n hn
 let C':ℝ:=16*81^5*(Fintype.card PlaqAxes:ℝ)+1; have hc:0<C':=by unfold C'; positivity
 let E:=1+D*C'; have he:0<E:=by unfold E; positivity
 let T:=max 1 t; have hT:0<T:=lt_of_lt_of_le zero_lt_one (le_max_left ..)
 let M:= 2*T*E; refine ⟨M,by unfold M; positivity,?_⟩
 filter_upwards [(tide_s C').eventually (ge_mem_nhds hδ),(tide_s E).eventually (ge_mem_nhds hε),Work.E01.radiusB_tendsto.eventually_ge_atTop 1000,eventually_gt_atTop (0:ℝ)] with x hx hp he' hpos
 let B:=radiusB x; let g:=temp x; let t':=tideF E x; have hg:0<g:=by unfold g temp; positivity
 have hB:1 ≤ B:=le_trans (by norm_num) he'; have hv:1 ≤ blockF x:=one_le_pow₀ (show (1:ℝ) ≤ B by exact_mod_cast hB)
 have hh:g  ≤  t':=(le_mul_of_one_le_left hg.le hv).trans (le_mul_of_one_le_left (mul_nonneg (zero_le_one.trans hv) hg.le) (show 1  ≤  E from le_add_of_nonneg_right (by positivity)))
 have hm:0<t':=hg.trans_le hh; intro s; have hz:s=2*T*t':=by unfold s M t' tideF; ring
 have hU:g  ≤  s:=by rw [hz]; apply hh.trans; exact le_mul_of_one_le_left hm.le (by have hT :1 ≤ T:=le_max_left ..; linarith)
 refine ⟨hg.trans_le hU,hU,?_⟩; intro c f S V F A o hQ hV hs
 have hOO (i:Site c)(hi:separation o i ≤ 40*B) (j:PlaqAxes): toll V (i,j) ≤ g:=by
  by_contra! hu; have he:i∈A.flags:=by rw [hV]; exact (flags_spec ..).mpr ⟨(i,j),Work.E01.base_touched _,hu⟩
  exact hQ (halo_spec.mpr ⟨i,Finset.mem_union_right _ he,(separation_comm ..).trans_le hi⟩)
 obtain ⟨z,hz'⟩:=Work.E08.axial_patch o V (25*B) (40*B) (by omega) (by unfold B; omega) g hg.le  hOO
 let R:=gauge z V; let u(i):=G.plog (G.mat (R i)); let L(i:Bond c):Prop:=separation o i.1 ≤ 25*B
 have hr(i:Bond c)(hs:L i):G.chord (R i) ≤  tideF C' x:=by
    apply (hz' i hs).trans; have hb:(1:ℝ) ≤ B:=by exact_mod_cast hB
    have hl: 2*((40*B:ℕ):ℝ)+1 ≤ 81*B:=by push_cast; linarith
    have ht':=(pow_le_pow_left₀ (show 0 ≤ 2*((40*B:ℕ):ℝ)+1 by positivity) hl 5)
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
 refine ⟨F',z,⟨hP.value,hP⟩,fun Y k=>?_⟩
 have h(i:Bond c):∀ᶠ y in 𝓝 0,L i→ gauge z (Vmove x V y) i=increment 1 (A' y) i:=by
    by_cases hi:L i
    · exact ((hK i hi).2).mono fun _ ha _=>ha
    exact Eventually.of_forall fun _ hi'=> (hi hi').elim
 unfold Fleet; filter_upwards [eventually_all.mpr h] with i hi; refine podium hQ he' ?_; intro p he; unfold F' facadeX; rw [smul_inv_smul₀ hS.ne',arte]; exact hi p he
end YM.CF.Char
