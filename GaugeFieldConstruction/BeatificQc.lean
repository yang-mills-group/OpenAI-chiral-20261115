import GaugeFieldConstruction.KestumQc
/-!
# Steps from a mesh to real
-/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.Fathom.Salam
open Function Filter Set TopologicalSpace YM Analysis MeasureTheory Points Bulb Payroll Metric
open scoped Topology BigOperators ContDiff Classical
variable {n : ℕ}
lemma lensContinuousQc :Continuous (fun t:E4×Points (n+1)=> LensQc t.1 t.2):= fuse.symm.continuous.comp (((helm.continuous.comp continuous_snd).add continuous_fst).prodMk continuous_snd)
noncomputable abbrev PieceQc (K:Points (n+2)→ℂ)(p:Test (n+1))(y:E4):ℂ:= ∫ x,p x*K (LensQc y x)
lemma MoneyLateQc (p:Test (n+1))(K:Points (n+2)→ℂ)(c:PlaqueQc K) (y:E4) (h:guild y) (q:∀ x∈tsupport p,LensQc y x∈conf (n+2)): ContinuousAt (PieceQc K p) y :=by
 let T:=tsupport p; let L:=fun x:E4×Points (n+1)=>LensQc x.1 x.2; have lp:Continuous L:= lensContinuousQc
 have ht:IsCompact T:=p.hasCompactSupport
 have he:∀ᶠ z in 𝓝 y,∀ x∈T,L (z,x)∈conf (n+2):=ht.eventually_forall_of_forall_eventually (fun x hx=> (lp.continuousAt.tendsto.eventually ((conf_open _).mem_nhds (q x hx)))) -- product. tune
 obtain ⟨r,e,s⟩:= Metric.mem_nhds_iff.mp he
 let B:=closedBall y (r/2); have hb:B∈𝓝 y:=closedBall_mem_nhds _ (half_pos e)
 have H:IsCompact (L '' (B ×ˢ T)):= ((isCompact_closedBall ..).prod ht).image lp
 obtain ⟨V,u,v⟩:=c.tiled _ H (Set.image_subset_iff.mpr fun ⟨i,j⟩ k=> s (closedBall_subset_ball (half_lt_self e) k.1) j k.2)
 let W(x:Points (n+1)):=‖p x‖*V; have hi:Integrable W:=((p.continuous.integrable_of_hasCompactSupport p.hasCompactSupport).norm).mul_const _
 refine tendsto_integral_filter_of_dominated_convergence W (Eventually.of_forall fun i=> ((p.continuous.measurable.mul (c.bright.comp ((lp.comp (continuous_const.prodMk continuous_id)).measurable))).aestronglyMeasurable)) ?_ hi ((HeelQc y h).mono fun x k=> (show ContinuousAt (fun i:E4=> p x*K (LensQc i x)) y from continuousAt_const.mul ((c.warm _ k).comp_of_eq (f:=fun i:E4=>LensQc i x) ((lp.comp (continuous_id.prodMk continuous_const)).continuousAt) rfl)).tendsto)
 filter_upwards [hb] with i q; apply Eventually.of_forall; intro x
 change ‖p x * K (LensQc i x)‖ ≤ W x
 by_cases h':x∈T; · exact (norm_mul _ _).trans_le (mul_le_mul_of_nonneg_left (v _ ⟨(i,x),⟨q,h'⟩,rfl⟩) (norm_nonneg _))
 unfold W; rw [image_eq_zero_of_notMem_tsupport (f:=p) h']; simp
-- radial window
structure AnnulusQc (e:ℝ) (y:E4): Prop where
 low : e< ‖y‖
 high : ‖y‖< 2*e
lemma annOpenQc (e:ℝ) : IsOpen {y|AnnulusQc e y}:=by rw[show {y|AnnulusQc e y}= norm ⁻¹' Set.Ioo e (2*e) from (by ext; exact ⟨fun h=>⟨h.low,h.high⟩,fun h=>⟨h.1,h.2⟩⟩)]; exact isOpen_Ioo.preimage continuous_norm
lemma fillAnnQc (p:Test (n+1))(e:ℕ→ℝ)(hv:∀ i,0<e i)(u:Tendsto e atTop (𝓝 0)) : ∀ᶠ i:ℕ in atTop, ∀ y:E4,AnnulusQc (e i) y→∀ x∈tsupport p,LensQc y x∈conf (n+2):=by
 let T:=tsupport p; let U:E4→Points (n+1)→Prop:= fun y x=> ∀ i:Fin n, x i.succ ≠ x 0+y; have ht:IsCompact T:=p.hasCompactSupport
 have hEU:∀ᶠ y in 𝓝 (0:E4),∀ x∈T,U y x:= ht.eventually_forall_of_forall_eventually (fun x e=>by
    apply eventually_all.mpr; intro i
    have h1: (0,x)∈{y:E4×Points (n+1) | y.2 i.succ ≠ y.2 0+y.1}:= by simpa using (show x i.succ≠x 0 from (show x∈ conf _ from p.tsupport_subset e).ne i.succ_ne_zero)
    exact (isOpen_ne_fun ((loc i.succ).continuous.comp continuous_snd) (((loc 0).continuous.comp continuous_snd).add continuous_fst)).mem_nhds h1)
 obtain ⟨r,h,k⟩:= Metric.mem_nhds_iff.mp hEU
 filter_upwards [u.eventually (gt_mem_nhds (half_pos h))] with i hE y Y x pX
 have YU:=hv i; have hu:y≠0:=norm_pos_iff.mp (YU.trans Y.low)
 have hw: y∈ball (0:E4) r:=by rw [mem_ball,dist_zero_right]; linarith only [Y.high,hE]
 let z:=LensQc y x; have Hz:helm z=x 0+y:=by simp [z,helm_head,LensQc,cons,head]
 have H: riders z=x:=by ext1 j; simp [riders_tail,Points.tail,z,LensQc,cons]
 apply first_conf _ (H.symm ▸ p.tsupport_subset (a:=x) pX) -- tune x implicit
 rw [H,Hz]; intro j; refine Fin.cases ?_ ?_ j
 · simp [hu]
 intro l; exact k hw x pX l
lemma Lens0p (y:E4)(x:Points (n+1)): (LensQc y x) 0=x 0+y:=by simp [LensQc,cons,head]
lemma LensIp (y:E4)(x:Points (n+1))(i:Fin (n+1)): (LensQc y x) i.succ=x i:=by simp [LensQc,cons]
#print axioms MoneyLateQc
#print axioms fillAnnQc
end YM.GaugeFieldConstruction.Fathom.Salam
