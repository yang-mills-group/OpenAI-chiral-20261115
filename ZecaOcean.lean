import ZecaFloodtide
set_option autoImplicit false
set_option maxHeartbeats 220000
noncomputable section

namespace YM.ZecaSky
open Function Metric Filter Asymptotics Set
open scoped ComplexOrder InnerProductSpace BigOperators Topology

open MeasureTheory
variable {A:ℕ→ℂ→ℂ} {T:ℝ}{W:ℕ→ℝ→ℂ}
    {K:ℂ→ℂ} {φ:ℝ→ℂ}

lemma shore (h:Seaward A) (p:Splash A K)
 {x:ℝ}(u:0<x)(c:Continuous φ) :
 Tendsto (fun i=>shellI (A i) T φ x) atTop (𝓝 (shellI K T φ x)):=by
 obtain ⟨d,C,ck,b⟩:=h.cost
 let D:=C*spur d x
 refine tendsto_integral_filter_of_dominated_convergence (fun y=>‖φ y‖*D)
      (Eventually.of_forall (fun i=>
         (c.mul (surf_c (h.enters i).continuousOn _ u)).aestronglyMeasurable))
      (Eventually.of_forall fun i=>ae_of_all _ (fun y=>?_)) ?_
      (ae_of_all _ (fun y=> Tendsto.const_mul (φ y) (enters_all h p _ (tide_p u y))))
 · rw [norm_mul]
   apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
   simpa only [D,tide_re] using b i _ (tide_p u y)
 · exact (c.norm.mul continuous_const).continuousOn.integrableOn_Icc

def Bay (T:ℝ)(K:ℂ→ℂ) :=
 ContinuousOn (fun x:ℝ×ℝ=> K (tide x.1 x.2)) ((Icc 0 1) ×ˢ (Icc (-T) T))
lemma cove (p:Bay T K)(c:Continuous φ):
 Tendsto (shellI K T φ) (𝓝[>] 0) (𝓝 (shellI K T φ 0)):=by
 let U:=Icc (0:ℝ) 1
 let V:=Icc (-T) T
 have b:ContinuousOn (fun x:ℝ×ℝ=> φ x.2*K (tide x.1 x.2)) (U ×ˢ V):=
      (c.comp continuous_snd).continuousOn.mul p
 have j:U∈𝓝[>] (0:ℝ):= Icc_mem_nhdsGT zero_lt_one
 have ue:IsCompact (U ×ˢ V):=isCompact_Icc.prod isCompact_Icc
 obtain ⟨D,d⟩:= ue.bddAbove_image b.norm
 have m(x:ℝ)(a:x∈U):ContinuousOn (fun t=>φ t*K (tide x t)) V:=
    b.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun y t=>⟨a,t⟩)
 have l:∀ᶠ x in 𝓝[>] 0, x∈U:=j
 refine tendsto_integral_filter_of_dominated_convergence (fun _=>D)
   (l.mono (fun x a=> (m _ a).aestronglyMeasurable measurableSet_Icc))
   (l.mono (fun x a=> (ae_restrict_mem measurableSet_Icc).mono (fun t v=>d ⟨(x,t),⟨a,v⟩,rfl⟩)))
   continuous_const.continuousOn.integrableOn_Icc
   ((ae_restrict_mem measurableSet_Icc).mono (fun t v=>?_))
 have g:Tendsto (fun z:ℝ×ℝ=>φ z.2*K (tide z.1 z.2)) (𝓝[U×ˢV] (0,t)) _ :=
     b (x:=(0,t)) (show _ from ⟨⟨le_refl _,zero_le_one⟩,v⟩)
 have yz:Tendsto (fun x:ℝ=>(x,t)) (𝓝[>] 0) (𝓝[U×ˢV] (0,t)) :=
   tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
     ((tendsto_id.prodMk_nhds tendsto_const_nhds).mono_left nhdsWithin_le_nhds)
     (l.mono (fun x p=>⟨p,v⟩))
 exact g.comp yz

theorem current_boundary (h:Seaward A)(k:Splash A K)
    (p:0<T)(t:Bay T K)(q:Temporal T W):
   Tendsto (fun i=>sandpiperI (A i) T (W 0)) atTop
     (𝓝 (shellI K T (W 0) 0)):=by
 refine Metric.tendsto_nhds.mpr fun r e=>?_
 have e0:0<r/4:=by positivity
 let j(u x):= shellI u T (W 0) x
 have y:= (Metric.tendsto_nhds.mp (cove t (q.slow 0))) _ e0
 obtain ⟨x,u,v,w⟩:= ((eventually_mem_nhdsWithin).and
     ((jetty_uniform h p q _ e0).and y)).exists
 filter_upwards [Metric.tendsto_nhds.mp (shore (T:=T) h k u (q.slow 0)) _ e0] with i m
 calc
   _≤dist (sandpiperI (A i) T (W 0)) (j (A i) x)+
         dist (j (A i) x) (j K 0):= dist_triangle ..
   _≤ r/4+(r/4 + r/4):= add_le_add (v _) <| (dist_triangle _ (j K x) _).trans
               (add_le_add m.le w.le)
   _ < r :=by linarith
#print axioms current_boundary
