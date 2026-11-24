import GaugeFieldConstruction.BasinRP
/-! boundary from strong positive pads, no extra generator outside it. -/
set_option autoImplicit false
set_option maxHeartbeats 350000
noncomputable section
namespace YM.NSF.Boundary
open YM.Boundary Function Mink Set Filter MeasureTheory Analysis Distribution LD Bid Work.C22 Work.C23 Work.C24 OS Small Complex
open scoped BigOperators Topology ContDiff InnerProductSpace NNReal
variable {n m:ℕ}{G:Gauge}{L:Register G}{S T:Table L}{C:LRoom T timeAxis}
variable {B:Small S C}{p q:ℝ≥0}{F:Waves S}{K:Spins S}{W:Surface S}{J:StarOp S}{D:∀ i,Blanket i}{R:S.Rotation}{s:S.RealSpin}
variable (d:PredictionL W F K J B R s){X:W.Aurora D}(H:X.FullBody F)(b: Hull B F J)
variable (v:Fin n→ Letter S)(w:Fin m→ Letter S)
def PtVectorRP(x:Points n):= d.mapSpace (d.system.operators.vector (List.ofFn (forwardRP v x)))
lemma profile_nRP:Tendsto (fun i:ℝ=>Small.profile i n) till (𝓝 0):= by
 apply tendsto_pi_nhds.2; intro i
 have hz:Tendsto (fun r:ℝ=> (i.val+1:ℝ)*r) till (𝓝 0):=by simpa using (tendsto_const_nhds (x:=(i.val+1:ℝ))).mul (show Tendsto id till (𝓝 (0:ℝ)) from tendsto_id.mono_right nhdsWithin_le_nhds)
 exact hz
include H b
variable {U:Type*}{l:Filter U} [l.NeBot] (u:U→ Points n)(t:U→ℝ≥0)(e:U→ Heights n)
lemma PtLoadsRP (t₀:Points n)(hp:Tendsto u l (𝓝 t₀))(ha:Tendsto e l (𝓝 0))(ht:∀ᶠ i in l, Small.ample (t i) (e i)): Tendsto (fun i=> capRP B (forwardRP v (u i)) (t i) (e i)) l (𝓝 (PtVectorRP d v t₀)):=by
 let F':= l ×ˢ till; let f:=fun i=>capRP B (forwardRP v (u i)) (t i) (e i); let E:=PtVectorRP d v t₀; let M:=List.ofFn (forwardRP v t₀); let N:=forwardRP v t₀; let g:=B.heatCup M
 have hv:E=(B.bowls d.link).cold M:= d.assign _
 have hn:Tendsto g till (𝓝 E):=by rw [hv]; exact (B.bowls d.link).chase M
 have hs:Tendsto (fun i: U × ℝ=> inner ℂ (f i.1) (f i.1)) F' (𝓝 (W.kernel J M M)):= (shineRP d H b v v e e t t ha ha ht ht u u t₀ t₀ hp hp).comp tendsto_fst
 have hz:Tendsto (fun i: U × ℝ=> inner ℂ (g i.2) (g i.2)) F' (𝓝 (W.kernel J M M)):= (d.link.here _ _).comp (tendsto_snd.prodMk tendsto_snd)
 have hc:Tendsto (fun i: U × ℝ=> inner ℂ (f i.1) (g i.2)) F' (𝓝 (W.kernel J M M)) := by
    refine (shineRP d H b v v (e ∘ Prod.fst) (fun i:U×ℝ=> Small.profile i.2 _) (t ∘ Prod.fst) (Small.logD ∘ Prod.snd) (ha.comp tendsto_fst) (profile_nRP.comp tendsto_snd) (tendsto_fst.eventually ht) (tendsto_snd.eventually (Eventually.mono (show ∀ᶠ x in till, 0<x from self_mem_nhdsWithin) fun x h=> Small.suitable h)) (u ∘ Prod.fst) (fun _=> t₀) _ _ (hp.comp tendsto_fst) tendsto_const_nhds).congr (fun i=>?_)
    exact congrArg (inner ℂ (f i.1)) ((CupAsRP B N _).symm)
 have hh:Tendsto (fun i: U × ℝ=> inner ℂ (g i.2) (f i.1)) F' (𝓝 (W.kernel J M M)) := by
    have h : ⟪E,E⟫_ℂ=W.kernel J M M:=tendsto_nhds_unique (((hn.comp tendsto_snd).inner (hn.comp tendsto_snd))) hz
    have he: star (W.kernel J M M)=W.kernel J M M:=by rw [← h]; exact inner_conj_symm _ _
    have hr:= (continuous_star.continuousAt.tendsto.comp hc); rw [he] at hr
    exact hr.congr (fun i=> inner_conj_symm _ _)
 have hK:Tendsto (fun i:U × ℝ=> inner ℂ (f i.1-g i.2) (f i.1-g i.2)) F' (𝓝 0) := by
    simp_rw [inner_sub_right,inner_sub_left]
    simpa only [sub_self] using (hs.sub hh).sub (hc.sub hz)
 have hi:Tendsto (fun i:U × ℝ=> f i.1-g i.2) F' (𝓝 0):=by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simp_rw [@norm_eq_sqrt_re_inner ℂ]
    simpa using! (Real.continuous_sqrt.continuousAt.tendsto.comp (Complex.continuous_re.continuousAt.tendsto.comp hK))
 have hg:Tendsto f (Filter.map Prod.fst F') (𝓝 E):=by rw[tendsto_map'_iff]; simpa only [Function.comp_def,sub_add_cancel,zero_add] using! hi.add (hn.comp tendsto_snd)
 rw [show Filter.map Prod.fst F'=l from ?_] at hg; exact hg
 simp [F']
#print axioms PtLoadsRP
end YM.NSF.Boundary
end
