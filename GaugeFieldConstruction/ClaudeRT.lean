import GaugeFieldConstruction.ArtoriusRT
/-! # E^i(f) dx known for partial exterior. Show sides share analytic germ. -/
set_option autoImplicit false
set_option synthInstance.maxSize 15000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.NSF.Boundary
open YM.Boundary Mink Function Set Filter MeasureTheory Complex Finset Distribution Probe Surface PortRT Metric
open scoped Topology BigOperators ContDiff InnerProductSpace NNReal ENNReal
variable {n:ℕ}(k:Fin n)
local notation "ιᵢ" => k.castSucc
local notation "ιⱼ" => k.succ
local notation "Nx"=> τNearRT k
local notation "W_A"=> Full (n+1)
abbrev ΛLitRT (n:ℕ)(g:Bool): Set (ZSideRt n):={w | w.1 ∈ HalfRT g}
variable {G:Gauge}{L:Register G}{S:Table L}{Y:Surface S}{B:∀ i, Blanket i}{F:Waves S}{X:Y.Aurora B}
variable (o:Points n)(y:Heights (n+1))
variable (V:Fin (n+1)→ S.Union)(J:(τNearRT k).Panes X V y)(v:J.sameGround)
abbrev CabinTRt (g:Bool):Fin (n+1)→ S.Union:= if g then V ∘ (Nx).s else V
noncomputable abbrev TPanRt (f:Space3→ℂ)(g:Bool)(w: ZSideRt n):= StemRailRt k g f (X.emit (CabinTRt k V g)) w
variable (f:Space3→ℂ)(hc:Continuous f)(e:HasCompactSupport f)(g:0∉tsupport f)
noncomputable abbrev ΛArchRt : ZSideRt n:= (0, glow o (dawn (remΛ ιᵢ y)))
include hc e g J v
local notation "D"=> tsupport f
local notation "ΛB"=> TPanRt (X:=X) k V f
local notation "w"=> ΛArchRt k o y
lemma SideSaLiveRT: QuiltLocalRt (μ:=volume) (ΛLitRT n) (TPanRt (X:=X) k V f) (ΛArchRt k o y) (tsupport f) :=by
 apply quiltCombineRt e; intro m h
 let t:Points (n+1) := addMeterRT k (position m 0,o)
 have hp:t∈(Nx).gap:= centRoomRT k o m (fun e=>g (e ▸ h))
 let φ:= glow t (dawn y); have hy: QchIRt k false w m=φ := centχRT k o y J.permitted _
 let T:=(J.original t hp).extendF; have hZ: T =ᶠ[𝓝[(Nx).name ⁻¹' tube (n+1)] φ] ((X.emit (V ∘ (Nx).s)) ∘ (Nx).name):=
    ((J.reaches v t hp).filter_mono nhdsWithin_le_nhds).trans (J.tilted t hp|>.fits)
 have hW: T =ᶠ[𝓝[tube (n+1)] φ] X.emit V:= (J.original t hp).fits
 have hB: ∀ᶠ z in 𝓝 φ, AnalyticAt ℂ T z ∧ (z∈tube (n+1)→T z=X.emit V z) ∧ (z∈(Nx).name ⁻¹' tube (n+1)→ T z=X.emit (CabinTRt k V true) ((Nx).name z)):=
    ((J.original t hp).doc.eventually_analyticAt).and ((eventually_nhdsWithin_iff.1 hW).and (eventually_nhdsWithin_iff.1 hZ))
 obtain ⟨r,hr,hR⟩:=Metric.mem_nhds_iff.mp hB
 let χ:=fun z:ZSideRt n × Space3 => QchIRt k false z.1 z.2
 obtain ⟨d,hd,hD⟩:=Metric.mem_nhds_iff.mp (((χTintRt k false).tendsto (w,m)).eventually (by change ball φ r∈𝓝 (QchIRt k false _ _); rw[hy]; exact ball_mem_nhds _ hr)) -- tune
 let K:= closedBall m (d/2)
 let A:= ball w d
 have ht:MapsTo χ (A ×ˢ K) (ball φ r):=by
    intro z hz; exact hD ((ball_prod_same w m d).symm ▸ ⟨hz.1,closedBall_subset_ball (half_lt_self hd) hz.2⟩ : z∈ball (w,m) d) -- tune
 have Ht: AnalyticOnNhd ℂ T (ball φ r):=fun z p=>(hR p).1
 refine ⟨ball m (d/2),Metric.isOpen_ball,mem_ball_self (half_pos hd),?_⟩
 intro U s q; have p:U⊆K:= s.trans (inter_subset_right.trans ball_subset_closedBall)
 let SaU(z:ZSideRt n):=∫ m in U,f m * T (QchIRt k false z m)
 refine ⟨SaU,TαNormalRT k false f hc T _ Metric.isOpen_ball Ht (isCompact_closedBall ..) q p ht Metric.isOpen_ball _ (mem_ball_self hd),?_⟩
 intro g'; filter_upwards [self_mem_nhdsWithin, (roomXRt k o y J.permitted g').filter_mono nhdsWithin_le_nhds, (Eventually.filter_mono nhdsWithin_le_nhds (ball_mem_nhds w hd))] with z hz hg ha
 change IntegrableOn (ΛB g' z) U ∧ _; have he: ΛB g' z=ᵐ[volume.restrict U] StemRailRt k false f T z:= by
    filter_upwards [ae_restrict_mem q] with y hy
    unfold TPanRt StemRailRt; congr 1; obtain ⟨-,a,b⟩:=hR (@ht (z,y) ⟨ha,p hy⟩); cases g' with
    | false=> exact (a (hg hz y)).symm
    | true=> exact (b (hg hz y)).symm
 exact ⟨(TownGlassRT k false f hc T _ Metric.isOpen_ball Ht (isCompact_closedBall ..) p ht z ha).congr he.symm,integral_congr_ae he⟩
#print axioms SideSaLiveRT
end YM.NSF.Boundary
end
