import GaugeFieldConstruction.WaxportRT
import GaugeFieldConstruction.BironRT
/-!
 # f integral extension tracked for all real points, boundary at equal imaginary clocks pair. Center panels. ∂_w fancert.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 15000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.NSF.Boundary
open YM.Boundary Mink Function Set Filter MeasureTheory Complex Finset Distribution Probe Surface PortRT Metric
open scoped Topology BigOperators ContDiff InnerProductSpace NNReal ENNReal
variable {n:ℕ}(k:Fin n)
local notation "Nx"=> τNearRT k
local notation "Ψ"=> ZSideRt n
variable {G:Gauge}{L:Register G}{S:Table L}{Y:Surface S}{B:∀ i, Blanket i}{F:Waves S}{X:Y.Aurora B}
variable (T:Axis→Axis→ S.Union)(e:MintDΛ (X:=X) T)(p:X.FullBody F)
variable (V:Fin n→S.Union)(a:Axis)(o:Points n)(y:Heights (n+1))
variable (J:∀ i:Axis,(τNearRT k).Panes X (TxRT k T V a i) y)(v:∀ i,(J i).sameGround)
variable (f:Space3→ℂ)(hc:ContDiff ℝ ∞ f)(h:HasCompactSupport f)(hF:f=ᶠ[𝓝 0] 1)
local notation "H_W"=> PanProjRT (X:=X) k T V a f timeAxis
local notation "D_rt"=> DawnSideRt (X:=X) k T V a f
local notation "ΛE"=> ΛArchRt k o y
abbrev αVertRT (k:Fin n) (y:Heights (n+1)):= remΛ k.castSucc y
lemma litΓRt (n:ℕ)(g:Bool): ΛLitRT n g=HalfRT g ×ˢ univ:=Set.ext fun x=>⟨fun h=>⟨h,mem_univ _⟩,fun h=>h.1⟩
lemma litOpenRt (n:ℕ)(g:Bool): IsOpen (ΛLitRT n g):=by rw [litΓRt]; exact (halfOpenRT g).prod isOpen_univ
lemma litCloseRt (g:Bool): (𝓝[ΛLitRT n g] (ΛArchRt k o y)).NeBot:=by apply mem_closure_iff_nhdsWithin_neBot.mp; rw[litΓRt,closure_prod_eq,closure_univ]; exact ⟨zeroHRT g,mem_univ _⟩
lemma halfχVRt (g:Bool):Convex ℝ (HalfRT g):=by
 cases g
 · exact (convex_Iio (0:ℝ)).linear_preimage Complex.imCLM.toLinearMap
 exact (convex_Ioi (0:ℝ)).linear_preimage Complex.imCLM.toLinearMap
-- scale.A
lemma foyerΛRT (g:Bool)(v:(τNearRT k).Fleck y): ∃ r:ℝ,0<r ∧ MapsTo (fun z:ZSideRt n × Space3=>QchIRt k g z.1 z.2) ((ΛLitRT n g∩ ball (ΛArchRt k o y) r) ×ˢ univ) (tube (n+1)):=by
 obtain ⟨r,hr,hR⟩:= Metric.mem_nhds_iff.mp (roomXRt k o y v g); exact ⟨r,hr,fun z b=> hR b.1.2 b.1.1 z.2⟩
-- use ∀ i
include J v hF h hc p
lemma dualFacturaRT : ∃ Q: ZSideRt n →ℂ, AnalyticAt ℂ Q (ΛArchRt k o y) ∧ ∀ (g:Bool),DawnSideRt (X:=X) k T V a f g =ᶠ[𝓝[ΛLitRT n g] (ΛArchRt k o y)] Q:=by
 choose H C A using fun i:Fin 3=> SideSaLiveRT k o y _ (J i.castSucc) (v _) (dxTRt i f) (show Continuous (dxTRt i f) from (hc.continuous_fderiv (by simp)).clm_apply continuous_const) (h.fderiv_apply ..) (show 0 ∉ tsupport (dxTRt i f) from notMem_tsupport_iff_eventuallyEq.2 (by filter_upwards [hF.fderiv (𝕜:=ℝ)] with x t; unfold dxTRt; rw [t,show fderiv ℝ (1:Space3→ℂ) x=0 from fderiv_const_apply ..]; simp))
 refine ⟨fun u=> ∑ i:Fin 3,H i u, Finset.analyticAt_fun_sum _ (fun i _=> C i),fun g=>?_⟩
 obtain ⟨r,p',hR⟩:=foyerΛRT k o y g ((J 0).permitted)
 filter_upwards [eventually_all.mpr (fun i=>A i g)] with y e
 refine Finset.sum_congr rfl fun i _=> ?_; exact ((PaneBandsRT k T p V a f hc h g ((litOpenRt n g).inter Metric.isOpen_ball) hR y i.castSucc).symm.trans (e i).2)
include e
lemma VestAuraRT : ∃ G:Bool→ZSideRt n→ℂ, ∃ Q:ZSideRt n→ℂ,AnalyticAt ℂ Q (ΛArchRt k o y) ∧ ∀ g:Bool, AnalyticAt ℂ (G g) (ΛArchRt k o y) ∧ G g =ᶠ[𝓝[ΛLitRT n g] (ΛArchRt k o y)] PanProjRT (X:=X) k T V a f timeAxis g ∧ DawnSideRt (X:=X) k T V a f g =ᶠ[𝓝[ΛLitRT n g] (ΛArchRt k o y)] Q ∧ SunStrRt (G g) =ᶠ[𝓝 (ΛArchRt k o y)] Q :=by
 obtain ⟨Q,i,Hi⟩:= dualFacturaRT k T p V a o y J v f hc h hF
 have he(g:Bool): ∀ᶠ z:Ψ in 𝓝[ΛLitRT n g] ΛE,AnalyticAt ℂ (H_W g) z ∧ SunStrRt (H_W g) z= Q z:=by
    obtain ⟨r,p',hR⟩:=foyerΛRT k o y g ((J 0).permitted)
    filter_upwards [Eventually.filter_mono nhdsWithin_le_nhds (ball_mem_nhds ΛE p'), Hi g,self_mem_nhdsWithin] with z hz i h'
    have ht : z ∈ ΛLitRT n g ∩ ball ΛE r:= ⟨h',hz⟩
    exact ⟨hellStarRt k T p V a f hc h g ((litOpenRt n g).inter Metric.isOpen_ball) hR timeAxis z ht,(pricedSurgeRT k T e p V a f hc h g ((litOpenRt n g).inter Metric.isOpen_ball) hR ht).trans i⟩
 choose G C A K using fun g=>shelterXRt (glow o (dawn (αVertRT k y))) (HalfRT g) (halfOpenRT g) (halfχVRt g) (zeroHRT g) (H_W g) Q i (show ∀ᶠ z:ZSideRt n in 𝓝[HalfRT g ×ˢ univ] ΛE,AnalyticAt ℂ (H_W g) z∧WetαRt (H_W g) z=Q z from by rw [← litΓRt]; exact he g)
 refine ⟨G,Q,i,fun g=>⟨C g,?_,Hi g,K g⟩⟩; rw [litΓRt]; exact A g
#print axioms VestAuraRT
end YM.NSF.Boundary
end
