import Velour.Sequins.Fish
/-!
OnceHere plus near-fixed prism in the real price. Reissues a part of 
SatinThinJetsPurchase, adapting ordersPrism to also use
Spine.spot_net (analytic shimmer).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 5000
set_option quotPrecheck false
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Casting Six OS.Semigroup.Balloon
open MacroGrid SatinNucleus Set
open YM.Six YM.SatinJets
variable (P:Spine)(x:P.Spectrum0 3)
local notation "κ"=> P.wealth 3 (P.advocate 3 x 3)
local notation "Γ"=> P.cartage 3 (P.advocate 3 x 3)
local notation "H"=> P.ManyF 3 (P.advocate 3 x 3)
local notation "S"=> P.seasons 3 (P.advocate 3 x 3)
local notation "E"=> (S).E
local notation "ℒ"=> Lead.Clan
variable (f n:ℕ)(V:∀ j:Axis,List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j))
variable (p:ℒ→ Prism)(μ:ℝ)(s k:ℕ)(F G:SampleDose)
-- principal profile of new prisms sitting on this x

variable {Y:ℕ→ P.Apron} (R: GalaxyShow P x f n Y V)(J:P.Ellis 3 x)
include R
variable (K:P.Register)(U W: Doorway)(e:U.Later W thinAlongOrder 0)(u:U.upper 3≤ -μ)(w:μ ≤ W.lower 3)

-- prove plus shelf general domain ∀ U∩ open could reuse. don't introduce new tolerance
include e J
private lemma spark_seek (T:P.AllOpens x s k U W thinAlongOrder):
    ∃ a∈ (U.invites ×ˢ W.invites), ReadsSix (P.pointMatrix x s k (a.2-a.1)) ∧ ∃ p:ℒ→ Prism,Clean (P.pointPrism x V p (a.2-a.1)):=by
 let A:=U.invites ×ˢ W.invites; let T':= {a:Vantage×Vantage| ReadsSix (P.pointMatrix x s k (a.2-a.1))}
 let D:= {p∈ brightShelf| Clean (P.reach_chords x f n V p)}; have t(z:Vantage×Vantage)(w:z∈ A): z.2-z.1∈ brightShelf:=by
    intro i; have hp:= (Doorway.covers e (subset_closure (show z.1∈ U.invites from w.1)) (subset_closure (show z.2∈ W.invites from w.2))) i; simpa [Set.mem_Ioi,OrderSlab,thinAlongOrder] using hp
 obtain ⟨p,hp⟩:= Set.Nonempty.prod U.doorNonempty W.doorNonempty
 have he:p∈ closure (A∩T'):= T.point_density.2 hp; obtain ⟨q,_,hq⟩:= mem_closure_iff_nhds.mp he _ (show A∈𝓝 p from (U.doorOpen.prod W.doorOpen).mem_nhds hp)
 obtain ⟨r,_,z,g⟩:=mem_closure_iff_nhds.mp (diff_dense D T.point_density.1 (fun g u=> P.right_spread x f n V R J (t g u.1)) hq) _ (show A∩T'∈ 𝓝 q from T.point_density.1.mem_nhds hq)
 exact ⟨r,z.1,z.2,P.find_prism x f n V R g.1 g.2⟩ -- tune binder conflicts
omit e J
omit R

open DoseTravel
open YM.SatinEdge.RealSheet

/-- collect edge vector. -/
def signal(Ht:∀ i:ℒ, TemperedAtEdge (P.ManyF 3 (P.advocate 3 x 3)) (P.profilesZ x V p i)) :=
   fun i:ℒ => _root_.YM.SatinEdge.RealSheet.awake (S) (P.profilesZ x V p i) (Ht i)

private lemma two_pay (ℋ:Hilbert)
   (Z N:ℒ→Vantage→ℋ) (a b:Vantage) (r:ℕ→Vantage)
   (g:Tendsto r atTop (𝓝 b))(j:∀ i,Continuous (Z i))(l:∀ i,Continuous (N i)):
   Tendsto (fun i=> crossBeams ℋ Z N (velourSampleBead a i) (velourSampleBead (r i) i))
    atTop (𝓝 (matchRoles ℋ (fun k =>Z k a) (fun k=>N k b))) ∧
   Tendsto (fun i=> matchRoles ℋ (fun k=>Z k a) (fun k=> N k (r i)))
    atTop (𝓝 (matchRoles ℋ (fun k=>Z k a) (fun k=>N k b))):=
    ⟨tendsto_pi_nhds.mpr fun i=>tendsto_pi_nhds.mpr fun k=>
      (sprinkle a ℋ (Z i) (j i)).inner (reap b r g (N k) (l k)),
     tendsto_pi_nhds.mpr fun _=> tendsto_pi_nhds.mpr fun k=>
      tendsto_const_nhds.inner (((l k).tendsto _).comp g)⟩

include R e u w J
lemma spark_order {c r:ℕ→ℕ}(B:P.Experiment K c r x J)(w':0<μ)
    (Ht:∀ (p:Lead.Clan→Prism)(i:ℒ), TemperedAtEdge (P.ManyF 3 (P.advocate 3 x 3)) (P.profilesZ x V p i)):
    ∀ᶠ i:ℕ in atTop, ∃ (F G:SampleDose)(p:ℒ→ Prism), P.OnceHere x V p μ (c i) (r i) F G K U W ∧ ReadsSix (paycheck (P.signal x V p (Ht p)) F G):= by
 let t:= P.probeWidth; let b:= thinAlongOrder
 have a':= limit_width B.launch
 filter_upwards [atDoors B,Doorway.affordable_margins B.launch U W thinAlongOrder e, (a' 3).eventually (gt_mem_nhds w'),U.spareCosts _ a', W.spareCosts _ a', B.launch.eager.tendsto_atTop.eventually (eventually_gt_atTop P.calibration.ℓ)] with i y l d A₁ A₂ i₀
 let n':= c i; let k':=r i; let T:= y _ _ _ (U.spareLater l)
 obtain ⟨⟨a,c'⟩,⟨p₀,h⟩,hr,P',p'⟩:= P.spark_seek x f n V _ _ R J _ _ (U.spareLater e) T
 have q₁: a∈ U.invites:= U.sparesDoor (subset_closure p₀)
 have q₂: c'∈ W.invites:= W.sparesDoor (subset_closure h)

 have hi:μ ≤ -(a 3):=by linarith only [(show a∈Set.Icc U.lower U.upper from (show a∈U.sealing from U.doorSeal ▸ subset_closure q₁)).2 3,u]
 have hj (x:Vantage)(h:x∈W.invites):μ ≤ x 3:=
   le_trans w ((show x∈Set.Icc W.lower W.upper from (show x∈W.sealing from W.doorSeal ▸ subset_closure h)).1 3)
 have hk:0<(c'-a) 3:= by rw [Pi.sub_apply]; linarith only [w',hi,hj _ q₂]
 obtain ⟨l,tg,tk⟩:= P.spot_net x V P' (Ht P') (P.profile_pos x f n V P' R) a c' hk p'
 let F(i):= velourSampleBead a i; let G(i):= velourSampleBead (l i) i 
 let Z:= P.backwardRay x; let N:= P.forwardRay x
 let Z':= P.earlierProfile x V P' μ; let N':= P.laterProfile x V P' μ
 have h₁: U.upper 3 +((t n' k') 3) < 0:= by linarith only [u,w,show (t n' k') 3 < μ from d]
 have h₂: 0 +((t n' k') 3) < W.lower 3:= by linarith only [w,show (t n' k') 3 < μ from d]
 -- original profile estimates at chosen points, both supported in smaller boxes

 have o:=two_pay H (fun k=> Z k n' k' 0) (fun k=> N k n' k' 0) a c' l tg
               (fun i=>P.cold_cont ..) (fun i=>P.hot_cont ..)
 have s :=two_pay H Z' N' a c' l tg (fun i=> P.profile_solid x f n V P' μ R w' i|>.1) (fun i=> P.profile_solid x f n V P' μ R w' i|>.2)
 have hr':ReadsSix (matchRoles H (fun k=>Z k n' k' 0 a) (fun k=>N k n' k' 0 c')):=P.array_at_point x n' k' 0 U W J h₁ h₂ a c' (subset_closure q₁) (subset_closure q₂) ▸ hr
 have pr':ReadsSix (matchRoles H (fun k=>Z' k a) (fun k=>N' k c')):=
    (P.prism_between x f n V P' μ R w' a c' hi (hj _ q₂)) ▸ p'

 have of':=readsSix_open.mem_nhds hr'; have sf:=readsSix_open.mem_nhds pr'
 obtain ⟨n'',⟨x₀,u₀⟩,⟨x₁,u₁⟩,g₁,g₂,g₃,x₂⟩:=
        (((o.1.eventually of').and (o.2.eventually of')).and
         (((s.1.eventually sf).and (s.2.eventually sf)).and
         ((concentrates a _ (U.spare.doorOpen.mem_nhds p₀)).and
         ((closes c' l tg _ (W.spare.doorOpen.mem_nhds h)).and
         ((tg.eventually (W.doorOpen.mem_nhds q₂)).and tk))))).exists
 let u₀' :ReadsSix (P.pointMatrix x n' k' (l n''-a)):=by
    rw [P.array_at_point x n' k' 0 U W J h₁ h₂ a _ (subset_closure q₁) (subset_closure g₃)]; exact u₀
 let u₁' :ReadsSix (P.pointPrism x V P' (l n''-a)):=by
    rw [P.prism_between x f n V P' μ R w' a _ hi (hj _ g₃)]; exact u₁
 have pF: tsupport (F n'').val ⊆ U.invites:= g₁.trans (subset_trans subset_closure U.sparesDoor)
 have pG: tsupport (G n'').val ⊆ W.invites:= g₂.trans (subset_trans subset_closure W.sparesDoor)
 have hT:= P.paidReturn x n' k' 0 (F n'') (G n'') (fun i=>P.beforeTest n' k' 0 U h₁ (F n'') i (pF.trans subset_closure)) (fun i=>P.afterTest n' k' 0 W h₂ (G n'') i (pG.trans subset_closure)) J x₀ i₀
 exact ⟨F n'', G n'',P',⟨w',pF,pG,⟨prescribed ..,prescribed ..⟩,⟨hT, P.reviewWardContrast K x _ _ 0 _ _ hT⟩,(fun i=>⟨bounded_within (P.RTest i n' k') (F n'') g₁ A₁,bounded_within (P.FTest i n' k') (G n'') g₂ A₂⟩),x₁,a,q₁,l n'',g₃,n'',rfl,rfl,u₁',u₀'⟩,x₂⟩
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.spark_order

