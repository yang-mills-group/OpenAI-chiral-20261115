import SatinPP.Stagefront
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
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

local notation "X₀"=>reviewEarlierBox
local notation "Y₀"=>reviewLaterBox
lemma balance(a b:Vantage)(u:a∈(X₀).spare.invites)(v:b∈(Y₀).spare.invites):
 ∃c∈(Y₀).spare.invites, 1<c 3 ∧ -c∈(X₀).spare.invites ∧ c- -c=b-a:= by
 let c:Vantage:=fun i=>(b i-a i)/2
 have e(i): 4/3<c i ∧ c i<5/3:=by
    have h:=u i (Set.mem_univ _)
    have k:=v i (Set.mem_univ _)
    simp only [Set.mem_Ioo,Doorway.spare,reviewEarlierBox,reviewLaterBox] at h k
    constructor <;> unfold c <;> linarith only [h.1,h.2,k.1,k.2]
 refine ⟨c,fun i _=>?_,by linarith only [(e 3).1], fun i _=>?_,?_⟩
 · simp only [Set.mem_Ioo,Doorway.spare,reviewLaterBox]; constructor<;>linarith only [(e i).1,(e i).2]

 · simp only [Pi.neg_apply,Set.mem_Ioo,Doorway.spare,reviewEarlierBox];constructor <;>linarith only [(e i).1,(e i).2]
 ext i; simp [c]

variable (μ:ℝ)(s k:ℕ) {Y:ℕ→ P.Apron}(R: GalaxyShow P x f n Y V)(J:P.Ellis 3 x)
include R
-- exact experiment and density in **both** time-differenced tests. Pick one pair support once and for all. no existential drift with width. Positive-axis order for user experiment.
variable (K:P.Register)(U W: Doorway)(e:U.Later W thinAlongOrder 0)(u:U.upper 3≤ -μ)(w:μ ≤ W.lower 3)

-- prove plus shelf general domain ∀ U∩ open could reuse. don't introduce new tolerance
include e J
private lemma intersect_prisms₂ (T:P.AllOpens x s k U W thinAlongOrder):
    ∃ a∈ (U.invites ×ˢ W.invites), ReadsSix (P.pointMatrix x s k (a.2-a.1)) ∧ ∃ p:ℒ→ Prism,Clean (P.pointPrism x V p (a.2-a.1)):=by
 let A:=U.invites ×ˢ W.invites; let T':= {a:Vantage×Vantage| ReadsSix (P.pointMatrix x s k (a.2-a.1))}
 let D:= {p∈ brightShelf| Clean (P.reach_chords x f n V p)}; have t(z:Vantage×Vantage)(w:z∈ A): z.2-z.1∈ brightShelf:=by
    intro i; have hp:= (Doorway.covers e (subset_closure (show z.1∈ U.invites from w.1)) (subset_closure (show z.2∈ W.invites from w.2))) i; simpa [Set.mem_Ioi,OrderSlab,thinAlongOrder] using hp
 obtain ⟨p,hp⟩:= Set.Nonempty.prod U.doorNonempty W.doorNonempty
 have he:p∈ closure (A∩T'):= T.point_density.2 hp; obtain ⟨q,_,hq⟩:= mem_closure_iff_nhds.mp he _ (show A∈𝓝 p from (U.doorOpen.prod W.doorOpen).mem_nhds hp)
 obtain ⟨r,_,z,g⟩:=mem_closure_iff_nhds.mp (diff_dense D T.point_density.1 (fun g u=> P.right_spread x f n V R J (t g u.1)) hq) _ (show A∩T'∈ 𝓝 q from T.point_density.1.mem_nhds hq)
 exact ⟨r,z.1,z.2,P.find_prism x f n V R g.1 g.2⟩ -- tune binder conflicts
omit e J
-- optional package height B and *all* reference experiment forms incl `ThinFixedLab` later
open DoseTravel

include J
lemma ordersVoucher {c r:ℕ→ℕ}(B:P.Experiment K c r x J)(A:P.Silhouette x V):
    ∀ᶠ i:ℕ in atTop, ∃ (F G:SampleDose)(p:ℒ→ Prism), P.OnceHere x V p 1 (c i) (r i) F G K X₀ Y₀ ∧ P.WalkVoucher x V p F G:= by
 let U:=reviewEarlierBox; let W:=reviewLaterBox; let μ:ℝ:=1
 have w':0<μ:=zero_lt_one
 have e:U.Later W thinAlongOrder 0:=thinEarlier
 have u:U.upper 3≤ -μ:=le_rfl
 have w:μ≤ W.lower 3:=le_rfl
 let t:= P.probeWidth; let b:= thinAlongOrder
 have a':= limit_width B.launch
 filter_upwards [atDoors B,Doorway.affordable_margins B.launch U W thinAlongOrder e, (a' 3).eventually (gt_mem_nhds w'),U.spareCosts _ a', W.spareCosts _ a', B.launch.eager.tendsto_atTop.eventually (eventually_gt_atTop P.calibration.ℓ)] with i y l d A₁ A₂ i₀
 let n':= c i; let k':=r i; let T:= y _ _ _ (U.spareLater l)
 obtain ⟨⟨α,β⟩,⟨γ,σ⟩,hr,P',p'⟩:= P.intersect_prisms₂ x f n V _ _ R J _ _ (U.spareLater e) T
 obtain ⟨c',h,Q,p₀,Y⟩:= balance α β γ σ
 change ReadsSix (P.pointMatrix x n' k' (β-α)) at hr; change Clean (P.pointPrism x V P' (β-α)) at p'
 let a:Vantage:= -c'; rw [←Y] at hr p'
 have q₁: a∈ U.invites:= U.sparesDoor (subset_closure p₀)
 have q₂: c'∈ W.invites:= W.sparesDoor (subset_closure h)
 let F(i:ℕ):= slider a (chosen a i); let G(i:ℕ):= slider c' (chosen c' i)
 let Z:= P.backwardRay x; let N:= P.forwardRay x
 let Z':= P.earlierProfile x V P' μ; let N':= P.laterProfile x V P' μ
 have h₁: U.upper 3 +((t n' k') 3) < 0:= by linarith only [u,w,show (t n' k') 3 < μ from d]
 have h₂: 0 +((t n' k') 3) < W.lower 3:= by linarith only [w,show (t n' k') 3 < μ from d]
 -- original profile estimates at chosen points, both supported in smaller boxes
 have v₁: Tendsto (fun i=> P.arrayReading x n' k' 0 (F i) (G i)) atTop (𝓝 (P.pointMatrix x n' k' (c'-a))):=by
    rw [P.array_at_point x n' k' 0 U W J h₁ h₂ a c' (subset_closure q₁) (subset_closure q₂)]
    exact normal_beam_price H (fun k=> Z k n' k' 0) (fun k=> N k n' k' 0) a c' (fun i=>P.cold_cont ..) (fun i=>P.hot_cont ..)
 have v₂: Tendsto (fun i=> P.readPrism x V P' μ (F i) (G i)) atTop (𝓝 (P.pointPrism x V P' (c'-a))):=by
    have p': μ≤ -(a 3):= by linarith only [(show a∈Set.Icc U.lower U.upper from (show a∈U.sealing from U.doorSeal ▸ subset_closure q₁)).2 3,u]
    rw [P.prism_between x f n V P' μ R w' a c' p' (le_trans w ((show c'∈Set.Icc W.lower W.upper from (show c'∈W.sealing from W.doorSeal ▸ subset_closure q₂)).1 3))]
    exact normal_beam_price H Z' N' a c' (fun i=> P.profile_solid x f n V P' μ R w' i|>.1) (fun i=> P.profile_solid x f n V P' μ R w' i|>.2)
 let foo i:= ReadsSix (P.arrayReading x n' k' 0 (F i) (G i)) ∧ tsupport (F i).val ⊆ U.spare.invites ∧ tsupport (G i).val ⊆ W.spare.invites
 have ej:∀ᶠ i in atTop,foo i := (v₁.eventually (readsSix_open.mem_nhds hr)).and ((concentrates a _ (U.spare.doorOpen.mem_nhds p₀)).and (concentrates c' _ (W.spare.doorOpen.mem_nhds h)))
 obtain ⟨n'',P',ho,p',x₁,arm⟩:= P.jumpSeats x V R A a c' (c' 3) Q (show dials false a=c' 3 by simp [dials,a]) rfl P' p' foo (ej.and (v₂.eventually (readsSix_open.mem_nhds p')))
 obtain ⟨x₀,g₁,g₂⟩:=ho
 have pF: tsupport (F n'').val ⊆ U.invites:= g₁.trans (subset_trans subset_closure U.sparesDoor)
 have pG: tsupport (G n'').val ⊆ W.invites:= g₂.trans (subset_trans subset_closure W.sparesDoor)
 have hT:= P.paidReturn x n' k' 0 (F n'') (G n'') (fun i=>P.beforeTest n' k' 0 U h₁ (F n'') i (pF.trans subset_closure)) (fun i=>P.afterTest n' k' 0 W h₂ (G n'') i (pG.trans subset_closure)) J x₀ i₀
 exact ⟨F n'', G n'',P',⟨w',pF,pG,⟨prescribed ..,prescribed ..⟩,⟨hT, P.reviewWardContrast K x _ _ 0 _ _ hT⟩,(fun i=>⟨bounded_within (P.RTest i n' k') (F n'') g₁ A₁,bounded_within (P.FTest i n' k') (G n'') g₂ A₂⟩),x₁,a,q₁,c',q₂,n'',rfl,rfl,p',hr⟩,arm⟩

#print axioms ordersVoucher
