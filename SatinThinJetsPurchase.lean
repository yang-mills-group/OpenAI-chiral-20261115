import SatinThinJetsSpread
import SatinThinFront
/-!
# Order for six thin channels on one pair of fixed boxes and Lab

CP13: order release. Re-issue `Front` compatibility on any such pair of
interval boxes (also review ones later). Sculpt finite temporal jets depending on that exact
pair of spatially separated areas, **fixed** smooth test functions also from the same
verified experiment. They target the charged raw-continuous and projected limits (see proof files),
not a requirement to match the earlier-wider-mark *value*.
-/
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
variable (p:ℒ→ Prism)(μ:ℝ)(s k:ℕ)(F G:SampleDose)
-- principal profile of new prisms sitting on this x

def profilesZ (a:ℒ) (t:ℝ): H:= prism (S) (P.route_y x V a) (p a) t
local notation "X"=> P.profilesZ x V p
-- totalize for Smears with U.upper ≤ -µ <0 and V.lower≥µ; not heat credit. Don't take boundary.
def earlierProfile (a:ℒ)(q:Vantage):H:= Γ q (X a (max μ (-(q 3))))
def laterProfile (a:ℒ)(q:Vantage):H:= Γ q (X a (max μ (q 3)))
local notation "X₁"=> P.earlierProfile x V p μ
local notation "X₂"=> P.laterProfile x V p μ

def readPrism : CrossRead:= crossBeams H (P.earlierProfile x V p μ) (P.laterProfile x V p μ) F G

def pointPrism (t:Vantage): CrossRead:= P.chartRoles x t (fun i:ℒ=> X i (t 3/2))
variable {Y:ℕ→ P.Apron} (R: GalaxyShow P x f n Y V)(J:P.Ellis 3 x)
include R
lemma profile_pos (i:ℒ): Positive (S) (X i):= prism_pos (S) _ (p i) (P.route_pos x f n V R i)
lemma profile_solid(p':0<μ)(a:ℒ): Continuous (X₁ a) ∧ Continuous (X₂ a):= by
 let W:= X a
 have hx(c:Vantage→ℝ)(h:Continuous c): Continuous (fun w=> Γ w (W (max μ (c w)))):= P.caravan 3 _ id _ continuous_id (continuous_iff_continuousAt.mpr (fun w=> (Positive.cont _ _ (P.profile_pos x f n V p R a) (show 0< max μ (c w) from p'.trans_le (le_max_left _ _))).comp (f:=fun w=> max μ (c w)) (continuous_const.max h|>.continuousAt)))
 exact ⟨hx _ (continuous_apply 3|>.neg),hx _ (continuous_apply 3)⟩
lemma prism_between(p':0<μ)(a b:Vantage)(u:μ ≤ -(a 3))(v:μ ≤ b 3):
    P.pointPrism x V p (b-a)= matchRoles H (fun i=> X₁ i a) (fun i=> X₂ i b):=by
 ext1 i j; let e:= Γ (b-a); let A:= -(a 3); let B:= b 3; let s':= (b-a) 3 / 2; have p₀:0<A:= p'.trans_le u; have q:0<B:= p'.trans_le v; have ht:A+B=(b-a) 3:=by unfold A B; rw [Pi.sub_apply]; abel
 have hw:s'+s'=A+B:= (add_halves .. |>.trans ht.symm); have e':0<s':=by linarith only [p₀,q,hw]
 change inner ℂ (X i s') (e (X j s'))= inner ℂ (Γ a (X i (max μ A))) (Γ b (X j (max μ B)))
 rw [max_eq_right u,max_eq_right v,SatinJets.spectrum_meet (S) _ (P.travelers_temporal x (3:Axis) (b-a)) (X i) (X j) (P.profile_pos x f n V p R i) (P.profile_pos x f n V p R j) e' e' p₀ q hw]
 have hq: (Γ a).adjoint.comp (Γ b)=e:= by unfold e; rw [P.cart_reverses, ← P.cart_paves,sub_eq_add_neg,add_comm]
 rw [← ContinuousLinearMap.adjoint_inner_right]; rw [← ContinuousLinearMap.comp_apply, hq]

lemma find_prism {t:Vantage}(u:t∈ brightShelf)(h:Clean (P.reach_chords x f n V t)):
    ∃ p:ℒ→ Prism,Clean (P.pointPrism x V p t):= by
 let X':= P.route_y x V
 let δ(i):= P.offset_d f n i
 let T (i:ℒ):= δ (seventh (family_six i))
 let s:= t 3/2
 let Z':= fun i:ℒ=> E (T i) (X' i s)-E (δ 0) (X' i s)
 let U':={(p:ℒ→ H) | Clean (P.chartRoles x t p)}
 have hf: Continuous (P.chartRoles x t):= (P.chartRoles_cont x).comp (show Continuous fun (z:ℒ→ H)=>(t,z) from continuous_const.prodMk continuous_id)
 have hU: Z' ∈ U':= h
 have h': U'∈ 𝓝 Z':= (clean_open hf).mem_nhds hU
 obtain ⟨q,hq⟩:= spectrum_seek (S) (half_pos (show 0<t 3 from u 3)) X' (P.route_pos x f n V R) T (fun _=>δ 0) U' h'
 exact ⟨q,hq⟩

-- exact experiment and density in **both** time-differenced tests. Pick one pair support once and for all. no existential drift with width. Positive-axis order for user experiment.
variable (K:P.Register)(U W: Doorway)(e:U.Later W thinAlongOrder 0)(u:U.upper 3≤ -μ)(w:μ ≤ W.lower 3)

-- prove plus shelf general domain ∀ U∩ open could reuse. don't introduce new tolerance
include e J
private lemma intersect_prisms (T:P.AllOpens x s k U W thinAlongOrder):
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
structure OnceHere : Prop where
 eps : 0 < μ
 earlier : tsupport F.val ⊆ U.invites
 laterProbe : tsupport G.val ⊆ W.invites
 normalized : F.Normalized ∧ G.Normalized
 fixed : P.ReturnsSix x s k 0 F G ∧ P.FixedSatinReadings K x s k 0 F G
 all (m:ℒ) : P.spacePrice (P.RTest m s k) F ⊆ U.invites ∧ P.spacePrice (P.FTest m s k) G ⊆ W.invites
 read : ReadsSix (P.readPrism x V p μ F G) -- Not claim thin field yet
 centers : ∃ a∈ U.invites,∃ b ∈ W.invites, ∃ i:ℕ, F=slider a (chosen a i) ∧ G=slider b (chosen b i) ∧
             Clean (P.pointPrism x V p (b-a)) ∧ ReadsSix (P.pointMatrix x s k (b-a))

include e u w J
lemma ordersPrism {c r:ℕ→ℕ}(B:P.Experiment K c r x J)(w':0<μ):
    ∀ᶠ i:ℕ in atTop, ∃ (F G:SampleDose)(p:ℒ→ Prism), P.OnceHere x V p μ (c i) (r i) F G K U W:= by
 let t:= P.probeWidth; let b:= thinAlongOrder
 have a':= limit_width B.launch
 filter_upwards [atDoors B,Doorway.affordable_margins B.launch U W thinAlongOrder e, (a' 3).eventually (gt_mem_nhds w'),U.spareCosts _ a', W.spareCosts _ a', B.launch.eager.tendsto_atTop.eventually (eventually_gt_atTop P.calibration.ℓ)] with i y l d A₁ A₂ i₀
 let n':= c i; let k':=r i; let T:= y _ _ _ (U.spareLater l)
 obtain ⟨⟨a,c'⟩,⟨p₀,h⟩,hr,P',p'⟩:= P.intersect_prisms x f n V _ _ R J _ _ (U.spareLater e) T
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
 obtain ⟨n'',⟨x₀,x₁⟩,g₁,g₂⟩:= (((v₁.eventually (readsSix_open.mem_nhds hr)).and (v₂.eventually (readsSix_open.mem_nhds p'))).and ((concentrates a _ (U.spare.doorOpen.mem_nhds p₀)).and (concentrates c' _ (W.spare.doorOpen.mem_nhds h)))).exists
 have pF: tsupport (F n'').val ⊆ U.invites:= g₁.trans (subset_trans subset_closure U.sparesDoor)
 have pG: tsupport (G n'').val ⊆ W.invites:= g₂.trans (subset_trans subset_closure W.sparesDoor)
 have hT:= P.paidReturn x n' k' 0 (F n'') (G n'') (fun i=>P.beforeTest n' k' 0 U h₁ (F n'') i (pF.trans subset_closure)) (fun i=>P.afterTest n' k' 0 W h₂ (G n'') i (pG.trans subset_closure)) J x₀ i₀
 exact ⟨F n'', G n'',P',w',pF,pG,⟨prescribed ..,prescribed ..⟩,⟨hT, P.reviewWardContrast K x _ _ 0 _ _ hT⟩,(fun i=>⟨bounded_within (P.RTest i n' k') (F n'') g₁ A₁,bounded_within (P.FTest i n' k') (G n'') g₂ A₂⟩),x₁,a,q₁,c',q₂,n'',rfl,rfl,p',hr⟩
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.ordersPrism
