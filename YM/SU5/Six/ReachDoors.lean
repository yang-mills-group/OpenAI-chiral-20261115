import YM.SU5.Six.Chambers
import YM.SU5.Six.FineRays
import YM.SU5.Six.DoseTour
import YM.SU5.Six.TransitWall
import YM.SU5.Six.Photos
import YM.SU5.Six.OrdinaryMist
import YM.SU5.Aria.Grotto
import YM.SU5.Six.KeepCharge
import YM.SU5.Six.MirrorCharge
set_option maxHeartbeats 200000
set_option autoImplicit false
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
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia) -- tune
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Set
open Cheer (Narrow)
open scoped ContDiff
open Casting DoseTravel
abbrev CrossRead := Matrix Lead.Clan Lead.Clan ℂ

section general
variable (H:Hilbert)
local notation "Ξ"=> (Lead.Clan → H)
def matchRoles (X Y:Ξ) : CrossRead:= Matrix.of (fun i j=> inner ℂ (X i) (Y j))
lemma roles_open : Continuous (fun v : (Ξ) × (Ξ)=> matchRoles H v.1 v.2) := by
 exact continuous_pi (fun a=> continuous_pi (fun b=> Continuous.inner ((continuous_apply a).comp continuous_fst) ((continuous_apply b).comp continuous_snd)))

variable (X Y:Lead.Clan→Vantage → H)(F G: SampleDose)
def crossBeams: CrossRead:= matchRoles H (fun i=>beam H F (X i)) (fun i=>beam H G (Y i))
local notation "U"=> crossBeams H X Y
lemma normal_beam_price(p q:Vantage)(x:∀ i, Continuous (X i))(y:∀ i,Continuous (Y i)): Tendsto (fun i=> (U) (slider p (chosen p i)) (slider q (chosen q i))) atTop (𝓝 (matchRoles H (fun i=>X i p) (fun i=>Y i q))):=
 tendsto_pi_nhds.mpr fun a=> tendsto_pi_nhds.mpr fun b=> (sprinkle p H (X a) (x a)).inner (sprinkle q H (Y b) (y b))
private def proofSign (x:CrossRead):ℂ:= x.det * ∏ i:Lead.Clan,x i i
private lemma proof_sign_lit(M:CrossRead): ReadsSix M ↔ proofSign M ≠ 0 := by rw [proofSign,mul_ne_zero_iff,Finset.prod_ne_zero_iff]; simp [ReadsSix]
lemma open_beam_price (f g:SampleDose)(h:ReadsSix ((U) f g))(x:∀ i, Continuous (X i))(y:∀ i,Continuous (Y i)):∀ᶠ t:ℝ in 𝓝[≠] 0, ReadsSix ((U) (convexSeek F f t) (convexSeek G g t)):= by
 let M(t:ℝ):=(U) (convexSeek F f t) (convexSeek G g t); let v:= proofSign ∘ M
 have hx:AnalyticOnNhd ℝ v Set.univ:=by
   intro t a
   have he(i j:Lead.Clan): AnalyticAt ℝ (fun q=> M q i j) t:= ((seek_beams F f H _ (x i) t a|>.contDiffAt (n:=ω)).inner ℂ ((seek_beams G g H _ (y j) t a).contDiffAt (n:=ω))).analyticAt -- tune
   change AnalyticAt ℝ (fun q=> (M q).det * ∏ i:Lead.Clan,M q i i) t
   refine AnalyticAt.mul ?_ (Finset.analyticAt_fun_prod _ (fun i _=> he i i))
   simp_rw [Matrix.det_apply']; exact Finset.analyticAt_fun_sum _ fun i _=> analyticAt_const.mul (Finset.analyticAt_fun_prod _ (fun _ _=> he _ _))
 have hg : v 1≠0:= by apply (proof_sign_lit _).mp; unfold M; rw [seek_one,seek_one]; exact h
 by_contra e
 refine hg (hx.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ (z₀:=0) (Set.mem_univ 0) ?_ (Set.mem_univ 1))
 refine (show ∃ᶠ (z:ℝ) in 𝓝[≠] 0, ¬ ReadsSix (M z) from ?_).mono (fun a g=>not_ne_iff.mp (mt ((proof_sign_lit _).2) g))
 exact not_eventually.mp e
lemma ever_right (f g:SampleDose)(h:ReadsSix ((U) f g))(x:∀ i, Continuous (X i))(y:∀ i,Continuous (Y i)):
    ∀ᶠ t:ℝ in 𝓝[>] 0, t∈ Set.Icc (0:ℝ) 1 ∧ ReadsSix ((U) (convexSeek F f t) (convexSeek G g t)):= by
  filter_upwards [(eventually_mem_nhdsWithin : ∀ᶠ t:ℝ in 𝓝[>] (0:ℝ), t∈ Set.Ioi (0:ℝ)), (show ∀ᶠ t:ℝ in 𝓝[>] 0,t<1 from mem_nhdsWithin_of_mem_nhds (gt_mem_nhds (zero_lt_one : 0<(1:ℝ)))), (open_beam_price H X Y F G f g h x y).filter_mono (nhdsGT_le_nhdsNE _)] with t a b v; exact ⟨⟨le_of_lt a,b.le⟩,v⟩
lemma beam_near (K:Set Vantage)(t:IsCompact K)(x:∀ i,Continuous (X i)) (p:(tsupport F.val)⊆K) (u:ℝ)(g:0<u):∃ d:ℝ,0<d∧∀ f:SampleDose,tsupport f.val⊆K→ AltNear d F f → dist (fun i=>beam H f (X i)) (fun i=>beam H F (X i))<u:= by
 choose C a h using fun i=>affordable H (X i) (x i) K t
 obtain ⟨d,e,pd⟩:∃ d:ℝ,0<d∧∀ i:Lead.Clan,d*C i<u:= by
    have hZ(i:Lead.Clan):∀ᶠ z:ℝ in 𝓝[>] (0:ℝ), z*C i < u:= (((continuous_id.mul continuous_const).tendsto (0:ℝ)).eventually (gt_mem_nhds (show (0:ℝ)*C i<u by simpa using g))).filter_mono nhdsWithin_le_nhds
    exact ((Filter.eventually_all.mpr hZ) |>.and (self_mem_nhdsWithin : ∀ᶠ d:ℝ in 𝓝[>] (0:ℝ), d∈ Set.Ioi 0)|>.mono (q:=fun d=> 0< d ∧ ∀ i,d*C i<u) (fun i d=>d.symm)|>.exists)
 refine ⟨d,e,fun f w v=> (dist_pi_lt_iff g).2 (fun i=> (dist_comm ..).trans_lt ((h i _ e _ _ p w v).trans_lt (pd i)))⟩
lemma stability (K L:Set Vantage)(t:IsCompact K)(s:IsCompact L)(x:∀ i,Continuous (X i))(y:∀ i,Continuous (Y i))(p:(tsupport F.val)⊆K)(q:(tsupport G.val)⊆L) (D:Set CrossRead)(d:D∈𝓝 ((U) F G)):
    ∃ e:ℝ,0<e∧∀ (F' G':SampleDose), tsupport F'.val ⊆ K →tsupport G'.val⊆L → AltNear e F F' → AltNear e G G' → (U) F' G'∈D := by
 let a(G : SampleDose):=fun i=> beam H G (X i); let b(G : SampleDose):=fun i=> beam H G (Y i)
 obtain ⟨ε,t',h⟩:= Metric.mem_nhds_iff.mp (((roles_open H).continuousAt (x:=(a F,b G))).preimage_mem_nhds d)
 obtain ⟨f,H0,pf⟩:= beam_near H X F K t x p ε t'
 obtain ⟨g,P,pg⟩:= beam_near H Y G L s y q ε t'
 refine ⟨min f g, lt_min H0 P, fun F' G' u u' v w=> h (show (a F',b G')∈ Metric.ball _ _ from ?_)⟩
 rw [Metric.mem_ball,Prod.dist_eq]; exact max_lt (pf F' u fun i=>(v i).trans_le (min_le_left _ _)) (pg G' u' fun i=> (w i).trans_le (min_le_right _ _)) -- H shadow issue
end general

-- Frames fixed at t, cover apertures in tick units including prices. Positive-time axes still j=3; no geometry with cones real-time.
namespace Doorway
-- The caller sets two nonempty rectangles with STRICT margins for their closures
-- on all axes. Doesn't require a reflected pair.
def Later (X Y: Doorway)(σ:Orders) (w: Vantage):Prop:= ∀ i, if σ.val i then X.upper i+2*w i<Y.lower i else Y.upper i+2*w i<X.lower i
lemma affordable_margins {P:Spine}{c r:ℕ→ℕ}(B:Launch P c r)(X Y:Doorway)(σ:Orders)(p: X.Later Y σ 0):∀ᶠ i:ℕ in atTop,X.Later Y σ (P.probeWidth (c i) (r i)):= by
 unfold Later; apply eventually_all.mpr
 intro i
 let w(k):= P.probeWidth (c k) (r k)
 specialize p i; split at p
 · rename_i z; simp only [z,ite_true]; simp only [Pi.zero_apply,mul_zero,add_zero] at p
   exact ((tendsto_const_nhds (x:= X.upper i)).add ((limit_width B i).const_mul (2:ℝ))).eventually (gt_mem_nhds (show X.upper i+2*(0:ℝ)<Y.lower i by simpa using p))
 rename_i z; simp only [if_neg z]; simp only [Pi.zero_apply,mul_zero,add_zero] at p
 exact ((tendsto_const_nhds (x:=Y.upper i)).add ((limit_width B i).const_mul (2:ℝ))).eventually (gt_mem_nhds (show Y.upper i+2*(0:ℝ)<X.lower i by simpa using p))
variable {X Y :Doorway} {σ:Orders} {w:Vantage}(b: X.Later Y σ w)
include b
lemma covers {p q:Vantage}(x:p∈closure X.invites)(y:q∈closure Y.invites): q-p∈OrderChamber σ w:= by
 intro j; have h:=b j
 obtain ⟨v,s⟩ : p∈ Set.Icc X.lower X.upper:= (show _ ∈ X.sealing from X.doorSeal ▸ x)
 obtain ⟨t,k⟩ : q∈ Set.Icc Y.lower Y.upper:= (show _ ∈ Y.sealing from Y.doorSeal ▸ y)
 unfold OrderSlab; split at h
 · rename_i u; rw [if_pos u]; change 2*w j < q j-p j; linarith only [h,s j,t j]
 rename_i u; rw [if_neg u]; change q j-p j < -(2*w j); linarith only [h,v j,k j]
lemma wallBetween : ∃ c:ℝ,X.upper 3+w 3<c∧c+w 3<Y.lower 3:= by
 have h:=b (3:Axis); rw [if_pos σ.property] at h; obtain ⟨v,a,g⟩:= exists_between (show X.upper 3+w 3< Y.lower 3-w 3 by linarith); exact ⟨v,a, by linarith⟩
end Doorway

variable (P:Spine)(x:P.Spectrum0 3)(s n:ℕ)(c:ℝ)(σ:Orders)(U V:Doorway)(J:P.Ellis 3 x)
-- same readings at t. convert vectors to actual investments. No spectral projection V relevant here.
local notation "K"=> P.pointMatrix x s n
local notation "S"=> P.probeWidth s n
local notation "H"=> P.ManyF 3 (P.otherSpectrum 3 3 x)
local notation "X" i:max => P.landingCost x s n i
local notation "Y" i:max => P.launchCost x s n i
def arrayReading (F G:SampleDose): Matrix Lead.Clan Lead.Clan ℂ:= Matrix.of (fun Z W=> inner ℂ (P.landingCost x s n Z F c) (P.launchCost x s n W G c))
def arrayFine (t:ℕ)(F G:SampleDose): Matrix Lead.Clan Lead.Clan ℂ:= Matrix.of (fun Z W=>P.chargedCost x s t n Z W F G)
local notation "Q"=> P.arrayReading x s n c
lemma array_beam (F G:SampleDose): Q F G=crossBeams H (fun i=> P.backwardRay x i s n c) (fun i=> P.forwardRay x i s n c) F G:=rfl
variable (h: U.Later V σ (P.probeWidth s n))(p: U.upper 3 +(P.probeWidth s n) 3 < c)(q: c+(P.probeWidth s n) 3 < V.lower 3)
include J p q
lemma array_at_point (x' y:Vantage)(a:x'∈ closure U.invites)(b:y∈closure V.invites):
   K (y-x')=matchRoles H (fun Z=>P.backwardRay x Z s n c x') (fun Z=>P.forwardRay x Z s n c y):= by
 ext1 Z W; refine P.ordered_wall x J Z W s n c x' y ?_ ?_
 · exact (add_le_add_left (show x' 3≤U.upper 3 from (show x'∈Set.Icc U.lower U.upper from (show _∈U.sealing from U.doorSeal ▸ a)).2 _) _).trans_lt p -- mathlib add_le uses? 
 exact q.trans_le ((show y∈Set.Icc V.lower V.upper from (show _∈V.sealing from V.doorSeal ▸ b)).1 _)
omit J p q
include p
lemma beforeTest (F: SampleDose)(Z:Lead.Clan)(f:tsupport F.val⊆closure U.invites): P.WallBefore (P.experimentBody Z s n) F c:= fun i v=> by have g: i∈Set.Icc U.lower U.upper:= (show _∈U.sealing from U.doorSeal ▸ f v); exact (add_le_add_left (g.2 _) _).trans_lt p
omit p
include q
lemma afterTest (F:SampleDose)(Z:Lead.Clan)(f:tsupport F.val⊆closure V.invites): P.WallAfter (P.experimentBody Z s n) F c:= fun i v=> by have g:i∈ Set.Icc V.lower V.upper:= (show _∈V.sealing from V.doorSeal ▸ f v); exact q.trans_le (g.1 _)
omit q
include J h p q
lemma shining (w:∃ p∈ OrderChamber σ S,ReadsSix (K p)): ∃ (F G:SampleDose), F.Normalized∧tsupport F.val ⊆ U.invites∧ G.Normalized ∧tsupport G.val ⊆V.invites∧ ReadsSix (Q F G):= by
 obtain ⟨u,hu⟩:=U.doorNonempty; obtain ⟨v,g⟩:=V.doorNonempty
 let D:= OrderChamber σ S
 have hp:v-u∈ D:= Doorway.covers h (subset_closure hu) (subset_closure g)
 have ht:= live_poses J s n σ w; let d:= {p:Vantage×Vantage|p.2-p.1∈D ∧ ReadsSix (K (p.2-p.1))}; let k:=(u,v)
 have wk:k∈ closure d:= ht.2 hp
 obtain ⟨⟨i,j⟩,⟨a,b⟩,_,y⟩:=mem_closure_iff_nhds.mp wk _ ((U.doorOpen.prod V.doorOpen).mem_nhds (show k∈U.invites ×ˢ V.invites from ⟨hu,g⟩))
 have hp:=normal_beam_price H (fun i=>P.backwardRay x i s n c) (fun i=>P.forwardRay x i s n c) i j (fun i=>P.cold_cont ..) (fun i=>P.hot_cont ..);
 change ReadsSix (K (j-i)) at y; rw [P.array_at_point x s n c U V J p q i j (subset_closure a) (subset_closure b)] at y
 obtain ⟨r,f,l,m⟩:= ((hp.eventually (readsSix_open.mem_nhds y)).and ((concentrates i U.invites (U.doorOpen.mem_nhds a)).and (concentrates j V.invites (V.doorOpen.mem_nhds b)))).exists
 exact ⟨_,_,prescribed ..,l,prescribed ..,m,f⟩
lemma perturbations (w:∃ p∈ OrderChamber σ S,ReadsSix (K p)) (F G:SampleDose)(f:F.Normalized)(u: G.Normalized)(e:tsupport F.val⊆U.invites)(l:tsupport G.val⊆V.invites)(k:ℕ)(ε:ℝ)(r:0<ε):
 ∃ F' G':SampleDose,F'.Normalized∧G'.Normalized∧tsupport F'.val⊆U.invites∧tsupport G'.val⊆V.invites∧NearSmear k ε F F'∧ NearSmear k ε G G'∧ReadsSix (Q F' G'):=by
 obtain ⟨a,b,ha,g,t,s',w⟩:=P.shining x s n c σ U V J h p q w
 have he:= ever_right H (fun i=>P.backwardRay x i s n c) (fun i=>P.forwardRay x i s n c) F G a b w (fun i=>P.cold_cont ..) (fun i=>P.hot_cont ..)
 obtain ⟨z,⟨y,xz⟩,i,j⟩:= (he.and (((early_costs F a k ε r).filter_mono nhdsWithin_le_nhds).and ((early_costs G b k ε r).filter_mono nhdsWithin_le_nhds))).exists
 exact ⟨_,_, convex_normal F a z y f ha, convex_normal G b z y u t, convex_seal F a z _ e g, convex_seal G b z _ l s',i,j,xz⟩
omit h p q J
-- Stability of BOTH kinds of answer for fixed wall and test perturbations
-- keeping geometry. The centers are included by changing the tests (in
-- the same allowed neighborhoods); we assert stability in every such space.
lemma near_wall (F G:SampleDose) (S' T:Set Vantage)(a:IsCompact S')(b:IsCompact T)(f:tsupport F.val⊆ S')(t:tsupport G.val⊆T)(U':Set CrossRead)(e: U'∈𝓝 (Q F G)):
 ∃ v:ℝ,0<v ∧∀  (F' G':SampleDose),tsupport (Dose.val F')⊆ S'→ tsupport (Dose.val G')⊆T→DoseTravel.AltNear v F F'→DoseTravel.AltNear v G G'→Q F' G'∈U':=stability H (fun i=> P.backwardRay x i s n c) (fun i=> P.forwardRay x i s n c) F G S' T a b (fun i=>P.cold_cont ..) (fun i=>P.hot_cont ..) f t U' e
include J
lemma answersTogether (F G:SampleDose)(p:∀ i:Lead.Clan,P.WallBefore (P.experimentBody i s n) F c) (e:∀ i:Lead.Clan,P.WallAfter (P.experimentBody i s n) G c):
   Tendsto (fun t=> P.arrayFine x s n t F G) atTop (𝓝 (P.arrayReading x s n c F G)):= tendsto_pi_nhds.mpr (fun i=>tendsto_pi_nhds.mpr (fun j=>P.measured_both x s n i j F G c J (p i) (e j)))
omit J
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
