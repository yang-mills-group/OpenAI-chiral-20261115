import VerifiedSatinWidthAndUVNovember4
import YM.SU5.Six.Magnified
import YM.SU5.Six.Momentum
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import YM.SU5.Six.ChamberCosts
import YM.SU5.Six.ReachDoors
import YM.SU5.Six.Charges
import YM.SU5.Six.Rates
import YM.SU5.Six.Elected
import YM.SU5.Six.MSplit
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

/-!
# Compact formats to read `t:trans6`.

* `ReturnsSix` the strict Euclidean frame cost in the same character,
  actual two-body limit and the split prediction on these same evaluations.
* `ReflectMeter` the mirror full-rank Gram on the *same* character; even
  a lower bound using the cone-interior projection.
* `AllOpens` the independent cross-test reading on two chosen rectangles of
  centers. (Vary both densities independently.)

`ε` for probe excitation/rank is NOT a scale-independent lower bound.

Part III split: any complex-linear pricing on the same even-mark system
at the queried implementing height that factors in the indicated
pure/pure products, with Ward on either marginal. Not a Ward test on
charged pin operators of a claimed relativistic model. Not a notion of
split on functions of already dressed observations. The true choices
and opponent statements are on one normalized signed Euclidean price;
no Wick continuation to Minkowski motion, e.g. disjoint projections on
ALL axes in Euclidean physical units is NOT Lorentz local commutativity.
-/
open Casting DoseTravel
open Spectral Orbit.Prairie Caino
open Six
section
variable (P:Spine)(x:P.Spectrum0 3)(s n:ℕ)
-- body positions use widths independent of Clan
abbrev FTest (P:Spine)(Z:Lead.Clan)(s n:ℕ) := P.experimentBody Z s n
abbrev RTest (P:Spine)(Z:Lead.Clan)(s n:ℕ) := (P.experimentBody Z s n).kiss P 3
-- consultation call *at t*. Closed-algebra character reading.
lemma fineReading (R:P.Register) (t:ℕ)(F G:SampleDose)(Z W:Lead.Clan) :
    let A:= (P.prepared t (P.RTest Z s n) F)*(P.prepared t (P.FTest W s n) G)
    P.arrayFine x s n t F G Z W=P.chi 3 x (P.reading 3 t A) ∧ P.arrayFine x s n t F G Z W=P.spirits R 3 x (P.slotHole t A):= ⟨rfl,(P.oneCup R 3 x _ _).symm⟩

def splitArray (P:Spine)(t:ℕ)(X:P.Test→ₗ[ℂ]ℂ)(F G:SampleDose)(s n:ℕ) : CrossRead:= Matrix.of (fun Z W=> X ((P.prepared t (P.RTest Z s n) F)*(P.prepared t (P.FTest W s n) G)))
lemma forecast (t:ℕ) (hM:n>P.calibration.ℓ) (h:s≤t)(F G:SampleDose)(c:ℝ) (l:∀ i:Lead.Clan,P.WallBefore (P.experimentBody i s n) F c)(e:∀ i:Lead.Clan,P.WallAfter (P.experimentBody i s n) G c)
    (X:P.Test→ₗ[ℂ]ℂ)(u:Factors P.calibration X)(m:MatterWard P.calibration X∨GaugeWard P.calibration X):
    P.splitArray t X F G s n=0:=by
 ext1 i j; let A:=P.RTest i s n; let B:=P.FTest j s n
 exact P.split_test t A F B G (P.test_apart A F c B G (l i) (e j)) h h i.2 (P.sensor_mirror i.2 3 _ (P.body_senses i s n hM)) X u m

structure ReturnsSix (c:ℝ)(F G:SampleDose):Prop where
 beforeY(Z:Lead.Clan) : P.WallBefore (P.RTest Z s n) F c
 beyondY(Z:Lead.Clan) : P.WallAfter (P.FTest Z s n) G c
 spaces(Z W:Lead.Clan) : Disjoint (P.spacePrice (P.RTest Z s n) F) (P.spacePrice (P.FTest W s n) G)
 steady : Tendsto (fun t=>P.arrayFine x s n t F G) atTop (𝓝 (P.arrayReading x s n c F G))
 integral(Z W:Lead.Clan) : P.arrayReading x s n c F G Z W=
        ∫ p:Vantage,∫ q:Vantage,(F.val p:ℂ)*(G.val q:ℂ) * P.commonWell 3 x (P.gridStory s n Z W) (usher p q) [false,true]
 exact_from(t:ℕ)(u:s≤t)(Z W:Lead.Clan) : P.arrayFine x s n t F G Z W = inner ℂ (P.preVector x s t n Z F c) (P.postVector x s t n W G c)
 centered(t:ℕ)(u:s≤t)(Z:Lead.Clan) : P.singleState 3 t x (P.prepared t (P.RTest Z s n) F)=0∧ P.singleState 3 t x (P.prepared t (P.FTest Z s n) G)=0
 disqualifies(t:ℕ)(u:s≤t)(X:P.Test→ₗ[ℂ]ℂ)(a: Factors P.calibration X)(p: MatterWard P.calibration X ∨ GaugeWard P.calibration X): P.splitArray t X F G s n=0
 poles : ReadsSix (P.arrayReading x s n c F G)
 eventual : ∀ᶠ t:ℕ in atTop, ReadsSix (P.arrayFine x s n t F G)
lemma paidReturn (c:ℝ)(F G:SampleDose)(a:∀ Z,P.WallBefore (P.RTest Z s n) F c) (p:∀ Z,P.WallAfter (P.FTest Z s n) G c) (l:P.Ellis 3 x) (h:ReadsSix (P.arrayReading x s n c F G)) (w:P.calibration.ℓ < n) : P.ReturnsSix x s n c F G:=
 let T:= P.answersTogether x s n c l F G a p
 { beforeY:=a,beyondY:=p
   spaces Z W:= P.test_apart _ _ c _ _ (a Z) (p W)
   steady:= T
   integral Z W:= P.continuousAnswer x s n Z W F G c l (a Z) (p W)
   exact_from t u Z W:= P.pinPricing x s t n Z W F G c (a Z) (p W) u
   centered t u Z:= ⟨P.Dose_zero t _ F x (P.body_central x s n Z).2 u,P.Dose_zero t _ G x (P.body_central x s n Z).1 u⟩
   disqualifies t u X a' p':= P.forecast s n t w u F G c a p X a' p'
   poles:=h
   eventual:= T.eventually (readsSix_open.mem_nhds h) }
variable (F G: SampleDose)
-- Robust. Here any compact layout supporting the original pair and keeping the time gap when varying. Could take compact enlargement of their support (w/ buffering relative to the open set).
structure Perturbative (c:ℝ) (F G: SampleDose)(U:Set CrossRead) : Prop where
 stable (X Y : Set Vantage) (x':IsCompact X)(y:IsCompact Y)(u:tsupport F.val ⊆ X)(v:tsupport G.val⊆Y):
  ∃ e>0, ∀ F' G':SampleDose,tsupport (Dose.val F')⊆X→tsupport (Dose.val G')⊆Y→ AltNear e F F'→ AltNear e G G' → (∀ Z, P.WallBefore (P.RTest Z s n) F' c) → (∀ W,P.WallAfter (P.FTest W s n) G' c) → (P.arrayReading x s n c F' G')∈ U ∧ P.ReturnsSix x s n c F' G' -- e sup cost; compact sets; no projection conclusion
lemma robustPays (c:ℝ) (J:P.Ellis 3 x)(U:Set CrossRead)(w:U∈𝓝 (P.arrayReading x s n c F G))(u:ReadsSix (P.arrayReading x s n c F G)) (h:P.calibration.ℓ<n): P.Perturbative x s n c F G U:=by
 constructor
 intro X Y x' y a b
 obtain ⟨e,t,p⟩:= P.near_wall x s n c F G X Y x' y a b (U ∩ {m|ReadsSix m}) (inter_mem w (readsSix_open.mem_nhds u))
 refine ⟨e,t,fun A B t r w x' l f=>?_⟩
 have ht:= p A B t r w x'; exact ⟨ht.1,paidReturn P x s n c _ _ l f J ht.2 h⟩
end

section rank
variable (P:Spine)(x:P.Spectrum0 3)(J:P.Ellis 3 x)(s n:ℕ)
local notation "K"=> P.calibration
local notation "V"=> P.otherSpectrum 3 3 x
local notation "S"=> P.seasons 3 V
local notation "H"=> P.ManyF 3 V
local notation "Γ"=> (S).ℚmeasure.region
local notation "W₀"=> P.probeWidth s n 3
-- array_rank
variable (U:SampleDose)
abbrev reflectorGram (P:Spine) (x:P.Spectrum0 3) (s n:ℕ) (u:SampleDose):= Matrix.gram ℂ (fun Z=> P.launchCost x s n Z u 0)
def windowGram (A:Set E4): CrossRead:= Matrix.gram ℂ (fun Z:Lead.Clan=> Γ (Cheer.press (P.dew s n) A) (P.launchCost x s n Z U 0))
lemma reflector_matches : P.arrayReading x s n 0 (flipDose U 3) U= P.reflectorGram x s n U:= by
 ext1 Z W; exact congrArg (fun x':H=>inner ℂ x' (P.launchCost x s n W U 0)) (P.poseFlipCost x s n Z U)
lemma reflector_consult (t:ℕ)(Z W:Lead.Clan) :
 P.arrayFine x s n t (flipDose U 3) U Z W=P.singleState 3 t x (P.reflectTest 3 (P.prepared t (P.FTest Z s n) U) * P.prepared t (P.FTest W s n) U):= congrArg (fun y:P.Test=>P.singleState 3 t x (y*P.prepared t _ U)) (P.prepared_opposition t _ U 3)
structure ReflectMeter (A:Set E4):Prop where
 exposure: U.Normalized ∧ P.ReturnsSix x s n 0 (flipDose U 3) U
 bounded_below: ∃ d:ℝ,0<d ∧ ((d:ℂ) • (1:CrossRead)) ≤ P.windowGram x s n U A ∧ ((d:ℂ) • (1:CrossRead)) ≤ P.arrayReading x s n 0 (flipDose U 3) U
 verify: ∀ t:ℕ,s≤t→∀ Z: Lead.Clan,∃ h:P.birthF 3 t (P.prepared t (P.FTest Z s n) U), P.viewF 3 V t h=P.postVector x s t n Z U 0
 inbound(Z:Lead.Clan) : Tendsto (fun t=>P.postVector x s t n Z U 0) atTop (𝓝 (P.enter 3 V (P.launchCost x s n Z U 0)))
 positiveTime(Z:Lead.Clan) : ((P.seasons 3 V).ℚmeasure).region {p:E4|YM.time p=0} (P.launchCost x s n Z U 0)=0
 diagonals(Z:Lead.Clan) : 0< (P.arrayReading x s n 0 (flipDose U 3) U Z Z).re
 stable(Z:Set CrossRead)(a:Z∈𝓝 (P.arrayReading x s n 0 (flipDose U 3) U)): -- arbitrarily close retain diagonal costs (real parts as well) same clocks
   P.Perturbative x s n 0 (flipDose U 3) U Z

open FrameBound
-- building from local inequalities & resolution vector identifications. Maybe r binders order
include J
lemma meter_odds (f:U.Normalized)(p:∀ i∈tsupport U.val,P.probeWidth s n 3< i 3)(h:P.calibration.ℓ<n)(A:Set E4)(d:ℝ)(e:0<d)
    (k:Coercive Lead.Clan (P.ManyF 3 (P.otherSpectrum 3 3 x)) (fun Z=>((P.seasons 3 (P.otherSpectrum 3 3 x)).ℚmeasure).region (Cheer.press (P.dew s n) A) (P.launchCost x s n Z U 0)) d)(v:Coercive Lead.Clan H (fun Z=>P.launchCost x s n Z U 0) d):
   P.ReflectMeter x s n U A:= by
 let l(i):= P.launchCost x s n i U 0; let G:=flipDose U 3; let T:= P.arrayReading x s n 0 G U
 have hp:T=Matrix.gram ℂ l:= P.reflector_matches x s n U
 have hv : ReadsSix T:=hp.symm ▸ (entryCharge H d e l v).1
 have ha(Z:Lead.Clan): P.WallAfter (P.FTest Z s n) U 0:= fun i g=> by change 0+W₀ < i 3; rw [zero_add]; exact p i g
 have hf(Z:Lead.Clan) : P.WallBefore (P.RTest Z s n) G 0 := by
    intro i hi; have hx:= (ha Z) (opposeR 3 i) (show i∈ poseMirror 3 ⁻¹' tsupport U.val from ((show tsupport G.val=_ from flipBudget U 3) ▸ hi)) -- rw variant
    change 0+W₀ < opposeR 3 i 3 at hx; change i 3+W₀<0; rw [show opposeR 3 i 3= -i 3 from if_pos rfl] at hx; linarith
 refine ⟨⟨f,P.paidReturn x s n 0 _ _ hf ha J hv h⟩, ⟨d,e,loewnerCharge H d _ k,(show _≤T from by rw [hp]; exact loewnerCharge H d l v)⟩,?_, (fun i=>P.toLaunch x s n i U 0 J), (fun i=> P.strictlyAdvancing ..),?_, (fun Z a=>P.robustPays x s n G U 0 J Z a hv h)⟩
 · intro t p Z; exact P.positive_exposure x s t n Z U (ha Z) p
 intro Z; change 0< (T Z Z).re
 rw [hp]; exact (RCLike.lt_iff_re_im.mp ((entryCharge H d e _ v).2 Z)).1
omit J
end rank

section rectangles
variable (P:Spine)(x:P.Spectrum0 3)(J:P.Ellis 3 x)(s n:ℕ)(Y X: Doorway)(b:Orders)
local notation "S"=> P.probeWidth s n
local notation "L"=> Y.invites ×ˢ X.invites
local notation "M"=> P.pointMatrix x s n
local notation "Γ"=> OrderChamber b S
lemma turnStage(Z W:Lead.Clan)(q p:Vantage)(h:p-q∈ OrderChamber b S):
 let l:=P.gridStory s n Z W; let l₀:=[false,true]; let k:= usher q p
 P.Turnstile 3 l l₀ k ∧ P.Plenum l l₀ k:=by
 intro l' G p' -- L notation conflict
 constructor
 · have ht:=order_forward b S (p-q) h; change 2*_ < p 3-q 3 at ht; exact List.pairwise_pair.mpr (show q 3+S 3<p 3-S 3 by linarith only [ht])
 constructor
 intro k
 have t:= h k; unfold OrderSlab at t; split at t
 · refine ⟨_,List.Perm.refl _,List.pairwise_pair.mpr (show q k+S k<p k-S k from ?_)⟩; change 2*S k<p k-q k at t; linarith only [t]
 refine ⟨[true,false],List.Perm.swap .., List.pairwise_pair.mpr (show p k+S k<q k-S k from ?_)⟩; change p k-q k < -(2*S k) at t; linarith only [t]
include J
lemma pointPaid(t:ℕ)(i j:Cover)(p:s≤t)(Z W:Lead.Clan)(e:P.meshPose t j-P.meshPose t i∈OrderChamber b S):
 P.pointMatrix x s n (P.meshPose t j-P.meshPose t i) Z W=P.singleState 3 t x (P.issuing t (P.RTest Z s n) i*P.issuing t (P.FTest W s n) j):=by
 let q:=P.meshPose t i; let p':=P.meshPose t j
 let u:=P.gridStory s n Z W; let d:=usher i j; let l:List Bool:=[false,true]; let r:=P.vtile t∘d; let T:=P.advocate 3 x 3
 have he:P.laysM ∘ r =usher q p':=funext fun x=>by cases x<;> rfl
 have Ht:=P.turnStage s n b Z W q p' e
 have h:P.Turnstile 3 u l (P.laysM ∘ r):=he.symm ▸ Ht.1
 have hz:= (P.entirely_now 3 x u l J 3 r h (he.symm ▸ Ht.2)).symm.trans (P.turn_purchase 3 T u d t l h (fun i _=>by cases i <;> exact p))
 refine (P.transmission_shifted x s n Z W q p' J (order_forward b S _ e)).symm.trans ((P.common_cult 3 x u (usher q p') l J (List.Perm.refl _) Ht.1).trans ?_)
 exact (congrArg (P.memorial 3 T u l) he.symm).trans (hz.trans ((P.single_agrees 3 3 x t _).trans (congrArg (P.singleState 3 t x) (show P.fullScroll t u d l=_ by change _*(_*1)=_; rw [mul_one]; rfl))))
omit J
structure AllOpens : Prop where
 cover : Y.Later X b (P.probeWidth s n) -- all axes!
 allW : closure Y.invites ×ˢ closure X.invites ⊆ {p | p.2-p.1∈Γ}
 point_density : let C:= {p:Vantage×Vantage| ReadsSix (M (p.2-p.1))}; IsOpen (L ∩ C) ∧ L ⊆ closure (L ∩ C)
 realizable(t:ℕ)(i j:Cover)(p:s≤t)
    (h:P.meshPose t i ∈ closure Y.invites) (k:P.meshPose t j∈ closure X.invites)(Z W:Lead.Clan):
    P.pointMatrix x s n (P.meshPose t j-P.meshPose t i) Z W=P.singleState 3 t x (P.issuing t (P.RTest Z s n) i*P.issuing t (P.FTest W s n) j)
 reading : ∃ c:ℝ, (∀ i F,tsupport (F:SampleDose).val⊆ closure Y.invites→ P.WallBefore (P.RTest i s n) F c)∧ (∀ i F,tsupport (F:SampleDose).val⊆ closure X.invites → P.WallAfter (P.FTest i s n) F c) ∧
   (∃ F G:SampleDose,F.Normalized ∧ G.Normalized∧ tsupport F.val ⊆ Y.invites ∧ tsupport G.val ⊆ X.invites ∧ P.ReturnsSix x s n c F G) ∧
   (∀ k (r:ℝ),0<r→ ∀ F G:SampleDose,F.Normalized→G.Normalized→tsupport F.val ⊆ Y.invites→tsupport G.val ⊆ X.invites→
     ∃ F' G':SampleDose,F'.Normalized∧G'.Normalized∧tsupport F'.val ⊆ Y.invites∧tsupport G'.val ⊆ X.invites∧ NearSmear k r F F'∧NearSmear k r G G'∧ P.ReturnsSix x s n c F' G') ∧
   ∀ F G (W:Set CrossRead),P.ReturnsSix x s n c F G→ W∈𝓝 (P.arrayReading x s n c F G)→ P.Perturbative x s n c F G W -- final clause perhaps S shadows
include J
lemma allClear(p:Y.Later X b (P.probeWidth s n))(e:P.calibration.ℓ<n)(w:∃ p∈Γ,ReadsSix (M p)) : P.AllOpens x s n Y X b:=by
 have he: closure Y.invites ×ˢ closure X.invites ⊆ {p | p.2-p.1∈Γ}:= fun y v=> Doorway.covers p v.1 v.2
 refine ⟨p,he,?_,fun t i j p u v Z W=> P.pointPaid x J s n b t i j p Z W (he (show (P.meshPose t i,P.meshPose t j)∈ _ from ⟨u,v⟩)),?_⟩
 · intro C
   let R:= {p:Vantage×Vantage|p.2-p.1∈Γ}; let U:= R ∩ C
   have H := live_poses J s n b w; have hf:L ⊆ R:= fun i v=>he (show i∈ closure Y.invites ×ˢ closure X.invites from ⟨subset_closure v.1,subset_closure v.2⟩)
   have hk:IsOpen L:=Y.doorOpen.prod X.doorOpen
   have ht:L∩ C=L∩ U := Set.Subset.antisymm (fun i v=> ⟨v.1,hf v.1,v.2⟩) (fun i v=> ⟨v.1,v.2.2⟩)
   rw [ht]; refine ⟨hk.inter H.1,fun i v=>mem_closure_iff_nhds.mpr (fun t e=>?_)⟩
   obtain ⟨j,⟨h,u⟩,x⟩: (t∩ L ∩ U).Nonempty:=mem_closure_iff_nhds.mp (H.2 (hf v)) _ (inter_mem e (hk.mem_nhds v)); exact ⟨j,h,u,x⟩
 obtain ⟨c,a,b'⟩:= Doorway.wallBetween p -- syntax
 have hY:(∀ (i:Lead.Clan)(F:SampleDose),tsupport F.val⊆ closure Y.invites→ P.WallBefore (P.RTest i s n) F c):=fun i F v=> P.beforeTest s n c Y a F i v
 have hX:(∀ (i:Lead.Clan)(F:SampleDose),tsupport F.val⊆ closure X.invites→ P.WallAfter (P.FTest i s n) F c):=fun i F v=> P.afterTest s n c X b' F i v
 have g : ∀ F G:SampleDose, tsupport F.val⊆ Y.invites→tsupport G.val⊆ X.invites → ReadsSix (P.arrayReading x s n c F G)→ P.ReturnsSix x s n c F G:=fun F G z u t=>P.paidReturn x s n c F G (fun i=> hY i F (z.trans subset_closure)) (fun i=> hX i G (u.trans subset_closure)) J t e
 refine ⟨c,hY,hX,?_,?_,fun F G t p z=> P.robustPays x s n F G c J t z p.poles e⟩
 · obtain ⟨F,G,f,h,u,v,t⟩:= P.shining x s n c b Y X J p a b' w; exact ⟨F,G,f,u,h,v,g F G h v t⟩
 intro k r h F G f u hf hg
 obtain ⟨F',G',a₁,b₁,v,x',e,f,k⟩:= P.perturbations x s n c b Y X J p a b' w F G f u hf hg k r h
 exact ⟨F',G',a₁,b₁,v,x',e,f,g F' G' v x' k⟩
omit J
end rectangles
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
