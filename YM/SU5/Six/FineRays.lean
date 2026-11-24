import YM.SU5.Six.PressSmear
import Mathlib.MeasureTheory.Function.L2Space
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
/-!
# Actual grid measurements pass the wall

No reprojection/change of spatial-continuum space; no smoothing *after*
the limit. The true paired insertion at t is being sent into the mirror
Gram and more generally into the mixed chronologically ordered calls. This
calculation doesn't require transverse qualification; even the continuously
posed answer only needs time order here.
-/
open MacroGrid
open Casting
open scoped ContDiff
section
-- some color-linear inner product lemmas
variable (X:Hilbert)
lemma right_weight (z:ℂ)(x:X)(p y:X)(h:∀ i∈[x,y],inner ℂ i y=z*inner ℂ i x): y=z • x:= by
 apply sub_eq_zero.mp; apply (inner_self_eq_zero (𝕜:=ℂ)).1
 rw [inner_sub_left,inner_smul_left,inner_sub_right,inner_sub_right,inner_smul_right,inner_smul_right,h x (by simp), h y (by simp)]; ring
private lemma bill_at_entry (Y:Type)[Ring Y][Algebra ℂ Y](E:Y→ₗ[ℂ]ℂ)(s t:Finset Cover)(a b:Cover → Y)(p q:Cover→ℝ)(V W:Cover → X)
    (h:∀ i∈s,∀ k∈t,E (a i*b k)=inner ℂ (V i) (W k)): E ((∑ i∈s,(p i:ℂ) • a i)*(∑ k∈t, (q k:ℂ) • b k))=inner ℂ (∑ i∈s,(p i:ℂ) • V i) (∑ k∈t,(q k:ℂ) • W k):=by
 rw [Finset.sum_mul,map_sum,sum_inner]; refine Finset.sum_congr rfl fun i u=>?_
 rw [Finset.mul_sum,map_sum, inner_sum]; refine Finset.sum_congr rfl fun k l=>?_
 rw [smul_mul_assoc,mul_smul_comm,map_smul,map_smul,h i u k l,inner_smul_left,inner_smul_right]; simp
lemma both_integral {a b:Vantage→X} (h:Integrable a)(g:Integrable b) : inner ℂ (∫ x,a x) (∫ x,b x)= ∫ x, ∫ y, inner ℂ (a x) (b y):= by
 simp_rw [integral_inner g]; let x:=∫ x,b x
 have hv(v:X): inner ℂ v x= starRingEnd ℂ (inner ℂ x v):= (inner_conj_symm ..).symm
 change inner ℂ _ x=∫ i, inner ℂ (a i) x; simp_rw [hv,integral_conj (𝕜:=ℂ), integral_inner h]
end
section birth
variable (P:Spine)(x:P.Spectrum0 3)(t:ℕ)
lemma birthAdd {a b:P.Test}(f:P.birthF 3 t a)(g:P.birthF 3 t b) : P.birthF 3 t (a+b):= by
 obtain ⟨f,rfl⟩:=f; obtain ⟨g,rfl⟩:=g
 exact ⟨⟨f.val+g.val,Subalgebra.add_mem (enclave P.calibration) f.property g.property⟩,rfl⟩
lemma birthScale (z:ℂ) {a:P.Test}(f:P.birthF 3 t a): P.birthF 3 t (z • a):= by
 obtain ⟨f,rfl⟩:=f; exact ⟨⟨z • f.val,Subalgebra.smul_mem (enclave P.calibration) f.property z⟩,rfl⟩
lemma view_plus {a b:P.Test}(f:P.birthF 3 t a)(g:P.birthF 3 t b):
    P.viewF 3 x t (P.birthAdd t f g)=P.viewF 3 x t f + P.viewF 3 x t g:= by
 let p:=P.birthAdd t f g
 have hg:=P.sixWard_view_sub 3 x t p g ((show P.birthF 3 t ((a+b)-b) by rwa [add_sub_cancel_right]))
 have he:P.viewF 3 x t f=P.viewF 3 x t p-P.viewF 3 x t g:= (P.identical_F 3 x t f _ (add_sub_cancel_right ..).symm).trans hg
 exact (eq_sub_iff_add_eq.mp he).symm
lemma sixWard_view_scale (z:ℂ) {a:P.Test}(f:P.birthF 3 t a):
    P.viewF 3 x t (P.birthScale t z f)=z • P.viewF 3 x t f := by
 let p:= P.birthScale t z f
 have hh (e:P.Test)(g:P.birthF 3 t e): inner ℂ (P.viewF 3 x t g) (P.viewF 3 x t p)=z*inner ℂ (P.viewF 3 x t g) (P.viewF 3 x t f):= ((P.released_gram 3 x t g p).trans (congrArg (P.singleState 3 t x) (mul_smul_comm ..))).trans ((map_smul (P.singleState 3 t x) z _).trans (congrArg (fun x:ℂ=>z*x) (P.released_gram 3 x t g f).symm))
 apply right_weight (P.ColorHil 3 x) _ _ (0:P.ColorHil 3 x); intro i v; simp only [List.mem_cons,List.not_mem_nil,or_false] at v; rcases v with v|v <;> subst i <;> exact hh _ _
lemma birthSum (S:Finset Cover)(f:Cover→P.Test) (X:Cover → P.ColorHil 3 x)
    (p:∀ i∈ S,∃ h:P.birthF 3 t (f i),P.viewF 3 x t h=X i):∃ h:P.birthF 3 t (∑ i∈ S,f i),P.viewF 3 x t h=∑ i∈ S,X i:= by
 induction S using Finset.induction_on with
 | empty=>
   rw [sum_empty,sum_empty]
   let g:= P.faceUnit 3 t
   have hx:= P.birthScale t 0 g
   have h:P.birthF 3 t 0:= by simpa only [zero_smul] using hx
   exact ⟨h, (P.identical_F 3 x t _ hx (zero_smul ..).symm).trans ((P.sixWard_view_scale x t 0 g).trans (zero_smul ..))⟩
 | @insert a L h ih=>
   obtain ⟨i,x₀⟩:= ih (fun i z=> p i (mem_insert_of_mem z))
   obtain ⟨g,x'⟩:=p a (mem_insert_self ..)
   rw [sum_insert h,sum_insert h]
   exact ⟨P.birthAdd t g i,(P.view_plus x t g i).trans (congrArg₂ (· + ·) x' x₀)⟩
end birth

variable (P:Spine)(x:P.Spectrum0 3)(s t n:ℕ)(Z W:Lead.Clan)(F G:SampleDose)(c:ℝ)(J:P.Ellis 3 x)
local notation "Θ"=> P.reflectTest 3
local notation "u"=>P.otherSpectrum 3 3 x
local notation "H"=> P.ColorHil 3 u
local notation "Η"=> P.ManyF 3 u
local notation "Φ"=> P.filterVector x s n Z
local notation "E"=> (P.physicalEnergy 3 u).E
local notation "S"=> P.seasons 3 u
local notation "ψ"=> P.sixWard_macroVector x s n Z
local notation "τ"=> P.probeWidth s n 3
local notation "A"=> P.experimentBody Z s n
local notation "B"=> P.experimentBody W s n
local notation "A'"=>(A).kiss P 3
local notation "α" k:max => P.activation t F k
local notation "β" k:max => P.activation t G k
local notation "U"=>P.meshPose t
local notation "Q"=> P.usedGrid t F
local notation "R"=> P.usedGrid t G
local notation "θ"=>P.macroStep t
local notation "M'"=> P.singleState 3 t x
local notation "ρ"=> P.enter 3 u
local notation "π'"=> P.wealth 3 u
local notation "V₀"=> P.forwardRay x W s n c
local notation "V"=> P.cartage 3 u
local notation "Ω"=> P.colorZero 3 u
open scoped BigOperators
def chargedCost := M' (P.prepared t ((P.experimentBody Z s n).kiss P 3) F * P.prepared t (P.experimentBody W s n) G)
def preVector : H:=∑ i∈ Q, α i • P.coldRead t x Z s n c i
def postVector : H:=∑ i∈ Q, α i • P.hotRead t x Z s n c i
lemma pinPricing (a:P.WallBefore A F c)(b:P.WallAfter B G c)(p:s≤t) :
    P.chargedCost x s t n Z W F G= inner ℂ (P.preVector x s t n Z F c) (P.postVector x s t n W G c):= by
 let i:=fun k:Cover=>(θ^4 * F.val (U k)); let j:=fun k:Cover=> ((θ)^4 * G.val (U k))
 exact bill_at_entry H P.Test M' Q R (P.issuing t A') (P.issuing t B) i j (P.coldRead t x Z s n c) (P.hotRead t x W s n c) (fun i e j v=> P.raw_wall t x Z W s n c i j (a _ ((P.usedPose t F i).mp e)) (b _ ((P.usedPose t G j).mp v)) p)
-- Incorporated at the CURRENT height t: stronger than compatibility of single products.
set_option maxHeartbeats 400000 in
private lemma one_positive (a:P.WallAfter A F 0)(p:s≤t)(i:Cover)(v:i∈Q):∃ h:P.birthF 3 t ((α i) • P.issuing t A i),P.viewF 3 u t h= α i • P.hotRead t x Z s n 0 i:=by
 have hv:τ < U i 3:= (zero_add τ).symm.trans_lt (a _ ((P.usedPose t F i).mp v))
 let K:=P.manifestRead t x Z s n i hv p
 exact ⟨P.birthScale t (α i) K.choose,(P.sixWard_view_scale u t (α i) K.choose).trans (congrArg (fun y:H=> P.activation t F i • y) K.choose_spec)⟩
lemma positive_exposure (a:P.WallAfter A F 0)(p:s≤t):∃ h:P.birthF 3 t (P.prepared t A F),P.viewF 3 u t h=P.postVector x s t n Z F 0:=by
 exact P.birthSum u t Q _ _ (one_positive P x s t n Z F a p) -- infer f
section general
private lemma intoGrid (X:Hilbert)(f:Vantage→X)(T:Cover → X.Op):
 poseApprox X (fun z:Vantage=>(F.val z:ℂ) • f z) T (θ) =∑ i∈ Q, α i • T i (f (U i)):=by
 let g:=fun i:Cover=> T i ((F.val (U i):ℂ) • f (U i));
 have he(i:Cover)(x:i∉Q): g i=0:= by
    have hu : F.val (U i)=0:=by by_contra p; exact x ((P.usedPose t F i).2 (subset_closure p))
    unfold g; rw [hu,Complex.ofReal_zero,zero_smul,map_zero]
 refine (room_price θ (P.macroStep_pos t) g Q he).2.trans ?_
 rw [Finset.smul_sum]; apply Finset.sum_congr rfl; intro i h; change ((θ)^Fintype.card Axis:ℝ) • _=_; unfold g; rw [map_smul,show Fintype.card Axis=4 by rfl, ← Complex.coe_smul (θ^4), smul_smul]; push_cast [activation]; rfl
private def baseCost (a:Vantage→ℝ≥0) (p:Vantage): H:= ((F.val p:ℂ) • E (a p) Φ)
private def gridVector (a:Vantage→ℝ≥0) : H := ∑ i∈ Q, α i • P.truck 3 u (P.vtile t i) (E (a (U i)) Φ)
private def costRay (a:Vantage→ℝ≥0)(p:Vantage): Η:= (F.val p:ℂ) • ((V) p ((S).E (a p) ψ))
include J
private lemma toStage (a:Vantage→ℝ≥0)(p:Continuous a):
    Tendsto (fun t'=>gridVector P x s t' n Z F a) atTop (𝓝 (ρ (∫ p:Vantage,costRay P x s n Z F a p))) := by
 let H₀:= P.physicalEnergy 3 u
 let g(p:Vantage):= baseCost P x s n Z F a p; let f(p:Vantage):= E (a p) Φ
 let B₀(p:Vantage):= costRay P x s n Z F a p; let K:=π'; let l(p:Vantage):= V p (K (g p))
 have he:HasCompactSupport g:= F.budget.mono (fun i v t=> v ((congrArg (fun b:ℝ=> (b:ℂ) • (f i)) (show F.val i=0 from t)).trans (zero_smul ℂ _)))
 have ht:Continuous g:= (Complex.continuous_ofReal.comp F.smooth.continuous).smul ((H₀.continuousE Φ).comp p)
 have hp : B₀=l:=funext fun z=> by
    let E':=(S).E; let x':=K Φ; let T:= V z; let c:= (F.val z:ℂ)
    exact ((congrArg (fun w:H=> T (K w)) (show g z=c • f z from rfl)).trans ((congrArg T (map_smul K c (f z))).trans ((map_smul T c _).trans (congrArg (fun y:Η=> c • (T y)) (P.bankHeat 3 u (a z) Φ))))).symm -- pars
 change Tendsto _ _ (𝓝 (ρ (∫ p:Vantage,B₀ p)))
 rw [hp]
 exact (P.macroRiemann x 3 J g he ht).congr fun i=> intoGrid P i F (H) f _
omit J
end general
def launchCost : Η := ∫ p:Vantage,(F.val p:ℂ) • (P.forwardRay x Z s n c p)
def landingCost : Η := ∫ p:Vantage,(F.val p:ℂ) • (P.backwardRay x Z s n c p)
lemma cold_cont : Continuous (P.backwardRay x Z s n c) := P.caravan 3 u id _ continuous_id (((S).continuousE _).comp (continuous_real_toNNReal.comp (continuous_const.sub (continuous_apply 3))))
lemma hot_cont : Continuous (P.forwardRay x Z s n c):= P.caravan 3 u id _ continuous_id (((S).continuousE _).comp (continuous_real_toNNReal.comp ((continuous_apply 3).sub continuous_const)))
include J
lemma toLaunch : Tendsto (fun i=> P.postVector x s i n Z F c) atTop (𝓝 (ρ (P.launchCost x s n Z F c))) := toStage P x s n Z F J (fun p:Vantage=> (p 3-c).toNNReal) (continuous_real_toNNReal.comp ((continuous_apply _).sub continuous_const))
lemma toLand : Tendsto (fun i=> P.preVector x s i n Z F c) atTop (𝓝 (ρ (P.landingCost x s n Z F c))) := toStage P x s n Z F J (fun p:Vantage=> (c-p 3).toNNReal) (continuous_real_toNNReal.comp (continuous_const.sub (continuous_apply _)))
omit J
lemma poseFlipCost : P.landingCost x s n Z (flipDose F 3) 0=P.launchCost x s n Z F 0:= by
 let m:=poseMirror 3; let f(p:Vantage):=((flipDose F 3).val p:ℂ) • P.backwardRay x Z s n 0 p
 have he: MeasurePreserving m.toMeasurableEquiv volume volume:= opposite_money 3
 refine (he.integral_comp' f).symm.trans (integral_congr_ae (Eventually.of_forall fun p=>?_))
 exact congrArg₂ (fun (z:ℝ)(w:Η)=> (z:ℂ) • w) (congrArg F.val (reflectPose_twice 3 p)) (P.mirrored_ray x Z s n p)
lemma weightedMoney (X:Hilbert)(G':Vantage→X)(v:Continuous G') : Integrable (fun z=>(F.val z:ℂ) • G' z):= (((Complex.continuous_ofReal.comp F.smooth.continuous).smul v).integrable_of_hasCompactSupport (F.budget.mono (fun i g t=> g ((congrArg ((fun z:ℝ=> (z:ℂ) • G' i)) (show F.val i=0 from t)).trans (zero_smul ℂ _))))) -- tune zero smul
private lemma scaledPair (X:Hilbert)(v w:X)(a b:ℝ) : inner ℂ ((a:ℂ) • v) ((b:ℂ) • w)=(a:ℂ)*(b:ℂ)*inner ℂ v w:= by rw [inner_smul_left,inner_smul_right,Complex.conj_ofReal,mul_assoc]
include J
lemma measured_both (a:P.WallBefore A F c)(b:P.WallAfter B G c) : Tendsto (fun t=>P.chargedCost x s t n Z W F G) atTop (𝓝 (inner ℂ (P.landingCost x s n Z F c) (P.launchCost x s n W G c))):=by
 let u':= P.landingCost x s n Z F c; let v:= P.launchCost x s n W G c
 let X:=fun t=> P.postVector x s t n W G c; let Y:= fun t=> P.preVector x s t n Z F c
 let L:=fun i=>inner ℂ (Y i) (X i); have he:inner ℂ (ρ u') (ρ v)= inner ℂ u' v:=(ρ).inner_map_map ..
 refine ((show Tendsto (fun t=> L t) atTop (𝓝 (inner ℂ u' v)) from Eq.mp (congrArg (fun t=> Tendsto L atTop (𝓝 t)) he) ((P.toLand x s n Z F c J).inner (P.toLaunch x s n W G c J)))).congr' ((eventually_ge_atTop s).mono fun i p=>(P.pinPricing x s i n Z W F G c a b p).symm)
lemma continuousAnswer (a:P.WallBefore A F c)(b:P.WallAfter B G c): inner ℂ (P.landingCost x s n Z F c) (P.launchCost x s n W G c) =
 ∫ x',∫ y',(F.val x':ℂ) * (G.val y':ℂ) * P.commonWell 3 x (P.gridStory s n Z W) (usher x' y') [false,true] := by
 refine (both_integral Η (weightedMoney F Η _ (P.cold_cont x s n Z c)) (weightedMoney G Η _ (P.hot_cont x s n W c))).trans ?_
 refine integral_congr_ae (Eventually.of_forall fun i=> integral_congr_ae (Eventually.of_forall fun k=>?_))
 let d:ℂ:=(F.val i:ℂ)*(G.val k:ℂ)
 let y:= P.backwardRay x Z s n c i; let w:= P.forwardRay x W s n c k
 let K:= P.commonWell 3 x (P.gridStory s n Z W) (usher i k) [false,true]
 refine (scaledPair Η y w (F.val i) (G.val k)).trans (show d*inner ℂ y w=d*K from ?_)
 suffices u': d=0 ∨ K= inner ℂ y w by
    rcases u' with h|h; · exact (congrArg (fun d'=>d'*inner ℂ y w) h).trans ((zero_mul _).trans ((congrArg (fun d'=>d'*K) h).trans (zero_mul _)).symm)
    exact congrArg (d*·) h.symm
 by_cases t:F.val i=0; · left; unfold d; rw [t,Complex.ofReal_zero,zero_mul]
 by_cases h:G.val k=0; · left; unfold d; rw [h,Complex.ofReal_zero,mul_zero]
 right
 have ha:=a i (subset_closure t); have hb:=b k (subset_closure h)
 change i 3+τ < c at ha; change c+τ < k 3 at hb
 have ht:2*τ < (k-i) 3:=by change _< k 3-i 3; linarith only [ha,hb]
 -- avoid complicated rewriting
 have hp: P.commonWell 3 x (P.gridStory s n Z W) (usher i k) [false,true]= inner ℂ (P.backwardRay x Z s n c i) (P.forwardRay x W s n c k):=(P.transmission_shifted x s n Z W i k J ht).trans (P.ordered_wall x J Z W s n c i k ha hb)
 exact hp
omit J
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
