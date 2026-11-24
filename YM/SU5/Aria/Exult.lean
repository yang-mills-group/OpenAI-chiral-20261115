import YM.SU5.Aria.Affliction
import YM.SU5.Cheer.Harp
set_option maxHeartbeats 250000
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
variable (P:Spine)(x:P.Spectrum0 3)(Z:Lead.Clan)(s n:ℕ)(c r:ℕ→ℕ)
local notation "K"=> P.calibration
local notation "Λ"=> P.par
local notation "R"=> ruler P.par.block
local notation "ξ"=> P.advocate 3 x 3
local notation "H"=> P.ColorHil 3 (P.advocate 3 x 3)
local notation "Ω"=> P.heaven 3 (P.advocate 3 x 3)
local notation "ω"=> P.colorZero 3 (P.advocate 3 x 3)
local notation "S"=> P.seasons 3 (P.advocate 3 x 3)
local notation "G"=> P.ManyF 3 ξ
local notation "L₀"=>P.leftX Z s n
local notation "L₁"=>P.rightX Z s n
local notation "η"=> P.pairStory Z s n
local notation "p"=> P.stockS Z (P.flash n)
local notation "Σ₀"=> Prod.fst (α:=P.Apron) (β:=Vantage)
local notation "Σ₁"=> Prod.snd (α:=P.Apron) (β:=Vantage)
local notation "Χ" L:max=> P.commonWell 3 x Σ₀ Σ₁ L
variable (J:P.Ellis 3 x)
local notation "κ"=> P.cartage 3 ξ
local notation "u"=> P.palp s
local notation "E"=> (S).E
local notation "F"=>P.crownT Z s n
local notation "Z'"=> P.allowance x Z s n
local notation "Δ"=> P.lucid x Z s n
local notation "a"=>P.markX s
abbrev palpBank : Bank:= transverse 3 (fun i=> P.palp s i.val)
lemma pall : κ (u)=(S).U (P.palpBank s):= uses_cart ..
def enteredPart : ℂ:= P.commonWell 3 x Σ₀ Σ₁ (P.pairStory Z s n)- P.commonWell 3 x Σ₀ Σ₁ [(P.turnModel 3 L₀)]*P.commonWell 3 x Σ₀ Σ₁ [L₁]
include J
lemma honorEntry : P.enteredPart x Z s n= inner ℂ Δ (κ (u) (E (a+a) Δ))-star Z'* Z':= congrArg₂ HSub.hSub (P.doublet_ready x Z s n J) (congrArg₂ (· * ·) (P.single_pays x Z s n J).2.2 (P.single_pays x Z s n J).2.1)
omit J
-- zoom economics
local notation "ρ" i:max=> P.dew (c i) (r i)
variable{P x c r}(A:Launch P c r){g:ℕ→ℝ} (T:readyUV P c r x g)(d:Tendsto g atTop (𝓝 0))
include A
lemma shrinkBeat (m:ℕ): P.dimensionS c r (fun i=>whenly (timeMesh Λ) (c i) m) 0:=by
 have he:Tendsto (fun i=>(r i:ℝ)) atTop atTop:=tendsto_natCast_atTop_atTop.comp A.eager.tendsto_atTop
 have hp:P.bargain r (fun i=> (m:ℤ)) 0:= tendsto_const_nhds.div_atTop he
 exact (P.priceV c r _ _ hp A.unitSize).congr fun i=>congrArg (·/ρ i) (natural_time (timeMesh Λ) (c i) m) -- syntax
lemma stampB : Tendsto (fun i=>(ρ i)⁻¹ • P.palpBank (c i)) atTop (𝓝 0):=by
 let g:Street→ℝ:= fun _=>1; let i':= transverse 3 g; let t(i:ℕ):ℝ:= ↑(whenly (timeMesh Λ) (c i) P.MarginX)
 have he(i:ℕ): P.palpBank (c i)= t i • i':=by
    -- apply eyes_toFace
    let z:= (P.palpBank (c i)); let w:=t i • i'
    apply (eyes_toFace (3:Axis) z).trans _; apply Eq.trans (congrArg (transverse (3:Axis)) ?_) (eyes_toFace (3:Axis) w).symm; funext k
    change (z.val k.val:ℝ)= t i*(i'.val k.val)
    rw [show i'.val k.val=1 from transverse_eyes (3:Axis) g k,mul_one,show z.val k.val=_ from transverse_eyes (3:Axis) (fun k=> P.palp (c i) k.val) k]; change bell (timeMesh Λ) (c i) (P.following k.val)=_; unfold following; rw [if_neg k.property]; exact natural_time ..
 have hv:= (shrinkBeat A P.MarginX).smul_const i'; rw [zero_smul ℝ i'] at hv -- zero_smul notation?
 refine hv.congr fun i=>?_ ; rw [he,smul_smul, mul_comm («a»:=(ρ i)⁻¹),div_eq_mul_inv]
-- norm growth & spectral presence
include T d
lemma duet_limit : Tendsto (fun i=> inner ℂ (P.lucid x Z (c i) (r i)) ((κ) (P.palp (c i)) (E ((P.markX (c i))+(P.markX (c i))) (P.lucid x Z (c i) (r i))))) atTop (𝓝 (ovoid Z 0 0)):=by
 let V(i):= P.lucid x Z (c i) (r i); let y(i):=P.markX (c i); let s (i):= whenly (timeMesh Λ) (c i) 2
 have hs(i:ℕ): y i+y i=s i:=by unfold y s markX whenly; push_cast; ring
 have hv : Tendsto (fun i=>inner ℂ (V i) ((S).U (P.palpBank (c i)) (E (s i) (V i)))) _ _:= EuclidAll Z A T d 0 0 (by norm_num) _ (shrinkBeat (P:=P) (c:=c) A 2) _ (stampB A)
 exact hv.congr fun i=>by change inner ℂ (V i) ((S).U (P.palpBank (c i)) (E (s i) (V i))) = _; refine congrArg (inner ℂ (V i)) ?_; change (S).U _ _=κ _ (E (y i+y i) _); rw [P.pall x (c i),hs]
omit A T d
lemma mass_spec : ovoid Z 0 0-(purePrice Z:ℂ)^2= ↑((promenade Z).mass:ℝ) := by
 have he:=blinded Z 0 0; have ht:cutPulse 0=0:=Subtype.ext (show position (0:Space3) 0=0 from (by rw [←Mink.combine_at]; exact map_zero _))
 simpa only [NNReal.coe_zero,ht,Complex.ofReal_zero,Cheer.launched_z] using he
lemma guiding : 0< (promenade Z).mass:=(FiniteMeasure.mass_nonzero_iff (promenade Z)|>.2 (show promenade Z ≠ 0 from fun h=> promenade_ne Z (congrArg (fun x:Narrow=>(x:Measure E4)) h))).bot_lt -- syntax
include A T d
include J
lemma sallete : Tendsto (fun i=>P.enteredPart x Z (c i) (r i)) atTop (𝓝 (↑((promenade Z).mass:ℝ):ℂ)):=by
 let Uu(i):=P.allowance x Z (c i) (r i); let z:ℂ:=↑(purePrice Z); have he:=refreshing Z A T d
 have ht:Tendsto (fun i=>star (Uu i)*Uu i) atTop (𝓝 (z^2)):=by
    rw [show z^2=star z*z from (by simp [z,pow_two])]; exact he.star|>.mul he
 rw [← mass_spec]; exact ((duet_limit Z A T d).sub ht).congr fun i=> (P.honorEntry x Z (c i) (r i) J).symm -- J variable omitted? static P inferred from g? macro expansions
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
