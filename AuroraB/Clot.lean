import AuroraB.Esteem
import AuroraB.Viaduct
import AuroraB.Clockw
import AuroraB.Xphase
import SatinHeatSpecies
import AuroraB.Gill
import Mussel.Seal
import Mussel.Foil
import Mussel.Super
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 250000
set_option quotPrecheck false
noncomputable section

open Filter Function Set Metric MeasureTheory
open scoped Topology InnerProductSpace NNReal ComplexOrder BigOperators
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Casting Six
namespace Habitat
variable {P:Spine} {x:P.Spectrum0 3} {c r:ℕ→ℕ} {K:P.Register} {J:P.Ellis 3 x}
variable (B:P.Experiment K c r x J)(Z:Lead.Clan)
local notation "ξ"=> P.otherSpectrum 3 3 x
local notation "ω"=> P.colorZero 3 (P.otherSpectrum 3 3 x)
local notation "Ω"=> P.heaven 3 ξ
local notation "H"=> P.ManyF 3 ξ
local notation "G"=> P.ColorHil 3 (P.otherSpectrum 3 3 x)
namespace Hemlock
open PledgeT MiterT Broker
namespace AuroraB
open PledgeT MiterT Broker Py.Rate.Pitching.Focus
open _root_.Yoland
-- need real Space scalar tower? inferred.Instance `noon` ℝ.Also `pay`. arm use bank comp.
variable (d:ℕ)(C D:ℕ→ℕ→ℝ)
local notation "Γ" j:max s:max=> agent P d C D s B j
local notation "qt" j:max s:max=> offer_update P d C D s B j
local notation "φ" s:max=> (P.macroStep s:ℂ)
local notation "zQ" s:max=> MiterT.central P d s
local notation "Ψ"=> P.seasons 3 ξ
local notation "a₀" i:max s:max t:max n:max V:max=> schema B i d C D s t n V
local notation "B₀" i:max s:max n:max V:max =>works B i d C D s n V
local notation "μ" t:max=> P.singleState 3 t x
local notation "ϕ"=> P.reflectTest 3
local notation "𝒯"=> P.ColorHil 3 ξ
variable (s t n:ℕ)(U G':SampleDose)
lemma rStorm(m:ℕ)(Z₀:Lead.Clan): B₀ Z₀ s (m+1) U= (φ s)⁻¹ • (B₀ Z₀ s m (shuf U (P.macroStep s))-B₀ Z₀ s m U):=rfl
variable (h:tidal P d s <1)
include h
lemma fine_h(hU:hosp U): Tendsto (fun t=>(μ t) (a₀ Z s t n U)) atTop (𝓝 (inner ℂ (Ω) (B₀ Z s n U))):=by
 induction n generalizing U with
 | zero=>exact (each B Z d C D Z U U s hU hU h).2
 | succ n ih=>
    let F:=shuf U (P.macroStep s); have hc:=ih F (wards _ hU (P.macroStep_pos _ |>.le)); have he:=ih U hU
    simp_rw [rSchema,map_smul,map_sub,smul_eq_mul,rStorm,inner_smul_right,inner_sub_right]; exact (hc.sub he).const_mul _
set_option maxHeartbeats 420000 in
lemma fine_time(W:Lead.Clan)(m:ℕ)(t:hosp U)(v:hosp G'): Tendsto (fun t'=> (μ t') (ϕ (a₀ Z s t' n U)*a₀ W s t' m G')) atTop (𝓝 (inner ℂ (B₀ Z s n U) (B₀ W s m G'))):=by
 let F(X:SampleDose):=shuf X (P.macroStep s); have u(X:SampleDose)(p:hosp X): hosp (F X):= wards X p (P.macroStep_pos _|>.le)
 induction n generalizing U with
 | zero=> induction m generalizing G' with
    | zero=> exact (each B Z d C D W U G' s t v h).1
    | succ n ih=>
       have p:=((ih (F G') (u G' v)).sub (ih G' v)).const_mul ((φ s)⁻¹)
       simp_rw [rSchema,Algebra.mul_smul_comm,mul_sub,map_smul,map_sub,smul_eq_mul,rStorm,inner_smul_right,inner_sub_right]; exact p
 | succ n ih=>
    have p:=((ih (F U) (u U t)).sub (ih U t)).const_mul (star (φ s)⁻¹)
    simp_rw [rSchema,P.scale_mirror,map_sub,smul_mul_assoc,_root_.sub_mul,map_smul,map_sub,smul_eq_mul,rStorm,inner_smul_left,inner_sub_left]; exact p
-- vista transport forward
lemma vista_roll₂(a:ℝ)(p:0 ≤a)(q:hosp U):vistaH B Z d C D s (shuf U a)=dawn (Ψ) a (vistaH B Z d C D s U):= apronShift x (qt Z s) a p _ U (zQ s) (inside_d d U q s h)
-- frame semigroup finite height. use induction
local notation "τ"=>P.macroStep s
private lemma color_morph{X:Hilbert}(p:ℝ)(z:X): (p:ℂ) • z=p • z:=Complex.coe_smul p z
omit h in
private lemma budgetF {R:Hilbert}(g:R.Op)(t:R){A B a c q w:R}{u:ℂ}(p:A=g a)(v:B=g c)(h:a=q)(r:c=w)(k:g (u •(q-w))=t): u • (A-B)=t:=by rwa [p,v,h,r,←map_sub,←map_smul]
#check @rStorm
set_option maxHeartbeats 500000 in
lemma crypto(q:hosp U): works B Z d C D s n U=(frame (Ψ) n (τ) (ContinuousLinearMap.id ℂ (H).space)) (vistaH B Z d C D s U):=by
 let e:= (ContinuousLinearMap.id ℂ (H).space); let S:= (Ψ); let Y(i):=frame S i (τ) e
 let w(F:SampleDose):=vistaH B Z d C D s F; let t:= P.macroStep s; let f(F:SampleDose):= shuf F t; let c:ℂ:= (t:ℂ)⁻¹
 induction n generalizing U with
 | zero=>rfl
 | succ n ih=>
    let hp:=rStorm B d C D s U n Z -- order? rStorm B Z? section Z argument explicit Z0 duplicate: #check
    have h':w (f U)=dawn S t (w U):= vista_roll₂ B Z d C D s U h t (P.macroStep_pos _|>.le) q
    exact Eq.trans hp (budgetF (R:=H) (Y n) ((Y (n+1)) (w U)) (ih (f U) (wards U q (P.macroStep_pos _|>.le))) (ih U q) h' rfl (plain (R:=H) S n t (w U)))
where plain {R:Hilbert}(S:OS.Semigroup R (3:Axis))(n:ℕ)(t:ℝ)(z:R) : let w:= ((t:ℂ)⁻¹ • (dawn S t z-z)); let Y(i):=frame S i t (ContinuousLinearMap.id ℂ R.space); Y n w= ((noon S t).comp (Y n)) z:=by
        intro w Y; have hw:w=noon S t z:=by rw [show (noon S t z)= t⁻¹ • (dawn S t z - z) from rfl]; unfold w; rw [show (t:ℂ)⁻¹=((t⁻¹:ℝ):ℂ) from (Complex.ofReal_inv ..).symm]; exact Complex.coe_smul .. 
        rw [hw]; change Y n _=noon S t (Y n z)
        have he(i:ℕ)(x:R):Y i (noon S t x)=noon S t (Y i x):=by induction i generalizing x with|zero=>rfl |succ i ih=> change noon S t (Y i (noon S t x))=noon S t (noon S t (Y i x)); rw [ih]
        exact he ..
#print axioms fine_time
#print axioms crypto
end AuroraB
end Hemlock
end Habitat
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
