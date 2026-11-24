import YM.SU5.Registration.M6
set_option autoImplicit false
set_option maxHeartbeats 380000
noncomputable section
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000

namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection

open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase
     MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound
     Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker
     ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy
     Tapestry Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn

open CF.Velvet CF.Pannier.Chancel
open Spine Pitching.Focus
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel

open SatinNucleus Six
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
namespace YM.SatinRegistration
open Function Filter Metric
open scoped Topology NNReal ENNReal BigOperators InnerProductSpace ComplexOrder Classical
variable {H:Hilbert}{A B:ℕ→ H.Op} {U V:H.Op}
lemma Flying.add' (p:Flying A U)(q:Flying B V): Flying (A+B) (U+V) := by
 intro z; simp_rw [Pi.add_apply,map_add]; exact ⟨(p z).1.add (q z).1,(p z).2.add (q z).2⟩
lemma Flying.sub' (p:Flying A U)(q:Flying B V): Flying (A-B) (U-V):= by
 intro z; simp_rw [Pi.sub_apply,map_sub]; exact ⟨(p z).1.sub (q z).1,(p z).2.sub (q z).2⟩
lemma Flying.by_norm (p:Tendsto A atTop (𝓝 U)): Flying A U:=by intro v; exact ⟨((continuous_id.clm_apply (continuous_const (y:=v))).tendsto U).comp p, ((ContinuousLinearMap.adjoint.continuous.clm_apply (continuous_const (y:=v))).tendsto _).comp p⟩
lemma Flying.by_wages (p:Tendsto (fun i=> ‖A i-B i‖) atTop (𝓝 0)) (q:Flying B U): Flying A U:=by
 have he:Flying (A-B) (0:H.Op):= by_norm (tendsto_zero_iff_norm_tendsto_zero.mpr p)
 have h:= he.add' q; rwa [sub_add_cancel,zero_add] at h
lemma Flying.unique (p:Flying A U)(q:Flying A V): U=V:=by ext1 i; exact tendsto_nhds_unique (p i).1 (q i).1
end YM.SatinRegistration
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry Germ Alliance
namespace Spine
open Aria Casting Six OS.Semigroup OS.Semigroup.Balloon SatinJets
open MacroGrid SatinNucleus YM.SatinRegistration
set_option quotPrecheck false
variable (P:Spine)(x:P.Spectrum0 3)
local notation "ξ" => P.advocate 3 x 3
local notation "G"=> P.ManyF 3 ξ
local notation "Ε"=>P.physicalEnergy 3 ξ
local notation "T"=> (P.physicalEnergy 3 ξ).E
local notation "E"=> (P.seasons 3 ξ).E
local notation "M" a:max b:max=> whenly (timeMesh P.par) a b
open _root_.YM.CF.Buffered.Afterglow.Hierarchy
variable (A:ℕ→ P.Apron) (t:ℝ≥0)
local notation:max "H!" k:max=> P.stageH 3 ξ (A k)
local notation:max "G!" k:max=> P.stageG 3 ξ (A k)
lemma toGlate (c:P.Apron){l w v u:ℝ≥0}(p:c.allowance P 3 ≤ l)(q:l≤w)(s:c.allowance P 3≤v)(t':v≤u): P.stageG 3 ξ c w u= E (w-l)* P.stageG 3 ξ c l v * E (u-v):=by unfold stageG; rw [P.stage_more _ _ _ p q s t',P.bank_both]

-- `CapPrice` even if not by this election's pannel_sales; can consume on arbitrary parameters
lemma received_moves (p:CapReady P x A)(u:0<t) : Flying (H:=G) (fun i=> (G! i) t t) (P.managed x A p t):=by
 obtain ⟨E',q⟩:= Flying.settles (H:=G) (A:=fun i=> (G! i) t t) (by
   have he:= p.2.1 t u
   simp_rw [manage,P.honestBridge] at he; exact he)
 suffices P.managed x A p t= E' from this.symm ▸ q
 ext1 v; apply tendsto_nhds_unique ((P.delivery_cap x A p).accepted t u v); refine (q v).1.congr fun i=>?_ ; exact DFunLike.congr_fun (P.honestBridge x (A i) t t).symm v

variable (u v:ℕ→ℝ≥0)(g1:Tendsto u atTop (𝓝 t))(g2:Tendsto v atTop (𝓝 t))(ht:0<t)
include g1 g2 ht
lemma uniform_pit (p:CapReady P x A) : Flying (H:=G) (fun i=> (G! i) (u i) (v i)) (P.managed x A p t):=by
 let a:= t/2; have ha: a < t:= half_lt_self ht; have hA:0<a:= half_pos ht; let V:= P.managed x A p a
 let B:= P.seasons 3 ξ
 have he:Tendsto (fun i=>u i-a) atTop (𝓝 (t-a)):= g1.sub_const _
 have hh:Tendsto (fun i=>v i-a) atTop (𝓝 (t-a)):= g2.sub_const _
 have hx:P.managed x A p t = E (t-a) * V * E (t-a):= by
    unfold V; exact (congrArg (P.managed x A p) (add_tsub_cancel_of_le ha.le).symm).trans ((P.delivery_cap x A p).isSound a hA (t-a))
 have hb:= ((Flying.heat B he).multiply (P.received_moves x A a p hA)).multiply (Flying.heat B hh)
 rw [hx]; refine hb.late ?_; filter_upwards [P.eventuallyCovered x A p a hA,g1.eventually (le_mem_nhds ha),g2.eventually (le_mem_nhds ha)] with i v₁ g f
 rw [priceWidth, Apron.width_real,Real.toNNReal_coe] at v₁; exact (P.toGlate x _ v₁.le g v₁.le f).symm
omit g1 g2 ht

structure Bought3 (P:Spine)(x:P.Spectrum0 3)(A:ℕ→ P.Apron) : Prop where
 card:P.CapReady x A
 grow:RisePrice (fun s i=> (P.stageH 3 (P.advocate 3 x 3) (A i) s s))
lemma Bought3.funded (F:P.Funding x A):Bought3 P x A:=⟨F.backed P x, F.price 3 []⟩
abbrev ThinHere (P: Spine)(A:ℕ→ P.Apron):Prop:=∀ j:Axis,Tendsto (fun i=> (A i).realWidth P j) atTop (𝓝 0)

lemma toBought (h:RisePrice (fun t i=> (H! i) t t))(p:∀ t:ℝ≥0,0<t→ Travels (H:=G) (fun i=> (G! i) t t))(u:ThinHere P A) :P.Bought3 x A:=by
 refine ⟨⟨u,fun t v=>?_,?_⟩, h⟩
 · simp_rw [manage,P.honestBridge]; exact p t v
 obtain ⟨k,C,b,f⟩:=h; refine ⟨k,C,b,fun t v q=>?_⟩; simp_rw [manage,P.honestBridge]; exact (f t v q).mono (fun i g=> (mul_le_mul_of_nonneg_left (P.toG_cost ..) (by positivity)).trans g)

lemma all_width_paid (a:Axis)(h: P.CapReady x A): Tendsto (fun i=>(A i).allowance P a) atTop (𝓝 0):= NNReal.tendsto_coe.mp (by
 have hv:=h.1 a; simp_rw [Apron.width_real] at hv; exact hv)
lemma Bought3.moving (U:P.Bought3 x A) (a b:ℝ≥0→ℕ→ ℝ≥0) (g1:∀ t,0<t→ Tendsto (a t) atTop (𝓝 t)) (g2:∀ t,0<t→ Tendsto (b t) atTop (𝓝 t)) : RisePrice (fun t i=> (H! i) (a t i) (b t i)):=by
 obtain ⟨k,C,v,w⟩:= U.grow; refine ⟨k,2^k*C,by positivity,fun t p q=>?_⟩; let s:=t/2; have g0:=half_lt_self p; have ht:0<s:=half_pos p
 filter_upwards [w s ht (g0.le.trans q), (P.eventuallyCovered x A U.card s ht), (g1 t p).eventually (le_mem_nhds g0), (g2 t p).eventually (le_mem_nhds g0)] with i u x' D A'
 rw [priceWidth, Apron.width_real,Real.toNNReal_coe] at x'
 change (t:ℝ)^k* ‖(H! i) (a t i) (b t i)‖ ≤ _
 have he:‖(H! i) (a t i) (b t i)‖ ≤ ‖(H! i) s s‖:=by rw [P.stage_more _ _ _ x'.le D x'.le A']; exact P.heater_norm ..
 -- use
 refine (mul_le_mul_of_nonneg_left he (by positivity)).trans ?_; rw [show (t:ℝ)^k= 2^k*(s:ℝ)^k from ?_,mul_assoc]; exact mul_le_mul_of_nonneg_left u (by positivity)
 unfold s; rw [NNReal.coe_div,NNReal.coe_ofNat,←mul_pow]; congr 1; ring
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms Spine.uniform_pit
#print axioms Spine.Bought3.moving
#print axioms Spine.toBought
