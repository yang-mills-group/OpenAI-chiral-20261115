import YM.SU5.Twilight.Sledge
import YM.SU5.Celeste.Everywhere
import YM.SU5.Twilight.Tidings
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 220000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
variable (P: Spine) (j:Axis) (x:P.Spectrum0 j)
local notation "ω"=> P.colorZero j x
local notation "M"=> timeMesh P.par
local notation "Γ"=> marks M
local notation "N"=> notch M
local notation "κ"=> P.voyageF j x
local notation "ω'"=> P.bank j x
open WeakDual TopologicalSpace
open scoped Pointwise
local notation "Y"=> P.run
local notation "T"=>P.par
local notation "Z"=>P.history.circuit
local notation "K"=>P.calibration
local notation "Φ" i:max=> P.reflectTest i
local notation "Ξ" i:max=> P.shifts i
local notation "W"=> enclave K
local notation "Γr" t:max=> P.conveying t
local notation "ℓ"=> P.calibration.ℓ
variable (s t:ℕ)
local notation "B"=> P.par.block
open Lamour Bridge.Celeste Glimpse
open Ballad
-- import uniform term `P.memo`. 
open SlabMark MeshClock
-- horizontal & vertical step selection. 
namespace RadiusF
variable (Q:Side)(n p:ℕ)(δ:Trans (3:Axis))
open Morn Cube
lemma normalBox {x:Cover}(u:x∈(rayL Q n).patio): x δ.val=3:= by
 obtain ⟨t,h,rfl⟩:= Cube.range_leg (nodeC (birth Q n)) (posDir 3) (2*separationR Q n) x (List.mem_toFinset.mp u); have hv:=δ.property; simp [birth,nodeC,hv]
-- offset units in both reference and actual geometry
abbrev hairStep (ℓ':ℕ):ℤ:= (ℓ':ℤ)+3
noncomputable def next (ℓ':ℕ):ℤ:=2*hairStep ℓ'+1
lemma enough_L : 3+(SlabMark.ruler Q)*(-hairStep p)≤-(p:ℤ):=by have hp: 0 < SlabMark.ruler Q:=SlabMark.ruler_gene _; unfold hairStep; nlinarith only [hp, show 1 ≤ SlabMark.ruler Q from hp, show 0≤(p:ℤ) from by positivity]
lemma enough_R : (p:ℤ) ≤ (3+SlabMark.ruler Q*(next p))+SlabMark.ruler Q*(-hairStep p-1):=by have hp: 0 < SlabMark.ruler Q:=SlabMark.ruler_gene _; unfold hairStep next; nlinarith only [show 1 ≤ SlabMark.ruler Q from hp, show 0≤(p:ℤ) from by positivity] -- hairStep after
lemma next_p :0< next p:=by unfold next hairStep; omega
end RadiusF
open RadiusF Morn
open Py.Rate.LocalLimit.Papal (Weaver)
private lemma defineEntry {S:Finset Cover}{f:Weaver}(p: Lamour.Bridge.Celeste.Voice f S)(a:Axis)(q:ℤ): P.shifts a q (P.tuneK p)= P.tuneK (p.tract a (Glimpse.pace B q)):= rfl
-- use P natural or E? deliver for markings.
lemma travelsT {S:Finset Cover} {f:Weaver}(p: Lamour.Bridge.Celeste.Voice f S)(L:List (Trans j))(q:Trans j→ℤ): P.tuneK (Glimpse.Reading B L q p)= P.luggage j L q (P.tuneK p):=by
 induction L with
 | nil=>rfl
 | cons i L ih=> rw [P.ship_started, ←ih]; refine Eq.trans ?_ (P.defineEntry (Glimpse.Reading B L q p) i.val (q i)).symm; exact rfl
lemma fit_S {f:Weaver}{U:Finset Cover}(p: Lamour.Bridge.Celeste.Voice f U)(h: Tower.region j 0 P.calibration.ℓ U): P.birthF j s (P.tuneK p):= ⟨P.mantra j p h s,rfl⟩
lemma from_S {f:Weaver}{U:Finset Cover}(p: Lamour.Bridge.Celeste.Voice f U)(h: Tower.region j 0 P.calibration.ℓ U): P.coinK j p x h s=P.viewF j x s (P.fit_S j s p h):=(P.holdsF j x s _ (P.mantra j p h s) rfl).symm
variable {k:ℕ}
local notation "u₀"=> next P.calibration.ℓ
variable (z:P.Spectrum0 3)(δ:Trans (3:Axis))
local notation "T₃"=> P.voyageF 3 z
local notation "L₀"=> look 3
local notation "X"=> P.ColorHil 3 z
local notation "X₀"=> P.ManyF 3 z
local notation "V" i:max=> ((T₃).crew i).play
local notation "ψ"=> P.luggage 3 L₀
local notation "p₀"=> all0 (u₀)
abbrev landingP : OS.Cross 3:= transverse 3 (fun _ : Trans 3=> (N s (u₀)).val)
def starRide : (X).Op:= (T₃).raw L₀ (fun i=> N s (p₀ i)) -- type cast Op0 notation maybe
abbrev driving(x:ℤ):OS.Cross 3:= transverse 3 (fun i=> ((↑(if i=δ then N s x else (0:Γ))):ℝ))
def segRide (x:ℤ): (P.ColorHil 3 z).Op:= (V δ) (N s x)
local notation "Θ"=> P.reflectTest 3
local notation "P₀"=> (rayL B k).patio
local notation "P₁"=> P.border 3 L₀ p₀ P₀
lemma read_S {f:Weaver}(p: Lamour.Bridge.Celeste.Voice f (rayL P.par.block k).patio)(q:Cover)(h:q∈P.border 3 L₀ (all0 (u₀)) (rayL P.par.block k).patio): q δ.val=3+ruler B*(u₀):=by
 obtain ⟨i,v,t⟩:= P.always 3 δ L₀ p₀ P₀ h; rw [t,mass_all, normalBox _ _ δ v]
variable {f: Weaver}(p:Lamour.Bridge.Celeste.Voice f (rayL P.par.block k).patio)(u:Suit P.par.block P.calibration.ℓ k)
local notation "y₀"=> P.tuneK p
local notation "a₀"=> P.viewF 3 z s
local notation "h₀"=> P.fit_S 3 s p u
local notation "D" i:max => (ψ i)
local notation "h₁"=> (P.certify 3 s L₀ p₀ h₀)
lemma thereT : P.starRide s z (P.coinK 3 p z u s)= P.viewF 3 z s h₁:=by
 rw [P.from_S 3 z s]; exact (P.ship_ideal ..).symm -- arguments order check
lemma date_one (V₀:Finset Cover){g:P.Test}(hv:P.birthF 3 s g)(hg:g∈bay K V₀ true)(e: ∀ i∈V₀, 3+ruler B*(u₀) ≤ i δ.val): P.JointCuts 3 z (P.coinK 3 p z u s) (P.viewF 3 z s hv) δ:= by
 rw [P.from_S 3 z s]; refine P.payable_cut 3 z s δ (-hairStep ℓ) P₀ V₀ h₀ hv ((Tapestry.locates ..).2 ((p.1.narrow _).widen)) hg (fun i h=>?_) fun i h=>?_
 · rw [normalBox _ _ δ h]; exact enough_L B ℓ
 exact (enough_R B ℓ).trans (add_le_add_left (e i h) _) -- add_le_add_right?
lemma rightRho : P.JointCuts 3 z (P.coinK 3 p z u s) (P.starRide s z (P.coinK 3 p z u s)) δ:=by
 rw [P.thereT s z p u]; exact P.date_one s z δ p u (P₁) _ (P.shipping 3 L₀ p₀ ((Tapestry.locates ..).2 ((p.1.narrow _).widen))) (fun _ h=>(P.read_S δ p _ h).ge)
lemma farRho (i:Trans (3:Axis))(n:ℤ)(h:0≤n): P.JointCuts 3 z (P.coinK 3 p z u s) ((P.segRide s z i n) (P.starRide s z (P.coinK 3 p z u s))) δ:=by
 by_cases e:i=δ
 · subst i; rw [P.thereT s z p u]; unfold segRide; rw [P.registered]
   apply P.date_one s z δ p u (plow K δ.val n P₁) _ (P.shifts_support _ _ _ (P.shipping 3 L₀ p₀ ((Tapestry.locates ..).2 ((p.1.narrow _).widen)))) -- detail
   intro x0 h'; obtain ⟨v,e,rfl⟩ := plow_stays K δ.val n _ h'; rw [SlabMark.moves,if_pos rfl, (P.read_S δ p v e)]; exact le_add_of_nonneg_right (Int.mul_nonneg (ruler_gene _).le h) -- argument order check
 exact P.cut_slide 3 z δ i e _ (P.rightRho s z δ p u)

-- actual projected equality formulas
local notation "W₀"=> P.wealth 3 z
local notation "L"=> P.landingP s
local notation "P⁺" v:max=> P.landingP s+P.driving s δ v
local notation "U"=> (P.seasons 3 z).U
local notation "Vv"=> (P.seasons 3 z)
lemma lift_far (t:ℤ)(y:X): (U) (P.driving s δ t) (P.bank 3 z y)= P.bank 3 z ((P.segRide s z δ t) y):=by
 let x(i:Trans 3):Γ:=if i=δ then N s t else 0
 change (U) (transverse 3 (fun i=> ((x i):ℝ))) _= _; rw [P.roll_motion]; exact congrArg (fun v=> P.bank 3 z v) (DFunLike.congr_fun (P.motion_one 3 z δ (N s t)) y)
lemma lift_near (y:X): (U) (P.landingP s) (P.bank 3 z y)= P.bank 3 z (P.starRide s z y):= P.roll_motion 3 z (fun i=>N s (p₀ i)) y
lemma lift_sp (t:ℤ)(y:X): (U) (P⁺ t) (P.bank 3 z y)=P.bank 3 z (P.segRide s z δ t (P.starRide s z y)):=by rw [add_comm,(Vv).space]; rw [ContinuousLinearMap.comp_apply,P.lift_near,P.lift_far]
lemma specific_step: P.tuneK (p.tract δ.val (pace B (u₀)))= P.shifts δ.val (u₀) (P.tuneK p):=rfl
lemma wallet : P.viewF 3 z s h₀=P.coinK 3 p z u s:= (P.from_S 3 z s p u).symm
local notation "z₀"=> P.coinK 3 p z u s
local notation "σ"=>P.singleState 3 s z
-- new witness purchase
lemma near_gram: inner ℂ (W₀ z₀) ((U) (P.landingP s) (W₀ z₀))=P.singleState 3 s z (P.luggage 3 (look 3) (all0 (u₀)) (P.tuneK p)* P.reflectTest 3 (P.tuneK p)):=by
 rw [P.banked,P.lift_near,P.livingH (j:=3) z (fun i=> P.rightRho s z i p u), P.thereT,← P.wallet]
 rw [P.released_gram,mul_comm]
lemma more_gram (n:ℕ): inner ℂ (W₀ z₀) ((U) (P⁺ (n:ℤ)) (W₀ z₀))= (σ) (P.reflectTest 3 (P.tuneK p) * P.shifts δ.val (n:ℤ) (P.luggage 3 (look 3) (all0 (u₀)) (P.tuneK p))):=by
 rw [P.banked,P.lift_sp,P.livingH 3 z (fun i=> P.farRho s z i p u δ (n:ℤ) (by positivity)), P.thereT]
 unfold segRide; rw [P.registered,← P.wallet,P.released_gram]
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
