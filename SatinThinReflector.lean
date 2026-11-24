import SatinThinStationary
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry

open TopologicalSpace
namespace Spine
open Lamour.Bridge.Celeste
open Lamour.Bridge.Celeste.Morn
open Py.Rate.LocalLimit.Papal (Weaver household)
open TopologicalSpace Tapestry.Exhibition
variable (P:Spine)(R : P.Register)(j:Axis)
local notation "φ"=> P.groundZero j
local notation "μ"=> P.pillars j
local notation "W"=> P.calibration
local notation "Q"=> P.par.block
local notation "ℓ"=> P.calibration.ℓ
open Papal Regis.Head Gleam
/-! # Price of ensemble-of-trips. Exactly composed on printed test level before estimation. -/
open Clock Clock.Hookah Clock.Hookah.Blaze
open Preparation.Yoke Yoke.Travel Regis.Head.Garland
open QuadClock Again Pressure
variable {s t f r v i k:ℕ}
local notation "Λ"=> P.par
local notation "L"=> P.par.R.L
local notation "H"=>P.large
local notation "N" s:max i:max => Journey.side P.run i s
/-! # Buy height and travel together. Keep both actual calibration and rank resolution schedule. -/
open CF.Pannier.Chancel CF.Py.Rate.LocalLimit.Preparation.Yoke
open Worth Pays CF.BProof
open Real (log)
open Aria Casting MacroGrid
local notation "z'" => witnessZ
open Regis.Head.Etch Push.Local AnalyticBridge.VerifiedReset
local notation "Δ" t:max x:max => P.tariffQ z' t x
variable (x : P.Spectrum0 3)
local notation "ξ"=> P.advocate 3 x 3
local notation "M"=> P.ColorHil 3 (ξ)
local notation "G"=> P.ManyF 3 (ξ)
local notation "E" r:max=> P.singleState 3 r x
local notation "Ω"=> P.colorZero 3 ξ
local notation "Γ"=>P.cartage 3 ξ
local notation "Η"=>P.seasons 3 ξ
local notation "κ"=>P.wealth 3 ξ
local notation "Πγ"=>P.enter 3 ξ
local notation "ω"=> P.heaven 3 ξ
local notation "B"=> P.basePlay x f r
local notation "K" f:max r:max=> P.megaK f r
local notation "W'" => P.tallWorth r
local notation "q!" i:max s:max=> P.runP f r i s
local notation "p!" i:max s:max=> P.meshPose r (q! i s)
local notation "O"=> P.charmF
local notation "oQ"=> opposeQ 3
local notation "oR"=> opposeR 3
abbrev strollQ (f r i c:ℕ):= P.thinGridRay x r (P.basePlay x f r) (P.base_birth x f r) (P.runP f r i c)
abbrev strollV (f r i c:ℕ):= P.thinRay x (P.basePlay x f r) (P.base_birth x f r) (P.meshPose r (P.runP f r i c))
abbrev struckW (f r v s:ℕ):= P.issuing r (P.basePlay x f r) (P.runP f r v s)
local notation "H!" i:max b:max=> P.strollQ x f r i b
local notation "Hu" i:max b:max=> P.strollV x f r i b
local notation "C!" i:max b:max=> P.struckW x f r i b
lemma commit_move (X:P.VMark)(z:P.ColorHil 3 (P.advocate 3 x 3)): κ (P.truck 3 ξ X z)= Γ (P.laysM X) (κ z):=by
 apply ext_inner_left ℂ; intro y; rw [←ContinuousLinearMap.adjoint_inner_left κ,P.bank_star,← ContinuousLinearMap.adjoint_inner_left (Γ (P.laysM X)),P.cart_reverses]; let w:= Γ (-(P.laysM X)); let w':=P.truck 3 ξ (-X)
 rw [←ContinuousLinearMap.adjoint_inner_left κ, P.bank_star, ←ContinuousLinearMap.adjoint_inner_left (P.truck 3 ξ X),P.truck_star]; change inner ℂ (w' (Πγ y)) z= _; rw [show w' (Πγ y)= Πγ (w y) from (by unfold w' w; rw [P.cart_and,P.lays_neg])]; rfl
lemma capStroll (i b:ℕ): κ (H! i b)= Hu i b:=by
 unfold strollV strollQ thinRay thinGridRay; rw [P.commit_move]; apply congrArg (Γ (p! i b)); exact P.bankHeat .. -- tune ε
variable (u:P.reached f r)(e:0 < i)(Q':0 < v)
include u e
lemma residentH(b:ℕ) : ∃ t:P.birthF 3 r (C! i b), P.viewF 3 ξ r t = H! i b := P.thin_grid_pose_view x r B (P.base_birth ..) (q! i b) (by rw [P.rent_only]; exact P.bought_as x u i e 3) (by rfl)
include Q'
lemma bracket_eq (b:ℕ) : inner ℂ (H! i b) (H! v 0)= (W':ℂ)^2 * P.pulseQ 3 z' r (P.focusF (K f r) v 0) (P.recoilF (K f r) i b) x:=by
 obtain ⟨y,p⟩:=P.residentH x u e b; obtain ⟨z,q⟩:=P.residentH x u Q' 0; rw [←p,←q,P.released_gram,P.single_agrees]; unfold struckW; rw [← P.issue_reflect, P.straight_price,P.rewind_price]; exact P.lens_price ..
lemma plenum_book (J:P.Ellis 3 x) : inner ℂ (Hu i O) (Hu v 0)= (W':ℂ)^2 * P.pulseQ 3 z' r (P.focusF (K f r) v 0) (P.recoilF (K f r) i O) x:=by
 let L₀:=[false,true]; let A:=usher ((B).kiss P 3) B; let y:= q! i O; let z:= q! v 0; let a:=usher (oQ y) z; let Y:= oR (p! i O); let Z:= p! v 0; let d:= usher Y Z
 have hx:P.gridSpot r ∘ a=d:=by funext i; cases i with|false=>exact P.tile_reflect r y 3|true=>rfl
 have ht:=P.spot_full x A L₀ a J r (fun b _ => by cases b <;> exact le_refl r) ((hx.symm) ▸ (show P.Turnstile 3 _ _ d from P.turn_point x u e Q' _)) ((hx.symm) ▸ (show P.Plenum _ _ d from P.turn_all x u e Q'))
 have hg: P.commonWell 3 x A d L₀=inner ℂ (Hu i O) (Hu v 0):= by
   let c:= (B).realWidth P 3
   have hy:Y 3 + c <0:=by rw [show Y 3= - P.rentTick f r i from Eq.trans (if_pos rfl) (congrArg (Neg.neg) (P.rent_only ..))]; linarith only [show c<P.rentTick f r i from P.bought_as x u i e 3]
   have hb:= P.thin_pair_well_price x B (P.base_birth x f r) B (P.base_birth x f r) Y Z hy ((P.bought_as x u v Q' 3).trans_eq (P.rent_only f r v 0).symm) J; rw [show opposeR 3 Y= p! i O from reflectPose_twice ..] at hb; exact hb
 have he:P.fullScroll r A a L₀= P.issuing r ((B).kiss P 3) (oQ y)*P.issuing r B z :=by change _*(_* (1:P.Test))=_; rw [mul_one]; rfl
 rw [hx,hg,he] at ht; change (E r) (P.issuing r ((B).kiss P 3) (oQ (q! i O))*P.issuing r B (q! v 0))= _ at ht; rw [P.straight_price,P.rewind_price] at ht; exact ht.symm.trans (P.lens_price ..)
-- cost moves after base (orthogonality to stone). holds by gearing analyticity and star projection, proof late.
omit e Q'
include x in
lemma purchase_time : 0≤ P.rentTick f r 1:= ((B).real_width_pos P 3).le.trans (P.bought_as x u 1 zero_lt_one 3).le -- x needed include
include e
lemma rises_by : P.rentTick f r 1 ≤ P.rentTick f r i:=by
 unfold rentTick; rw [P.pose_w,P.pose_w]; apply mul_le_mul_of_nonneg_right _ (P.macroStep_pos _|>.le); apply Int.cast_le.mpr; rw [P.run_here, P.run_here]; have hx: (1:ℤ)≤(i:ℤ):=by omega
 exact mul_le_mul_of_nonneg_right hx ((Int.natCast_nonneg _).trans u.le)
-- horizontal motion
omit u e
def launchTick(P:Spine)(f r k:ℕ):ℝ≥0:= Real.toNNReal (P.rentTick f r k-P.rentTick f r 1)
def launchPad(P:Spine)(r b:ℕ): Vantage:= fun j=> if j=(3:Axis) then 0 else -(b:ℝ) *P.macroStep r
include u e
lemma relative_boot (b:ℕ) : Hu i b= Γ (P.launchPad r b) ((Η).E (P.launchTick f r i) (Hu 1 0)):=by
 let y:= P.thinOrigin x B (P.base_birth x f r); let z:=p! 1 0; let z₁:=p! i b; let Kt:= P.launchPad r b; let A:= P.launchTick f r i; let R:= Η; let Q0:= Γ; let m:=q! 1 0; let v:=q! i b; let U:=P.persistD (K f r)
 have hx(d:Axis)(e:d≠3): z₁ d=(Kt+z) d:=by
   unfold z₁ z; simp only [Pi.add_apply]; rw [P.pose_w,P.pose_w] -- tune
   rw [show Kt d=-(b:ℝ)*P.macroStep r from if_neg e, show (q! i b) d= U-(b:ℤ) from if_neg e,show (q! 1 0) d= U- (↑(0:ℕ):ℤ) from if_neg e]; push_cast only [Int.cast_sub,Int.cast_zero,Nat.cast_zero,Int.cast_natCast]; ring
 have hp: Q0 z₁= Q0 (Kt+z):= by
    unfold Q0 cartage; congr 1; exact funext fun a:Trans 3=> hx a.val a.property
 have hR: (z₁ 3).toNNReal=A+(z 3).toNNReal:=by
    unfold z₁ z; rw [P.rent_only,P.rent_only]; ext; have he:= P.purchase_time x u; have h:=P.rises_by u e; unfold A launchTick; rw [NNReal.coe_add,Real.coe_toNNReal _ (he.trans h),Real.coe_toNNReal _ (sub_nonneg.mpr h),Real.coe_toNNReal _ he]; ring
 change Q0 z₁ (R.E (z₁ 3).toNNReal (κ y))=Q0 Kt (R.E A (Q0 z (R.E _ (κ y)))); rw [hp]; unfold Q0 R; rw [P.cart_paves,P.warm_drive,hR]; nth_rw 1 [(Η).time]; rfl -- unif Q0 def
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.plenum_book
