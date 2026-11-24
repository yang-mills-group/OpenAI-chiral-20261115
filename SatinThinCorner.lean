import SatinThinReflector
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
/- x costs live on axis 3. Use advocate on the same axis for the plane-vector costs - rigorously commute with the color projection. -/
local notation "τ" v:max => P.clockPlate f v (P.baseRoot f)
lemma lent_anchor (f:ℕ) : Plans 3 (P.baseRoot f) f P:= P.seat_plan 3 _ le_rfl -- elabor
lemma tickedH (s:ℕ) : P.struckW x f s 1 0=P.centeredQ x s (τ s):= (P.straight_price x 1 0).trans (congrArg (P.centeredQ x s) (P.focus_clock f s))
abbrev naturalPlate(f s:ℕ): P.naturalVox 3 s:= ⟨P.flume 3 (P.baseRoot f) s (P.lent_anchor f),P.clock_colors (P.clockPlate f s (P.baseRoot f))⟩
lemma plate_born(f r:ℕ): P.birthF 3 r (P.visitOne r (P.clockPlate f r (P.baseRoot f))):= ⟨P.naturalPlate f r, rfl⟩
local notation "P?" f:max s:max=> P.province 3 ξ s (P.naturalPlate f s)
local notation "F?" s:max=> P.visitOne s (τ s)
lemma plateau_enter (s f:ℕ): P? f s=P.viewF 3 ξ s (P.plate_born f s):= Eq.symm (P.holdsF 3 ξ s (P.plate_born f s) _ rfl)
lemma plateau_center (s:ℕ)(u:P.reached f s): P.strollQ x f s 1 0=P? f s - (inner ℂ Ω (P? f s)) • Ω:=by
 obtain ⟨t',g⟩:=P.residentH x u (zero_lt_one) 0; have t:P.birthF 3 s (P.centeredQ x s (τ s)):=by rw [←P.tickedH]; exact t' -- tune dependent g
 let p:= P.plate_born f s; let Z:=F? s; have hZ:=P.view_scalar 3 ξ s p; change inner ℂ Ω (P.viewF 3 ξ s p)= P.singleState 3 s ξ Z at hZ
 rw [P.plateau_enter, hZ, P.single_agrees]; let w:= (E s) Z; let q:= P.faceUnit 3 s -- tune signature
 rw [← g]; refine (P.identical_F 3 ξ s _ t (P.tickedH x s)).trans ?_; exact Eq.trans (P.sixWard_view_sub 3 ξ s p (P.birthScale s w q) t) (congrArg (fun r:M=> P.viewF 3 ξ s p-r) (show _=w • Ω from Eq.trans (P.sixWard_view_scale ξ s w q) (congrArg (w •·) (P.view_one ..))))
private lemma smaller {Z:Hilbert}(w z s₁:Z)(h:‖w‖=1)(a:ℂ): ‖a • (z-inner ℂ w z • w)-(s₁-inner ℂ w s₁ • w)‖ ≤ 2*‖a • z-s₁‖:=by
 let v:= a • z-s₁; have he : a • (z- inner ℂ w z • w)-(s₁- inner ℂ w s₁ • w)= v- inner ℂ w v • w:=by
    unfold v; rw [inner_sub_right,inner_smul_right, sub_smul,smul_sub,smul_smul]; abel
 rw [he]; refine (norm_sub_le ..).trans ?_; rw [norm_smul,h,mul_one]; change _≤ _ *(‖v‖); have hp:= norm_inner_le_norm w v (𝕜:=ℂ); rw [h,one_mul] at hp; linarith only [hp] -- linarith won't h * v use rw
local notation "Ui"=> P.flume 3 (P.baseRoot f)
lemma price_caps (s:ℕ)(y:P.Vox 3 s) : ‖P.stateVox 3 ξ s y‖=‖P.stateVox 3 x s y‖:=by
 let v:= P.stateVox 3 ξ s y; let u:= P.stateVox 3 x s y; have he:inner ℂ v v=inner ℂ u u:=by unfold v u; rw [P.gram_at,P.gram_at,P.single_agrees]
 have hx:= congrArg Complex.re he; change RCLike.re (inner ℂ v v)=RCLike.re (inner ℂ u u) at hx; rw [inner_self_eq_norm_sq,inner_self_eq_norm_sq] at hx; change ‖v‖=‖u‖; nlinarith only [hx,norm_nonneg v,norm_nonneg u]
lemma lens_cost (u:r ≤ v) (hf:f≤r)(s:ℝ) : ‖P.stateVox 3 x v (P.cameo 3 (P.baseRoot f) s hf u (P.lent_anchor f))‖ = zoomM P.par.R.L^(r-f)* ‖(s:ℂ) • (P? f v) - (P? f r)‖:=by
 rw [←P.price_caps]; let S:= P.lent_anchor f; change ‖P.compared_state 3 (P.baseRoot f) S u hf s ξ‖ = _; rw [P.state_moving, norm_smul, Complex.norm_real, Real.norm_of_nonneg (pow_nonneg (zoomM_p L|>.le) _), ← (P.gnsIn 3 ξ).norm_map ((s:ℂ) • (P? f v) - (P? f r)),map_sub,map_smul]; simp_rw [P.coincides]
 -- -- tune defeq
 try rfl
lemma compare_stroll (s:ℝ)(u:r ≤ v) (hf:f≤r)(p:P.reached f r) : zoomM P.par.R.L^(r-f) * ‖(s:ℂ) • P.strollV x f v 1 0 - P.strollV x f r 1 0‖≤ 2*‖P.stateVox 3 x v (P.cameo 3 (P.baseRoot f) s hf u (P.lent_anchor f))‖:=by
 rw [←P.capStroll,←P.capStroll, P.lens_cost x u hf s, ← map_smul κ, ← map_sub κ, P.plateau_center x r p, P.plateau_center x v (P.reach_onward p u)]; rw [mul_left_comm 2]; exact mul_le_mul_of_nonneg_left ((P.bank_cost ..).trans (smaller (Z:=P.ColorHil 3 (P.advocate 3 x 3)) Ω (P? f v) (P? f r) (P.norms_color ..) (s:ℂ))) (pow_nonneg (zoomM_p L|>.le) _)
abbrev invoiceV(P:Spine)(x:P.Spectrum0 3)(f r v:ℕ)(a:ℂ): P.ManyF 3 (P.advocate 3 x 3):= (P.rewardK f r:ℂ) • a • P.strollV x f v 1 0
lemma compare_distance (u:r ≤ v) (hf:f≤r)(t:ℝ)(s:ℝ)(s0:0<s)(θ:0<P.rewardK f r)(p:P.reached f r)(q: ‖P.stateVox 3 x v (P.cameo 3 (P.baseRoot f) t hf u (P.lent_anchor f))‖^2 ≤ (s*slotFee P.par f)^2)(a:0<slotFee P.par f) : dist (P.invoiceV x f r v (t:ℂ)) (P.invoiceV x f r r 1) ≤ 2*s*(P.rewardK f r * slotFee P.par f/ zoomM P.par.R.L^(r-f)):=by
 let Kp:= P.rewardK f r; let Y:= (t:ℂ) • P.strollV x f v 1 0; let X':=P.strollV x f r 1 0; let v':= P.stateVox 3 x v (P.cameo 3 (P.baseRoot f) t hf u (P.lent_anchor f)); let Z':=zoomM P.par.R.L^(r-f); have hf₀:0<Z':=pow_pos (zoomM_p _) _; let D:= slotFee P.par f; have he: Z' * ‖Y-X'‖≤2*‖v'‖:= P.compare_stroll x t u hf p -- shadow
 have ht:‖v'‖≤ s*D:= (sq_le_sq₀ (norm_nonneg _) (mul_nonneg s0.le a.le)|>.mp q)
 unfold invoiceV; rw [dist_eq_norm,one_smul, ← smul_sub,norm_smul,Complex.norm_real,Real.norm_of_nonneg θ.le]; change Kp * ‖Y-X'‖ ≤ 2*s* (Kp *D/Z'); rw [← mul_div_assoc,le_div_iff₀ hf₀]; change 0<Kp at θ; nlinarith only [mul_le_mul_of_nonneg_left ht θ.le, mul_le_mul_of_nonneg_left he θ.le] -- variables Kp let vs unfolding
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.compare_distance
