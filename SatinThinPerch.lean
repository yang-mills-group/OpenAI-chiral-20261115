import SatinThinCorner
import SatinThinSeven
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
open Regis.Circuit SatinJets
local notation "r!" f:max r:max=> ((P.rewardK f r):ℝ)
local notation "Cσ"=> Yoke.canonWeight
local notation "H!" i:max b:max=> P.strollQ x f r i b
local notation "Hu" i:max b:max=> P.strollV x f r i b
def dBase (s:ℕ):ℝ:= (Aster P.run P.period P.cutoff s)^4 * canonWeight
abbrev min7 : ℝ := canonWeight /16
abbrev max7 : ℝ:=16*canonWeight
lemma dBase_interval(r:ℕ): min7 ≤ P.dBase r ∧ P.dBase r≤ max7:=by
 let s:=Aster P.run P.period P.cutoff r; obtain ⟨⟨h,t⟩,_⟩:= astral P.run P.period P.cutoff r; have hf:1/2≤ s:=h; have hx:s ≤2:=t; have hp:0 ≤ s:= le_trans (by norm_num) h; unfold min7 max7 dBase; change _ ≤ s^4*_ ∧ _; constructor
 · have ht:= mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (show 0≤(1/2:ℝ) by norm_num) hf 4) focus_positive.le; linarith only [ht]
 · have ht:= mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hp hx 4) focus_positive.le; change s^4*_≤_; linarith only [ht]
private lemma reward_funding (p:0<P.tallWorth r){t₀ Z:ℂ}(u:t₀=(W':ℂ)^2*Z) (c:ℝ): (c:ℂ)^8* (r! f r:ℂ)^2*t₀=((c*(P.megaK f r):ℝ):ℂ)^8 * Z:=by
 let x:ℝ:=P.tallWorth r; have hp: (x:ℂ)≠0:=Complex.ofReal_ne_zero.mpr p.ne'; rw [u]; let b:ℝ:=P.megaK f r; change _*(↑(b^4/x):ℂ)^2*((x:ℂ)^2*Z)=(↑(c*b):ℂ)^8*Z; rw [Complex.ofReal_div,Complex.ofReal_pow,Complex.ofReal_mul]; field_simp
lemma wager_value(s:ℕ) : P.wagerQ z' s (YM.basis 3)=(P.dBase s:ℂ):= by unfold wagerQ; rw [focusEst]; unfold dBase; push_cast; rfl
-- transformer from ellis to normalized Gram. 
abbrev actor7 (P:Spine)(x:P.Spectrum0 3)(f r:ℕ)(i:SatinJets.Seven)(b:ℕ):P.ManyF 3 (P.advocate 3 x 3) := (P.rewardK f r:ℂ) • P.strollV x f r (SatinJets.stride i) b
lemma stride_p (t:SatinJets.Seven):0 < SatinJets.stride t:= pow_pos (by decide) _
lemma glare_seven (s t:SatinJets.Seven)(J:P.Ellis 3 x)(p: P.reached f r)(h:0<P.tallWorth r) : P.glareF f r (SatinJets.stride t) (SatinJets.stride s) P.charmF x= ‖(SatinJets.bill7 s t:ℂ)*inner ℂ (P.actor7 x f r s P.charmF) (P.actor7 x f r t 0)-(P.dBase r:ℂ)‖:=by
 let i:=SatinJets.stride t; let v:= SatinJets.stride s; let b:= P.rewardK f r; let ζ:= inner ℂ (Hu v O) (Hu i 0); let c:=(P.focusF (K f r) i 0); let w:=P.recoilF (K f r) v O; let Q':= P.pulseQ 3 z' r c w x; let c':ℝ:= ↑(i+v); have he:= P.reward_funding (f:=f) (t₀:=ζ) (Z:=Q') h (P.plenum_book x p (stride_p s) (stride_p t) J) c' -- names K overshadow!
 have hv: (bill7 s t:ℂ)=(c':ℂ)^8:=by unfold c' i v; rw [show bill7 s t=((SatinJets.stride t:ℝ)+ SatinJets.stride s)^8 from congrArg (fun z:ℝ=> z^8) (add_comm (SatinJets.leader s) (SatinJets.leader t)),Nat.cast_add,Complex.ofReal_pow]
 unfold glareF mistake; rw [P.wager_value,actor7,actor7,hv,inner_smul_left,inner_smul_right,Complex.conj_ofReal]; change ‖_*Q'-_‖=‖(c':ℂ)^8*((b:ℂ)*((b:ℂ)*ζ))-_‖; rw [show (b:ℂ)*((b:ℂ)*ζ)=(b:ℂ)^2*ζ from (by ring),←mul_assoc,he] -- tune `he` b unfolded ∴rw
lemma unprojected_invoice (h:P.reached f r)(p:0<P.tallWorth r) : P.glareF f r 1 1 0 x= ‖(2:ℂ)^8* (↑(‖(r! f r:ℂ) • (H! 1 0)‖^2):ℂ)-(P.dBase r:ℂ)‖:=by
 let Y':= H! 1 0; let U:= P.rewardK f r; let Z:= P.pulseQ 3 z' r (P.focusF (K f r) 1 0) (P.recoilF (K f r) 1 0) x; have he:= P.reward_funding (f:=f) (Z:=Z) p (P.bracket_eq x h zero_lt_one zero_lt_one 0) (2:ℝ)
 have hu:inner ℂ ((U:ℂ) •Y') ((U:ℂ) •Y')=(U:ℂ)^2* inner ℂ Y' Y':=by rw [inner_smul_right,inner_smul_left,Complex.conj_ofReal]; ring
 unfold glareF mistake; rw [P.wager_value]; rw [show ((↑(‖(r! f r:ℂ) • (H! 1 0)‖^2)):ℂ)= (U:ℂ)^2* inner ℂ Y' Y' from (by rw [←hu,Complex.ofReal_pow,inner_self_eq_norm_sq_to_K]; rfl),← mul_assoc]; -- fold he pattern
 push_cast only [Complex.ofReal_ofNat] at he; exact congrArg (fun w:ℂ=> ‖w-(P.dBase r:ℂ)‖) (he.symm) -- cast `(1+1)` simp needed
lemma base_weight (u:P.reached f r)(p:0<P.tallWorth r) (h:P.glareF f r 1 1 0 x ≤ min7/4) : ‖P.invoiceV x f r r 1‖≤ max7+min7+1:=by
 let y:= (r! f r:ℂ) • (H! 1 0); rw [P.unprojected_invoice x u p] at h; have he:(‖y‖ :ℝ)^2≤ (max7+min7+1)^2:=by
    have hc:=Complex.re_le_norm _|>.trans h; rw [show (2:ℂ)^8=256 from by norm_num,←Complex.ofReal_ofNat (n:=256), ←Complex.ofReal_mul,←Complex.ofReal_sub,Complex.ofReal_re] at hc; change _*(‖y‖^2)-P.dBase r ≤ _ at hc; have ht:0 < min7:= div_pos focus_positive (by norm_num); have hz:= P.dBase_interval r; have hq:0 < max7:=ht.trans_le (hz.1.trans hz.2); nlinarith only [ht,hq,sq_nonneg ‖y‖, hc,hz.2];
 unfold invoiceV; rw [one_smul,←P.capStroll,← map_smul κ]; exact (P.bank_cost ..).trans ((sq_le_sq₀ (norm_nonneg y) (show 0≤ max7+min7+1 from (by unfold max7 min7; linarith only [focus_positive]))).mp he)
abbrev epochW(P:Spine)(x:P.Spectrum0 3)(f r:ℕ)(a:SatinJets.Seven) := (P.seasons 3 (P.advocate 3 x 3)).E (P.launchTick f r (SatinJets.stride a))
local notation "RΔ"=> P.invoiceV x f r r 1
lemma together_epoch (u:P.reached f r)(a:SatinJets.Seven)(b:ℕ): Γ (P.launchPad r b) ((P.epochW x f r a) RΔ)=P.actor7 x f r a b:=by
 unfold actor7; rw [P.relative_boot x u (stride_p a),invoiceV,one_smul,map_smul,map_smul]
lemma together_pos (u:P.reached f r)(a:SatinJets.Seven): (P.epochW x f r a) RΔ=P.actor7 x f r a 0:=by
 have ht:=P.together_epoch x u a 0; rw [show P.launchPad r 0=0 from (by ext; simp [launchPad]), P.cart_zero] at ht; exact ht
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.glare_seven
