import YM.SU5.SatinWard.Resolution.Statute
import Velour.Crepe.Aperture
import YM.SU5.SatinWard.Resolution.Belfry
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 700000
set_option maxRecDepth 8000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase
open MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound
open Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker
open scoped ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy
open Tapestry Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open CF.Velvet CF.Pannier.Chancel
open Spine Pitching.Focus QuadClock Ione Vow Swell
open _root_.Zephyr.Chern
universe uΩ


open Papal CF.Papyrus.Franc.SatinForce CF.Pannier.Chancel Checkers

open CF.Papyrus.Franc.Loaves
-- CP3 package. PUBLIC, no topology/order changes
open Moon
open Horizons FoliageP BareProgram Moonlit Moonlit.SwitchC
open _root_.YM.Regis.Head.Brecht _root_.YM.Regis.Circuit _root_.YM.Regis.Circuit.SpringDay
open SlabMark VelourBoard Papal.SkyTax Cygnet VelourWiggle
open YM.Stationary (Gaia)
open SwitchC.Garland SwitchC.Garland.Terrace SwitchC.Garland.Terrace.Juniper
open Abacus CheckerFlag SlopeCharge Maxwell
open scoped RealInnerProductSpace ContDiff
namespace Fame
open BProof Pressure
namespace Regulator

open _root_.YM.Gleam.Luster.Almanac Grade
open Papal.SkyTax
open _root_.YM.Regis.Head
open _root_.YM.Gleam.Luster.Almanac Grade
open _root_.YM.CF.Py.Rate.LocalLimit.Preparation _root_.YM.CF.Py.Rate.LocalLimit.Preparation.Tabletop Shrine Ione.Clock Moto
variable (P:Spine)
local notation "W★"=>P.calibration
local notation "Ω★"=>P.run.meter
open Preparation.Yoke Spine.Gingham Spine.Gingham.Diary
open ShapeLab ResolutionFrame Shrine 
open SatinWard
local notation "R"=> Option Tilted.Ramp
local notation "T"=> P.calibration
local notation "ι₀"=>Wage4
local notation "L"=> P.par.R.L
local notation "K"=> P.run
local notation "V"=> P.large
variable (X:R)
variable {s v g w:ℕ}(p:Cover)(e:Almanac P s w p)(h:s≤g)
local notation "Q" => P.calibration.ℓ
variable {f0:ℕ} {Z:ℕ→ℕ} {η:Type}[Fintype η]{C H A:ℝ}
variable (pZ:Tendsto Z atTop atTop)(W:Calendrical P C H A f0 η Z){Wq:Bool→ Coords Wage4} {Uq:ℕ→ Bool→ Coords Wage4} {F:ℕ→ℕ}(WX:CriticalClock P C H A g f0 η Wq F Z Uq) (b: Bool)
include pZ W WX h
local notation "Yt" => (sprintCost L)
local notation "k▶" i:max => P.engine ((Z ∘F) i)
local notation "j▶" i:max => P.nomadic ((Z ∘ F) i)
omit W WX pZ h
open Worth Pays BProof Aria Casting MacroGrid
-- Width economy Ht. Support all from even boxes standard, also operator. Need L≥4096 to repay unit (via Tint). Can choose > arbitrary. Slack.
noncomputable def plateMeter (D:ℕ):= 10*(D+1)^4
noncomputable abbrev moonSpan (P:Spine)(s:ℕ):= plateMeter (P.thresholdF s)
noncomputable def moonClock (P:Spine)(s:ℕ):ℝ:=(moonSpan P s:ℝ)*P.macroStep s
local notation "Θ"=> P.thresholdF
local notation "B"=> P.par.block.val
local notation "t" i:max=> P.macroStep i
local notation "c" i:max=> moonSpan P i
local notation "𝒙" s:max=>hat P.par.R.L P.par.x s
lemma reachM (s:ℕ) : 0< moonSpan P s:=by unfold moonSpan plateMeter; positivity
lemma clockP (s:ℕ) : 0< moonClock P s:=mul_pos (Nat.cast_pos.mpr (reachM ..)) (P.macroStep_pos _)
lemma forest_rental : Worth.Pays 0 0 8 (fun x:ℝ=> (plateMeter (radiusB x):ℝ)):=by
 have h: Worth.Pays 0 0 2 (fun x=> (↑(radiusB x):ℝ)+1):= Pays.property_plus -- tune
 unfold plateMeter; push_cast; have e:= pot h 4; norm_num at e; exact Pays.scale 10 e
lemma passage_rent (D:ℕ): ∀ᶠ s:ℕ in atTop,P.RentBox s (D*moonSpan P s):=by
 let Y:ℝ:= ↑(2*(P.sidesPerTick*D):ℕ); let x:= times (Pays.scale 14 (show Worth.Pays r_meter 0 0 Worth.meterC from Pays.whole ..)) (pot (Pays.scale Y forest_rental) 4)
 filter_upwards [(turnover P.par).eventually (leap (w:=0) (p:=0) (q:=0) x (Or.inl (by norm_num [r_meter])))] with s tu
 -- `t` notation kills
 rw [coin_zero] at tu; unfold RentBox; rw [moonSpan,show (Θ) s=radiusB (𝒙 s) from (P.run.meter.boot s).2.1,show (2*VelourBoard.pitch P.calibration (D*plateMeter (radiusB (𝒙 s)))) =(2*(P.sidesPerTick*D))*plateMeter (radiusB (𝒙 s)) from by change (2:ℕ)*(P.sidesPerTick*(D*_))=_; ac_rfl, Nat.cast_mul]; exact tu
lemma paceEq : ∀ s:ℕ, 𝒙 (s+1)=𝒙 s+billX L:=by intro s; unfold hat; push_cast; ring
lemma tumbleCY : ∀ᶠ s:ℕ in atTop,moonSpan P (s+1) ≤ 16*moonSpan P s:=by
 filter_upwards [(turnover P.par).eventually (Extra.Iteration.Rebuild.geometry (billX L))] with s st' -- ABI
 have h:(Θ) (s+1)≤2*(Θ) s:=by rw [show (Θ) (s+1)=radiusB (𝒙 (s+1)) from (P.run.meter.boot (s+1)).2.1,show (Θ) s=radiusB (𝒙 s) from (P.run.meter.boot s).2.1,paceEq]; exact st'.1.1
 unfold moonSpan plateMeter; calc
    _ ≤ 10*(2*((Θ) s+1))^4:=by gcongr; omega
    _ =_:=by ring
variable (pL:64 ≤ P.par.R.L.val)
include pL in
lemma slower : ∀ᶠ s:ℕ in atTop,moonClock P (s+1) ≤ (1/2:ℝ)*moonClock P s:=by
 filter_upwards [tumbleCY P] with s st'
 have u:t (s+1) ≥ 0:= (P.macroStep_pos _).le
 have p:((L).val:ℝ)*P.macroStep (s+1)= P.macroStep s:=by simpa using P.daysF (s+1) s (Nat.le_succ s)
 unfold moonClock; rw [←p]; calc
    _ ≤ (16:ℝ)*(moonSpan P s:ℝ)*P.macroStep (s+1):= by gcongr; exact_mod_cast st' -- annotated `16:ℕ` causing HMul
    _ ≤_ := by
         have hv:16 ≤ (1/2:ℝ)*(L).val:=(by have hu1:(64:ℝ) ≤ (P.par.R.L.val:ℝ):=Nat.cast_le.mpr pL; exact by linarith); linarith only [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hv (Nat.cast_nonneg (α:=ℝ) (moonSpan P s))) u]
include pL in
lemma clocksPast : ∀ᶠ N:ℕ in atTop,∀ s:ℕ,N≤ s→∀ k:ℕ, s ≤ k→moonClock P k ≤ ((1/2:ℝ)^(k-s))*moonClock P s:=by
 filter_upwards [eventually_forall_ge_atTop.mpr (slower P pL)] with N st' s h k p; induction p with
 | refl=> rw [Nat.sub_self,pow_zero,one_mul]
 | step w ih => rw [Nat.succ_sub w,pow_succ',mul_assoc]; exact (st' _ (h.trans w)).trans (mul_le_mul_of_nonneg_left ih (by norm_num))
include pL in
lemma clocks_zero : Tendsto (moonClock P) atTop (𝓝 0):=by
 obtain ⟨N,h⟩:=(clocksPast P pL).exists
 let L':= fun k : ℕ=> (moonClock P N)* (1/2:ℝ)^((k-N):ℕ)
 have ht:Tendsto L' atTop (𝓝 0):=by simpa only [L',Function.comp_apply,mul_zero] using ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num : (1/2:ℝ)<1)).comp (show Tendsto (fun k:ℕ=> k-N) atTop atTop from tendsto_atTop.2 fun i=> (eventually_ge_atTop (i+N)).mono fun _ _=>by omega)).const_mul (moonClock P N)
 exact squeeze_zero' (Eventually.of_forall fun k=> (clockP P k).le) ((eventually_ge_atTop N).mono fun i p=> (h N le_rfl _ p).trans_eq (mul_comm ..)) ht
#print axioms clocks_zero
section positions
-- a odd lifts residues. Need L ≡ 1 mod16 (select). ABI.Nonempty example fan.Spectral convention c_h. choose once.
structure ResidualPermit (a:Cover): Prop where
 odd : ∀ i:Axis, Odd (a i)
 cost : ∀ i:Axis,(a i).natAbs < 8
variable (m: P.par.R.L.val % 16 = 1) (a:Cover)
local notation "B₀"=> P.par.block.val
noncomputable abbrev homeTag (P:Spine)(a:Cover):Cover:= (P.par.block.val • a)
lemma sidesTick_eq : P.sidesPerTick= 16*P.par.block.val:= rfl
lemma rulerTicks : ruler P.par.block= P.sidesPerTick:= by unfold ruler; rw [sidesTick_eq]; push_cast; rfl
include m in
lemma roofJuneW (n:ℕ): (↑P.par.R.L.val:ℤ)^n %16=1:=by
 induction n with| zero=> simp| succ n ih=> rw [pow_succ,Int.mul_emod,ih]; have u:(↑(L).val:ℤ)%16=1:=(by exact_mod_cast m); rw [u, one_mul]; decide -- `include m`
include m in
lemma residues_delta (s v:ℕ):∃ p:Cover, (P.par.R.L.val^(v-s)) • homeTag P a=homeTag P a+ P.sidesPerTick • p:=by
 let u:ℤ:=(↑(L).val:ℤ)^(v-s); have he:u%16=1:= roofJuneW P m (v-s)
 let p:=(u/16) • a
 refine ⟨p,?_⟩; funext i; rw [sidesTick_eq]; change (P.par.R.L.val^(v-s):ℕ) • (B₀ • a i)= (B₀ • a i)+(16*B₀:ℕ) • ((u/16) • a i); simp only [nsmul_eq_mul,zsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_mul]; change u*((↑B₀:ℤ)*a i)= _; conv_lhs => lhs; rw [show u=1+16*(u/16) from by omega];
 push_cast; norm_cast; push_cast; ring
include m in
lemma nodeHome (h:ResidualPermit a):∃ p:Cover,nodeC p=homeTag P a:=by
 have h0:Odd P.par.R.L.val:= ⟨(L).val/2,by omega⟩ ; have hh:Odd B₀:=h0.pow
 choose x hx using fun i:Axis=>h.odd i
 obtain ⟨n,h⟩:= hh
 have h: (B₀:ℤ)=2*n+1:= by exact_mod_cast h
 refine ⟨fun i=> n+ (B₀:ℤ)*x i,?_⟩; funext i; change (2:ℕ) • ((n:ℤ)+ (B₀:ℤ)*x i)+1=B₀ • a i; simp only [hx,nsmul_eq_mul, Nat.cast_ofNat]; rw [h]; ring
lemma homeCost (h:ResidualPermit a)(i:Axis): |homeTag P a i| ≤ P.sidesPerTick:=(by
 change |B₀ • (a i)| ≤ _; rw [nsmul_eq_mul,abs_mul,abs_of_nonneg (Int.natCast_nonneg _),sidesTick_eq]; push_cast
 have t':|a i| ≤16:=(by have he:=h.cost i; rw [abs_le]; omega)
 exact (mul_le_mul_of_nonneg_left t' (by positivity)).trans_eq (mul_comm _ _))
abbrev waitZ (P:Spine)(s:ℕ):ℕ:=5*(P.thresholdF s+1)^4
lemma pay_half(s): moonSpan P s= 2 * waitZ P s:= by unfold moonSpan waitZ plateMeter; ring
lemma wait_tends : Tendsto (waitZ P) atTop atTop:= tendsto_atTop.2 fun i=> ((Yoke.waist P.run 0).eventually (eventually_ge_atTop i)).mono fun s h=> by
    let r:=P.thresholdF s; change i≤r at h; change i≤5*(r+1)^4; let e:(r+1:ℕ)≤(r+1)^4:= le_self_pow₀ (by omega) (by norm_num); omega
-- For REAL pose pricing: ∃ y root each s at exactly mid tick & all dimensions. Lift of same through pole & h correspond.Fixed residue. proof all late seats (apure). housing growth L free; `v-f` always *.Jinu. Earn with arbitrary time margin for explicit pad normalization.
structure ShowField (s:ℕ)(o p:Cover) : Prop where
 reach : nodeC p=o+ P.sidesPerTick • (fun _=> (waitZ P s:ℤ))
 cost : Almanac P s (moonSpan P s) p
-- just geometry
lemma rises_june : ∀ᶠ s:ℕ in atTop,(petalD:ℕ)+P.calibration.ℓ+P.sidesPerTick+rural (P.thresholdF s)+1 ≤ waitZ P s:=by
 filter_upwards [ (Yoke.waist P.run 0).eventually (eventually_ge_atTop (petalD+P.calibration.ℓ+P.sidesPerTick))] with s h; let r:= P.thresholdF s; change _≤ r at h; change _+_+_+ (r^3+r^3+r+r)+_ ≤5*(r+1)^4; refine le_trans (Nat.add_le_add_right (Nat.add_le_add_right h _) _) (?_ : r+(r^3+r^3+r+r)+1≤ _); have tA:r≤ (r+1)^4:=Nat.le_trans (by omega:r≤ r+1) (le_self_pow₀ (by omega) (by norm_num)); have tB:r^3≤ (r+1)^4:=(pow_le_pow_left' (by omega:r≤r+1) 3).trans (pow_le_pow_right₀ (by omega:1≤r+1) (by norm_num)); nlinarith [Nat.zero_le (r^3), Nat.zero_le (r^4)];
include m in
lemma zenith : ∀ᶠ s:ℕ in atTop,∀ a:Cover,ResidualPermit a→ ∃ p:Cover, ShowField P s (homeTag P a) p:=by
 filter_upwards [ passage_rent P 1,rises_june P] with s h h' a q; obtain ⟨p,u⟩:=nodeHome P m a q
 let p':Cover:= p+fun _=>8*(B₀:ℤ)*waitZ P s; let r:= P.sidesPerTick; let W':= waitZ P s; have ht: nodeC p'=homeTag P a + P.sidesPerTick • (fun _=> (waitZ P s:ℤ)):=by rw [←u,sidesTick_eq]; funext i; change (2:ℕ) • (p i+8*(B₀:ℤ)*waitZ P s)+1= 2 • p i+1+(16*B₀:ℕ) • (waitZ P s:ℤ); simp only [nsmul_eq_mul, Nat.cast_ofNat,Nat.cast_mul]; ring
 have hs:1≤(P.sidesPerTick:ℤ):= (by exact_mod_cast P.sides_pos) -- x pos not ≥1
 have hC: (W':ℤ)≤ P.sidesPerTick*(W':ℤ):=le_mul_of_one_le_left (by positivity) hs
 let d:=(↑r* (↑W':ℤ)); have hC1: ruler P.par.block*(moonSpan P s:ℕ)=2*d:=by
    unfold d r; rw [pay_half,rulerTicks]; conv_lhs => rhs; rw [Nat.cast_mul,Nat.cast_ofNat]
    unfold W'; ac_rfl
 let x:=homeTag P a; have hd(j:Axis):nodeC p' j=x j+d:=by rw [ht]; change _+r • (W':ℤ) = _; rw [nsmul_eq_mul]
 have hV(j:Axis): -(P.sidesPerTick:ℤ)+d ≤ nodeC p' j ∧ nodeC p' j≤ (P.sidesPerTick:ℤ)+d:=by rw [hd]; constructor<;> linarith only [(abs_le.mp (show |x j|≤(P.sidesPerTick:ℤ) from homeCost P a q j)).1,(abs_le.mp (show |x j|≤(↑P.sidesPerTick:ℤ) from homeCost P a q j)).2] -- r transparency
 rw [one_mul] at h; change _≤W' at h'; change (W':ℤ) ≤ d at hC
 refine ⟨p',ht, reachM P s,h,fun i=>?_, fun i=>?_,fun i=>?_⟩
 · unfold VelourBoard.Wall; simp only [Pi.zero_apply,mul_zero,zero_add,mul_one]; change _∧_≤ ruler P.par.block*(moonSpan P s:ℕ); rw [hC1]; specialize hV i; omega
 · specialize hV i; omega
 rw [hC1]; specialize hV i; omega
end positions
#print axioms zenith
end Regulator
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
