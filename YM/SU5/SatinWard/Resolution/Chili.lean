import YM.SU5.SatinWard.Resolution.Venue
import YM.SU5.SatinWard.Resolution.NeedleY
import YM.SU5.SatinWard.Resolution.Chorister
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
open Worth Pays BProof Aria Casting MacroGrid Selected OS.Semigroup OS.Semigroup.Marble PSE MarbleFace
open SatinWard.Installment
open Internal
open Dovetail
namespace Polaris
namespace Chili
local notation "Θ" v:max=> moonClock P (corridorHeight P v)
abbrev diagram (j:Axis):ℝ:= if j=2 then -80 else if j=0 then 100 else 80
noncomputable abbrev wallClock (P:Spine)(v:ℕ):skit:= frontage 0 (moonClock P (corridorHeight P v) • diagram)
local notation "VV" v:max=> wallClock P v
noncomputable def dawnV : Gaia :=WithLp.toLp 2 (-diagram)
lemma cogent : dawnV≠0:=by intro h; have p:= congrArg (fun z:Gaia=> z (2:Axis)) h; change -diagram 2=0 at p; unfold diagram at p; split_ifs at p<;> norm_num at *
lemma majors (v:ℕ) : Ordered (wallClock P v) 3 false (60*Θ v) ∧ Breezeway (wallClock P v) (Θ v) 60 120 ∧ loomDay (wallClock P v false-wallClock P v true) (moonClock P (corridorHeight P v))=dawnV:=by
 let k:= Θ v; have ht:0<k:=clockP P _; refine ⟨⟨?_⟩,⟨fun j=>?_⟩,?_⟩; · change 60*k≤ k*diagram 3-0; rw [show diagram 3=80 from rfl]; linarith only [ht]
 · change 60*k ≤ |0-k*diagram j|∧|0-k*diagram j| ≤ 120*k; rw [zero_sub,abs_neg,abs_mul,abs_of_pos ht]; have h:|diagram j|=80∨|diagram j|=100:=by unfold diagram; split_ifs<;> norm_num
   rcases h with h|h<;> rw [h] <;> constructor <;> linarith only [ht]
 ext1 i; change k⁻¹*(0-k*diagram i)= -diagram i; field
lemma chili_rise (v:ℕ): ript (VV v)=(VV v):=by
 funext b i; unfold ript; by_cases t:i=ac2.a
 · subst i; rw [ac2.move_a]; cases b; · change -(0:ℝ)=0; ring
   change -(Θ v* (80:ℝ))= Θ v *(-80); ring
 by_cases t':i=ac2.b
 · subst i; rw [ac2.move_b]; cases b; · change -(0:ℝ)=0; ring
   change -(Θ v*(-80))=Θ v*80; ring
 exact ac2.move_h _ t t'
abbrev depth(p:skit) := |p true 3-p false 3| -- name clashes; change
-- spacer even tighter than standard. local Px values will also use WakePatch.
abbrev canopy(G:ℝ)(p:skit):Prop:= |p true 3-p false 3|+G < p true 0-p false 0
structure Coast (w:ℝ)(p:skit):Prop where
 quest: qualifier w p
 wind : canopy w p
theorem coastal (w:ℝ)(p:skit)(h:Coast w p) : ∀ᶠ z in 𝓝 p, Coast w z:=by
 let v: Continuous (fun p:skit=>|p true 3-p false 3|+w):=by fun_prop
 have k: Continuous (fun p:skit=>p true 0-p false 0):= by fun_prop
 filter_upwards [(isOpen_lt v k).mem_nhds h.wind,qual_open p w h.quest] with z x y using ⟨y,x⟩
lemma lives (v:ℕ): Coast (10* Θ v) (wallClock P v):=by
 let t:= majors P v; let k:= Θ v; have h:0< k:=clockP ..; refine ⟨⟨?_,fun j=>?_⟩,?_⟩; · exact lt_of_lt_of_le (show 2*(10*k)<60*k by linarith only [h]) t.1.gap
 · exact lt_of_lt_of_le (show 2*(10*k)<60*k by linarith only [h]) (t.2.1.shelter j).1
 change |k*80-0|+10*k<k*100-0; rw [abs_of_pos (by linarith only [h] : 0<k*80-0)]; linarith only [h]
variable {Z:ℕ→ℕ} {C H A:ℝ}{η:Type}[Fintype η] {f0:ℕ}
 (K:P.NightCop)(ρ: Piano P f0 C H A η Z) (M:P.par.R.L.val%16=1)(hP:64≤ P.par.R.L.val) {Kn:P.Register}
 {C' b':ℝ}{Wp}{t β:ℕ→ℝ} (T: CouncilGrant P Kn b' C' t Z Wp β) (H':PublicKernel P Z Wp)
local notation "U" x:max=> P.advocate 3 x 3
local notation "Kg" x:max=> pricedPSE P M 3 (U x) rayP ρ
noncomputable abbrev windowχ (v:ℕ):ℝ:=10*moonClock P (corridorHeight P v)
local notation "Φρ" v:max=> ((corridorR P v:ℝ):ℂ)
noncomputable abbrev dialT (β:ℕ→ℝ)(v:ℕ):ℝ:= (tollηw P β v*psScale P ρ v)⁻¹^2*(corridorR P v)^8
local notation "Uρ" v:max=> (dialT P ρ β v)
local notation "Pve" x:max v:max=> Harbor P 3 (U x) (Kg x) (Kg x) (wallClock P v) (windowχ P v)
local notation "Zp" v:max x:max=> pSeason P M 3 (U x) ρ (wallClock P v) false (fun _=>rayPost) (fun _=>rayP) v β (windowχ P v)
lemma viewpay (v:ℕ)(x:P.Spectrum0 3): ((Φρ v)^8* Zp v x)= (↑(Uρ v):ℂ)*(Pve x v):=by
 let s:=windowχ P v; let N:= U x; let u:ℝ:= (tollηw P β v * psScale P ρ v)⁻¹; let F:= pricedPSE P M 3 N rayP ρ; let B:= bankedStar P M 3 N rayP ρ β v; let q':= wallClock P v; have f:Zp v x=Harbor P 3 N B B q' s:=by unfold pSeason Harbor; rw [vistaGap]; rw [←two_mul s]; rfl
 rw [f]; have h:B=(u:ℂ) • F:= by unfold u F B bankedStar; push_cast; try rfl -- might no goal
 rw [h,unitS]; unfold dialT u; push_cast; ring
local notation "A0"=> posix dawnV
include K hP T H'
lemma rank_glow : ∀ᶠ v in atTop, f0 ≤ corridorHeight P v ∧ 0<Uρ v ∧ ∀ x:P.Spectrum0 3,A0/2< (Uρ v)*(Pve x v).re :=by
 obtain ⟨B,h,Bp⟩:=rank_awake P K ρ M hP T H' 120 (by norm_num); let A:=posix dawnV; have hx:0<A:=optic_pos _ cogent
 filter_upwards [Bp,(polish_late P).eventually_gt_atTop (B*2/A)] with v p e
 obtain ⟨hp0,hp,pu,hv,hl,ht,HA⟩:=p; have hk:= (scale_corridor P (v:=v)).1; refine ⟨hp0,by unfold dialT; positivity,fun x=>?_⟩; obtain ⟨o,f,d⟩:=majors P v
 have w:= ((HA x 3 _ f).2 false o (fun _=>rayPost) (fun _=>rayP)).1; rw [Bool.not_false,d] at w
 let y:=(Φρ v)^8* Zp v x; have ht: ‖y - (↑A:ℂ)‖ ≤ B/polishQ P v:= w.amount; have hP:=faderP P v; have hD:A-y.re < A/2:=by
    calc
       _ = ((↑A:ℂ)-y).re:=by simp
       _ ≤ ‖(↑A:ℂ)-y‖:= Complex.re_le_norm _
       _ ≤ B/polishQ P v:= (norm_sub_rev ..).trans_le ht
       _ < A/2 :=by rw [div_lt_iff₀ (by positivity)]; linarith only [(div_lt_iff₀ hx).1 e]
 unfold y at hD; rw [viewpay] at hD; simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at hD; linarith only [hD]
#print axioms rank_glow
end Chili
end Polaris
end Regulator
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
