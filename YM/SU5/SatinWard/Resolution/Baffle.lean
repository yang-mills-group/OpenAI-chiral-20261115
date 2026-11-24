import YM.SU5.SatinWard.Resolution.ScaleW
import YM.SU5.SatinWard.Resolution.Basin
import YM.SU5.SatinWard.Resolution.Discus
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
local notation "V"=> P.large
variable (X:R)
variable {s v g w:ℕ}(p:Cover)(e:Almanac P s w p)(h:s≤g)
variable {f0:ℕ} {Z:ℕ→ℕ} {η:Type}[Fintype η]{C H A:ℝ}
variable (pZ:Tendsto Z atTop atTop)(W:Calendrical P C H A f0 η Z){Wq:Bool→ Coords Wage4} {Uq:ℕ→ Bool→ Coords Wage4} {F:ℕ→ℕ}(WX:CriticalClock P C H A g f0 η Wq F Z Uq) (b: Bool)
include pZ W WX h
local notation "Yt" => (sprintCost L)
local notation "k▶" i:max => P.engine ((Z ∘F) i)
local notation "j▶" i:max => P.nomadic ((Z ∘ F) i)
omit W WX pZ h
open Worth Pays BProof Aria Casting MacroGrid
open Selected
local notation "ζ"=>P.sidesPerTick
-- Annotated center. translate with the REAL home clock (not simplified half). Pose Hc later.
variable (M:P.par.R.L.val %16 =1) (k:P.NightCop) (j:Axis)(x:P.Spectrum0 j)
variable {a: Cover} (qa:ResidualPermit a) (y:Coords Wage4) (q:payable P v 2) {u d:ℝ}
variable (f:ℕ)(g₀:f ≤ v)
local notation "τ" i:max=> P.macroStep i
local notation "W₀" => choirWidth P
variable (ρ:Piano P f0 C H A η Z)
variable {C' d' μ Q:ℝ} {t' β Wp} {R':P.Register} (T₁:CouncilGrant P R' d' C' t' Z Wp β) (H': PublicKernel P Z Wp)
local notation "Ψ" i:max=> tollηw P β i
local notation "ℓ" i:max=> moonClock P i
local notation "fρ" i:max=> corridorHeight P i
local notation "R♛" i:max=> corridorR P i
local notation "M♛" i:max=> (R♛ i:ℝ)
local notation "ζ₁" i:max=> (↑(Ψ i):ℂ)
open OS.Semigroup OS.Semigroup.Marble PSE MarbleFace
variable (c:Cover) (t:P.Apron)
-- pre-cost any minted clover sales of fixed height and budget. annotations where needed.
structure Stamped (v:ℕ)(q:payable P v 2) (c: Cover) (D:P.Apron):Prop where
 origin : D.s=v
 ink : D.F=τEnd P v c pseV q
 fare :∀ i:Axis, D.u i= choirWidth P ∧ |c i| ≤ P.sidesPerTick
lemma Stamped.kissed (s:Stamped P v q c t) : Stamped P v q ((plane j 0).motion c) (t.kiss P j):=by
 refine ⟨s.1, ?_,fun i=> ⟨(s.fare i).1,?_⟩⟩
 · change P.reflectTest j t.F = _; rw [s.ink,temple_reflect]
 by_cases h:j=i <;> simpa only [fling_move,h,↓reduceIte,mul_zero,add_zero,abs_neg] using (s.fare i).2 -- `h=j=i` rw j in result? ok
lemma minted (q:payable P v 2): Stamped P v q (homeTag P a) (soloV P v q a qa pseV):= ⟨rfl,rfl,fun i=> ⟨rfl,homeCost P a qa i⟩⟩ -- homeCost P a qa i
lemma stamp_width (s:Stamped P v q c t) : t.realWidth P j= (choirWidth P:ℝ)*P.macroStep v:=by unfold Apron.realWidth MeshClock.bell; rw [(s.fare _).1,s.origin,Int.cast_natCast]; rfl
variable (m:Cover)(T₂:Stamped P v q c t)
local notation "p₀"=> c+ ζ • m
include T₂ T₁
lemma minute : P.chartAll m t.F=(ζ₁ v) • aptLabel P β 1 1 v (c+ζ • m) q:=by
 rw [T₂.ink,temple_sweep]; apply Subtype.ext; change bumper P v p₀ (multiplier pseV)= _; rw [mpse]; exact bump_scaled (a:=1) (b':=1) P v _ q β (beta_quarter P T₁).1 -- mpse form
omit T₂ T₁
variable {β₁:ℕ→ℝ}
structure WickBank (P:Spine)(β:ℕ→ℝ)(v:ℕ)(U μ Q:ℝ): Prop where
 positive : 0≤ U
 rank :∀ (q:payable P v 2)(x y:Cover)(d:Gaia), Addressing x y d μ (corridorR P v) Q→
    ∀ (j:Axis)(t:P.Spectrum0 j), let S:= P.singleState j v t; let A:= aptLabel P β 1 1 v x q; let B:= aptLabel P β 1 1 v y q;
            Disp (corridorR P v) U ((↑(corridorR P v):ℂ)^8*(S (A*B)-S A * S B)) (optic d)
structure StockedR (P:Spine)(f v₀:ℕ)(μ:ℝ)(η:Type)[Fintype η](Z:ℕ→ℕ)(C H A:ℝ)(β:ℕ→ℝ): Prop where
 money : f ≤ corridorHeight P v₀ ∧ corridorHeight P v₀ < v₀
 magnify : μ+8 ≤ corridorR P v₀ ∧ 1 ≤ corridorR P v₀ ∧ polishQ P v₀ ≤ corridorR P v₀
 credit : 4*ageBudget P η A C H (corridorHeight P v₀)*2*((sprintCost P.par.R.L)^(v₀-corridorHeight P v₀))⁻¹*((tollηw P β v₀))⁻¹*(corridorR P v₀)^4*(polishQ P v₀) ≤ 1
variable (pLoan:64≤P.par.R.L.val)
include k T₁ H' ρ pLoan
lemma bank_e (Q μ:ℝ)(u:0≤Q)(h:0≤μ) : ∃ U:ℝ,0≤U ∧∀ᶠ v:ℕ in atTop, StockedR P f0 v μ η Z C H A β ∧ WickBank P β v U μ Q:=by
 obtain ⟨n,w⟩:= polish_Rscope P pLoan; obtain ⟨U,F,t⟩:= telescope T₁ H' (Q:=Q) (μ:=μ) (n:=n) 1 1 1 1 u h k; refine ⟨U,F,?_⟩
 filter_upwards [t,w, (polish_late P).eventually_ge_atTop (μ+8), stamp_credit P ρ T₁,(cue_infinite P).eventually_ge_atTop f0,f_still P] with v gt z hz y e w; have he:μ+8 ≤ R♛ v:=hz.trans z.1; exact ⟨ ⟨⟨e,w.1⟩,⟨he,by linarith,z.1⟩,y⟩,⟨F,fun q x y d t=> (gt.2 q x y _ d z.2 t).2⟩⟩
omit k H' ρ pLoan
-- select axis. Mesh poses t_i. Y at centre (D.c_i). move Mint to any cover.Vacuum. pays raw regardless plenum
local notation "p⦇" i:max => (Q:ℝ) -- Q notation dangerous forgot local Q = ℓ in header! remove Q notation. quote syntax
variable {U:ℝ}(pw: WickBank P β v U μ Q)
local notation "ξ"=> P.physicalEnergy j x
local notation "ν"=> P.seasons j x
local notation "Ω"=> P.heaven j x
local notation "ω"=> P.colorZero j x
variable (b:Bool)(N:Bool→P.Apron)(O u:Bool→ Cover)(Bt:∀ i,Stamped P v q (O i) (N i))
local notation "l"=> [b, !b]
local notation "d'" v:max=> N v
local notation "U₀"=> P.vtile v ∘ u
local notation "u₀" i:max=> O i+P.sidesPerTick • u i
local notation "Z₀"=> (ζ₁ v)
include pw Bt ρ
#check minute
lemma bank_use (hρ:f0 ≤ v) (d:Gaia)(s:Addressing (u₀ b) (u₀ (!b)) d μ (R♛ v) Q) (w:P.Turnstile j N [b,!b] (P.laysM ∘ U₀)): Disp (R♛ v) U ((↑(R♛ v):ℂ)^8*((Z₀)^2)⁻¹*preMosaic P j x N b U₀) (optic d):=by
 let A:= aptLabel P β 1 1 v (u₀ b) q; let B:= aptLabel P β 1 1 v (u₀ (!b)) q; let e:P.Test→ ℂ:= P.singleState j v x; let G:= e (A*B)-e A*e B
 have g:0< β v:=(beta_quarter P T₁).1; -- ALSO need toll nonzero p! include Stocked.
 have h:preMosaic P j x N b (U₀)= (Z₀)^2 * G:=by
    rw [reveal_here P j x N b u v w (fun i=>(Bt i).1)]
    dsimp only; rw [minute P q T₁ _ _ _ (Bt b), minute P q T₁ _ _ _ (Bt (!b)), smul_mul_assoc,mul_smul_comm,map_smul,map_smul]; simp only [map_smul, smul_eq_mul]; unfold G e A B; ring
 have he:Z₀≠0:=Complex.ofReal_ne_zero.mpr (tollηw_p P ρ T₁ hρ).ne'; rw [h,mul_assoc ((corridorR P v:ℂ)^8), inv_mul_cancel_left₀ (pow_ne_zero 2 he)]; exact pw.rank q _ _ _ s j x
end Regulator
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
