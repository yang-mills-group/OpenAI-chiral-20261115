import YM.SU5.SatinWard.Resolution.RadiusT
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
open CF.Onyx (moor moor_z)
local notation "Wₗ"=> (↑W₀:ℝ)*τ v
local notation "q◁"=> ℓ (fρ v)
local notation "μ✩"=> R♛ v
local notation "𝔅"=> (↑(Ψ v):ℂ)
local notation "𝓓"=> (↑(μ✩):ℂ)
local notation "𝒦"=> (Ψ v)
local notation "Υ"=> P.charter j x
local notation "Iₐ"=> P.ColorHil j x
local notation "ξ"=> P.physicalEnergy j x
local notation "ω₁"=> P.colorZero j x
local notation "△"=> quietArm (P.colorZero j x)
-- no spatial shifts needed. place positive wall probe at distance32 ℓ, cost exactly.
section venue
noncomputable def markWaitQ (v:ℕ):Cover:=Pi.single j (32*(P.reachLeaf (corridorHeight P v) v (moonSpan P (corridorHeight P v)):ℤ))
local notation "b★"=> markWaitQ P j v
local notation "t₀"=> P.vtile v
local notation "B★"=> (t₀ b★)
lemma wait_distance (i:Axis): P.laysM B★ i=if i=j then 32*q◁ else 0:=by
 change P.tock v (b★ i) =_; by_cases d:i=j; swap; · rw [if_neg d,markWaitQ,Pi.single_eq_of_ne d,P.tock_zero]
 let r:=fρ v; let g:= P.reachLeaf r v (moonSpan P r); have e: P.tock v g=q◁:= (extending_clock P (Nat.sub_le ..)).trans (by rw [P.tock_price]; push_cast; rfl); rw [if_pos d]; unfold markWaitQ; rw [d,Pi.single_eq_same,P.tock_price]; rw [P.tock_price] at e; push_cast at *; rw [←e]; unfold g r reachLeaf; push_cast; ring
noncomputable abbrev lofty (j:Axis): Gaia:= EuclideanSpace.single j (-32)
lemma lofty_norm : ‖lofty j‖=32:=by norm_num [lofty]
noncomputable abbrev lookBehind (v:ℕ)(c:Cover):Cover:= c+ ζ • markWaitQ P j v
local notation "Bq" => lookBehind P j v c
lemma look_d : patchF (c-Bq) μ✩=lofty j:=by
 rw [←geoB]; ext i; unfold lookBehind; rw [geo_pose]; have z:0<q◁:=clockP ..; change (q◁)⁻¹*(geoAt P v c i-(geoAt P v c i+P.laysM B★ i))= _; rw [wait_distance]; by_cases p:i=j<;> simp [p,lofty] <;> field_simp -- i smul goal
-- Address μ=0.
lemma palace (u:8 ≤ μ✩): Addressing c Bq (lofty j) 0 μ✩ 64:= ⟨le_rfl,by linarith, by rw [lofty_norm]; norm_num,by rw [lofty_norm]; norm_num, by rw [look_d, sub_self,norm_zero,zero_div]⟩
lemma chart_null (T₁:P.Test): P.chartAll 0 T₁=T₁:=by suffices u:∀ Lq,P.cruise Lq 0 T₁=T₁ from u Vacancy.ordinate; intro Lq; induction Lq with| nil=>rfl| cons i Lq ih=>rw [P.cruise_step,AlgHom.comp_apply,ih,Pi.zero_apply,P.shifts_zero]; -- semicolon parser
local notation "DX"=> 4*(q◁)
variable (F G:P.Apron) (u0:F.s=v)(u1:G.s=v)(w0:F.realWidth P j≤4*(moonClock P (corridorHeight P v)))(w1:G.realWidth P j≤4*(moonClock P (corridorHeight P v)))
local notation "β₀"=>24*(q◁)
include u0 u1 w0 w1
lemma momentumPlate : let e:=P.singleState j v x; let Q₁:=F.F; let Q₂:=P.chartAll b★ G.F; e (Q₁*Q₂)-e Q₁*e Q₂=seam (ξ) (ω₁) (24*q◁) (P.rawBase j x F DX DX) (P.rawBase j x G DX DX):=by
 intro e q t; let Θ(i:Bool):=if i then G else F; let Z(i:Bool):=if i then b★ else 0; let u:=t₀ ∘ Z
 let D:F.s=v:=u0; let L':= (P.laysM ∘ u); let a:=F.realWidth P j; let b:=G.realWidth P j; have g:L' false j=0:=by change P.tock v _=_; exact P.tock_zero v -- notation .t
 have h:L' true j=32*(q◁):= by change P.laysM B★ j= _; rw [wait_distance,if_pos rfl]
 have ha:P.resignY j Θ L' false=a:= by unfold resignY Apron.time_edge; change L' false j+a=a; rw [g,zero_add]
 have hb:P.porchY j Θ L' true=32*(q◁)-b:= by unfold porchY Apron.time_panel; change L' true j-b=_; rw [h]
 have he:0<q◁:=clockP ..; have hz:P.Turnstile j Θ [false,true] L':= List.pairwise_pair.mpr (by rw [ha,hb]; change a < _; change a ≤ _ at w0; change b ≤ _ at w1; linarith)
 have hv:preMosaic P j x Θ false u=e (q*t)-e q*e t:= by
    rw [reveal_here P j x Θ false Z v hz (fun i=>by cases i; exact u0; exact u1)]; change e ((P.chartAll 0 q)*t)-e (P.chartAll 0 q)*e t= _; rw [chart_null]
 rw [←hv, anchor_pre P j x Θ false _ (24*q◁) (DX-a) (DX-b) (DX-a) (DX-b) (by positivity) (sub_nonneg.mpr w0) (sub_nonneg.mpr w1) (by change DX-a+24*(q◁)+(DX-b)= P.porchY j Θ L' true-P.resignY j Θ L' false; rw [ha,hb]; ring)]
 change seam (ξ) (ω₁) (β₀) ((ξ).sand (Υ (t₀ 0) (F.engine P j x)) _ _) ((ξ).sand (Υ B★ (G.engine P j x)) _ _)=_; rw [tick_s P j x 0 (fun _ _=>rfl), tick_s P j x b★ (by intro i e; unfold markWaitQ; rw [Pi.single_eq_of_ne e])]; rfl
end venue
end Regulator
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
