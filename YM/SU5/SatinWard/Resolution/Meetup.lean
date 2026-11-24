import YM.SU5.SatinWard.Resolution.Stoop
import YM.SU5.SatinWard.Resolution.Rhombus
import YM.SU5.SatinWard.Resolution.TunicW
import YM.SU5.SatinWard.Resolution.Journal
import YM.SU5.SatinWard.Resolution.Waive
import YM.SU5.SatinWard.Resolution.Belfry
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 75000
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
namespace Internal
open Preparation.Tabletop Harmonic CasaF Signboard Ceremo LitCurrent LitCurrent.Chamber
local notation "Y"=> P.run
local notation "L★"=> P.par.R.L
local notation "B$"=> P.calibration
variable {v j f0 s w:ℕ}(p x:Cover)(wp:nodeC x=P.clockPlate s v p){a b A c φ H:ℝ}{F T: Family P.calibration}{S S': Finset Cover}
local notation "U$"=> pavilion (P.clockPlate s v p) (rentWidth P j v)
variable {G R:ℕ→Family P.calibration}{D:ℕ→ℕ}(q:Tendsto D atTop atTop)(e:BQueue S G F)(e':BQueue S' R T)
local notation "ι₀"=> Wage3
local notation "iv" i:max=> P.nomadic (D i)
local notation "kv" i:max=> P.engine (D i)
local notation "Mp" i:max=> side P.run (P.nomadic (D i)) v
variable (hb:Almanac P s w p) (hz: Closeted P j p s v w) (pc:S ⊆ pavilion (P.clockPlate s v p) (rentWidth P j v)) (pc':S' ⊆ pavilion (P.clockPlate s v p) (rentWidth P j v)) (k:P.NightCop) (i:Axis)
local notation "κ"=> sprintCost P.par.R.L
variable (h:s<v) (f:f0 ≤ s) (Hc:1≤H)(Ac:1≤A) (fA:0<a)
local notation "εμ"=> Wage4
local notation "j⊗"=> yardF (spinFrame 3)
local notation "v!"=> hourBound P.run v
variable (η:Type)[Fintype η]
variable {Z:Visit → Cover→ Family P.calibration}{M: PitchZ} {d:Division}(L:Ceremo P η v j f0 a b φ H A d D Z M)
local notation "O⋆" => fullStar P.par v j Z
local notation "ΨH" s:max=>pinpr P.par.R.L (hat P.par.R.L P.par.x s)
open Selected Reconstruction.Atlas CasaF
variable (D₀:Cover) (M0:P.par.R.L.val %16=1) (qa:ResidualPermit D₀)(x₀:P.Spectrum0 i)
variable (uv:StretchClock P j s v D₀ p)
variable (B:P.Apron)(X:P.Card i v (P.reachLeaf s v (moonSpan P s)))(pX:P.voxTest i v X.val∈enclave P.calibration)
variable {H_:Cover→ Family P.calibration} (vH: Domicile w H_)(qh: w ≤ rentWidth P j v)
variable {u₁ v₁:ℝ} (p₁:moonClock P s≤u₁) (p₂:moonClock P s≤v₁) {v0:ℕ}(hp:v0 ≤ v)(u:payable P v 2)
local notation "s$"=> moonSpan P s
local notation "Y$"=> P.reachLeaf s v (moonSpan P s)
local notation "W$"=> uv.located.cost
local notation "hⓐ" i:max=>home P D₀ i
-- combine and state orientation independent prices.
-- stage prices preserve path
lemma priceStar {w:ℕ}(t_v:Domicile w H_) : P.locate i x₀ (-home P D₀ v0) (P.reprise i x₀ (frontPrice P i D₀ M0 qa x₀ hp t_v u₁ v₁))= annoFace P i x₀ v (home P D₀ v) (cloakF P M0 qa t_v v) u₁ v₁:=by unfold frontPrice lined; rw [P.reprise_charter,P.locate_sum,P.reprise_rawBase,seated,show -(home P D₀ v0)+(home P D₀ v0-home P D₀ v)= -home P D₀ v from by abel]; rfl
lemma priceSolo (y:Coords Wage4): P.locate i x₀ (-home P D₀ v0) (P.reprise i x₀ (rawSolo P M0 i x₀ qa y u v0 hp u₁ v₁))= annoFace P i x₀ v (home P D₀ v) (soloV P v u D₀ qa y) u₁ v₁:=by rw [rawTicket, P.reprise_charter, P.locate_sum,P.reprise_rawBase,seated,show -(home P D₀ v0)+(home P D₀ v0-home P D₀ v)= -home P D₀ v from by abel]; rfl
variable (hv:0<lapQ P.run s)(ht:0<lapQ P.run v)
local notation "α₀"=>annoFace P i x₀ v (home P D₀ v)
structure Spirit (i:Axis)(x:P.Spectrum0 i)(p:Cover)(Q V:P.Apron)(z:ℂ)(v s:ℕ)(H:ℝ)(M:P.par.R.L.val%16=1) :Prop where
  raw : ∀ (f:ℕ)(k:f≤v)(u r:ℝ), moonClock P s ≤ u→ moonClock P s≤ r→ ‖lined P M i x f p k Q u r-z • lined P M i x f p k V u r‖ ≤ H
  price :∀ u r:ℝ,moonClock P s ≤ u→ moonClock P s≤ r→ ‖annoFace P i x v (home P p v) Q u r-z • annoFace P i x v (home P p v) V u r‖≤ H
lemma encodeFront (t:P.Apron) (u v':ℝ)(q:t.s=v): P.locate i x₀ (-home P D₀ v0) (P.reprise i x₀ (lined P M0 i x₀ v0 D₀ hp t u v'))= annoFace P i x₀ v (home P D₀ v) t u v':=by unfold lined; rw [P.reprise_charter,P.locate_sum,P.reprise_rawBase,seated,q,show -(home P D₀ v0)+(home P D₀ v0-home P D₀ v)= -home P D₀ v from by abel]; rfl
lemma spirit (Q V:P.Apron)(z:ℂ)(ht:Q.s=v)(hv:V.s=v) (hu: ∀ (f:ℕ)(k:f≤v)(u r:ℝ), moonClock P s ≤ u→ moonClock P s≤ r→ ‖lined P M0 i x₀ f D₀ k Q u r-z • lined P M0 i x₀ f D₀ k V u r‖ ≤ H): Spirit P i x₀ D₀ Q V z v s H M0:=by
 refine ⟨hu,fun a b ha hc=>?_⟩; rw [←encodeFront P i D₀ M0 x₀ (Nat.zero_le _) Q _ _ ht, ←encodeFront P i D₀ M0 x₀ (Nat.zero_le _) V _ _ hv,← P.locate_smul,← P.locate_sub,P.locate_cost, ← P.reprise_smul,← P.reprise_sub]; exact (P.reprise_pay ..).trans (hu _ _ _ _ ha hc)
noncomputable abbrev JpriceApp (y:Coords Wage3)(i:Axis)(v:ℕ):P.Apron:= cloakF P M0 qa (Signboard.letterShape (J:=P.calibration) (Λ:=P.par) i v y) v
structure Monitored (P:Spine)(η:Type)[Fintype η](v j f0:ℕ){a b φ H A:ℝ}{d:Division} (M0:P.par.R.L.val%16=1) {D:ℕ→ℕ}{Z: Visit→ Cover→ Family P.calibration}{M:PitchZ}(L:Ceremo P η v j f0 a b φ H A d D Z M):Prop where
  current (s:ℕ)(i:Axis)(x:P.Spectrum0 i) : f0 ≤ s → s<v → ∀ D₀:Cover,∀ qa:ResidualPermit D₀,∀ u:payable P v 2,
   let V(t:Visit):= cloakF P M0 qa (L.earnedZ P η t) v
   let T:= cloakF P M0 qa (logStarCore P η L) v
   let X:= soloV P v u D₀ qa pseV
   Spirit P i x D₀ (V none) X (↑(gatherG M.1):ℂ) v s (wageMonth P η A H s v) M0 ∧ Spirit P i x D₀ T X (↑(gatherG M.2.1):ℂ) v s (wageMonth P η A H s v) M0 ∧ ∀ j: Axis, Spirit P i x D₀ (V (some j)) (JpriceApp P D₀ M0 qa M.2.2 j v) 1 v s (pulseMonth P η A H s v) M0
-- available. Zoe zero not needed.
variable (crew: ∀ s:ℕ,f0 ≤ s→ ∀ v,s≤v→∀ D₀:Cover,ResidualPermit D₀→ ∃ p:Cover, StretchClock P j s v D₀ p)(xp:∀ s:ℕ,f0≤ s→ 0<lapQ P.run s)
include xp k crew q Ac Hc
set_option maxHeartbeats 250000 in
lemma monitor : Monitored P η v j f0 M0 L:=by
 constructor; intro s i x f h D₀ qa u; obtain ⟨p,uv⟩:=crew s f v h.le _ qa; obtain ⟨y,z⟩:=placement_m P M0 s v p
 let V':= soloV P v u D₀ qa pseV; let w':= wageMonth P η A H s v; let ht0:= xp s f; let hs:= xp v (f.trans h.le)
 let Pq:= logStarCore P η L; let φ(t:Visit):= cloakF P M0 qa (L.earnedZ P η t) v
 refine ⟨spirit P i D₀ M0 x (φ none) V' _ rfl rfl (fun i t _ _ p₁ p₂=>?_), spirit P i D₀ M0 x _ V' _ rfl rfl (fun i t _ _ p₁ p₂=>?_),fun kμ=>?_⟩ -- i shadow; fix
 · exact frontQ P p y z q k _ h f Hc Ac η L D₀ M0 qa x uv p₁ p₂ t u ht0 -- Γ order check
 · exact frontStar P p y z q k _ h f Hc Ac η L D₀ M0 qa x uv p₁ p₂ t u ht0 hs
 let T':=letterShape (J:=P.calibration) (Λ:=P.par) kμ v M.2.2; let D:= pulseMonth P η A H s v; refine spirit P _ D₀ M0 x (φ (some kμ)) (cloakF P M0 qa T' v) _ rfl rfl ?_; intro v' h' u' d' p₁ p₂; rw [one_smul]; exact frontJ P p y z q k _ h f Hc Ac η L D₀ M0 qa x uv p₁ p₂ h' ht0 kμ -- might `≤s` token
#print axioms monitor
omit xp k crew q Ac Hc
lemma oriented_staff (j:ℕ)(pL:64 ≤ P.par.R.L.val)(b:P.par.R.L.val %16=1): ∀ᶠ s:ℕ in atTop,∀ v,s≤v→∀ D₀:Cover,ResidualPermit D₀→ ∃ p:Cover, StretchClock P j s v D₀ p:=by filter_upwards [sky P pL j,zenith P b] with s h u v f d t; obtain ⟨x,t'⟩:=u d t; exact ⟨x,h d t v f x t'⟩
#print axioms oriented_staff
end Internal
end Regulator
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
