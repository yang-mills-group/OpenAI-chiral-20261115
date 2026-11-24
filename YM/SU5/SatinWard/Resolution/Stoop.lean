import YM.SU5.SatinWard.Resolution.Rowan
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
-- transport every column still to our Pace.Projected Frame basis.Frag.Aux
noncomputable abbrev cloakCard : P.Card i v (P.reachLeaf s v (moonSpan P s)):= cardC P p uv.art i (vH.valid x) (pavilionWidth P p x wp qh)
lemma cloak_paidCard : P.voxTest i v (cloakCard P p x wp i D₀ uv vH qh).val∈enclave P.calibration:= by apply (enclave_spec ..).2; exact vH.neutral x
lemma cloak_chart : hangs_it P p i D₀ (cloakF P M0 qa vH v) (cloakCard P p x wp i D₀ uv vH qh):= fun U r=> cloak_pocket P M0 p qa vH x wp U r -- order
include uv qh in
lemma cloak_support : blankRent P (cloakF P M0 qa vH v) v s i :=⟨rfl, by rw [real_cloak,←mul_assoc]; exact uv.fit qh⟩
noncomputable abbrev boomCard (u:payable P v 2)(C:Coords Wage4): P.Card i v (P.reachLeaf s v (moonSpan P s)):= cardWave P none p uv.located.cost u i C
include uv in
lemma solo_rent (y:Coords Wage4):blankRent P (soloV P v u D₀ qa y) v s i:=by
 refine ⟨rfl,?_⟩; rw [solo_width,←mul_assoc]; let V':= uv.fit (show petalD ≤ rentWidth P j v from Nat.le_add_left petalD _); exact V' -- choirWidth=deltaWing P petalD
lemma solo_chart (y:Coords Wage4):hangs_it P p i D₀ (soloV P v u D₀ qa y) (cardWave P none p uv.located.cost u i y):=by intro t r; change P.chartAll t (τEnd P v (homeTag P D₀) y u)=τEnd P v (P.clockPlate s v p) y u; rw [r,temple_sweep]
local notation "Φ"=>lined P M0 i x₀ v0 D₀ hp
local notation "Vx"=> poleDay P p uv.located.cost i
include uv pX p₁ p₂ in
set_option maxHeartbeats 190000 in
lemma fee_line (z:ℂ)(qc:hangs_it P p i D₀ B X)(t:blankRent P B v s i)(h:‖poleDay P p uv.located.cost i (cloakCard P p x wp i D₀ uv vH qh) - z • poleDay P p uv.located.cost i X‖ ≤ A) : ‖lined P M0 i x₀ v0 D₀ hp (cloakF P M0 qa vH v) u₁ v₁ - z • lined P M0 i x₀ v0 D₀ hp B u₁ v₁‖ ≤ A := lineup P p i D₀ M0 (cloakF P M0 qa vH v) qa x₀ uv (cloakCard P p x wp i D₀ uv vH qh) (cloak_paidCard P p x wp i D₀ uv vH qh) (cloak_support P p i D₀ M0 qa uv vH qh) hp X pX (cloak_chart P p x wp i D₀ M0 qa uv vH qh) B t qc z p₁ p₂ h -- dot indexing. order
include uv p₁ p₂ in
lemma fee_solo (z:ℂ)(y:Coords Wage4)(pp: ‖poleDay P p uv.located.cost i (cloakCard P p x wp i D₀ uv vH qh)-z • frameWave P none p uv.located.cost u i y‖ ≤ A): ‖lined P M0 i x₀ v0 D₀ hp (cloakF P M0 qa vH v) u₁ v₁ - z • rawSolo P M0 i x₀ qa y u v0 hp u₁ v₁‖≤ A:=by
 let Q:= boomCard P p i D₀ uv u y; let U:= fee_line P p x wp i D₀ M0 qa x₀ uv (soloV P v u D₀ qa y) Q (arcStencil P none p uv.located.cost u i (Set.mem_range_self y)) vH qh p₁ p₂ hp z (solo_chart P p i D₀ qa uv u y) (solo_rent P p i D₀ qa uv u y) pp; exact U
-- use prerequisites.Pose rank reference probe later.There.
variable (hv:0<lapQ P.run s)(ht:0<lapQ P.run v)
local notation "Σ'"=> P.par.R.L
local notation "W▸"=> hourBound P.run v
noncomputable def front (v:ℕ){w:ℕ}{F:Cover→ Family P.calibration}(k:Domicile w F) : P.RawLag i x₀:= lined P M0 i x₀ v D₀ le_rfl (cloakF P M0 qa k v) -- v0=v.Aux.Book.F. Keep external parameter v0.
noncomputable abbrev frontPrice (k:Domicile w H_): P.RawLag i x₀:= fun l r => lined P M0 i x₀ v0 D₀ hp (cloakF P M0 qa k v) l r
lemma widthPaid : hourBound P.run v ≤ rentWidth P j v:= by change P.thresholdF v +_ ≤ _; unfold rentWidth; omega -- recursion
lemma starPad : hourBound P.run v+2*j≤ rentWidth P j v:= Nat.le_add_right _ _ -- order
include h f q k Hc Ac uv p₁ p₂ hv wp
lemma frontQ : ‖frontPrice P i D₀ M0 qa x₀ hp (L.earnedZ P η none) u₁ v₁ -(↑(gatherG M.1):ℂ) • rawSolo P M0 i x₀ qa pseV u v0 hp u₁ v₁‖≤ wageMonth P η A H s v:= by
 let X:=L.earnedZ P η none; let ht:=(widthPaid (j:=j) (v:=v) P); have t:=phaseQ P p x wp q uv.located.cost uv.art k i h f Hc Ac η L hv u
 have c: ‖poleDay P p uv.located.cost i (cloakCard P p x wp i D₀ uv X ht)-(↑(gatherG M.1):ℂ) • frameWave P none p uv.located.cost u i pseV‖≤ wageMonth P η A H s v:=t; exact fee_solo P p x wp i D₀ M0 qa x₀ uv X ht p₁ p₂ hp u (↑(gatherG M.1):ℂ) pseV c
include ht in
lemma frontStar : ‖frontPrice P i D₀ M0 qa x₀ hp (logStarCore P η L) u₁ v₁-(↑(gatherG M.2.1):ℂ) • rawSolo P M0 i x₀ qa pseV u v0 hp u₁ v₁‖ ≤ wageMonth P η A H s v:=by
 let X:=logStarCore P η L; let ht':=starPad (j:=j) (v:=v) P; have t:=phaseStar P p x wp q uv.located.cost uv.art k i h f Hc Ac η L hv ht u
 have c: ‖poleDay P p uv.located.cost i (cloakCard P p x wp i D₀ uv X ht')-(↑(gatherG M.2.1):ℂ) • frameWave P none p uv.located.cost u i pseV‖≤ wageMonth P η A H s v:=t; exact fee_solo P p x wp i D₀ M0 qa x₀ uv X ht' p₁ p₂ hp u _ pseV c
lemma frontJ (kμ:Axis): let c:= L.earnedZ P η (some kμ); let T:=Signboard.letterShape (J:=P.calibration) (Λ:=P.par) kμ v M.2.2
 ‖frontPrice P i D₀ M0 qa x₀ hp c u₁ v₁- frontPrice P i D₀ M0 qa x₀ hp T u₁ v₁‖ ≤ pulseMonth P η A H s v:=by
 intro c' T'; have t:=phaseJ P p x wp q uv.located.cost uv.art k i h f Hc Ac η L hv kμ; let co:= cloakCard P p x wp i D₀ uv c' (widthPaid (j:=j) (v:=v) P); let ca:=cloakCard P p x wp i D₀ uv T' (Nat.zero_le _); have c:‖poleDay P p uv.located.cost i co-(1:ℂ) •poleDay P p uv.located.cost i ca‖ ≤ pulseMonth P η A H s v:= (by rw [one_smul]; exact t)
 let d₀:= cloakF P M0 qa T' v; have e:= fee_line P p x wp i D₀ M0 qa x₀ uv d₀ ca (cloak_paidCard P p x wp i D₀ uv T' (Nat.zero_le _)) c' (widthPaid P) p₁ p₂ hp 1 (cloak_chart P p x wp i D₀ M0 qa uv T' (Nat.zero_le _)) (cloak_support P p i D₀ M0 qa uv T' (Nat.zero_le _)) c; rw [one_smul] at e; exact e
#print axioms frontQ
#print axioms frontStar
#print axioms frontJ
end Internal
end Regulator
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
