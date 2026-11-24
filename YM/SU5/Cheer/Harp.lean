import YM.SU5.Cheer.Verse
set_option maxHeartbeats 80000
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia) -- tune
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
namespace Spine
open OS.Semigroup (F)
open OS.Semigroup.Balloon
open Cheer
open Cheer (Narrow)
variable (P:Spine)(x:P.Spectrum0 3)(Z:Lead.Clan)(s n:ℕ)(c r:ℕ→ℕ)
local notation "S"=> P.seasons 3 (P.otherSpectrum 3 3 x)
local notation "ψ"=> P.lucid x Z
local notation "ξ"=> P.otherSpectrum 3 3 x
local notation "H"=> P.ManyF 3 ξ
local notation "Ω"=> P.heaven 3 ξ
local notation "G" i:max=> P.comesFrom x Z (c i) (r i)
local notation "ρ" i:max=> P.dew (c i) (r i)
local notation "z" i:max=> P.allowance x Z (c i) (r i)
local notation "φ" i:max=> ψ (c i) (r i)
local notation "η" i:max=> P.birthCloud x Z (c i) (r i)
local notation "M"=> Cheer.FLap
variable{P x c r Z}
lemma lit (A:P.Bands x Z c r)(U:Set E4)(t:IsOpen U)(h:(Mink.inside∩U).Nonempty): let S₀:= P.seasons 3 (P.otherSpectrum 3 3 x); ∃ d:ℝ, 0 < d ∧ ∀ᶠ i:ℕ in atTop, d < ‖S₀.ℚmeasure.region (Cheer.press (P.dew (c i) (r i)) U) (P.birthCloud x Z (c i) (r i))‖^2:= by
 let p:= (promenade Z:Measure E4).real U; have he:0<p:=ENNReal.toReal_pos (importance Z t h).ne' (measure_ne_top (promenade Z:Measure E4) U); exact ⟨p/2,half_pos he,A.funded U t h _ (half_lt_self he)⟩
end Spine
namespace Prototype
open Spine Lamour Bridge.Celeste Glimpse Morn Spine.RadiusF Ballad
open CF.Velvet CF.Pannier.Chancel Altitude
-- CP12. choose one sufficiently late watching rung i; x is held fixed through Bands.
lemma stellar (e v D:ℝ)(X:Supplier)(hx:0<v)(u:0<D) (z:ℕ→ℕ): ∃ (P:Spine)(K:P.Register), uniform P K X e v ∧ ∃ (r:ℕ→ℕ), z≤r ∧
 ∃ (c:ℕ→ℕ), Launch P c r ∧ roughUV P c r keyV ∧ ∃ (α t:ℝ),0<α∧ 0<t∧t<D ∧ ∃ Y: Glimpse.Voyage P.par.block P.calibration.ℓ 4 α (RadiusF.next P.calibration.ℓ),
     ∀ᶠ i:ℕ in atTop, ∃ x:P.Spectrum0 3, P.party 3 K x ∧ readyUV P c r x keyV ∧ P.funds i (P.otherSpectrum 3 3 x) Y t ∧
       ∀ z:SU.Slot, P.Intact K i Y.toGaze x z t∧ P.Royal i (P.otherSpectrum 3 3 x) Y (Window.family z) t ∧ P.Passage x c r K z ∧ P.Bands x (Window.family z) c r:=by
 obtain ⟨P,K,H,r,Hr,c,Q,V,α,t,z,a,e,Y,p⟩:= luminous e v D X hx u z
 refine ⟨P,K,H,r,Hr,c,Q,V,α,t,z,a,e,Y,?_⟩
 filter_upwards [p] with i F; obtain ⟨x,t,p,w,W⟩:=F; exact ⟨x,t,p,w,fun z=> ⟨(W z).1,(W z).2.1,(W z).2.2,fertile (Window.family z) Q p keyV_go (t.2.1.accepted 3)⟩⟩
end Prototype
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#check @Spine.halo_zero
#print axioms Spine.halo_zero
#check @Spine.pays_move
#print axioms Spine.pays_move
#check @Spine.promenade_strict
#print axioms Spine.promenade_strict
#check @Spine.priceStream
#print axioms Spine.priceStream
#check @Spine.Bands.weak
#check @Spine.Bands.finite_t
#check @Spine.Bands.exhausted
#check @Spine.Bands.funded
#check @Spine.lit
#print axioms Spine.lit
#check @Spine.fertile
#print axioms Spine.fertile
#check @Prototype.stellar
#print axioms Prototype.stellar
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
