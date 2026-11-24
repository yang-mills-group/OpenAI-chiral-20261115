import SatinFixedContrastNovember4
import SatinThinLoss
import YM.SU5.Six.ViewHom
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 250000
set_option quotPrecheck false
noncomputable section

open Filter Function Set Metric MeasureTheory
open scoped Topology InnerProductSpace NNReal ComplexOrder BigOperators
namespace YM.Mussel
/-- Lifting a short-rod fusion to the uncompressed purchase, not assuming
stationarity after selling only the continuous spatial sector. $$`b` strictly positive. -/
theorem short_fuses {H G:Hilbert} {a:Axis} (S:OS.Semigroup H a)
   (φ:G →L[ℂ] H) (π:H →ₗᵢ[ℂ] G) (proj:G→L[ℂ] G)(proj_def:∀ z,proj z=π (φ z))
   (b:ℝ≥0)(E:G.Op) (shrinks:‖E‖≤1)
   (warm:∀ z,E (π z) = π (S.E b z))
   (w:H)(stasis:S.E b w=w)
   (p:ℂ)(hp:p≠0)(x:ℕ→G)(y:ℕ→H)(c:ℕ→ℂ)
   (q: Tendsto (fun i=>proj (x i)-x i) atTop (𝓝 0))
   (f:∀ i,φ (x i)= y i + c i • w)
   (hc:Tendsto (fun i=>c i) atTop (𝓝 p))(he:Tendsto (fun i=>S.E b (y i)) atTop (𝓝 0)) :
   Tendsto (fun i=> E (p⁻¹ • x i)) atTop (𝓝 (π w)):=by
 have hq:= E.continuous.continuousAt.tendsto.comp q
 have hl : Tendsto (fun i=>S.E b (y i)+ c i • w) atTop (𝓝 (p • w)):=by simpa only [zero_add] using he.add (hc.smul_const w)
 have h:Tendsto (fun i=> E (proj (x i))) atTop (𝓝 (p • π w)):=by
   have h' := π.continuous.continuousAt.tendsto.comp hl
   rw [map_smul] at h'
   exact h'.congr fun i=>by
    change π (_+_)=_
    rw [proj_def,warm,f i,map_add (S.E b),map_smul (S.E b),stasis]
 have Hq : Tendsto (fun i=> E (x i)) atTop (𝓝 (p • π w)):=by
    have hu := h.sub hq
    rw [map_zero,sub_zero] at hu
    exact hu.congr fun i=> by
     change _ - E (_-_)=_
     rw [map_sub]; abel
 have hy := Hq.const_smul p⁻¹
 rw [smul_smul,inv_mul_cancel₀ hp,one_smul] at hy
 exact hy.congr fun i=> (map_smul E _ _).symm
end YM.Mussel

namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Casting Six
namespace Habitat
variable {P:Spine} {x:P.Spectrum0 3} {c r:ℕ→ℕ} {K:P.Register} {J:P.Ellis 3 x}
variable (B:P.Experiment K c r x J)(Z:Lead.Clan)
local notation "ξ"=> P.otherSpectrum 3 3 x
local notation "ω"=> P.colorZero 3 (P.otherSpectrum 3 3 x)
local notation "Ω"=> P.heaven 3 ξ
local notation "H"=> P.ManyF 3 ξ
local notation "G"=> P.ColorHil 3 (P.otherSpectrum 3 3 x)
local notation "S"=> P.seasons 3 ξ
local notation "E"=> (P.physicalEnergy 3 ξ).E
local notation "ν" i:max=> P.shard x Z (c i) (r i)
local notation "Vᴮ"=> P.viewF 3 ξ
local notation "τ"=> P.stockS Z
abbrev purity(Z:Lead.Clan):ℂ := purePrice Z
section sector
include B
/-- At a strictly positive occupied point, normalization reciprocal of purePrice;
 unprojected strong limit at any time. -/
lemma short_born (b:ℝ≥0)(p:0<b):
    Tendsto (fun i:ℕ=> E b ((purity Z)⁻¹ • ν i)) atTop (𝓝 ω):=
 Mussel.short_fuses S (P.wealth 3 ξ) (P.enter 3 ξ) (P.visitors 3 ξ) (fun _=>rfl)
    b (E b) ((P.physicalEnergy 3 ξ).shrinks b) (fun _=>rfl) (Ω) (P.heaven_hot 3 ξ b)
    _ (Complex.ofReal_ne_zero.mpr (purePrice_p Z).ne') _ _ _
    (whole_sky Z B.launch B.ready Twah.keyV_go) (fun _=>P.halo_split ..)
    (refreshing Z B.launch B.ready Twah.keyV_go) (cloud_escape B Z b p)
end sector
end Habitat
#print axioms Habitat.short_born
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
