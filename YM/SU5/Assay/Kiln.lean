import YM.SU5.Assay.Porcelain
import YM.SU5.Assay.SlotTurn
import YM.SU5.Assay.Espresso
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4900
set_option maxHeartbeats 420000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
open Aria Set OS.Semigroup
variable (P:Spine)(j:Axis)(x:P.Spectrum0 j)
local notation "K"=> P.calibration
local notation "H"=> P.ColorHil j x
local notation "B"=> P.ManyF j x
local notation "X"=> (P.ColorHil j x).Op
local notation "Y"=> (P.ManyF j x).Op
local notation "Lag"=>ℝ→ℝ→(P.ManyF j x).Op
local notation "S"=> P.seasons j x
local notation "U"=> P.physicalEnergy j x
local notation "ω"=> (P.seasons j x).wax
local notation "W"=> P.cartage j x
local notation "θ"=> P.tableau j x
local notation "E"=> P.enter j x
local notation "R"=> P.wealth j x
local notation "Vac"=> P.colorZero j x
local notation "Ω"=> P.heaven j x
local notation "σ"=>P.rawSlot j x
local notation "β"=>P.base j x
local notation "κ"=>P.coffee j x
local notation "𝔤"=>P.Grips j x
local notation "ξ"=>P.prepared
local notation "μ"=>P.singleState j
local notation "⟪" T "⟫"=>inner ℂ Ω ((T:Y) Ω)
/-!
 `Kiln`: Euclidean thin fields currency. `coffee` is the smeared
 answer at every pair of real walls `Walled` about sample support,
 i.e. paying **just** strictly positive lags (and selected by point
 limit also in `normal`). Actual grids can have to satisfy larger
 lags and a `t ≥ (D s).s` condition; on restricting to valid slice,
 `Porcelain` gives all price readings directly on this character,
 with *this* coffee the answer whether sequential (first fine pose
 grid then widths) or simultaneous. All purchase, including adjoint
 family, even at a fixed experiment demanding the prices at molds
 moving to zero width. No claims of this nature for unearned widths,
 coincidence, Minkowski or Lorentz fields. No invoking path integrals
 as measures on colored pin fields.
-/
structure Kiln (D:ℕ→P.Apron)(T:Lag) : Prop where
 gridded : P.Gridded j x
 normal : P.Normal j x D T
 pressed : ∀(F:SampleDose)(a b:ℝ), Walled j F a b 0 → P.Rehearses j x
    (fun i:ℕ×ℕ=>σ i.2 (D i.1) a b F) atTop (κ T a b F)
variable {P j x}{D:ℕ→P.Apron}{T:P.LagOp j x}{F G:SampleDose}{a b c:ℝ}
local notation "δ" s:max =>(D s).realWidth P j
lemma RawNormal.settles {g:ℕ→P.VMark}{p:Vantage}{u:P.RawLag j x}(h:P.RawNormal j x D g p u)(r:P.Gridded j x):
 P.Kiln j x D (P.respool j x p u) := ⟨r,h.normal,fun _ _ _ v=>h.parallel r v⟩
lemma RawNormal.kiln {g:ℕ→P.VMark}{p:Vantage}{u:P.RawLag j x}(h:P.RawNormal j x D g p u)(r:P.Register):
 P.Kiln j x D (P.respool j x p u):=h.settles (P.metered _ _ r)
lemma flip_twice (j:Axis)(F:SampleDose): flipDose (flipDose F j) j=F:=by
 suffices p:(flipDose (flipDose F j) j).val=F.val from ((show ∀i k:SampleDose,i.val=k.val→i=k by
   rintro ⟨_,_,_⟩ ⟨_,_,_⟩;simp) _ _ p)
 exact funext fun y=>congrArg F.val (reflectPose_twice ..)

namespace Kiln
variable (h:P.Kiln j x D T)
include h
lemma porcelain (w:Walled j F a b 0):
 P.Porcelain j x (fun s=>(D s).s) (fun s t=>ξ t (D s) F) a b
   (fun s t=> σ t (D s) a b F) (fun s=>κ (β (D s)) a b F) (κ T a b F):=
 ⟨(h.normal.fades.room w).mono fun _ v _ p=>P.prepared_grips j x _ _ p v,fun s=>P.grid_base _ _ h.gridded ..,
    h.normal.pour w,h.pressed _ _ _ w⟩
lemma brew (w:Walled j F a b 0):P.Brew j x T a b F:=w.brew h.normal.credits
lemma kiss : P.Kiln j x (fun s=>(D s).kiss P j) (P.otherLag j x T):=by
 refine ⟨h.gridded,h.normal.kiss,?_⟩
 intro F a b w
 have t:=(h.pressed _ _ _ w.flip).dagger
 simp only [P.rawSlot_flip,coffee_dagger h.normal.credits w.flip,flip_twice,neg_neg] at t;exact t
-- All support and production strict at fine enough width, independently of stage ≥all engravings. Covers reflected price as well.
lemma itinerary (w:Walled j F a b 0):
 ∀ᶠ s in atTop,
   Walled j F a b (δ s) ∧ (∀t≥(D s).s, P.asked_at t (ξ t (D s) F) (P.spacePrice (D s) F) ∧ 𝔤 t a b (ξ t (D s) F) (σ t (D s) a b F)):=
 ((h.normal.fades.room w).and (h.porcelain w).earned).mono fun _ v=>⟨v.1,fun _ i=>⟨P.prepared_at _ _ _ i,v.2 _ i⟩⟩
lemma both (w:Walled j F a b 0):BothWays (fun s=>(D s).s) (fun s t=> μ t x (ξ t (D s) F))
 (fun s=>⟪κ (β (D s)) a b F⟫) ⟪κ T a b F⟫:=(h.porcelain w).traces
variable {D':ℕ→P.Apron}{T':P.LagOp j x}
lemma tested (u:P.Kiln j x D' T')(w:Walled j F a b 0)(z:Walled j G b c 0):
  BothWays (fun s=>max (D s).s (D' s).s) (fun s t=> μ t x (ξ t (D s) F * ξ t (D' s) G))
  (fun s=>⟪κ (β (D s)) a b F * κ (β (D' s)) b c G⟫)
  ⟪κ T a b F*κ T' b c G⟫:=((h.porcelain w).compound (u.porcelain z)).traces
end Kiln
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
