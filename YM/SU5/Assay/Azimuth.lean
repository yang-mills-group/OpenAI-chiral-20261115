import YM.SU5.Assay.Beacon
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
local notation "η"=>P.pharos j x
local notation "τ"=>P.otherLag j x
local notation "ρ"=>P.slot j x
local notation "Φ"=>P.thrust j x
local notation "Ψ"=>P.retort j x
local notation "Ξ"=>P.two_call j x
variable {P j x}{T T':P.LagOp j x}{D D':ℕ→P.Apron}{F G:SampleDose}{a b c:ℝ}
/-!
 Vacuum beams tested from raw limit, also coherence on every ordered
 multi-axis overlap (from *the exact same* regulator call).
-/
namespace Kiln
variable (k:P.Kiln j x D T)
include k
-- norms of first-slot beams etc also converge; raw vectors not preprojected.
lemma called (h:Walled j F a b 0): BothWays (fun s=>(D s).s)
 (fun s t=>σ t (D s) a b F (Vac)) (fun s=>E (Φ (β (D s)) F a)) (E (Φ T F a)):=by
 rw [←(thrust_launch k.normal.credits h).2]
 let q:=k.porcelain h
 have p:BothWays (fun s=>(D s).s) (fun s t=>σ t (D s) a b F (Vac)) (fun s=>E (κ (β (D s)) a b F Ω)) (E (κ T a b F Ω)):=
  ⟨Eventually.of_forall fun s=>(q.stationary s).shows Ω, (E).continuous.continuousAt.tendsto.comp (q.next.showAt Ω),
     (q.together.shows Ω).comp (Escrow.visits _)⟩
 exact p.congr' ((k.normal.fades.room h).mono fun _ w=>⟨congrArg (E) (thrust_launch (P.base_credits j x _) w).2, fun _ _=>rfl⟩)
lemma landed (h:Walled j F a b 0): BothWays (fun s=>(D s).s)
 (fun s t=>star (σ t (D s) a b F) (Vac)) (fun s=>E (Ψ (β (D s)) F b)) (E (Ψ T F b)):=by
 rw [←(retort_land k.normal.credits h).2]
 let q:=k.porcelain h
 have p:BothWays (fun s=>(D s).s) (fun s t=>star (σ t (D s) a b F) (Vac)) (fun s=>E (star (κ (β (D s)) a b F) Ω)) (E (star (κ T a b F) Ω)):=
  ⟨Eventually.of_forall fun s=>(q.stationary s).back Ω, (E).continuous.continuousAt.tendsto.comp (q.next.starAt Ω),
     (q.together.back Ω).comp (Escrow.visits _)⟩
 exact p.congr' ((k.normal.fades.room h).mono fun _ w=>⟨congrArg (E) (retort_land (P.base_credits j x _) w).2, fun _ _=>rfl⟩)
variable (k':P.Kiln j x D' T') {i:Axis}
include k'
lemma paid {y:P.Spectrum0 i}(h:Walled j F a b 0)(q:Walled j G b c 0)(e:x=P.advocate i y j):
 BothWays (fun s=>max (D s).s (D' s).s)
   (fun s t=>P.singleState i t y (ξ t (D s) F*ξ t (D' s) G))
   (fun s=>Ξ (β (D s)) F b (β (D' s)) G) (Ξ T F b T' G):=by
 rw [two_call_from k.normal.credits k'.normal.credits h q]
 exact (((k.porcelain h).compound (k'.porcelain q)).claims y e).congr'
    (((k.normal.fades.room h).and (k'.normal.fades.room q)).mono fun s r=>
     ⟨(two_call_from (P.base_credits j x _) (P.base_credits j x _) r.1 r.2).symm,fun _ _=>rfl⟩)
lemma ok (h:Walled j F a b 0)(q:Walled j G b c 0):
 BothWays (fun s=>max (D s).s (D' s).s)
   (fun s t=>P.singleState j t x (ξ t (D s) F*ξ t (D' s) G))
   (fun s=>Ξ (β (D s)) F b (β (D' s)) G) (Ξ T F b T' G):=by
 rw [two_call_from k.normal.credits k'.normal.credits h q]
 exact ((k.porcelain h).compound (k'.porcelain q)).traces.congr'
    (((k.normal.fades.room h).and (k'.normal.fades.room q)).mono fun s r=>
     ⟨(two_call_from (P.base_credits j x _) (P.base_credits j x _) r.1 r.2).symm,fun _ _=>rfl⟩)
lemma paid_rev {y:P.Spectrum0 i}(h:Walled j F a b 0)(q:Walled j G b c 0)(e:x=P.advocate i y j):
 BothWays (fun s=>max (D s).s (D' s).s)
   (fun s t=>P.singleState i t y (ξ t (D' s) G*ξ t (D s) F))
   (fun s=>Ξ (β (D s)) F b (β (D' s)) G) (Ξ T F b T' G):=by
 exact (k.paid k' h q e).congr' (Eventually.of_forall fun _=>⟨rfl,fun _ _=>congrArg (P.singleState ..) (mul_comm ..)⟩)
variable {i₀:Axis}{y₀:P.Spectrum0 i₀}{y:P.Spectrum0 i}{Z Z':P.LagOp i y}{d e r:ℝ}
lemma compares (l:P.Kiln i y D Z)(l':P.Kiln i y D' Z')
 (p:x=P.advocate i₀ y₀ j)(t:y=P.advocate i₀ y₀ i)
 (h:Walled j F a b 0)(q:Walled j G b c 0)(v:Walled i F d e 0)(w:Walled i G e r 0):
 Ξ T F b T' G=P.two_call i y Z F e Z' G:= (k.paid k' h q p).via (l.paid l' v w t)
lemma compares_rev (l:P.Kiln i y D Z)(l':P.Kiln i y D' Z')
 (p:x=P.advocate i₀ y₀ j)(t:y=P.advocate i₀ y₀ i)
 (h:Walled j F a b 0)(q:Walled j G b c 0)(v:Walled i G d e 0)(w:Walled i F e r 0):
 Ξ T F b T' G=P.two_call i y Z' G e Z F:= (k.paid k' h q p).via (l'.paid_rev l v w t)
end Kiln
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
