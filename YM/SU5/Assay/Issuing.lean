import YM.SU5.Assay.Calendar
import YM.SU5.Assay.RawSlot
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
variable (t:ℕ)
local notation "Φ"=>P.colorSpace j x
local notation "μ"=>P.seenBox j x t
local notation "σ"=>P.shifts j
local notation "τ"=>P.tock t
local notation "T"=>enclave P.calibration
local notation "ℇ"=>(P.physicalEnergy j x).wax
local notation "β"=>P.costing j x t
local notation "𝕤"=>P.Sill j x t
local notation "𝔤"=>P.Grips j x t
variable {P j x t}{a b c d:ℝ}{f g:P.Test}{A L:(P.ColorHil j x).Op}{m n:ℤ}{w v:ℕ}
/-! **Gripping quadrature exactly** once paid by the chosen real walls
 and at least as far along as stencil engraving. Even when one or both
 walls not on grid. -/
variable (P j x t)(D:P.Apron)(i:Cover)
local notation "ξ"=>P.issuing t D
local notation "ρ"=>P.rawSlot j x t D
local notation "δ"=>D.realWidth P j
local notation "Ζ"=>D.zoom P t j
local notation "φ"=>P.charter j x
local notation "M"=>D.engine P j x
local notation "π"=>P.vtile t
lemma issuing_brim (q:D.s ≤ t):P.Brim j (i j-Ζ) (Ζ+Ζ) (ξ i) ∧ β (i j-Ζ) (Ζ+Ζ) (ξ i)=φ (π i) M:=by
 obtain ⟨h,p,hh,hξ⟩:=D.transported P j x t q i
 have hw:=add_pos (D.zoomP P j t) (D.zoomP P j t)
 have k: P.entryTest j t h= σ (-(i j-Ζ)) (ξ i):=by rw [neg_sub];exact hh
 exact ⟨⟨BEntry.ofCard h hw k,P.issuing_color t i D⟩,(seenBox_card t x h hw p k).trans hξ.symm⟩
lemma issuing_grips (q:D.s ≤ t)(p:δ ≤ P.meshPose t i j-a)(r:δ ≤ b-P.meshPose t i j):
  𝔤 a b (ξ i) (P.raze j x D a b (π i)):=by
 obtain ⟨v,e⟩:=P.issuing_brim j x t D i q
 have hz:τ Ζ=δ:=D.zoom_bell P j t q
 have hz₁:τ (i j-Ζ)=P.meshPose t i j-δ:=by rw [P.tock_sub,hz,tock_pose]
 have hz₂:τ (i j-Ζ+((Ζ+Ζ:ℕ):ℤ))=P.meshPose t i j+δ:=by
    rw [Nat.cast_add,show i j-Ζ+(Ζ+(Ζ:ℤ))=i j+Ζ by abel,P.tock_add,hz,tock_pose]
 refine Sill.grips (m:=i j-Ζ) (w:=Ζ+Ζ) ⟨by rw [hz₁]; linarith only [p],by rw [hz₂]; linarith only [r],v,?_⟩
 rw [e,hz₁,hz₂,P.raze_base]
 have y:P.laysM (π i) j=P.meshPose t i j:=rfl
 rw [y,show P.meshPose t i j-a-δ=P.meshPose t i j-δ-a by abel,show b-P.meshPose t i j-δ=b-(P.meshPose t i j+δ) by abel]

lemma seen_issuing (q:D.s ≤ t)(p:δ ≤ P.meshPose t i j)(r:δ ≤ τ w-P.meshPose t i j)(hw:0<w):
 P.BEntry j w (ξ i) ∧ μ w (ξ i)=P.raze j x D 0 (τ w) (π i):=by
 have u:= P.issuing_grips j x t D i q (a:=τ 0) (by rw [P.tock_zero,sub_zero]; exact p) (b:=τ (0+w)) (by rw [zero_add];exact r)
 obtain ⟨⟨p,_⟩,e⟩:=u.exact hw
 unfold costing at e
 rw [neg_zero,P.shifts_zero,P.tock_zero,zero_add] at e
 rw [neg_zero,P.shifts_zero] at p
 exact ⟨p,e.symm⟩

lemma prepared_grips {F:SampleDose}(q:D.s ≤ t)(h:Walled j F a b δ):
 𝔤 a b (P.prepared t D F) (ρ a b F):=by
 rw [P.rawSlot_raze,prepared]
 refine Grips.sum _ _ _ (fun i u=>?_)
 obtain ⟨v,w⟩:=h.used P u
 exact (P.issuing_grips j x t D i q v.le w.le).smul _
lemma priced_rawSlot {F:SampleDose}(q:D.s ≤ t)(h:Walled j F a b δ):
 inner ℂ (Vac) (ρ a b F (Vac))= P.singleState j t x (P.prepared t D F):=
 (P.prepared_grips j x t D q h).price
lemma priced_pair {F G:SampleDose}(N:P.Apron)(q:D.s ≤ t)(r:N.s ≤ t)(h:Walled j F a b δ)(p:Walled j G b c (N.realWidth P j)):
 inner ℂ (Vac) ((ρ a b F*P.rawSlot j x t N b c G) (Vac))= P.singleState j t x (P.prepared t D F * P.prepared t N G):=
 ((P.prepared_grips j x t D q h).join (P.prepared_grips j x t N r p)).price
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
