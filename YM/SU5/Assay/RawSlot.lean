import YM.SU5.Assay.FreezePose
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
/-!
 Literal uncompressed quadrature on an Apron, paid by REAL lag (width
 clip convention). `RawNormal` guarantees simultaneous and iterated
 limits for fixed frames paying strictly at every support point. Also
 each *fixed* width, possibly clipped, has quadrature limit, even
 if not Walled (in that case not claiming true price identification).
 
 `s` (index of width sequence) and `t` (sampling height) entirely separate.
 Operators with t smaller than engraving height come with **no** claim
 they price actual raw tests. No fixed subresolution samples asserted to
 price a width limit.
-/
local notation "σ"=>P.sampler j x
local notation "β"=>P.rawBase j x
local notation "κ"=>P.coffee j x
local notation "μ"=>P.laid j x
def rawSlot (t:ℕ)(D:P.Apron)(a b:ℝ)(F:SampleDose):X:=σ t F (μ (β D) a b)
local notation "Ψ"=>P.rawSlot j x
lemma rawSlot_raze (t:ℕ)(D:P.Apron)(a b:ℝ)(F:SampleDose):
 Ψ t D a b F=∑i∈P.usedGrid t F, P.activation t F i • P.raze j x D a b (P.vtile t i):=by
 simp only [P.raze_align];rfl
lemma grid_base (r:P.Gridded j x)(D:P.Apron)(a b:ℝ)(F:SampleDose):
 P.Rehearses j x (fun t=>Ψ t D a b F) atTop (κ (P.base j x D) a b F):=by
 have m:=P.sampler_rehearses j x F (μ (β D) a b) r (P.laid_cont j x D a b F) (P.laid_cost j x D a b F) (norm_nonneg _)
 unfold stirred at m
 rw [P.laid_base] at m;exact m
variable {P j x}{F:SampleDose}{a b:ℝ}
namespace RawNormal
variable {I:Type*}{l:Filter I}{s t:I→ℕ}{D:ℕ→P.Apron}{g:ℕ→P.VMark}{p:Vantage}{T:P.RawLag j x}
local notation "Α"=> P.respool j x p T
lemma grid (h:P.RawNormal j x D g p T)(r:P.Gridded j x)(w:Walled j F a b 0)
 (f:Tendsto s l atTop)(k:Tendsto t l atTop):
 P.Rehearses j x (fun i=> Ψ (t i) (D (s i)) a b F) l (κ Α a b F):=by
 obtain ⟨u,c,d,y⟩:=Walled.laid w h.credits
 obtain ⟨z,m,q⟩:=w.more
 obtain ⟨v,_,e,n⟩:=h.merit m
 rw [←respool_laid w h.credits h.normal.credits]
 exact freeze_pose (g:=g ∘ s) (v:=fun i=>μ (β (D (s i))) a b) r d u y k (h.shift.comp f) (e.comp f)
    ((f.eventually n).mono fun i t x g=> t _ (q _ g).1.le _ (q _ g).2.le)
lemma parallel (h:P.RawNormal j x D g p T)(r:P.Gridded j x)(w:Walled j F a b 0):
 P.Rehearses j x (fun i:ℕ×ℕ=> Ψ i.2 (D i.1) a b F) atTop (κ Α a b F):=by
 rw [←prod_atTop_atTop_eq]; exact h.grid r w tendsto_fst tendsto_snd
end RawNormal
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
