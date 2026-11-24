import YM.SU5.Assay.Reprise
import YM.SU5.Assay.LagOp
import YM.SU5.Assay.SeenBox
import YM.SU5.Aria.Repertoire
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
# Fixed marks. Width on evaluated axis `j` is Apron's own capacity, at
 *that* height, measured in time units for `ColorHil`. Base endowment
 in continuous space is reprised engine. Add real walls; no extra
 damping (up to clip convention). Certified strict purchase uses both lags
 **strictly** larger than that width; some laws also at equality.
-/
variable (D:P.Apron)(a b:ℝ)(y:Vantage)
local notation "π"=> P.reprise j x
local notation "M"=> D.engine P j x
local notation "u"=> D.u j
local notation "G"=> (P.shifts j (D.u j:ℤ) D.F)
local notation "τ"=> D.realWidth P j
def base : Lag:= (S).hang τ (π (M))
local notation "β"=> P.base j x D
lemma engine_seen : M=P.seenBox j x D.s (u+u) G:=
  (seenBox_card D.s x (D.cardB P j) (add_pos (D.pos j) (D.pos j)) (D.color P j) (f:=G) rfl).symm
lemma engine_pay : ‖M‖ ≤ ‖P.meanBox j D.s (u+u) G‖:=by
 rw [P.engine_seen];exact seenBox_pay _ _ (D.admit j) (D.color P j)
lemma base_pay : ‖β a b‖ ≤ ‖M‖:=((S).hang_pay ..).trans (P.reprise_pay ..)
lemma base_cost : ‖β a b‖ ≤ ‖P.meanBox j D.s (u+u) G‖:= (P.base_pay ..).trans (P.engine_pay ..)
lemma base_at : β τ τ= π (M):= (S).hang_at ..
lemma base_credits : (S).Credits τ β:= Credits.hang (S) (π M) τ
lemma base_step {a b d e:ℝ}(p:τ≤a)(q:τ≤b)(t:a≤d)(v:b≤e):
 β d e= (S).sand (β a b) (d-a) (e-b):=(S).sand_step p q t v _
lemma base_kiss : P.base j x (D.kiss P j)= P.otherLag j x (β):=by
 funext a b
 change (S).sand (π ((D.kiss P j).engine P j x)) (a-τ) (b-τ)=star ((S).sand (π M) _ _)
 rw [sand_star,←D.peer P j x,P.reprise_star]
lemma base_slide {I:Type*}{l:Filter I}{f g:I→ℝ}{a b:ℝ}(p:Tendsto f l (𝓝 a))(q:Tendsto g l (𝓝 b)):
 BSOT (fun i=> β (f i) (g i)) l (β a b):=(S).hang_slide τ p q
lemma base_slide_slot {I:Type*}{l:Filter I}{f g:I→ℝ}{a b:ℝ}{r:I→Vantage}{p:Vantage}
 (q:Tendsto f l (𝓝 a))(v:Tendsto g l (𝓝 b))(z:Tendsto r l (𝓝 p)):
 BSOT (fun i=>P.slot j x (β) (f i) (g i) (r i)) l (P.slot j x (β) a b p):=by
 have t:Tendsto (fun i=>r i j) l (𝓝 (p j)):= ((continuous_apply j).tendsto p).comp z
 exact P.locate_limit j x z (P.base_slide j x D (t.sub q) (v.sub t))
lemma base_slot_pin : BSOT (P.slot j x (β) a b) (𝓝 y) (P.slot j x (β) a b y):=
 P.base_slide_slot j x D tendsto_const_nhds tendsto_const_nhds tendsto_id
lemma base_slot_pay : ‖P.slot j x (β) a b y‖≤‖M‖:= (P.flown_cost ..).trans_le (P.base_pay ..)

local notation "κ"=>P.charter j x
lemma base_slot : P.slot j x (β) a b y= (S).sand (θ y M) (y j-a-τ) (b-y j-τ):=by
 unfold slot flown base hang
 rw [P.locate_sand,P.reprise_table]
lemma base_pillar : P.slot j x (β) a b y=P.pillar j x D a b y:=by
 rw [P.base_slot,show y j-a-τ=y j-τ-a by abel,show b-y j-τ=b-(y j+τ) by abel]; ext1; rfl
variable (g:P.VMark)
local notation "z"=> P.laysM g
lemma raze_base : P.raze j x D a b g= (U).sand (κ g M) (z j-a-τ) (b-z j-τ):=by
 rw [show z j-a-τ=z j-τ-a by abel,show b-z j-τ=b-(z j+τ) by abel];ext1;rfl
lemma raze_slot : π (P.raze j x D a b g)= P.slot j x (β) a b z:=by
 rw [P.raze_base,P.base_slot,P.reprise_table,P.reprise_sand,P.reprise_charter]
lemma charter_kiss : star (κ g M)= κ g ((D.kiss P j).engine P j x):=by
 apply star_injective; rw [star_star]; exact (P.charter_opposed ..).symm
lemma raze_star : star (P.raze j x D a b g)=(U).sand (κ g ((D.kiss P j).engine P j x)) (b-z j-τ) (z j-a-τ):=by
 rw [P.raze_base,sand_star,P.charter_kiss]
-- slot bound in terms of **raze**, useful on both calibrations
lemma slot_cost_at : ‖P.slot j x (β) a b z‖ ≤ ‖P.raze j x D a b g‖:= by
 rw [←P.raze_slot]; exact P.reprise_pay ..
lemma raze_step {a b c d:ℝ}(p:τ≤z j-a)(q:τ≤b-z j)(t:c≤a)(v:b≤d):
   P.raze j x D c d g= (U).sand (P.raze j x D a b g) (a-c) (d-b):=by
 rw [P.raze_base,P.raze_base,(U).sand_join (sub_nonneg.mpr p) (sub_nonneg.mpr q) (sub_nonneg.mpr t) (sub_nonneg.mpr v),
    show z j-a-τ+(a-c)=z j-c-τ by abel,show b-z j-τ+(d-b)=d-z j-τ by abel]
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
