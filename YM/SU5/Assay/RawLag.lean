import YM.SU5.Assay.Base
import YM.SU5.Assay.CharterCost
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
 Raw base and its alignment. Charge is again in lags from **that
 center** (not the displaced one) by convention. `align D p l r`
 moves it to the transverse chamber at `p`. Substituting adjusted
 lags costs temporal displacement; e.g. center at `P.laysM p`
 in span [a,b] with that charge gives `P.raze j x D a b p`.
-/
abbrev RawLag:= ℝ→ℝ→(P.ColorHil j x).Op
def rawOther (T:P.RawLag j x):P.RawLag j x:= fun a b=>star (T b a)
-- Converting a raw limit charged at measured transverse position p
-- back to pose-action in undisplaced chamber. Ignores temporal component of p.
def respool (p:Vantage)(T:P.RawLag j x):Lag:=fun a b=>
  P.locate j x (-p) (P.reprise j x (T a b))
lemma respool_turn (p:Vantage)(T:P.RawLag j x): P.respool j x p (P.rawOther j x T)=P.otherLag j x (P.respool j x p T):=by
  ext a b;unfold respool otherLag rawOther; rw [P.locate_star,P.reprise_star]

variable (D:P.Apron)(g:P.VMark)(a b:ℝ)
local notation "π"=> P.reprise j x
local notation "M"=> D.engine P j x
local notation "u"=> D.u j
local notation "N"=> (P.shifts j (D.u j:ℤ) D.F)
local notation "τ"=> D.realWidth P j
local notation "ℛ"=> P.charter j x
local notation "ν"=> P.laysM g
def rawBase:P.RawLag j x:= (U).hang τ M
local notation "β"=> P.rawBase j x D
def align :P.RawLag j x:=fun l r=> ℛ g (β l r)
local notation "α"=> P.align j x D g
lemma reprise_rawBase: π (β a b)=P.base j x D a b:=P.reprise_hang ..
lemma align_credits:(U).Credits τ α:=by
 unfold align rawBase hang
 intro a b c d h t v y;dsimp only
 rw [←P.charter_sand,←(U).sand_step h.le t.le v y]
lemma rawBase_pay : ‖β a b‖ ≤ ‖M‖:= (U).hang_pay ..
lemma rawBase_step {a b d e:ℝ}(h:τ≤a)(q:τ≤b)(t:a≤d)(v:b≤e):
 β d e=(U).sand (β a b) (d-a) (e-b):=(U).sand_step h q t v _
lemma rawBase_kiss:P.rawBase j x (D.kiss P j)= P.rawOther j x β:=by
 funext a b
 change (U).sand ((D.kiss P j).engine P j x) _ _= star ((U).sand M (b-τ) (a-τ))
 rw [sand_star,←D.peer P j x];rfl
lemma rawBase_slide {I:Type*}{l:Filter I}{f h:I→ℝ}{a b:ℝ}(t:Tendsto f l (𝓝 a))(q:Tendsto h l (𝓝 b)):
 BSOT (fun i=>β (f i) (h i)) l (β a b):=(U).hang_slide τ t q
lemma align_kiss:P.align j x (D.kiss P j) g=P.rawOther j x α:=by
 funext a b; unfold align;rw [rawBase_kiss];unfold rawOther;rw [P.charter_star]
lemma align_zero : P.align j x D 0 = β:=by funext a b; exact P.charter_zero ..
lemma respool_align : P.respool j x (ν) (α)=P.base j x D:=by
 funext a b; unfold respool align
 rw [P.reprise_charter,P.locate_cancel,P.reprise_rawBase]
lemma raze_align:P.raze j x D a b g = α ((ν) j-a) (b-(ν) j):=by
 unfold align rawBase hang; rw [P.raze_base,P.charter_sand]
lemma align_dist (C:P.Apron): ‖α a b-P.align j x C g a b‖=‖β a b-P.rawBase j x C a b‖:=P.charter_dist ..
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
