import YM.SU5.Assay.Locate
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
 Positive lags and translations of an operator at a mark with physical
 center y and walls a,b. Terms defined on all real args for convenience;
 only claim compatibility etc on legitimate arguments. `flown` arguments are
 two *lags* (measured **from the center**); `slot` uses absolute cuts.
-/
abbrev LagOp:=ℝ→ℝ→(P.ManyF j x).Op
def otherLag (T:P.LagOp j x):Lag:=fun l r=>star (T r l)
noncomputable def flown (T:Lag)(l r:ℝ)(y:Vantage):Y:= P.locate j x y (T l r)
noncomputable def slot (T:Lag)(a b:ℝ)(y:Vantage):Y:= P.flown j x T (y j-a) (b-y j) y
local notation "ℛ"=> P.locate j x
local notation "β"=> P.flown j x
local notation "σ"=> P.slot j x
variable (T:P.LagOp j x)(y:Vantage)(a b d e l r:ℝ)
lemma flown_shift (p:Vantage): β T l r (p+y)=ℛ p (β T l r y):= (P.locate_sum ..).symm
lemma flown_zero : β T l r 0= T l r:= P.locate_zero ..
lemma flown_star : star (β T l r y)=β (P.otherLag j x T) r l y:= P.locate_star ..
lemma flown_cost : ‖β T l r y‖= ‖T l r‖:=P.locate_cost ..
lemma slot_shift (p:Vantage): σ T (p j+a) (p j+b) (p+y)=ℛ p (σ T a b y):=by
 unfold slot; rw [Pi.add_apply,add_sub_add_left_eq_sub,add_sub_add_left_eq_sub,P.flown_shift]
lemma slot_reflection : star (σ T a b y)=σ (P.otherLag j x T) (-b) (-a) (opposeR j y):=by
 have h:opposeR j y j= -y j:= if_pos rfl
 unfold slot; rw [P.flown_star,h,neg_sub_neg,neg_sub_neg]
 exact P.locate_same j x (fun i u=>(if_neg u).symm) _
variable {P j x T a b d e l r}{w:ℝ}
lemma flown_credits (p:(S).Credits w T): (S).Credits w (fun l r=> β T l r y):=by
 intro z u v a h t q g; change ℛ y (T v a)=_
 rw [p h t q g,P.locate_sand]; rfl
lemma slot_credits (p:(S).Credits w T)(h:w<y j-a)(t:w<b-y j)(q:d≤a)(v:b≤e):
 σ T d e y=(S).sand (σ T a b y) (a-d) (e-b):=by
 have x':=flown_credits y p h t (sub_le_sub_left q (y j)) (sub_le_sub_right v (y j))
 rw [show y j-d-(y j-a)=a-d by abel, show e-y j-(b-y j)=e-b by abel] at x'; exact x'
lemma slot_limit {I:Type*}{F:Filter I}{f g:I→ℝ}{r:I→Vantage}{p:Vantage}
 (u:(S).Credits w T)(h:w<p j-a)(t:w<b-p j)(q:Tendsto f F (𝓝 a))(v:Tendsto g F (𝓝 b))(z:Tendsto r F (𝓝 p)):
 BSOT (fun i=>σ T (f i) (g i) (r i)) F (σ T a b p):=by
 have ht:Tendsto (fun i=>r i j) F (𝓝 (p j)):= ((continuous_apply j).tendsto p).comp z
 exact P.locate_limit j x z (u.slide h t (ht.sub q) (v.sub ht))
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
