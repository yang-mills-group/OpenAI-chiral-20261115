import YM.SU5.Assay.Credits
import YM.SU5.Six.TransitWall
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
/-! Displacement on the transversely continuous space of this very color
 character. Real everywhere. -/
abbrev locate (y:Vantage)(T:Y):Y:= W y*T*W (-y)
local notation "ℛ"=> P.locate j x
lemma cart_star (y:Vantage): star (W y)= W (-y):=P.cart_reverses j x y
lemma cart_splice (y z:Vantage): W y*W z=W (y+z):= (P.cart_paves ..).symm
lemma cart_null : W 0=1:= P.cart_zero j x
lemma cart_wax (y:Vantage)(t:ℝ): W y*ω t=ω t*W y:=
   ContinuousLinearMap.ext fun _=> (P.warm_drive ..).symm
lemma cart_same {y z:Vantage}(p:∀i≠j,y i=z i):W y=W z:=
 congrArg ((P.voyageF j x).aviation _ _) (funext fun i=>p i.val i.property)
lemma cart_pin (y:Vantage):BSOT (P.cartage j x) (𝓝 y) (W y):=by
 refine ⟨⟨1,by norm_num,Eventually.of_forall (P.cart_pay j x)⟩,fun _=>(P.cart_cont ..).tendsto _,?_⟩
 intro u; simp only [P.cart_star]; exact ((P.cart_cont j x u).comp continuous_neg).tendsto y
lemma cart_pin' {I:Type*}{l:Filter I}{f:I→Vantage}{y:Vantage}(p:Tendsto f l (𝓝 y)):
   BSOT (fun i=> W (f i)) l (W y):= (P.cart_pin j x y).visit p
lemma cart_vac (A:Y)(y:Vantage):ℛ y A Ω= W y (A Ω):=by
 change W _ (A (W _ Ω))=_; rw [P.cart_empty]
lemma cart_wash (A:Y)(y:Vantage): inner ℂ Ω (ℛ y A Ω) = inner ℂ Ω (A Ω):=by
 rw [P.cart_vac]; have ht:= P.inner_pay j x y Ω (A Ω); rw [P.cart_empty] at ht; exact ht

lemma locate_star (p:Vantage)(A:Y): star (ℛ p A)=ℛ p (star A):=by
 unfold locate; rw [star_mul,star_mul,P.cart_star,P.cart_star,neg_neg,mul_assoc]
lemma locate_credit (p:Vantage)(A:Y): ‖ℛ p A‖≤ ‖A‖:= by
 refine (norm_mul_le ..).trans ((mul_le_of_le_one_right (norm_nonneg _) (P.cart_pay ..)).trans ?_)
 exact (norm_mul_le ..).trans (mul_le_of_le_one_left (norm_nonneg _) (P.cart_pay ..))
lemma locate_sand (p:Vantage)(A:Y)(a b:ℝ): ℛ p ((S).sand A a b)= (S).sand (ℛ p A) a b:=by
 unfold locate sand; rw [←mul_assoc _ _ (ω b),←mul_assoc _ (ω a) A, P.cart_wax j x p]
 rw [mul_assoc _ (ω b), ←P.cart_wax j x (-p) b]; simp only [mul_assoc]
lemma locate_add (p:Vantage)(A L:Y): ℛ p (A+L)= ℛ p A+ℛ p L:=by unfold locate; rw [mul_add,add_mul]
lemma locate_sub (p:Vantage)(A L:Y): ℛ p (A-L)= ℛ p A-ℛ p L:=by unfold locate; rw [mul_sub,_root_.sub_mul]
lemma locate_smul (p:Vantage)(A:Y)(a:ℂ): ℛ p (a•A)= a • ℛ p A:=by unfold locate; rw [mul_smul_comm,smul_mul_assoc]
lemma locate_zero (A:Y): ℛ 0 A=A:=by unfold locate; rw [neg_zero,P.cart_null,one_mul,mul_one]
lemma locate_sum (p q:Vantage)(A:Y):ℛ p (ℛ q A)=ℛ (p+q) A:=by
 unfold locate; rw [←mul_assoc _ _ (W (-q)),←mul_assoc _ (W q) A,P.cart_splice]
 rw [mul_assoc _ (W (-q)), P.cart_splice, neg_add_rev]
lemma locate_cancel (p:Vantage)(A:Y): ℛ (-p) (ℛ p A)=A:=by rw [P.locate_sum,neg_add_cancel,P.locate_zero]
lemma locate_cost (p:Vantage)(A:Y): ‖ℛ p A‖= ‖A‖:= le_antisymm (P.locate_credit ..) (by
   nth_rw 1 [←P.locate_cancel j x p A]; exact P.locate_credit ..)
lemma locate_vac_cost (p:Vantage)(A:Y): ‖ℛ p A Ω‖= ‖A Ω‖:=by rw [P.cart_vac,P.cart_norm]
lemma locate_same {p q:Vantage}(h:∀i≠j,p i=q i)(A:Y):ℛ p A= ℛ q A:=by
 unfold locate; rw [P.cart_same j x h,P.cart_same j x (y:= -p) (z:= -q) (fun _ e=>congrArg Neg.neg (h _ e))]
lemma locate_limit {I:Type*}{l:Filter I}{A:Y}{f:I→Vantage}{y:Vantage}{g:I→Y}
    (p:Tendsto f l (𝓝 y))(u:BSOT g l A):BSOT (fun i=> ℛ (f i) (g i)) l (ℛ y A):=
 ((P.cart_pin' j x p).mul u).mul (P.cart_pin' j x p.neg)
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
