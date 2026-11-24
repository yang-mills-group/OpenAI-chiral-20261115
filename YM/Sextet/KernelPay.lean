import YM.Sextet.Discount
import YM.Sextet.Kernel
 
/-!
# Lemma `eq:exactS2`, spectral formula
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
set_option maxHeartbeats 280000
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

/-- A Vantage uses the Pi coordinates, `Space3` the Euclidean coordinates. -/
def poseSpace (r:Vantage) : Space3 := spatial (WithLp.toLp 2 r)
@[fun_prop] lemma poseSpace_cont : Continuous poseSpace := by
  unfold poseSpace; exact Mink.rest_cont.comp (by fun_prop)

lemma shore_coordinate (r:Vantage) :
    transverse 3 (fun i=>r i.val) = Cheer.shore (poseSpace r) := by
  apply Subtype.ext
  change WithLp.toLp 2 _=position _ _
  apply PiLp.ext; intro i
  refine Fin.lastCases ?_ (fun j=>?_) i
  · exact (show ((transverse 3 _).val) (3:Axis)=0 from (transverse 3 (fun i=>r i.val)).property).trans
      (time_position ..).symm
  have h:j.castSucc ≠ (3:Axis):=Fin.castSucc_ne_last _
  simp [position,poseSpace,spatial,h]
lemma cart_shore (P:Spine) (x:P.Spectrum0 3) (r:Vantage) :
    P.cartage 3 (P.advocate 3 x 3) r=(P.seasons 3 (P.advocate 3 x 3)).U (Cheer.shore (poseSpace r)) := by
  rw [P.uses_cart,shore_coordinate]

open Sextet
private lemma wall_help {H:Hilbert} (S:OS.Semigroup H timeAxis) (y:Space3) (t a:ℝ≥0) (v:H) :
    S.U (Cheer.shore y) (S.E t (v - S.E a v))=
      S.ℚmeasure.price (flightTag y t*lessLight a) v := by
  rw [S.ℚmeasure.price_mul (flight_cost ..) (less_cost a),less_op,flight_op]
  rfl

variable (P:Spine) (x:P.Spectrum0 3) (Z Y:Lead.Clan) (s n:ℕ)
local notation "S"=> P.seasons 3 (P.advocate 3 x 3)
local notation "Q"=>(S).ℚmeasure

/-- The new projected signal has *no* zero time energy. -/
theorem macroVector_dark : (Q).region darkSet (P.macroVector x Z s n)=0 := by
  rw [P.macroVector_formula]
  exact less_dark (S) _ _

theorem wall_formula (c:ℝ) (r:Vantage) :
    P.vectorWall x s n Z c r =
     (Q).price (flightTag (poseSpace r) (toWall c (r 3))*lessLight (P.advanceHeat s n))
       (P.birthCloud x Z s n) := by
  unfold vectorWall
  rw [P.macroVector_formula,P.cart_shore]
  exact wall_help .. 

theorem wall_dark (c:ℝ) (r:Vantage) : (Q).region darkSet (P.vectorWall x s n Z c r)=0 := by
  rw [P.wall_formula]
  exact price_dark (S) _ (flight_cost ..) _

theorem kernel6_tag (r:Vantage) :
    P.kernel6 x s n r Z Y=
      (Q).crossIntegral (P.birthCloud x Z s n) (P.birthCloud x Y s n)
        (signalTag (P.advanceHeat s n) (poseSpace r) (r 3).toNNReal) := by
  unfold kernel6
  rw [P.cart_shore,P.macroVector_formula,P.macroVector_formula]
  exact signal_formula (S) (P.advanceHeat s n) (r 3).toNNReal (poseSpace r) _ _

/-- Unclamped formula as in `eq:exactS2`. Coordinates of displacement `r` and
heat increments (even those occurring in the stored `F`) here in **physical** units,
so energy-momentum integrals with that conjugate scaling. -/
theorem kernel6_exactS2 (r:Vantage) (h:0≤r 3) :
    P.kernel6 x s n r Z Y=
      (Q).crossIntegral (P.birthCloud x Z s n) (P.birthCloud x Y s n)
        (fun p=>
          Complex.exp (Complex.I * ⟪poseSpace r,spatial p⟫_ℝ -
              ((r 3:ℂ)*(p timeAxis:ℂ))) *
          ((1:ℂ)- Real.exp (-((P.advanceHeat s n:ℝ)*p timeAxis)))^2) := by
  rw [P.kernel6_tag]
  apply Spectral.PVM.crossIntegral_congr; intro u
  filter_upwards [(S).bright u] with p hp
  simp only [signalTag, Pi.mul_apply,flightTag,lessLight,Pi.sub_apply,Pi.one_apply,phasor,
    real_inner_comm (poseSpace r),charge_bright _ _ hp,OS.Semigroup.Balloon.tinct,Real.coe_toNNReal _ h]
  rw [pow_two,←mul_assoc,Complex.ofReal_exp,←Complex.exp_add]
  push_cast; rw [mul_comm _ Complex.I]; rfl

end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
