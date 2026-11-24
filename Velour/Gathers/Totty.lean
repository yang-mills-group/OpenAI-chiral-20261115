import Velour.Tassel.Jewel
import Velour.Gathers.Hem
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Casting Six OS.Semigroup.Balloon



open MacroGrid SatinNucleus Velour

variable (P:Spine)(j:Axis)(x:P.Spectrum0 j)
local notation "H"=> P.ColorHil j x
local notation "S"=> P.physicalEnergy j x
local notation "τ"=>P.macroStep
open OS.Semigroup

lemma hem_time : Antitone τ := by
  refine antitone_nat_of_succ_le fun k=>(P.halvesClock k).trans ?_
  exact (half_lt_self (P.macroStep_pos k)).le

def priceCap (T:P.Apron)(k:ℕ):(P.ColorHil j x).Op:=
  T.velour P j x (T.realWidth P j + τ k)
lemma priceEq (T:P.Apron)(k:ℕ):
    P.priceCap j x T k=(S).pad (τ k) (τ k) (T.engine P j x):=by
 unfold priceCap Apron.velour Apron.dye
 rw [add_sub_cancel_left]
def Totty (T:ℕ→P.Apron):Prop:=
  Costly (P.ColorHil j x) (fun k i=>P.priceCap j x (T i) k)

lemma price_le (T:P.Apron)(k:ℕ):
    ‖P.priceCap j x T k‖ ≤ ‖T.engine P j x‖:=by
 rw [priceEq]; exact (S).pad_le ..
lemma price_mono (T:P.Apron) {k l:ℕ}(e:k ≤ l):
    ‖P.priceCap j x T k‖ ≤ ‖P.priceCap j x T l‖:=
 T.velour_le P j x (le_add_of_nonneg_right (P.macroStep_pos l).le)
      (by gcongr; exact P.hem_time e)


namespace Totty
variable {P j x}
variable {T:ℕ→P.Apron} {A F:ℝ}

lemma of_tail (m:ℕ)(a:1≤A)(b:1≤F)
   (h:∀ᶠ i:ℕ in atTop, ∀ k:ℕ, m≤k → ‖P.priceCap j x (T i) k‖ ≤ A*F^k):
   P.Totty j x T:=by
 obtain ⟨N,u⟩:=eventually_atTop.mp h
 let c:=∑ i∈Finset.range N, ‖(T i).engine P j x‖
 have z:0≤c:=Finset.sum_nonneg (fun _ _=>norm_nonneg _)
 have e:1≤ A*F^m:= one_le_mul_of_one_le_of_one_le a (one_le_pow₀ b)
 refine ⟨A*F^m + c,F,e.trans (le_add_of_nonneg_right z),b,fun k i=>?_⟩
 by_cases q:N ≤ i
 · have y:=u i q (m+k) (by omega)
   rw [pow_add,←mul_assoc] at y
   exact (P.price_mono j x (T i) (by omega:k ≤ m+k)).trans
      (y.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right z) (zero_le_one.trans (one_le_pow₀ b))))
 have t:‖(T i).engine P j x‖ ≤ c:= single_le_sum (f:=fun i=> ‖(T i).engine P j x‖) (fun _ _=> norm_nonneg _) (Finset.mem_range.mpr (by omega:i<N))
 refine (P.price_le j x (T i) k).trans (t.trans ((le_mul_of_one_le_right z (one_le_pow₀ b (n:=k))).trans ?_))
 exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (zero_le_one.trans e)) (zero_le_one.trans (one_le_pow₀ b))

-- permits spending the available budget asymmetrically
lemma capdyes (h:P.Totty j x T) (l r:ℕ→ℕ→ℝ)
   (p:∀k i, (T i).realWidth P j+τ (k+1) ≤ l k i)
   (q:∀k i, (T i).realWidth P j+τ (k+1) ≤ r k i) :
   Costly (H) (fun k i=>(T i).dye P j x (l k i) (r k i)):= by
 unfold Totty at h
 refine h.shift.smaller fun k i=> ?_
 have z: (T i).realWidth P j ≤ (T i).realWidth P j + τ (k+1):=
     le_add_of_nonneg_right (P.macroStep_pos _).le
 exact (T i).dye_le P j x z z (p k i) (q k i)

end Totty
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

