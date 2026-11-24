import YM.CF.Vp929.Pre.Ambit
import Gingham.Linen.Hank
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Py.Rate
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator ComplexConjugate
open Forge Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Vow Salt
open Ione Beau Haro Cascade
open scoped Mew
open Mew
variable {X Y:Type*}{n:Side}{P:BudgetPoint}{h v w:ℝ}{F:RegBudget n}{K:ForceBudget n}{t:Cusp n}
open Pressure
open Push.AbsoluteSums Trees Ursell Push.AbsoluteSums.Graph Bake Gas Wray Larch Nor
variable {a s d δ γ:ℝ}{G H:Pax n}
variable (p:0<d)(vx:0≤a)(h':1≤h)
open Wray
-- sweep obligations. elementary linear algebra lemmas.
open Lilt
namespace Cash
variable {F G:Pax n}(τ:Ids n)(pL:MonoQ P h (prominence P) F w)(pA: poise F)

include pA h' pL
local notation "dF"=> due τ F
local notation "fQ"=> Cash.returnV τ P F
lemma priceRun_two : IncX Utrue (Cash.earn τ P F) P.raisin h (reserveT P.power P.order P.B 1*(w+w)):=by
 obtain ⟨S,T,V⟩:= charter h' τ pL; have hc(X:Aura n):Vow.Medal P X.val ∅ (cashV dF X) h (S X):= (Medal.oneT.rum (dF X)).big (by rw [mul_one]; exact T X)
 let H:MonoQ P h (prominence P) (F-cashV dF) (w+w):= pL.sub ⟨S,hc,V⟩; obtain ⟨L,b,q⟩:=H; exact worth_two P fQ τ (booths τ pA).2 (booths τ pA).1 (zero_le_one.trans h') (fun i=>zen_B P (b i)) q
end Cash

variable {k:ℕ}(hk:FeeBook k γ 1)
include hk
namespace FeeBook
lemma halve : FeeBook k (γ/2) 1 ∧ degreePrice k (γ/2) 1 ≤ 1/2 := by
 have he: degreePrice k (γ/2) 1 = degreePrice k γ 1 / 2 := by
   unfold degreePrice Trees.stretch; ring
 have v:0<γ/2:= half_pos hk.coal
 refine ⟨⟨v,zero_lt_one, ?_, ?_⟩, ?_⟩
 all_goals rw [he]
 · linarith only [hk.rate]
 · exact div_nonneg hk.nominal (by norm_num)
 linarith only [hk.rate]

open Push.AbsoluteSums.Animals in
lemma capped : γ≤1 := by
 apply le_trans _ hk.rate.le
 unfold degreePrice Trees.stretch; rw [div_one]
 exact le_trans (le_mul_of_one_le_left hk.coal.le (show (1:ℝ)≤(ballCost k:ℝ) by exact_mod_cast neighbors_ge k))
   (le_mul_of_one_le_left (by have:=hk.coal; positivity) (by norm_num))

lemma thin_fee : ticket_f k (γ/2) 1 ≤ 1 := by
 let x:=degreePrice k (γ/2) 1; have h : x≤1/2:= hk.halve.2
 change γ/2*(1-x)⁻¹ ≤ _
 rw [←div_eq_mul_inv,div_le_iff₀ (by linarith : 0<1-x)]
 linarith only [hk.capped,h]

end FeeBook
omit hk
open Jet
lemma spicy6 : (1:ℝ)≤chi_f 6 := by
 norm_num [chi_f,Jet.composeCost,Nat.factorial]


open Linen PolyBill in
lemma coin_n_bill (n m : ℕ): PolyBill (coin_n n m) := by
 have k: PolyBill stilK := (PolyBill.const (by norm_num)).mul
          (PolyBill.mid.plus (PolyBill.const zero_le_one))
 let V:=k.expN n
 exact V.mul ((PolyBill.const (by positivity)).mul (((PolyBill.const (by norm_num)).mul V).expN m))

open Linen
lemma reserveT_bill (n m:ℕ) {a:ℝ}(s: 0≤a): PolyBill (fun b=> reserveT n m b a) :=
   (coin_n_bill n m).mul (PolyBill.const (by positivity))

/-- poly(b) cap for tapped, height fixed as in request -/
def bill_tap (b:ℕ):ℝ:= wren_K 6 2 + reserveT 2 6 b 1*(2+2)
lemma poly_tap : PolyBill bill_tap:=
 (PolyBill.const (add_nonneg zero_le_one (lucre ..))).plus ((reserveT_bill _ _ zero_le_one).mul (PolyBill.const (by norm_num)))
#print bill_tap
#print axioms poly_tap

