import YM.SU5.SatinWard.Resolution.LatticeFieldEstimates
import YM.SU5.SatinWard.Resolution.ColourFrame
import YM.SU5.SatinWard.Resolution.ShoreE
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 350000
noncomputable section
namespace YM.CF.LitCurrent
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour
open Stax Skye Jet Scroll Finset Palot Cadre Vow RG Rive Nor Hake MeasureTheory
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical Kronecker
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Rill
open Kennel Swell StressExchange
variable {N:Side}{X Y:SOp N}{o:Seat N}{a b c d v:ℝ}{r:ℕ}
local notation "Γ" => Single N
open Buffered _root_.Zephyr.Chern
open IndexMag Chamber Surplus
namespace AuroraX
local notation "I"=> _root_.Zephyr.Chern.IS
open Py.Rate.LocalLimit.Preparation QuadClock ShapeLab SoulField Mezzo Treaty
abbrev sectF (b:Bool):Division:= if b then {2} else {4}
abbrev shortTime (r:ℕ) :ℝ:= bmass r/(2*(r:ℝ))
noncomputable abbrev coreTrace (b:Bool)(r:ℕ): Soul:= shortTime r • genCore b
lemma priceSpinH (z:Soul)(q:ℝ):dynamicSpin (q • z)= q • dynamicSpin z:= congrArg (fun x: ↥chiralModule=>x.val) (map_smul Reg q z)
#check sonnet
lemma core_stamp (b:Bool): commission (sectF b)=dynamicSpin (genCore b):=by
 change _=(Reg (genCore b)).val; rw [←score_bracket,genCore]; cases b
 · rw [patch_here, show ribbon true (patchH false 1 (star_one _))=0 from patch_away false _]; ext ⟨i,a⟩ ⟨j,d⟩ -- wrong RC tag pair ext `ext ⟨i,a⟩ ...`
   all_goals (cases a<;> cases d <;> by_cases p:i=j <;> simp [commission,sonnet, Mezzo.suite,Mezzo.leaf, Join.both, existsSlot, sectF, SU.charge,Matrix.diagonal_apply,Matrix.one_apply,p])
 rw [patch_here, show ribbon false (patchH true 1 (star_one _))=0 from patch_away true _]; ext ⟨i,a⟩ ⟨j,d⟩; all_goals (cases a<;>cases d<;>by_cases p:i=j<;>simp [commission,sonnet,Mezzo.suite,Mezzo.leaf,Join.both,existsSlot,sectF,SU.charge,Matrix.diagonal_apply, Matrix.one_apply,p])
lemma short_live (h:0<r) :0< shortTime r:=by unfold shortTime bmass; positivity
lemma core_motion (b:Bool): coreTrace b r∈ pureHeart:= by
 refine Submodule.smul_mem _ _ (Submodule.subset_span ?_); cases b <;> simp
lemma corePay_here(b:Bool): generation b (coreTrace b r) = shortTime r * 3:=by rw [coreTrace,map_smul,core_bill]; rfl
lemma corePay_away(b:Bool): generation (!b) (coreTrace b r) = 0:=by rw [coreTrace,map_smul,core_other,smul_zero]
lemma corePay_ne(b:Bool)(h:0<r) : coreTrace b r ≠0:=by
 intro a; have ht:=congrArg (generation b) a; rw [corePay_here,map_zero] at ht; have h:= short_live h; exact ne_of_gt (show 0 < shortTime r * 3 by positivity) ht
#print axioms core_stamp
end AuroraX
end YM.CF.LitCurrent
