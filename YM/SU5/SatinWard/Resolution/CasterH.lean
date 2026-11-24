import YM.SU5.SatinWard.Resolution.Dolio
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
private abbrev plumI (g:Fin 3) (i:Fin 3) :ℂ:=if i=g then 1 else 0
noncomputable abbrev diagI (g:Fin 3) : Op (Fin 3):= Matrix.diagonal (fun i:Fin 3=>if i=g then 1 else 0)
lemma I_star (g:Fin 3):star (diagI g) = diagI g:=by ext i j; by_cases p:i=j<;> simp [diagI,Matrix.diagonal_apply,p, Ne.symm, apply_ite star]
noncomputable abbrev phaseI (b:Bool)(g:Fin 3) : Soul:= patchH b (diagI g) (I_star g)
lemma pointI_here (b:Bool)(g:Fin 3): generation b (phaseI b g)=1:= by
 change Treaty.zen _ = _; rw [phaseI,patch_here,Treaty.zen,diagI,Matrix.trace_diagonal, sum_eq_single g]; all_goals simp +contextual
lemma pointI_away (b:Bool)(g:Fin 3): generation (!b) (phaseI b g) = 0:=by change Treaty.zen _ = _; rw [phaseI,patch_away,Treaty.zen,Matrix.trace_zero]; rfl
-- pin.. matrix test. in particular unit label at β height in that packet. explicitly the projection. time Ink future
noncomputable def orbitalI (b:Bool)(g:Fin 3): Op SU.Slot:= Matrix.diagonal (fun i:SU.Slot=>if i.1=g∧SU.charge i∈ sectF b then 1 else 0)
lemma spoke_here (b:Bool)(g:Fin 3): dynamicSpin (phaseI b g)= orbitalI b g:=by
 change (Reg (phaseI b g)).val=_; rw [←score_bracket,phaseI]; cases b
 · rw [patch_here, show ribbon true (patchH false (diagI g) (I_star g))=0 from patch_away false _]; ext ⟨i,a⟩ ⟨j,d⟩; all_goals (cases a<;>cases d<;>by_cases p:i=j <;> by_cases q:i=g <;> simp [orbitalI,diagI,sonnet,Mezzo.suite,Mezzo.leaf, Join.both, existsSlot, sectF, SU.charge,Matrix.diagonal_apply,Matrix.one_apply,p,q] at * <;> aesop)
 rw [patch_here, show ribbon false (patchH true (diagI g) (I_star g))=0 from patch_away true _]; ext ⟨i,a⟩ ⟨j,d⟩; all_goals (cases a<;>cases d<;>by_cases p:i=j <;> by_cases q:i=g <;>simp [orbitalI,diagI,sonnet,Mezzo.suite,Mezzo.leaf, Join.both, existsSlot, sectF, SU.charge,Matrix.diagonal_apply,Matrix.one_apply,p,q] at * <;> aesop)
noncomputable abbrev warTax (r:ℕ):ℝ:= 1/(shortTime r*3)
lemma traceI (b:Bool)(g:Fin 3)(p:0<r): phaseI b g-warTax r • coreTrace b r∈ depth:=by
 have ht:=short_live p; apply (depth_iff _).2; intro i; have hi:i=b∨i= (!b):=by cases b<;> cases i<;>simp
 cases hi with | inl h=> rw [h,map_sub,map_smul,corePay_here,pointI_here,warTax,smul_eq_mul,div_mul_cancel₀ 1 (ne_of_gt (by positivity: 0<shortTime r*3)),sub_self]; | inr h=>rw [h,map_sub,map_smul,corePay_away,pointI_away,smul_zero,sub_self]
#print axioms spoke_here
#print axioms traceI
end AuroraX
end YM.CF.LitCurrent
