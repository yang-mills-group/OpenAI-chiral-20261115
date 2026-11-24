import YM.SU5.SatinWard.Resolution.Rivar
import YM.SU5.SatinWard.Resolution.Carmel
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
local notation "A"=> tickA N
-- Cover-relative cost at any pos first θ.
noncomputable abbrev shore (N:Side)(x y:Cover) : Op (Single N) →ₗ[ℂ] Op _root_.Zephyr.Chern.IS where
 toFun V:= fun i j=> _root_.Zephyr.Chern.lint V x y i j
 map_add' V W:=by ext i j; exact mul_add ..
 map_smul' a G:=by ext i j; exact mul_left_comm ..
local notation "Ψ"=> shore N
local notation "Φ"=> _root_.Zephyr.Chern.tag N
local notation "Ζ"=> _root_.Zephyr.Chern.flag N
lemma shore_one {x y:Cover}(h:(wrap N x= wrap N y)→ x=y): shore N x y 1=(if x=y then 1 else 0):=by
 by_cases hz:x=y
 · subst y; rw [if_pos rfl]; ext i j; rcases i with ⟨_,_⟩; rcases j with ⟨_,_⟩; simp [shore, _root_.Zephyr.Chern.tag, lint,Matrix.one_apply,flag_sq]
 rw [if_neg hz]; ext i j; simp [shore, _root_.Zephyr.Chern.tag,lint, Matrix.one_apply,mt h hz]
variable (D:Division)
abbrev commission(D:Division) : Op SU.Slot:= Matrix.diagonal fun i : SU.Slot=> if existsSlot D i then 1 else 0
abbrev coinPal (D:Division): Op I:= (1:Op SpinIdx) ⊗ₖ commission D
lemma coinPal_at : coinPal D= Matrix.diagonal (fun i=> if existsSlot D i.2 then 1 else 0):=by ext ⟨i,l⟩ ⟨j,c⟩; by_cases s:i=j<;>by_cases t:l=c<;> simp [coinPal,Matrix.one_apply,commission,Matrix.diagonal_apply,s,t]
local notation "H"=>hall D
lemma slice_h {V:Op (Single N)} {z:Site N}{x y: Single N}:
 (V*hall D (houseW z)) x y= if y.1.1=z∧ existsSlot D y.2 then V x y else 0:=by
 let Z:= markG D N; unfold hall houseW; rw [←mul_assoc V,←mul_assoc V,atRight, Fock.cutM, Matrix.mul_diagonal,atRight] -- atRight now once above.Diag cut.StampP. maybe first rw rewrites both
 by_cases h:y.1.1=z<;>by_cases t:existsSlot D y.2<;>simp [inhabit, fortune,h,t]
lemma crestWind (x y z:Cover) (S T:Op (Single N)): (shore N x y (S* hall D (houseW (wrap N z)) * T))= (shore N x z S)*coinPal D*(shore N z y T):=by
 ext i j; rw [coinPal_at,Matrix.mul_apply]; change _=∑ l:I,_ -- which mul rewritten first? `rw` finds inside `shore`? lemma Matrix.mul_apply does not find since under projection. OK.
 change Ζ x * Ζ y * (S * _*T) _ _= _; rw [Matrix.mul_apply, Finset.mul_sum] -- second rewrite maybe ℤx*Ζy
 let L(a b:SpinIdx)(l:SU.Slot):True:=trivial
 simp_rw [Fintype.sum_prod_type, Matrix.mul_diagonal, slice_h] -- order Λ; expr summation over Single & IS
 -- restructure collapse over Site.R.C
 rw [Finset.sum_eq_single (wrap N z)]; swap
 · intro a v h; simp only [h, not_false_eq_true, false_and, if_false, zero_mul, mul_zero, Finset.sum_const_zero] -- tune
 swap; · simp
 refine sum_congr rfl (fun s v=>sum_congr rfl (fun l' t=>sum_congr rfl (fun q v=>?_))); simp only [true_and]; let l:SU.Slot:=(l',q); by_cases hu:existsSlot D l; swap; · dsimp only [l] at hu; simp [hu]
 simp only [hu,if_true,mul_one, show existsSlot D (l', q) from hu]; -- maybe occurrence position, RHS. lhs `if_pos (wrap..) ?` from simp true_and. tune
 change (Ζ x)*(Ζ y)* (S _ (Φ z (s,l))* T (Φ z (s,l)) _)= ((Ζ x)*(Ζ z)* S _ _)* ((Ζ z)*(Ζ y)*T (Φ z (s,l)) _)
 have hp:= flag_sq N z; linear_combination - ((Ζ x)*(Ζ y)* (S (Φ x i) (Φ z (s,l))) *T (Φ z (s,l)) (Φ y j)) * hp -- syntax remove
lemma coast_coat {P:SOp N}{T':SOp N} {a r b:ℝ}(x y:Cover) (P':Op (Single N))(k l:I): _root_.Zephyr.Chern.lint P' x y k l=(shore N x y P') k l:=rfl
end AuroraX
end YM.CF.LitCurrent
