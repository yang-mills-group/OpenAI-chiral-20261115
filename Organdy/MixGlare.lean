import YM.SU5.Exchange.Stack.Racket
import Organdy.PlateGlare
/- Adapted from YM/SU5/Exchange/Stack/Manor, strengthening fences to movers. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Swell.Palace
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Rill
open Kennel
open Organdy
variable {N:Side}{X Y:SOp N}{o:Seat N}{a b c d v s t Nτ:ℝ}{l q B:ℕ}{p:BudgetPoint}
local notation "Ω"=> Single N
open Sault Leaf
-- mask & support sweep
variable {P W:SOp N}{K:Scree.Loom N}{V M:phy N}{h:ℝ}
namespace Fence
lemma aft {A:Sa N}(f:Fence P W K p q l o h s V a b)(pA:A⊆grooveB l p o):Fence P W K p q l o h s (houseK p A V) a b:=by
 obtain ⟨X,H,T⟩:=f.stock; refine ⟨_,H.mask A pA,fun i=>?_⟩; unfold houseK capR; by_cases u:i∈pingMask p A; rw [Set.indicator_of_mem u,Set.indicator_of_mem u]; exact T i; rw [Set.indicator_of_notMem u,Set.indicator_of_notMem u]; exact JointJ.nil
lemma tee {A:Sa N}(f:Fence P W K p q l o h s V a b)(pA:A⊆grooveB l p o):Fence P W K p q l o h s (V-houseK p A V) (a+a) 0:=by
 obtain ⟨X,H,T⟩:=f.stock; refine ⟨_,H.unmask A pA,fun i=> (T i).dec ?_⟩; unfold houseK capR; by_cases u:i∈ pingMask p A; rw [Set.indicator_of_mem u,Set.indicator_of_mem u]; exact T i; rw [Set.indicator_of_notMem u,Set.indicator_of_notMem u]; exact JointJ.nil -- defeq `Pi.sub` maybe
lemma sumF {ι:Type*}(Y:Finset ι)(V:ι→ phy N)(a b:ι→ℝ)(f:∀ i∈Y,Fence P W K p q l o h s (V i) (a i) (b i)): Fence P W K p q l o h s (∑ i∈Y,V i) (∑ i∈Y,a i) (∑ i∈Y,b i):=by
 induction Y using Finset.induction_on with
 |empty=>rw [sum_empty,sum_empty,sum_empty]; exact Fence.zeroJ
 |insert i S v ih=> rw [sum_insert v,sum_insert v,sum_insert v]; exact (f i (mem_insert_self ..)).arc (ih (fun j p=>f j (mem_insert_of_mem p)))
end Fence
variable (o':Site N) -- remove U
local notation "Uπ" => offsetMask p.B o'
local notation "Vπ" x:max=> offsetMask p.B x
local notation "Λ"=> grooveB l p (node o')
local notation "Nζ" z:max=> o'+gapPlus z B
local notation "Vζ" z:max=> o'-gapPlus z B
variable (E:DockPulse p K t d a h s l q)(hp: Solo a b P d)(w:Solo a b W d)
variable (r:B ≤ p.B)(D:ℝ)
include E hp w
variable {S:SOp N}
lemma locoFee (x:Site N)(u:separation o' x ≤ B) (T:Soak (node o') S a v d): Fence P W K p q l (node o') h s (grantLine K o' x S) (stampCost l p s h a b B *v) (stampCost l p s h a b B*v):=by
 have H:= soak_tr (o':=node o') (co_Ξ x o' (x:=rfl) T) E.hint.le
 have hv:0 ≤ Tenant.quota^2*v:=mul_nonneg (sq_nonneg _) (soakCostNN T); have ht:= trimQ (p:=p) (o:=node o') h E hp w (lift_U H (show _ ≤ Real.exp (a*(4*(2*(B:ℝ))+1))*(Tenant.quota^2*v) from ?_))
 · unfold grantLine stampCost; rw [mul_assoc,mul_assoc]; exact ht
 apply mul_le_mul_of_nonneg_right _ hv; apply Real.exp_le_exp.mpr; have hz:= E.hint.le; apply mul_le_mul_of_nonneg_left _ hz; have h': separation (node x) (node o') ≤ 2*B:=by rw [Hove.ζdist,separation_comm]; omega
 exact add_le_add_left (mul_le_mul_of_nonneg_left (by exact_mod_cast h') (by positivity)) _ -- tune `_`
variable {J T:Axis→ SOp N}
lemma squarePerk (t:∀ i:Axis,Soak (node o') (J i) a v d):Fence P W K p q l (node o') h s (northLine K o' J B) (salvoX l p s h a b B*v) (salvoX l p s h a b B*v):=by
 let C:= stampCost l p s h a b B *v; let G:= fun i:Axis=> (locoFee o' E hp w _ (stopBeam o' i B).1 (t i)).sub (locoFee o' E hp w _ (stopBeam o' i B).2 (t i)); let H:= Fence.sumF univ _ _ _ (fun i _=> G i)
 rw [show salvoX _ _ _ _ _ _ _*v=∑ _i:Axis,(C+C) from ?_]; exact H; simp [salvoX,C]; ring
omit E hp w
include E hp w
variable (hx:p.B+2*B ≤ l*p.B)
include hx
lemma mantlet (t:∀ i:Axis,Soak (node o') (J i) a v d): Fence P W K p q l (node o') h s (highLine K p o' J B) (salvoX l p s h a b B*v) (salvoX l p s h a b B*v):=by
 let C:= stampCost l p s h a b B *v; let X(i:Axis):= stopBeam o' i B; let G:= fun i:Axis=> ((locoFee o' E hp w _ (X i).1 (t i)).aft (offsetFit o' _ (X i).1 hx)).sub ((locoFee o' E hp w _ (X i).2 (t i)).aft (offsetFit o' _ (X i).2 hx)); let H:= Fence.sumF univ _ _ _ (fun i _=> G i)
 rw [show salvoX _ _ _ _ _ _ _ *v=∑ _i:Axis,(C+C) from ?_]; exact H; simp [salvoX,C]; ring
end YM.CF.Swell.Palace
