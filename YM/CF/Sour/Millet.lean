import YM.CF.Sour.Penny
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Sour
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
variable {n:Side}
local notation "SA"=> Seat n
local notation "VX"=> Aura n
local notation "Hk"=> hook SA
open Hake Jet Sault Stax
attribute [local instance] loreM loreN
variable {P:BudgetPoint}{X Y Z:Aura n}{V W:Firing n}{D:Support (More n)}
-- Col weights for ONE letter operator, bounds exact.H uses max; keep h≥1
variable {n':Type*}[LinearOrder n'][Fintype n']
structure Ark (F:FC n')(h v:ℝ):Prop where
 positive:0 ≤ v
 tubes:∀ j:Finset n', (∑ i:Finset n',h^i.card*‖F i j‖)≤v*h^j.card
variable (h:ℝ)(v:1≤ h)
include v
lemma Ark.blond(i:n'):Ark (put i) h h:=by
 have hv:0≤h:=zero_le_one.trans v; refine ⟨hv,fun j=>?_⟩; simp_rw [put_entry]; by_cases p:i∈j; · simp_rw [if_pos p,norm_zero,mul_zero,sum_const_zero]; positivity
 simp_rw [if_neg p,apply_ite _ _]; simp [card_insert_of_notMem p, parity,pow_succ']
lemma Ark.bud(i:n'):Ark (takeF i) h h:=by
 have hv:0≤h:=zero_le_one.trans v; refine ⟨hv,fun j=>?_⟩; simp_rw [take_entry]; by_cases p:i∈j; swap; · simp_rw [if_neg p,norm_zero,mul_zero,sum_const_zero]; positivity
 simp_rw [if_pos p, apply_ite _ _]; simp only [parity,norm_pow,norm_neg,norm_one,one_pow,mul_one,norm_zero,mul_zero,Finset.sum_ite_eq',mem_univ,ite_true]; exact (pow_le_pow_right₀ v (card_le_card (erase_subset ..))).trans (le_mul_of_one_le_left (by positivity) v)
lemma Ark.opus {A B:FC n'}{mQ w:ℝ}(p:Ark A h mQ)(q:Ark B h w):Ark (A*B) h (mQ*w):=by
 refine ⟨mul_nonneg p.positive q.positive,fun j=>?_⟩; have hp(i:Finset n'): h^i.card*‖(A*B) i j‖ ≤∑ k:Finset n', h^i.card*‖A i k* B k j‖:=by rw [←mul_sum,Matrix.mul_apply]; exact mul_le_mul_of_nonneg_left (norm_sum_le ..) (pow_nonneg (zero_le_one.trans v) _)
 apply (sum_le_sum fun i _=>hp i).trans; rw [mul_assoc, sum_comm]; refine le_trans ?_ (mul_le_mul_of_nonneg_left (q.tubes j) p.positive); rw [mul_sum]; apply sum_le_sum; intro i _; simp_rw [norm_mul,←mul_assoc,←sum_mul]; exact mul_le_mul_of_nonneg_right (p.tubes i) (norm_nonneg _)
omit v
lemma Ark.one:Ark (1:FC n') h 1:=by refine ⟨zero_le_one,fun i=>?_⟩; simp only [Matrix.one_apply,apply_ite _ _,mul_ite, norm_one,norm_zero,mul_one,mul_zero, sum_ite_eq',mem_univ,ite_true,one_mul]; rfl
local notation "J"=>Finset (Dwell n)
structure AuraOp(P:BudgetPoint)(X:Aura n)(D:Support (More n))(F:Firing n)(h b:ℝ): Prop where
 pay: ∃ C:J→J→ℝ,(∀ i j,0 ≤ C i j)∧ (∀ j:J,(∑ i:J,h^i.card*C i j)≤ b*h^j.card)∧ ∀ V:Orbit n,V.1 ∈ σX P X D →∀ Z:Support (More n),D⊆Z→∀ i j:Finset (Dwell n),Pence P.order (fun y:tangD n=>F (pressQ P Z V.1 y,V.2) i j) 0 (C i j)
lemma AuraOp.sumR{ι:Type*}(S:Finset ι)(Z:ι→Firing n)(B:ι→ℝ)(p:∀ i∈S,AuraOp P X D (Z i) h (B i)):
 AuraOp P X D (∑ i∈S,Z i) h (∑ i∈S,B i):=by
 induction S using Finset.induction_on with
 |empty=> simp only [sum_empty]; refine ⟨0,fun i j=> le_rfl,fun j=>by simp,fun V _ S _ i j=>?_⟩; exact (show Pence P.order (fun _:tangD n=> (0:ℂ)) 0 0 from (norm_zero (E:=ℂ)) ▸ Pence.const 0 (0:ℂ)) -- tune
 |insert i S g ih=>
    obtain ⟨c,u,z,hZ⟩:=(p i (mem_insert_self ..)).pay; obtain ⟨R,w,p',hR⟩:=(ih fun i j=>p i (mem_insert_of_mem j)).pay; rw [sum_insert g,sum_insert g]; refine ⟨⟨c+R,fun i j=>add_nonneg (u i j) (w i j),?_,fun V t Z p i j=> (hZ V t Z p i j).add (hR V t Z p i j)⟩⟩; intro j; simp only [Pi.add_apply,mul_add,sum_add_distrib,add_mul]; exact add_le_add (z j) (p' j)
lemma AuraOp.sat{mQ w:ℝ}(r: Orbit n→ℂ)(A: FC (Dwell n))(p:Ark A h w)(hx:0≤ mQ)(v:∀ V:Orbit n,V.1∈σX P X D →∀ Z:Support (More n),D⊆ Z→ Pence P.order (fun y:tangD n=>r (pressQ P Z V.1 y,V.2)) 0 mQ):AuraOp P X D (fun i=>r i • A) h (mQ*w):=by
 refine ⟨⟨fun i j=>mQ*‖A i j‖,fun i j=>mul_nonneg hx (norm_nonneg _),fun j=>?_ ,fun V g Z k i j=>?_ ⟩⟩
 · simp_rw [mul_left_comm (_^_) mQ,←mul_sum,mul_assoc]; exact mul_le_mul_of_nonneg_left (p.tubes j) hx
 exact (v _ g _ k).twice (Pence.const (k:=P.order) 0 (A i j))
end YM.CF.Sour
