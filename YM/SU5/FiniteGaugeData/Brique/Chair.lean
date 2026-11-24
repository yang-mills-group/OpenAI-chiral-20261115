import YM.SU5.FiniteGaugeData.Brique.Wood
import YM.CF.Continuum.Extensive

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 8192
noncomputable section
namespace YM.CF.Fock.Brique
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Spire Scroll Peaks Drapes Rush Tulip Pastry Scree Girt Gall Branch Dial
attribute [local instance] opCStarAlgebra
variable {n:Type*}[LinearOrder n][Fintype n]
local notation "Ω"=> Fintype.card n
local notation "Θ"=> Finset n
local notation "Γ"=> quant
variable {P U:Op n} {x:Wave n} (X:ℝ)
section
variable (A B:FC n) (t:A*B=1)
def shelter : FC n→+* FC n where
  toFun x:= A*x*B
  map_zero':=by simp
  map_one':=by simpa using t
  map_add' x y:=by simp only [mul_add,add_mul]
  map_mul' x y:=by
    have hv:B*A=1:= mul_eq_one_comm.mp t; rw [←mul_assoc A, ←mul_assoc (A*x*B) (A*y), ←mul_assoc (A*x*B) A, mul_assoc (A*x) B A,hv,mul_one]
lemma shelter_v(x:FC n): shelter A B t x=A*x*B:= rfl
lemma shelter_s (x:FC n)(c:ℂ): shelter A B t (c • x)= c • shelter A B t x:= by rw [shelter_v,Algebra.mul_smul_comm,Algebra.smul_mul_assoc]; rfl
lemma shelter_exp (x:FC n): shelter A B t (exp x) = exp (shelter A B t x):=by
 letI: NormedAlgebra ℚ (FC n) := NormedAlgebra.restrictScalars ℚ ℝ _; exact map_exp _ (show Continuous (shelter A B t) from (continuous_const.mul continuous_id).mul continuous_const) _
lemma shelter_act (x:Wave n)(C:FC n) : acts A (acts C x)=acts (shelter A B t C) (acts A x):=by
 rw [shelter_v,act_mul, ←act_mul B,show B*A=1 from mul_eq_one_comm.mp t,act_one,act_mul]
end
local notation "Η"=>scaleUp P X
local notation "Η⁻"=>scaleUp P (-X)
lemma hq (X T:ℝ)(p:IsStarProjection P)(t:X+T=0) : quant (scaleUp P X)*quant (scaleUp P T) = 1:=by rw [←quant_mul,up_mul P X p T,t,up_self,quant_one]
variable (p:IsStarProjection P)
def entryQ:= shelter (Γ (scaleUp P X)) (Γ (scaleUp P (-X))) (hq X (-X) p (by abel))
include p
variable {X} {h:ℝ} (u:0≤ X) (he:Real.exp X+1 ≤ h)
lemma ep_create (x:Ket n) : entryQ X p (create x)=create (acts Η x):= by rw [entryQ,shelter_v,quant_create,mul_assoc,hq _ _ p (by abel),mul_one]
lemma ep_remove (x:Ket n) : entryQ X p (remove x)=remove (acts Η⁻ x):= by rw [entryQ,shelter_v,mul_assoc, quant_ann,←mul_assoc,hq X (-X) p (by abel),one_mul,up_star P _ p] -- tune
-- rework from Graph.billP under this lift. The stake isn't charged for the vacuum column sizes from '‖quant‖^2'
include u he
variable [Nonempty n]
lemma ep_v (i:LeanV n)(V:Op n)(g:IsStarProjection V): ‖entryQ X p (drawT V i)‖ ≤ h := by
 have ht := up_cost P X p; have hr := up_cost P (-X) p; have hu: ‖Η‖ ≤ h:= ht.trans he; have hq: ‖Η⁻‖ ≤ h:= hr.trans (le_trans (by gcongr; linarith) he)
 have hp(A: Op n)(w:‖A‖≤1)(i:n): ‖acts A (basisKet i)‖ ≤ 1:= (Flare.opy A _).trans (by simp [basisKet,w]);
 have he(F:Op n)(k:Ket n)(w:‖F‖≤h)(u:‖k‖≤1) : ‖acts F k‖ ≤ h:= (Flare.opy F _).trans ((mul_le_of_le_one_right (norm_nonneg _) u).trans w) -- scope semicolon fix
 unfold drawT; split; rw [seekF,prong_p,ep_create]; exact (Flare.cost_pe false _).trans (he _ _ hu (hp _ (g.one_sub.norm_le _) _)); rw [hideF,prong_t,ep_remove]; exact (Flare.cost_pe true _).trans (he _ _ hq (hp _ (g.norm_le _) _))

lemma tank_h (V:Op n)(g:IsStarProjection V)(S:ribbon n): ‖entryQ X p (tank V S)‖ ≤ tier h S.val := by
 have hn: 0 ≤ h:=(le_trans (by positivity) he);
 have ht(L:List (LeanV n)):‖entryQ X p (L.map (drawT V)).prod‖ ≤ h^L.length:=by
    induction L with
    | nil=> rw [List.map_nil,List.prod_nil,map_one,List.length_nil,pow_zero,norm_one]
    | cons i L ih=> rw [List.map_cons,List.prod_cons,map_mul, List.length_cons,pow_succ']; exact (norm_mul_le ..).trans (mul_le_mul (ep_v p u he i V g) ih (norm_nonneg _) hn)
 have hW {I: Type _}[LinearOrder I][Fintype I](S:Finset I)(f:I→FC n)(t:∀L:List I, ‖entryQ X p (L.map f).prod‖≤h^L.length) : ‖entryQ X p (Scree.column f S)‖ ≤ h^S.card:=by
    have hx:= t (S.sort (· ≤ ·)); rw [length_sort] at hx; exact hx
 have hΦ (x:FC n) (C:ℂ): entryQ X p (C • x)=C • entryQ X p x := shelter_s ..
 rw [tank,map_sum]; simp_rw [hΦ]; refine (norm_sum_le ..).trans (sum_le_sum fun i (_:i∈ (univ : Finset (Finset (LeanV n))))=>?_); rw [norm_smul,mul_comm (h^_)]; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); exact hW i (drawT V) ht
omit u he p [Nonempty n]
end YM.CF.Fock.Brique
namespace YM.CF.Window
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Fock Spire Scroll Peaks Drapes Rush Tulip Pastry Scree Girt Gall Branch Dial Graph Brique Skye Laic
attribute [local instance] opCStarAlgebra
variable {m N B:Side}{T:GramM N}{X h a b r C:ℝ} (w:Graph.Ledger h a b r C T) (U:Scree.Loom N)(i:ℕ)(z:Orbit N)
set_option quotPrecheck false
local notation "P₀" => spar i T.J.M (U z)
variable (q:IsStarProjection (spar i T.J.M (U z))) (u:0≤ X) (he:Real.exp X+1 ≤ h) (P:Op (Single N)) (v:IsStarProjection P) (η:0 ≤ r)
local notation "Θ"=> entryQ X v
local notation "Γ"=> Fock.quant
local notation "Ε"=> scaleUp P X
include w q u he v
lemma tankV_damped: ‖Θ (tank P₀ (T.board z))‖ ≤ Real.exp ((a+a+b)*(More N).val^4) := by
 have hv : 0≤h:=by linarith [Real.exp_pos X]
 rw [GramM.board,Graph.shape _ _ _ q,map_mul,entryQ,shelter_exp]; change ‖exp (Θ _) * Θ _‖≤ _; rw [add_mul,Real.exp_add]; refine (norm_mul_le ..).trans (mul_le_mul ((bootC _).trans (Real.exp_le_exp.mpr ?_)) ?_ (norm_nonneg _) (Real.exp_pos _).le); exact (tank_h v u he _ q _).trans (marks T z w.reg w.slip hv); exact (tank_h v u he _ q _).trans (toeF w.force hv _)
local notation "A"=> actF i T U z
include η
/-- Damp comparison: in any field assignment, need a full Local projection with rescaled norm at most `b'` extending relative sea. Pay actual trajectory board not trivial field. -/
lemma armed (h':0 ≤ C) {b':ℝ} (f:1 ≤ b') (y:Scree.Phys N)(t:Sea P₀ y)(Z:‖Ε*(1+A)*P₀‖≤b') : ‖acts (Γ Ε) (acts (mile i T U z) y)‖ ≤ Real.exp (flagBill N a b C)*b'^ (Fintype.card (Single N)) := by
 let x:=Pec.pigment T.J.I (U z)
 have hx: ‖-x‖ ≤ pittance N 2 C:=by rw [norm_neg]; exact aurP _ _ w.field.2 (railT _ _ η) (by norm_num:(0:ℝ)≤2)
 have hZ:‖acts (Γ Ε) (acts (exp (dg A)) y)‖ ≤ b'^ (Fintype.card (Single N)):=by
    have hp:A*A=0:=by unfold actF Kennel.capT; simp only [mul_assoc]; rw [←mul_assoc P₀ (1-P₀), Porth q,zero_mul,mul_zero,mul_zero]
    rw [tallied A hp,←act_mul,←quant_mul]; exact Sea_upper q t (Ε*(1+A)) b' f Z
 let L:= tank P₀ (T.board z); let S:=Θ L; have hp:= tankV_damped w U i z q u he P v
 let α:= flagBill N a b C; let δ:= (a+a+b)*(More N).val^4
 have hv:Real.exp (pittance N 2 C)*Real.exp δ ≤ Real.exp α:=by rw [←Real.exp_add]; apply Real.exp_le_exp.mpr; unfold α flagBill doorF lark; exact add_le_add le_rfl (le_add_of_nonneg_right (by positivity))
 rw [mile,act_smul,act_mul,map_smul,norm_smul,shelter_act (Γ (scaleUp P X)) (Γ (scaleUp P (-X))) (hq X (-X) v (by abel))]; refine (le_trans (mul_le_mul ((Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr hx)) ((wing_opy S _).trans (mul_le_mul hp hZ (norm_nonneg _) (Real.exp_pos _).le)) (norm_nonneg _) (Real.exp_pos _).le) ?_); rw [←mul_assoc]; apply mul_le_mul_of_nonneg_right hv (pow_nonneg (zero_le_one.trans f) _) -- hZ & flag
end YM.CF.Window
