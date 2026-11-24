import YM.SU5.SatinWard.Resolution.Scarlatti
import ForceSatin.Cygnet
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
open Laurent
variable {P T:SOp N} (E:Pattern P T r d a v)
variable (q:BudgetPoint)(t:Scree.Loom N){k m:ℕ}{g:ℝ} (C:Checked q t g d a k m)
open Salt
open Laurent
open Papyrus.Franc.SatinForce Py.Rate.LocalLimit.Papal.Moon.Cygnet
local notation "Ψ"=>tickA N
noncomputable def beeC (Q:Op (Single N)):ℂ:= Matrix.trace ((tickA N)*Q)- (1/2:ℂ)* Q.trace
noncomputable def enamel (Q:Op (Single N)):Op (Single N):= (tickA N)*Q*(1-tickA N)
theorem startLedger (Q:Op Γ): preHalf (1/2) Ψ Q= beeC Q • 1+ dg (enamel Q):=by unfold beeC preHalf preJ enamel; rw [sub_smul,mul_smul]; push_cast; abel
lemma dg_deduction (S:Support (More N)){T:Op Γ}
 (u:∀ (i j:Γ), T i j ≠0→ node i.1.1∈S∧ node j.1.1 ∈ S) : Papyrus.Franc.SatinForce.Street S 2 (frameR T) (dg T):=by
 unfold frameR dg dyad; apply insum; intro i _; apply insum; intro j _
 by_cases v:T i j=0; · rw [v,zero_smul,norm_zero]; simpa [monomial,rollC] using (Street.enlarge (S:=S) le_rfl (show 0≤2 by omega) (Street.scale 0 Street.one))
 let V:=u i j v; have f(i:Γ)(b:Bool)(l:node i.1.1∈S):Street S 1 1 (Fock.creed b (basisKet i)):=by
    simpa [basisKet] using Street.leg b (node i.1.1) l (basisKet i) (within_basis _ _ ((modes_at ..).mpr (mem_singleton_self _))) -- name creed tune
 let H: Street S (1+1) (1*1) (put i *takeF j):=by rw [←create_put i,←remove_take j]; exact Street.mul (f i false V.1) (f j true V.2)
 rw [show ‖T i j‖=‖T i j‖*(1*1) from (by ring)]; exact H.scale _ -- rw rewrites inside no
lemma inTick (i:Γ) : i∈ Tset N ↔ i.1.2∈plusHalf:= Window.mem_Tset .. -- tune
lemma tickLeft (Q: Op Γ)(i j:Γ): (Ψ * Q) i j= if i.1.2∈ plusHalf then Q i j else 0:=by rw [touchP,Fock.cutM,Matrix.diagonal_mul]; by_cases u:i.1.2∈plusHalf<;>simp [inTick,u]
lemma tickRight (Q: Op Γ)(i j:Γ): (Q*(1-Ψ)) i j= if j.1.2∉ plusHalf then Q i j else 0:=by rw [touchP,mul_sub,mul_one,Fock.cutM,Matrix.sub_apply,Matrix.mul_diagonal]; by_cases u:j.1.2∈plusHalf<;>simp [inTick,u]
lemma enamelBill (Q:Op Γ)(i j:Γ): enamel Q i j=if i.1.2∈plusHalf∧ j.1.2∉plusHalf then Q i j else 0:=by rw [enamel,tickRight,tickLeft]; by_cases h:j.1.2∈plusHalf<;>simp [h]
lemma enamel_frames (Q:Op Γ): frameR (enamel Q)≤ frameR Q:=by refine sum_le_sum fun i _=> sum_le_sum fun j _=>?_ ; rw [enamelBill]; split; exact le_rfl; rw [norm_zero]; exact norm_nonneg _
lemma traceR (Q:Op Γ): ‖Q.trace‖ ≤ frameR Q:= (norm_sum_le ..).trans (sum_le_sum fun i _=> single_le_sum (f:=fun j:Γ=>‖Q i j‖) (fun _ _=>norm_nonneg _) (mem_univ i)) -- implicit type
lemma chargeBee (Q:Op Γ): ‖beeC Q‖ ≤ 2*frameR Q :=by
 unfold beeC; have h: frameR (Ψ * Q) ≤ frameR Q:=by refine sum_le_sum fun i _=>sum_le_sum fun j _=>?_ ; rw [tickLeft]; split; exact le_rfl; rw [norm_zero]; exact norm_nonneg _
 refine (norm_sub_le ..).trans ((add_le_add ((traceR _).trans h) ?_).trans_eq (two_mul _).symm); rw [norm_mul]; exact (mul_le_of_le_one_left (norm_nonneg _) (by norm_num : ‖(1/2:ℂ)‖≤1)).trans (traceR _) -- name
lemma enamel_pass {T:Op Γ} {S:Support (More N)} (u:∀ i j,T i j≠0→ node i.1.1∈ S∧ node j.1.1 ∈ S) (i j:Γ)(g:enamel T i j≠0): node i.1.1∈ S∧ node j.1.1∈ S:= by apply u; rw [enamelBill] at g; split at g; exact g; exact False.elim (g rfl)
lemma horn_F {A:Op Γ} {T:Support (More N)} (p:cutM (modesIn N T)*A*cutM (modesIn N T)=A): Street T 2 (3*frameR A) (Complex.I • preHalf (1/2) (tickA N) A):=by
 rw [startLedger]; refine Street.enlarge ?_ (le_refl _) ((Street.add (Street.enlarge (le_refl _) (show (0:ℕ)≤2 by omega) (Street.scale (beeC A) Street.one)) (dg_deduction T (enamel_pass (scope_cut p)))).scale _); rw [Complex.norm_I,one_mul]; linarith only [enamel_frames A,chargeBee A]
lemma pre_sub (Q G:Op Γ): preHalf (1/2) (tickA N) (Q-G) = preHalf (1/2) (tickA N) Q- preHalf (1/2) (tickA N) G:=by
 have he (Q G: Op Γ): dg (Q-G)= dg Q-dg G :=by simp only [sub_eq_add_neg,dg_add,dg_neg]
 unfold preHalf preJ; rw [mul_sub (tickA N),sub_mul (tickA N*Q), he, Matrix.trace_sub,Matrix.trace_sub,sub_smul,sub_smul,smul_sub]; abel -- parse h type ambiguous
#print axioms horn_F
end AuroraX
end YM.CF.LitCurrent
