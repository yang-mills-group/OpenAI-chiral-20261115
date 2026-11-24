import Compass.Energy
import YM.CF.Ione.Crore
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 25000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Compass
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Urn Hake Pastry Salt Hive Vow Skye Scion Levier Spire Scree Stilo
attribute [local instance] opCStarAlgebra
variable {n:Type*}[LinearOrder n][Fintype n]
open Nacre Ione
variable {N:Side}(U:UNI SpinIdx)
-- site = sparse every column even rotations
lemma ayes (p:Moncol U.val)(a:Shape)(b:Bool):Moncol (siteU a b U N).val:=by
 constructor
 intro i j k
 rcases i with ⟨⟨x,i⟩,t⟩; rcases j with ⟨⟨y,j⟩,v⟩; rcases k with ⟨⟨z,k⟩,w⟩
 let T:= Tofu a N
 have ℓ (m:Site N)(d:SpinIdx)(u:Slot) (h:(siteU a b U N).val ((m,d),u) ((x,i),t) ≠0) : T m=x ∧ u=t ∧ U.val d i≠0:=by
    change jump T (fun i=>(milU a U (xtra b) i).val) (m,(d,u)) (x,(i,t))≠0 at h; rw [jump_apply] at h
    split at h; swap; · contradiction
    rename_i ha; refine ⟨ha,?_,?_ ⟩
    · by_contra hb; apply h; change (a.payA m) • (U.val d i*(1:Op Slot) u t) = 0; rw [Matrix.one_apply_ne hb,mul_zero,smul_zero]
    intro hb; apply h; change (a.payA m) • (U.val d i*_)=0; rw [hb,zero_mul,smul_zero]
 intro h u; obtain ⟨h1,h2,h3⟩:=ℓ y j v h; obtain ⟨u1,u2,u3⟩:=ℓ z k w u
 exact Prod.ext (Prod.ext (T.injective (h1.trans u1.symm)) (p.subsingle i j k h3 u3)) (h2.trans u2.symm)
lemma spicy (M:UNI n)(t:Moncol M.val)(b:Bool): Moncol (spice M b).val:=by
 constructor; rintro ⟨a,i⟩ ⟨p,j⟩ ⟨w,k⟩ h u
 suffices p=w ∧ j=k from Prod.ext this.1 this.2
 constructor
 · rw [Urn.cream] at h u; split at h; next h' => split at u <;> rename_i u' <;> first|exact h'.trans u'.symm|contradiction
   contradiction
 exact t.subsingle i j k (fun t'=>h (spice_E M b (p,j) (a,i) t')) (fun t'=>u (spice_E M b (w,k) (a,i) t'))
lemma fiery {n:Type*}[DecidableEq n][Fintype n](M:UNI n)(t:Moncol M.val)(j:n):∑ i:n,‖M.val i j‖ ≤1:=by
 classical
 by_cases p:∃ i, M.val i j≠0
 · obtain ⟨i,v⟩:=p; rw [sum_eq_single i]; swap; · intro l _ h; rw [show M.val l j=0 from not_not.mp (fun w=>h (t.subsingle j l i w v)),norm_zero]
   swap; · simp
   rcases isEmpty_or_nonempty n
   · exact False.elim (isEmptyElim j)
   exact (norm_entry ..).trans (CStarRing.norm_of_mem_unitary M.property).le
 rw [sum_eq_zero (fun i _ => by rw [show M.val i j=0 from not_not.mp (fun w=>p ⟨i,w⟩),norm_zero])]; exact zero_le_one
end YM.CF.Compass
