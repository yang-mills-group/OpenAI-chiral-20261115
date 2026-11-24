import YM.CF.BProof.Oasis.Tube
/-! Pay the larger covers (radius from coverNumber). This handles the collars
also for regular-only, even when the Mark frame sum is varied. -/
set_option autoImplicit false
set_option synthInstance.maxSize 16000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BProof.Oasis
open Function Filter Fock Finset NormedSpace Garden Align Wick Double Pastry Crystal MeasureTheory Dew
open Lattice Tenant Lat Cube Tulip Scree Skye Spin Branch Stint Hearth Tape Palot RG Push.AbsoluteSums
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator Classical Hearth ENNReal
attribute [local instance] opCStarAlgebra
variable {N:Side}
def wageV (r v:ℝ)(k:ℕ):ℝ:= v*(1+r)^4 * ppT 1 k -- tweak k/2
abbrev payV(r v:ℝ):= v*(1+r)^4 * puffPrice (1/2)
section Bills
variable {V:Type}[Fintype V]{f: V→Seat N}{q:V→ Support (More N)}{P:BudgetPoint}{u:V→ℕ}{w:V→ℝ}{C:ℝ}
def heroes (f:V→Site N)(g:V→ℕ)(w:V→ℝ)(i:Site N):= ∑ j:V with i=f j, w j*Real.exp (g j)
lemma forward {r:ℕ}(h:∀ i, (q i).card ≤ r*u i)(v:∀ i,w i≠0 →Grove (terr _) (q i))(p:∀ i,w i≠0→ f i∈q i)(x:∀ i,0≤ w i)(t:∀ i,heroes f u w i≤ C){a:ℝ}(g:0≤a)(e:a*r ≤ 1/2): Moment.Toll q w a (payV r C):=by
 apply (tollPrice q x _ _).mpr; intro o; let A(o:Site (More N))(j:V):= if o∈ q j then w j*rent a (q j) else 0; unfold Gas.bill_X; rw [sum_filter]; change ∑ j:V,A o j≤_; let S:=univ.image u
 have hz:Summable (ppT (1/2)):= by convert fund_hit 1 16 (by linarith : (0:ℝ)<1) (by norm_num) using 1; funext i; unfold ppT; ring_nf
 have hC:0≤C:= le_trans (sum_nonneg (fun j _=>mul_nonneg (x _) (Real.exp_pos _).le)) (t o)
 have he(k:ℕ)(y:Site (More N)): (∑ j∈(univ.filter fun j=>u j=k).filter (fun j=>y=f j), A o j) ≤ if y∈ Branch.bay (terr (More N)) o (r*k) then C*Real.exp (-(k:ℝ)/2) else 0:=by
    let T:=Branch.bay (terr (More N)) o (r*k); let z:=Real.exp (-(k:ℝ)/2); by_cases g':y∈T
    · rw [if_pos g']; apply le_trans (b:=heroes f u w y * z) _ (mul_le_mul_of_nonneg_right (t _) (Real.exp_pos _).le); unfold heroes; rw [sum_mul]; refine le_trans (sum_le_sum (g:=fun i=> (w i*Real.exp (u i))*z) (fun i (hi)=>?_)) (sum_le_sum_of_subset_of_nonneg (fun _ hh=>mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hh).2⟩) (fun i _ _=>mul_nonneg (mul_nonneg (x _) (Real.exp_pos _).le) (Real.exp_pos _).le)); unfold A; split; swap; · exact mul_nonneg (mul_nonneg (x _) (Real.exp_pos _).le) (Real.exp_pos _).le
      have hk:= (mem_filter.mp (mem_filter.mp hi).1).2; rw [mul_assoc,hk]; apply mul_le_mul_of_nonneg_left _ (x _); unfold rent z; rw [← Real.exp_add]; apply Real.exp_monotone; have hp:=h i; rw [hk] at hp; have hl: ((q i).card:ℝ) ≤ r*(k:ℝ):=by exact_mod_cast hp
      nlinarith [mul_le_mul_of_nonneg_left hl g,mul_le_mul_of_nonneg_right e (Nat.cast_nonneg k)]
    rw [if_neg g', sum_eq_zero (fun i hi=>?_ )]; unfold A; split; rename_i b; · by_cases w':w i=0; rw [w',zero_mul]; apply False.elim (g' _); have hk:= mem_filter.mp hi; rw [hk.2]; apply (Branch.bay_mem _).mpr; exact ((v i w').lim o b _ (p i w')).le.trans ((h i).trans_eq (by rw [(mem_filter.mp hk.1).2]))
    rfl
 rw [←sum_fiberwise_of_maps_to (t:=S) (g:=u) (fun i _=> mem_image_of_mem _ (mem_univ _))]; refine le_trans (sum_le_sum (g:=fun k=> C*(1+r:ℝ)^4 * ppT (1/2) k) (fun k _=>?_)) (by rw [←mul_sum]; exact mul_le_mul_of_nonneg_left (hz.sum_le_tsum S (fun i _=>by unfold ppT; positivity)) (by positivity))
 let U:= (univ:Finset V).filter fun i=> u i=k; have hh : ∑ j∈U,A o j=∑ y:Site (More N),∑ j∈U with y=f j,A o j:=by rw [← sum_fiberwise U f]; congr 1; ext; simp only [eq_comm]; -- tune
 rw [hh]; apply (sum_le_sum (fun i _=> he k i)).trans; rw [← sum_filter,filter_mem_eq_inter, univ_inter,sum_const,nsmul_eq_mul]; have hx:=Tenant.reach o (r*k); unfold ppT; rw [show (-((k:ℕ):ℝ)/2)= (-(1/2:ℝ))*k by ring]; refine le_trans (mul_le_mul_of_nonneg_right hx (by positivity)) ?_; push_cast; let m:= C * Real.exp (-(1/2:ℝ)*k); apply le_trans (b:= 16*((1+r:ℝ)*(k+1))^4*m); · gcongr; nlinarith [Nat.cast_nonneg (α:=ℝ) r,Nat.cast_nonneg (α:=ℝ) k]
 unfold m; apply le_of_eq; ring
end Bills
end YM.CF.BProof.Oasis
