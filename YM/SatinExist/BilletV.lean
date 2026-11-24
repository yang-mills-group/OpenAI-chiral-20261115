import YM.SatinExist.LedgerUV
import YM.SatinExist.SlicePath
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 30000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Six
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
open Satin
attribute [local instance] opCStarAlgebra
open Mir Haro Tap Dial Cascade Girt Pastry
open Afterglow Tapestry Tower Py Py.Rate Py.Rate.LocalLimit Preparation Journey
namespace Xara
variable {N P:Side}
section
local notation "I"=> Single N
abbrev capP := (Fintype.card SpinIdx*(Fintype.card SU.Slot:ℝ))
local notation "m!" a:max i:max=> ‖WithLp.ofLp a i‖
private lemma ticket_sums (A:Ket (Single N)): (∑ i:Single N, ‖A.ofLp i‖^2)= ‖A‖^2:=by rw [PiLp.norm_sq_eq_of_L2]
private lemma mem_col (i:Single N)(C:ℝ): (∑ j:Single N, if i.1.1=j.1.1 then C else 0) = capP*C:=by
 simp only [Single,Fintype.sum_prod_type]; rw [sum_eq_single i.1.1]; swap; · intro a _ h; simp [Ne.symm h]
 swap; · simp
 simp [capP,mul_assoc] -- constants
abbrev locval (A B:Ket (Single N)) (i j: Single N) := if i.1.1=j.1.1 then ‖A.ofLp i‖*‖B.ofLp j‖ else 0
lemma quantum_bound (A B:Ket (Single N))(C:ℝ)(v: ‖A‖≤ C)(w: ‖B‖≤ C): (∑ i:Single N,∑ j:Single N, Xara.locval A B i j) ≤ 2* capP*C^2:=by
 let X (A:Ket I) (i j:I) := if i.1.1=j.1.1 then ‖A.ofLp i‖^2 else 0
 have hk(A:Ket I)(v:‖A‖≤C): (∑ i:I,∑ j:I, X A i j)≤ capP*C^2:=by
    unfold X; simp_rw [mem_col,←mul_sum,ticket_sums]; gcongr
 calc
   _ ≤ ∑ i:I,∑ j:I,(X A i j+X B j i) := sum_le_sum fun i _=>sum_le_sum fun j _=>by
     by_cases h:i.1.1=j.1.1; · simp only [Xara.locval,X,h,↓reduceIte]; nlinarith
     simp only [X,Xara.locval, if_neg h, if_neg (Ne.symm h),add_zero,le_refl]
   _ ≤ _:= by simp_rw [sum_add_distrib]; rw [sum_comm (f:=fun i j=> X B j i)]; exact (add_le_add (hk _ v) (hk _ w)).trans (le_of_eq (by ring))
end
section
-- one pure-degree stack
variable (S T : Finset (Seat N))
def Pat (S:Finset (Seat N))(i:Single N)(b:Bool): Prop:= i∈modesIn N S ∧ i∈ speciesSet N false ∧ if b then i∈ Tset N else i∈ (Tset N)ᶜ
variable (U:FC (Single N)→ₗ[ℂ]ℂ)(e:ℝ)
local notation "Q" a:max b:max=> (Fock.remove a*Fock.create b)
local notation "q" i:max j:max=> Q (basisKet i) (basisKet j)
private lemma rackT (A B:Ket (Single N)): Q A B=∑ i:Single N,∑ j:Single N,B.ofLp j • star (A.ofLp i) • q i j:=by
 nth_rw 1 [←basis_expand A, ←basis_expand B]; unfold Fock.remove; rw [map_sum,map_sum,star_sum,sum_mul]; apply sum_congr rfl; intro i _; rw [mul_sum,map_smul,star_smul]; simp_rw [map_smul, Matrix.mul_smul,Matrix.smul_mul]
def Wing : Prop:=∀ i,Pat S i false→∀ j,Pat S j true→∀ p,Pat T p false→∀ k,Pat T k true→ ‖U ((q i j)*(q p k))‖ ≤ if i.1.1=j.1.1 ∧ p.1.1=k.1.1 then e else 0
variable (L:Wing S T U e) (A B C D:Ket (Single N)) (r:0≤e)
include L r
def KeepC (a:ℝ) (S:Finset (Seat N))(b:Bool)(A:Ket (Single N)):= ‖A‖ ≤ a ∧ ∀ i,A.ofLp i≠0→Pat S i b
lemma quadrants {p:ℝ}(u:KeepC p S false A)(v:KeepC p S true B)(t:KeepC p T false C)(l:KeepC p T true D) : ‖U ( (Q A B)*(Q C D))‖ ≤ (2*capP*p^2)^2 * e :=by
 let g(i j k t:Single N):=locval A B i j * locval C D k t * e
 refine le_trans (b:=∑ i:Single N,∑ j:Single N,∑ k:Single N,∑ t:Single N,g i j k t) ?_ ?_; swap
 · unfold g; simp_rw [←Finset.sum_mul,←Finset.mul_sum,←Finset.sum_mul]; rw [pow_two]; refine mul_le_mul_of_nonneg_right (mul_le_mul (quantum_bound _ _ p u.1 v.1) (quantum_bound _ _ p t.1 l.1) ?_ ?_) r
   · exact sum_nonneg fun _ _=> sum_nonneg fun _ _=>by unfold locval; split <;> positivity
   unfold capP; positivity
 -- bill
 rw [rackT A B,rackT C D,sum_mul,map_sum]
 refine (norm_sum_le ..).trans (sum_le_sum fun i _=>?_); rw [sum_mul,map_sum]; refine (norm_sum_le ..).trans (sum_le_sum fun j _=>?_); rw [mul_sum,map_sum]; refine (norm_sum_le ..).trans (sum_le_sum fun k _=>?_); rw [mul_sum,map_sum]; refine (norm_sum_le ..).trans (sum_le_sum fun d _=>?_); simp only [Matrix.mul_smul,Matrix.smul_mul,map_smul]
 simp only [norm_smul,norm_star]; by_cases hA:A.ofLp i=0; · simp [hA,g,locval]
 by_cases hB:B.ofLp j=0; · simp [hB,g,locval]
 by_cases hC:C.ofLp k=0; · simp [hC,g,locval]
 by_cases hD:D.ofLp d=0; · simp [hD,g,locval]
 have he:=L i (u.2 i hA) j (v.2 j hB) k (t.2 k hC) d (l.2 d hD)
 refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he (norm_nonneg _)) (norm_nonneg _)) (norm_nonneg _)) (norm_nonneg _)).trans_eq ?_
 unfold g locval; split_ifs <;> simp_all only [not_true_eq_false,Bool.false_eq_true,false_and,and_false,true_and,and_true,not_false_eq_true] <;> ring -- tune ordering
#print axioms quadrants
end
end Xara
end YM.CF.Buffered.Afterglow.Six
