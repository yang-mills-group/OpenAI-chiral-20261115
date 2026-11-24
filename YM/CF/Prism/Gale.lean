import YM.CF.Prism.Meter
import YM.CF.Matter.Mass
set_option autoImplicit false
noncomputable section
namespace YM.CF.Prism
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory Mesa ProbabilityTheory Peaks Drapes Rush Precision Tree Push.SectorMeasure Next.SectorChange Tulip Jet Tap Laic Dial Paige Vault Pec Skye Pastry Cascade
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {n:Side}
open Scree
variable {B:RG.BudgetPoint}{X:Hub n}{h c:ℝ}{F:InkD n} (p: PressB B X F h c)
abbrev Rock(n:Side):= Site n× SpinIdx
abbrev gemT (A:E)(b:Bool): Op Slot:=if b then (matter A).val else cc (matter A).val
def mileT(x y:Rock n)(b z:Bool)(F:Cipher n):Op Slot:=Matrix.of fun i j=>portB F.val (b,x,i) (z,y,j)
lemma iceB(g:Seat n → E)(F:Cipher n)(x y:Rock n)(b z:Bool): mileT x y b z (paintR false false (tradew n g) F)= gemT (g (node x.1)) b* mileT x y b z F *(gemT (g (node y.1)) z)ᵀ:=by
 ext i j; let Q:= (spice (tradew n g) false).val
 have ht (x y:Rock n)(b z:Bool)(i j:Slot): Q (b,x,i) (z,y,j)=if b=z∧x=y then gemT (g (node x.1)) b i j else 0:=by
    by_cases hx:x=y <;> cases b <;> cases z <;> simp [Q,hx,Ne.symm,spice,gemT,closeV,Pastry.thread, tradew,jump_apply,ccU] -- tune
 have he (b:Bool)(x:Rock n)(i:Slot)(f:LeanV (Single n)→ℂ) : ∑ k:LeanV (Single n), Q (b,x,i) k*f k= ∑ j:Slot,gemT (g (node x.1)) b i j*f (b,x,j):=by
    rw [Fintype.sum_prod_type]; rw [sum_eq_single b]; swap
    · intro a _ h; refine sum_eq_zero fun j _=>?_ ; rw [ht,if_neg,zero_mul]; tauto
    swap; · simp
    rw [Fintype.sum_prod_type,sum_eq_single x]; exact sum_congr rfl fun j _=> by rw [ht,if_pos ⟨rfl,rfl⟩]
    intro a _ p; exact sum_eq_zero fun _ _=> by rw [ht,if_neg,zero_mul]; tauto
    simp
 change portB _ _ _ = (_:Op Slot) i j
 rw [drawn]; change ∑ k:LeanV (Single n),∑ l:LeanV (Single n),Q _ k*(Q _ l*portB F.val k l)=_; simp_rw [←Finset.mul_sum]; rw [he]; simp_rw [he]; simp only [mul_sum, Matrix.mul_apply]; rw [Finset.sum_comm]; refine sum_congr rfl fun i _=>?_ ; rw [sum_mul]; exact sum_congr rfl fun j _=>by simp [mileT]; ring -- tune
include p
lemma forge(x y:Rock n)(b z:Bool)(g:Seat n→ E)(V:Pane n): mileT x y b z (F (Lattice.gauge g V))= gemT (g (node x.1)) b* mileT x y b z (F V)*(gemT (g (node y.1)) z)ᵀ :=by rw [p.gaugeV]; exact iceB ..
omit p
lemma central_ok (g:E): central*g=g*central :=by
 apply group.mat_injective; change fund (?_) = fund (_); change fund (central*g)= fund (g*central); rw [fund_mul,fund_mul]; change (Matrix.diagonal _) * _=_*Matrix.diagonal _; ext i j; rw [Matrix.diagonal_mul,Matrix.mul_diagonal,mul_comm] -- tune
include p
lemma twice0 (V:Pane n)(x y:Rock n)(b:Bool): mileT x y b b (F V)=0:=by
 have he:= forge p x y b b (fun _=>central) V; rw [show Lattice.gauge (fun _=>central) V=V from funext fun i=>show central*V i*central⁻¹=_ from by rw [central_ok,mul_inv_cancel_right]] at he
 let f (i:Slot):= if b then SU.z^(SU.charge i) else star (SU.z^(SU.charge i)); have hg: gemT central b=Matrix.diagonal f:=by
    unfold gemT; cases b
    · change cc (matter central).val=_; rw [by_charge]; ext i j; by_cases h:i=j <;> simp [f,h]
    change (matter central).val=_; rw [by_charge]; rfl
 rw [hg,Matrix.diagonal_transpose] at he; let A:=mileT x y b b (F V)
 ext i j; change A i j=0; have hl: A i j=f i*A i j*f j:=by have H:= Matrix.ext_iff.mpr he i j; rwa [Matrix.mul_diagonal,Matrix.diagonal_mul] at H
 by_contra hp; have hv:f i*f j=1:= by apply mul_right_cancel₀ hp; rw [one_mul]; exact (mul_right_comm ..).trans hl.symm
 apply charge_protect i j; apply z_prim.dvd_of_pow_eq_one; rw [pow_add]; cases b; apply star_injective; rw [star_mul',star_one]; exact hv; exact hv -- tune
end YM.CF.Prism
