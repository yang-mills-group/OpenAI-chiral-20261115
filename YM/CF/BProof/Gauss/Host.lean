import YM.CF.BProof.Charge.Eclipse
import YM.SectorNext.VACUUM_NORMALIZATION.Panel

/- Whole space of the Hessian. `Stamp` uses ordinary Color indices D_P-independent. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Gauss
open Function Filter RG Wilson Lattice Finset Work Micro MeasureTheory Mag Angular Angular.Yard Charge Charge.Form Matrix Precision
open scoped Topology BigOperators Classical Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator
local notation "G"=> SU.group
abbrev Color := SU.group.ColorIndex
variable {I:Type*} {s:Side}
abbrev Via (I:Type*) := I→ ℝ
abbrev Pool (I:Type*) := Matrix I I ℝ
namespace Roll
variable (Y:Yard s)
abbrev Place := Y.Apt × Color
abbrev Stamp := Y.Col × Place Y
abbrev Plan := Via (Stamp Y)
variable (x:Plan Y)

def lowerMap : Plan Y ≃ₗ[ℝ] Y.Branch where
 toFun x := fun b=> WithLp.toLp 2 (fun i=>x (b.1,b.2,i))
 invFun x := fun p=> x (p.1,p.2.1) p.2.2
 left_inv x:=rfl
 right_inv x:=rfl
 map_add' x y := rfl
 map_smul' t x:=rfl
lemma lower_v (b:Y.Door)(i:Color): lowerMap Y x b i=x (b.1,b.2,i):=rfl
lemma tally : dotProduct x x=∑ b:Y.Col,∑ i:Y.Apt,‖lowerMap Y x (b,i)‖^2:=by
 simp_rw [PiLp.norm_sq_eq_of_L2]; unfold dotProduct Stamp Place; rw [Fintype.sum_prod_type]; apply sum_congr rfl; intro b _; rw [Fintype.sum_prod_type]; refine sum_congr rfl fun i _=>sum_congr rfl fun j _=>?_ ; rw [Real.norm_eq_abs,sq_abs,sq]; rfl
lemma tally₀ (b:Y.Col) : ∑ i:Place Y,(x (b,i))^2=∑ i:Y.Apt,‖lowerMap Y x (b,i)‖^2:= by
 unfold Place; simp_rw [PiLp.norm_sq_eq_of_L2]; rw [Fintype.sum_prod_type]; refine sum_congr rfl fun i _=>sum_congr rfl fun j _=> by rw [Real.norm_eq_abs,sq_abs]; rfl
lemma dimension : Fintype.card (Stamp Y)=Fintype.card Y.Col*(Y.short*3*SU.group.lieDim) := by simp [Stamp,Place,Apt,TAxis,Color]
end Roll
namespace RealM
variable [Fintype I][DecidableEq I]
def grip {E D:Type*}[AddCommGroup E][AddCommGroup D][Module ℝ E][Module ℝ D](g: E→ₗ[ℝ] D)(A : D→ₗ[ℝ] D→ₗ[ℝ] ℝ) : E→ₗ[ℝ] E→ₗ[ℝ] ℝ where
 toFun x:= (A (g x)).comp g
 map_add' x y := by ext; simp
 map_smul' t x := by ext; simp

def gram {E:Type*} [SeminormedAddCommGroup E][InnerProductSpace ℝ E] (g:(I→ℝ)→ₗ[ℝ] E) (a:ℝ) : Pool I := of fun i j=> a* inner ℝ (g (Pi.single i 1)) (g (Pi.single j 1))
lemma gram_eval {E: Type*}[SeminormedAddCommGroup E][InnerProductSpace ℝ E] (g:(I→ℝ)→ₗ[ℝ] E)(a:ℝ)(x y:I→ℝ): x ⬝ᵥ ((gram g a) *ᵥ y)=a*inner ℝ (g x) (g y):=by
 let hV (i:I):=g (Pi.single i 1)
 have he(w:I→ℝ): g w=∑ i:I,w i • hV i:=by
    conv_lhs=> rw [show w=∑ i:I,w i • Pi.single i (1:ℝ) from by ext x; simp [Finset.sum_apply,Pi.single_apply]]
    rw [map_sum]; simp only [hV,map_smul]
 rw [he x,he y,sum_inner]; unfold dotProduct mulVec gram; simp_rw [dotProduct,Matrix.of_apply,inner_sum, real_inner_smul_left, real_inner_smul_right, mul_sum]; unfold hV; apply sum_congr rfl; intro i _; refine sum_congr rfl fun j _=>?_ ; ring
lemma gram_H {E:Type*}[SeminormedAddCommGroup E][InnerProductSpace ℝ E] (g:(I→ℝ)→ₗ[ℝ] E) (a:ℝ): (gram g a).IsHermitian:= by apply Matrix.IsHermitian.ext; intro i j; rw [star_trivial]; exact congrArg (a*·) (real_inner_comm ..)
end RealM
open Roll RealM
variable (Y:Yard s)(T:PathData G)(M:ℕ)(c:Clip)(θ:ℝ)(S:Finset Y.Col)

def stepMap (l:Tile s): Plan Y→ₗ[ℝ] Lie:= (linear T M l).comp (Y.roll.comp (lowerMap Y).toLinearMap)
def extra : Pool (Stamp Y) := Matrix.diagonal fun b=> if b.1∈ S then 1 else 0
def host : Pool (Stamp Y) := extra Y S + ∑ l∈ good Y M S, gram (stepMap Y T M l) (unit c θ l)
lemma charge_H : (host Y T M c θ S).IsHermitian:= by
 unfold host; refine Matrix.IsHermitian.add ?_ ?_; unfold extra; exact Matrix.isHermitian_diagonal _; unfold Matrix.IsHermitian; rw [Matrix.conjTranspose_sum]; exact sum_congr rfl fun i _ => RealM.gram_H ..
lemma tax (x:Plan Y) : dotProduct x ((extra Y S) *ᵥ x)=∑ b∈ S,∑ i:Y.Apt, ‖lowerMap Y x (b,i)‖ ^2:=by
 unfold dotProduct Stamp; rw [Fintype.sum_prod_type]; simp_rw [extra,mulVec_diagonal, ← tally₀ (b:=_) Y x]; conv_rhs => rw [← show univ.filter (fun b=>b∈S)=S by simp]
 rw [sum_filter]; apply sum_congr rfl; intro i hi; split_ifs with v; simp [v,sq]; simp [v]
lemma paycheck (x:Plan Y): x ⬝ᵥ ((host Y T M c θ S) *ᵥ x) = (∑ b∈ S,∑ i:Y.Apt,‖lowerMap Y x (b,i)‖^2)+2*work Y M S c T θ (lowerMap Y x) :=by
 rw [host,Matrix.add_mulVec,dotProduct_add,tax, Matrix.sum_mulVec, dotProduct_sum]; unfold work; rw [mul_sum]; simp_rw [gram_eval, real_inner_self_eq_norm_sq]; congr 1; apply sum_congr rfl; intro i _; unfold Q; change _=2*(unit c θ i*‖stepMap Y T M i x‖^2/2); ring
end YM.CF.BProof.Gauss
