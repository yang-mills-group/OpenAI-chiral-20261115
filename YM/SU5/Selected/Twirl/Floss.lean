import YM.SU5.Selected.Twirl.Car
import YM.SU5.Selected.Cor.Clasp
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 450000
set_option maxRecDepth 3000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Pannier.Chancel.Lantern
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye RG
open Crest.Airy
open Reed (Fine)
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
namespace Bulb
set_option synthInstance.maxSize 24000
namespace Mezz
open Payroll Caste Silks
local notation "ⅈ" => Complex.I
open Nacre
open Afterglow Afterglow.Tower.SlabMark
variable {N:Side}(n:ℕ)(A:Mezz)(b:Bool){p:ℕ}
local notation "L" n:max=> (wandW (-(n:ℤ))) -- n nat in scope
local notation "S" n:max => shuffleW n N
lemma shift_calc {T:Type*}[Fintype T][DecidableEq T](a:T→ Site N× Fin p){X Y: Coast→ Wq p}(x:Site N)(i:SpinIdx)(h:T)(t:Crest.Airy.Lift p n X Y) : hire p Y a (x,i) h=ⅈ*Rush.wind x (L n)*(hire p X a (x+wrap N (L n),i) h):=by
 unfold hire; rw [mask_mem,mask_mem, ←Prod.eta (p:=a h),freeze_charge,freeze_charge,mul_sum]; refine sum_congr rfl (fun j z=>?_); simp only [Function.comp_apply,t.light,pend_h,Matrix.smul_apply,smul_eq_mul]
 linear_combination (norm:=ring) ⅈ*(X (brim N j) i (a h).2)*star (Fourier N (a h).1 j)*(flight_eq j x (L n)) -- maybe Matrix instances tr
private lemma rise_matrix (x y:Site N)(i j:SpinIdx)(a b:SU.Slot): (S n).val ((x,i),a) ((y,j),b)= if x+wrap N (L n)=y ∧ i=j ∧ a=b then Rush.wind x (L n) else 0 := by
 let t:= lagX (L n); change jump (Tofu t N) (fun i'=> (milU t 1 inert i').val) (x,i,a) (y,j,b)=_
 rw [jump_apply, show Tofu t N x = _ from lag_i (L n) x]
 split_ifs with p q q; · change t.payA x * ((1: Op SpinIdx) i j * (1:Op SU.Slot) a b)=_; obtain ⟨r,rfl,rfl⟩:= q; simp [t,lag_p]
 · change t.payA x *((1:Op SpinIdx) i j * (1:Op SU.Slot) a b)=0; rw [Matrix.one_apply,Matrix.one_apply]; split_ifs <;> simp_all
 · exact False.elim (p q.1)
 rfl
private lemma rise_times {T:Type*}[Fintype T](X: WRect (Single N) T)(x: Site N)(i:SpinIdx)(v:SU.Slot)(j:T) : ((S n).val * X) ((x,i),v) j = Rush.wind x (L n) * X ((x+wrap N (L n),i),v) j:=by
 rw [Matrix.mul_apply, sum_eq_single ((x+wrap N (L n),i),v)];
 · rw [rise_matrix,if_pos ⟨rfl,rfl,rfl⟩];
 · rintro ⟨⟨q,g⟩,v'⟩ t u; rw [rise_matrix,if_neg (fun e=>u (Prod.ext (Prod.ext e.1.symm e.2.1.symm) e.2.2.symm)),zero_mul];
 simp
variable {u:Type}[Fintype u][DecidableEq u](P:Society u)(i:A.Lot)(U:Pane N)
variable (v:A.ride=0)(g:n ≤ A.passW){X Y:Coast→ Wq A.marks} (Z:Coast→ Wq A.marks)(t:Crest.Airy.Lift A.marks n X Y)(C:ℝ)
local notation "A'"=> A.pumped n
local notation "χ" y:max=> shuffleG n y
local notation "Ω" => wrap (More N) (A.grape i.1 true)
local notation "w" n:max=> wandW (n:ℤ)
local notation "Σ" h:max=> wrap (More N) ( (2:ℕ) • w h)
local notation "κ" => (S n)
local notation "ρ" => Ro N
-- size free identity
include t
lemma honor : A.dart P N Y= ⅈ • ((κ).val * (A.dart P N X)):=by
 ext ⟨⟨x,k⟩,a⟩ ⟨y,i,v,q⟩;  rw [Matrix.smul_apply,smul_eq_mul,rise_times,read_d,read_d,shift_calc n _ _ _ _ t]; ring
include v g t
lemma honed : (A').pole P i true b Y Z C U =ⅈ • ((κ).val* A.pole P i true b X Z C (χ U)):=by
 let f:= (A.Front (N:=N) P X Z i true b); let V(Z:Pane N):= dressedK (Ω) f Z
 have he:(A').Front (N:=N) P Y Z i true b=ⅈ • ((κ).val*f):= by change A.Front P Y Z i true b= _; unfold f; rw [frontX,frontX,honor n A P t]; unfold cork; rw [Matrix.smul_mul,Matrix.mul_assoc];
 have ht(W:Pane N): dressedK (Ω + Σ n) (ⅈ • ((κ).val*f)) W=ⅈ • ((κ).val*V (χ W)):= by unfold V dressedK; rw [Matrix.mul_smul,←Matrix.mul_assoc, ←Matrix.mul_assoc]; exact congrArg (fun a: UNI _=> ⅈ • (a.val*f)) (guile_load _ _ W).symm
 unfold pole spangle; rw [he, root_repair A i.1 v n g,map_add,ht,ht,←swoop_shuffle]; rw [Matrix.mul_smul, ←Matrix.mul_assoc (ρ).val (κ).val,show (ρ).val*(κ).val=(κ).val*(ρ).val from congrArg Subtype.val (ro_rear (n:ℤ)).symm -- `.symm` is Commute wrong
    ]; rw [Matrix.mul_assoc (κ).val (ρ).val,Matrix.mul_smul,Matrix.mul_sub, Matrix.mul_smul]; rw [←smul_sub ⅈ, smul_comm ((Mezz.sizeW C true:ℝ):ℂ) ⅈ]; -- tune
omit v g t in
lemma honor_early : (A').pole P i false b Y Z C U=A.pole P i false b X Z C U:= by
 unfold pole spangle; rw [frontZ,frontZ,show (A.pumped n).cork P N i b ((A.pumped n).dart P N Z)=A.cork P N i b (A.dart P N Z) from rfl,show (A.pumped n).grape i.1 false=A.grape i.1 false from rfl]
end Mezz
end Bulb
end YM.CF.Pannier.Chancel.Lantern
open YM.CF.Pannier.Chancel.Lantern.Bulb.Mezz
#print axioms honed
#print axioms honor_early
#print axioms shift_calc
