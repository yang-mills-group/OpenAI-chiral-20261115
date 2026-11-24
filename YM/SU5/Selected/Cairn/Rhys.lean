import YM.SU5.Selected.Cairn.Ark
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Pannier.Chancel.Attic.Cairn
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye RG
open Crest Airy Rail Lantern Lantern.Bulb Attic Cuve
open Reed (Fine)
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
set_option synthInstance.maxSize 20000
local notation "I"=>Complex.I
open Mint Mezz Rubric Stencil
open Nacre Afterglow Afterglow.Tower.SlabMark
section
variable {N:Side}(n:ℕ)
local notation "L" n:max=> (Mezz.wandW (-(n:ℤ)))
local notation "S" n:max => Mezz.shuffleW n N
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
end
/-! # Phase-shift connection. 16B positive time in gauge units. -/
namespace Giant
open Real
variable (A:Giant) {N:Side}(Z:A.Notes→basisRule) {T:Type}[Fintype T][DecidableEq T](P:Society T)(y:Bool)(i:A.Block)(C:ℝ)
open Airy Rail Lantern.Bulb.Silks
local notation "λₖ"=>A.TourA.speed
local notation "u'"=> A.TourA
local notation "v⇡"=> wandW (- (λₖ:ℤ))
local notation "V"=> shuffleW λₖ N
local notation "d" s:max u:max=> ((u').hilt s u).val
local notation "W"=> A.Whistle
lemma shift_N (v:A.Notes): d true v=d false v+ (λₖ):=by rw [Tour.fed,Tour.fed]; simp [Tour.shiftH]
lemma accord (v:A.Notes): -(stick W A.t ((u').hilt true v))= -(stick W A.t ((u').hilt false v))+ v⇡:=by
 rw [← Mezz.pend_h]; ext i; cases i using Fin.lastCases
 next => rw [show Fin.last 3=(3:Axis) from rfl,Pi.add_apply,Pi.neg_apply,Pi.neg_apply,node₃]; unfold stick; rw [node₃,node₃,A.shift_N v]; push_cast; ring
 next i=> unfold stick; simp [Ε]
private lemma pitch_s(v:A.Notes)(x:Coast)(s:SpinIdx): let f:=Spouse W A.n A.t x; f s ((u').hilt true v)=prefixG (v⇡) x * f s ((u').hilt false v):=by intro f; unfold f Spouse tilt; simp only [Matrix.of_apply]; split; rw [accord,prefix_add,mul_comm]; rw [mul_zero]
lemma moved_star(q:A.Notes)(x:Site N)(s:SpinIdx) : clerks W N (atPut A N) A.n A.t (x,s) ((u').hilt true q)= Rush.wind x (v⇡)* clerks W N (atPut A N) A.n A.t (x+wrap N (v⇡),s) ((u').hilt false q):=by
 unfold clerks; rw [Rail.profile,Rail.profile,freeze_charge,freeze_charge,mul_sum]; apply sum_congr rfl; intro i hx; simp only [Function.comp_apply,pitch_s]; linear_combination (norm:=ring) ((Spouse W A.n A.t (brim N i)) s ((u').hilt false q))*star (Lat.Fourier N (atPut A N) i)*(flight_eq i x (v⇡))
lemma soma : Sweet A P N true= Complex.I • ((V).val* Sweet A P N false):=by
 apply uncoil; intro i b; unfold yoke; rw [Matrix.smul_mul,Matrix.mul_assoc]; ext ⟨⟨x,s⟩,v⟩ ⟨a,j⟩; change Mint.yoke _ i b _ _=(I • ( (V).val * Mint.yoke (A.Sweet P N false) i b)) _ _; rw [A.sweet_l, Matrix.smul_apply, rise_times,A.sweet_l,moved_star, Tour.ph,Tour.ph,if_pos rfl,if_neg (by decide)]; change _=I *_; ring
 -- etc
lemma anchor_b : anchorX A true= anchorX A false + (2:ℕ) • wandW (λₖ:ℤ):=by
 ext1 x; cases x using Fin.lastCases
 next=> rw [show Fin.last 3=(3:Axis) from rfl,Pi.add_apply,anchorX,anchorX,pin_track,pin_track]; change _+2*(↑(A.t+λₖ:ℕ):ℤ)= _ + 2*(↑(A.t+0:ℕ):ℤ) +_; push_cast; simp [wandW,pin_track]; ring_nf -- see
 next i=> rw [Pi.add_apply,anchorX,anchorX,east_v,east_v, two_smul]; have h: i.castSucc≠3:=Fin.castSucc_ne_last i; unfold wandW; simp [h] -- names
lemma move_E (U:Pane N): filmL A P true C U= I • ( (V).val * A.filmL P false C (Mezz.shuffleG λₖ U)):=by
 let Q:= Sweet A P N false; let X:= LHS A P false C (N:=N); have ht:LHS A P true C (N:=N)= I • ((V).val *X):=by unfold X LHS; rw [A.soma,Matrix.mul_smul,smul_comm]
 unfold filmL dressedK; rw [ht,anchor_b,map_add,Matrix.mul_smul, ←Matrix.mul_assoc,←Matrix.mul_assoc (V).val]; apply congrArg (fun a:UNI _=> I • (a.val * X)) (guile_load (λₖ:ℤ) (wrap (More N) (A.anchorX false)) U).symm
lemma hourE(c:Bool)(U:Pane N): A.Hours Z P true true C i c U = I • ((V).val* A.Hours Z P true false C i c (shuffleG λₖ U)):=by unfold Hours HourX yoke; simp_rw [if_true]; rw [move_E A P C, Matrix.smul_mul,Matrix.mul_assoc]
end Giant
end YM.CF.Pannier.Chancel.Attic.Cairn
open YM.CF.Pannier.Chancel.Attic.Cairn.Giant
#print axioms move_E
#print axioms hourE
