import YM.CF.Hove.Hood
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Hove
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Stationary Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Fock Tulip Font Spire Nacre Ember Pec
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker MatrixOrder Classical
attribute [local instance] opCStarAlgebra
open Tap Hake Urn Yaw Levier Proa Rill

variable(j m:ℕ)(e:Even j)(p:4 ≤ j)(v:2 ≤ m)
variable {c f:Side}(G:Ratio c f)(w: Odd G.count.val)(T:Script Male)(u:Use j G.count T)(M:Male)(b:Bool)(o:Site f)(U:Op (Single f))
def rampF: Matrix (Single f) Kt ℂ:= Matrix.of fun x i=> ζw o x*baseF b (portB x) i
def spanH(a:Axis): Matrix (Single f) Kt ℂ:= Matrix.of fun x i=> ζw o x*moonB b a (ox o x) (portB x) i
abbrev mornC : Op Kt:= (rampF false o)ᴴ*U*rampF true o
def partX (a: Axis):Op Kt:= (spanH false o a)ᴴ*U*rampF true o
def partY (a: Axis):Op Kt:= (rampF false o)ᴴ*U*spanH true o a
def wingF(d:List Axis): Matrix Kt (Single c) ℂ:= Matrix.of fun r i=> Tap.fan G w T j b M d (stickW o r) i
-- true mother Hessian
abbrev Dome:= Op Kt × (Axis→ Op Kt)× (Axis→ Op Kt)
def domF: Dome:= (mornC o U,partX o U,partY o U)
variable(D:Dome)(x:Single f)
def chipF : Op (Single c):= (wingF j G w T M false o [])ᴴ*D.1*wingF j G w T M true o [] + (∑ a:Axis, (wingF j G w T M false o [])ᴴ*D.2.2 a *wingF j G w T M true o [a]) + ∑ a:Axis, (wingF j G w T M false o [a])ᴴ * D.2.1 a*wingF j G w T M true o [] -- parentheses ambiguous fix
local notation "Y"=> wingF j G w T M
local notation "F" b:max x:max=> (fun i:Single c=>Qa j G w T M o b x i)
lemma fee_origin : Rush.wind o (0:Cover)=1:=by
 have ht:= route_H o 0 0; rw [add_zero,map_zero,add_zero,show Rush.wind o 0 * Rush.wind o 0=1 from fee_one _] at ht; exact ht
lemma spex (x:Kt)(d:List Axis): toneT G w T j b M o x d 0=Y b o d x:=by ext s; unfold toneT pax plot; simp only [fee_origin o,map_zero,add_zero,one_mul]; rfl
lemma jotB: ((fun i:Single c=> (rampF b o* Y b o []) x i)) = ζw o x • Qa j G w T M o b x:=by
 ext k:1; change _ = ζw o x* indexF G w T j b M o (portB x) k; unfold indexF; rw [Finset.sum_apply,Matrix.mul_apply, Finset.mul_sum]; apply sum_congr rfl; intro i _; unfold vowel; rw [spex]; simp only [rampF, Matrix.of_apply, mul_assoc, Pi.smul_apply,smul_eq_mul]
lemma jutB: (fun i:Single c=> (∑ a:Axis,spanH b o a *Y b o [a]) x i) = ζw o x • Qk j G w T M o b x:=by
 ext k:1; change _ = ζw o x * plyT G w T j b M o (portB x) (ox o x) k; unfold plyT; simp_rw [apron,spex]; simp only [Finset.sum_apply, Matrix.sum_apply, Matrix.mul_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]; rw [sum_comm]; apply sum_congr rfl; intro i _; apply sum_congr rfl; intro h _; simp only [spanH, Matrix.of_apply,mul_assoc]
local notation "ζ"=> ζw o
local notation "O"=> Single f
local notation "r"=> Single c
local notation "ψ" b:max=> Qa j G w T M o b
local notation "Ψ" b:max=> Qk j G w T M o b
private lemma ηv_ (A B:Matrix O r ℂ)(a b:O → r → ℂ)(h:∀ i,(fun j=> A i j)=ζ i • a i)(p:∀ i,(fun j=>B i j)=ζ i • b i): pinF (Aᴴ*U*B)=ΨH o U (fun x=>dishV (a x.1) (b x.2)):=by
 ext1 j; unfold ΨH; rw [Finset.sum_apply, Fintype.sum_prod_type, sum_comm]; change ((Aᴴ*U)*B) _ _=_; rw [Matrix.mul_apply]; apply sum_congr rfl; intro i _; rw [Matrix.mul_apply, Finset.sum_mul]; apply sum_congr rfl; intro k _; change star (A k _) * U k i * B i _ = ζl o U k i * dishV (a k) (b i) j; rw [congrFun (h k) j.1,congrFun (p i) j.2]; simp only [Pi.smul_apply,smul_eq_mul,dishV,star_mul,show ∀ i,star (ζ i)= ζ i from fun _=>fee_real _]; unfold ζl; ring
private lemma pin_add(A B:Op r):pinF (A+B)=pinF A +pinF B:= rfl
lemma faith : pinF (chipF j G w T M o (domF o U))= ΨH o U (fun x=> bushX j G w T M o x.1 x.2):=by
 let A:=Y false o []; let C:=Y true o []; let B0:= rampF false o; let B1:=rampF true o
 let K:= B0 *A; let L:=B1*C; let P(b:Bool):= ∑ a:Axis, spanH b o a*Y b o [a]
 have hp : chipF j G w T M o (domF o U)=Kᴴ*U*L + Kᴴ*U* P true+ (P false)ᴴ*U*L:=by
    unfold chipF; change _ + (∑ a:Axis,Aᴴ * partY o U a * Y true o [a]) + _=_; simp only [P,domF,Matrix.mul_sum,Matrix.conjTranspose_sum, Matrix.sum_mul, K,L, partY,partX, mornC]; simp only [B0,B1,C,A, Matrix.conjTranspose_mul, Matrix.mul_assoc]
 rw [hp,pin_add,pin_add, ηv_ o U K L (ψ false) (ψ true) (jotB j G w T M false o) (jotB j G w T M true o),ηv_ o U K (P true) _ _ (jotB j G w T M false o) (jutB j G w T M true o), ηv_ o U (P false) L _ _ (jutB j G w T M false o) (jotB j G w T M true o)] -- H inference
 unfold ΨH bushX billY; simp only [smul_add,Finset.sum_add_distrib]
end YM.CF.Hove
