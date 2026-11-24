import YM.SU5.Selected.Lantern.Root
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 450000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Pannier.Chancel.Lantern
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye RG
open Crest.Airy
open Reed (Fine)
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
local notation "I"=>Complex.I
-- Local payload constructor
open Stencil
variable {n:Type*}[LinearOrder n][Fintype n]{a:Type}[Fintype a][DecidableEq a]
private lemma antikeep {α X:Type*}[Ring X][Algebra ℂ X](L:List α)(F:α→ X)(G:X)(e:∀ i,F i * G = - (G * F i)):
 G*foil F L = (-1:ℂ)^ L.length • (foil F L*G) :=by
 induction L with
 |nil=> simp [foil]
 |cons i l ih=>
    rw [foil,List.map_cons,List.prod_cons,←mul_assoc,show G*F i=-(F i*G) from ?_]; swap; · rw [e i,neg_neg] -- tune
    unfold foil at ih; rw [neg_mul,mul_assoc,ih,Algebra.mul_smul_comm,←mul_assoc (F i), List.length_cons,pow_succ',mul_smul,neg_one_smul] -- tune
private lemma antichain {α X:Type*}[Ring X][Algebra ℂ X](X₀ Y₀:α→X)(p:∀ i j, X₀ i*Y₀ j= -(Y₀ j*X₀ i))(L:List α):
 foil (X₀*Y₀) L =((-1:ℂ) ^ (Nat.choose L.length 2)) • (foil X₀ L*foil Y₀ L):=by
 induction L with
 | nil=> simp [foil]
 | cons i l ih=>
    rw [show foil (_ * _) _=X₀ i*Y₀ i*foil (X₀*Y₀) l from rfl,ih]
    rw [Algebra.mul_smul_comm]; change _= _ • ((X₀ _* foil X₀ l)*(Y₀ _*foil Y₀ l)); rw [mul_assoc,mul_assoc,←mul_assoc (Y₀ i),antikeep l X₀ (Y₀ i) (fun t=>p t i),Algebra.smul_mul_assoc, Algebra.mul_smul_comm,List.length_cons, Nat.choose_succ_succ, Nat.choose_one_right, pow_add]; rw [smul_smul]; simp only [mul_assoc]; module -- assoc? tune
variable (X Z:WRect n a)(S:Finset n)(b:Bool)
def above:= hand b (cutM S) * Z -- implicit binder list dep order user
#print above
variable(p:hand (!b) (cutM S)*X=X)
include p
lemma fair_cost (L:List a) : markedArc b L S X Z= ((-1:ℂ)^(Nat.choose L.length 2)) • (party (col X) (!b) L*party (col (above Z S b)) b L):=by
 let x(i):= creed (!b) (col X i); let y(i):= creed b (col (above Z S b) i); let f(i):= cardH b (cutM S) (col Z i); have ht: col (above Z S b)=f:= funext (fun i=> line_a _ _ _)
 rw [markedArc,show rootLetter X Z b S-1=x*y from ?_,antichain x y]
 · rfl
 · intro i j; apply eq_neg_of_add_eq_zero_left; unfold x y; rw [ht,add_comm]; exact asGrade _ ((col_lim ..).2 p i) (col Z j)
 ext1 i; change 1 + x i * creed b (f i) -1=x i * _; unfold y; rw [ht,add_sub_cancel_left]
omit p
-- any L=10 even. det rule.
variable (t: Fintype.card a=10)
local notation "τ₀" => (univ:Finset a).toList
lemma rung_len(t:Fintype.card a=10): (τ₀).length=10:= by simp [t] -- tune
include t p
lemma pathCombine (A B:Op a)(h:A.det=1)(w:B.det=1)(x y:WRect n a)(g:X=x*A)(u:above Z S b=y*B):
 markedArc b (τ₀) S X Z=-(tape (!b) x*tape b y):=by
 rw [fair_cost X Z S b p,rung_len t,g,u]; change _ • (tape _ _ *tape _ _) = _; rw [wave_det,wave_det,h,w,map_one, map_one,one_smul,one_smul, show (-1:ℂ)^(Nat.choose 10 2) = (-1) from (by norm_num [Nat.choose_two_right]),neg_one_smul]
omit p t
-- noncomm map transport binder order
variable (c: pulseNode)
local notation "V"=> (pval c:ℂ)
def mixt_a (c:pulseNode)(X Z: WRect n a):= (pval c:ℂ) ^ (11:ℕ) • X+Z
def mixt_b (c:pulseNode)(X Z: WRect n a):= (heatize (pval c):ℂ) • ((pval c:ℂ) • X+Z)
-- `rake` applied to both after capture index=1
abbrev countOne (x y:WRect n a) (b:Bool):= rake (fun i=>creed b (col x i)) (fun i=>creed b (col y i)) (τ₀) 1
@[simp] lemma tone_real (c:ℝ):tone b (c:ℂ)=(c:ℂ):=by cases b <;> simp [tone]
include t in
lemma cubature {W Y: WRect n a}:
 ∑ c:pulseNode, Stencil.rho c • (tape (!b) (mixt_a c X Z) * tape b (mixt_b c W Y))=((10:ℂ)⁻¹ • countOne X Z (!b)) * countOne W Y b:=by
 have e(c:pulseNode): tape (!b) (mixt_a c X Z) = foil ((pval c:ℂ)^ (11:ℕ) • (creed (!b) ∘ col X) +(creed (!b) ∘ col Z)) (τ₀):=by
    unfold tape party; congr 1; ext1 i; rw [mixt_a,col_add,col_scale,creed_a,tax_r,map_pow,tone_real]; rfl
 have p(c:pulseNode): tape b (mixt_b c W Y)= foil ((heatize (pval c):ℂ) • ((pval c:ℂ) • (creed b ∘ col W)+ creed b ∘ col Y)) (τ₀):=by
    unfold tape party; congr 1; ext1 i; rw [mixt_b,col_scale,col_add,col_scale,tax_r,creed_a,tax_r,tone_real,tone_real]; rfl
 simp_rw [e,p]; exact polarized (creed (!b) ∘ col X) (creed (!b) ∘ col Z) (creed b ∘ col W) (creed b ∘ col Y) (τ₀) (rung_len t)
end YM.CF.Pannier.Chancel.Lantern
open YM.CF.Pannier.Chancel.Lantern
#print axioms cubature
#print axioms pathCombine
