import YM.CF.Buffered.Cushion
/-!
# Mark reflected tile copies with all directions
-/
set_option autoImplicit false
set_option synthInstance.maxSize 22000
set_option maxHeartbeats 480000
noncomputable section
namespace YM.CF.Buffered.Region
open Function Filter NormedSpace SU Lat Lattice Cube Finset Mir Mir.Trip Phase RP MeasureTheory Roost Rails Mil RG WilsonStartup Spark Nova Fock Push.SectorMeasure Ordered Cin Stripe Tile Traversed Stack Bays Saddle
open Installed (point)
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder Fin.NatCast Function
attribute [local instance] opCStarAlgebra
variable {m v p B:Side}{δ:Axis→Side}
variable (i j:Axis)
local notation "W" => Post (CSide v B)
local notation "G" => GridM v B
local notation "X" => Locale v B
local notation "J" => turnF i v B
local notation "Q" => turnF j v B

lemma turn_spin_A (h:i≠j) (u:Ket G) : acts (turnF i v B).val (acts (turnF j v B).val u)= -acts (turnF j v B).val (acts (turnF i v B).val u):=by
 let A:= mirrorSpin i; let B':=mirrorSpin j
 have hp: pin i*pin j = -(pin j*pin i) := by unfold pin; simp only [←mul_assoc]; rw [mul_assoc (gammaOp i), gradingSwap, mul_neg, ←mul_assoc, neg_mul, gammaSwap i j h, neg_mul, neg_mul,neg_neg, mul_assoc (gammaOp j) grading, gradingSwap, mul_neg, neg_mul, neg_neg, mul_assoc]; simp only [mul_assoc]
 have he (w:Ket Spin): acts A.val (acts B'.val w)= -acts B'.val (acts A.val w):=by rw [←act_mul,←act_mul]; rw [show A.val*B'.val= -(B'.val*A.val) by unfold A B' mirrorSpin; dsimp only; rw [op_kron_mul,op_kron_mul,hp, op_kron_neg],act_neg]
 nth_rw 1 2 [← basis_expand u]; simp_rw [map_sum,map_smul,←sum_neg_distrib]; apply sum_congr rfl; intro t _
 obtain ⟨⟨z,k⟩,rfl⟩:= (wall W Spin).surjective t; rw [←smul_neg]; apply congrArg; change acts _ (acts _ (basisKet (Bays.install Spin z k)))= _
 -- issue implicit wrong app
 rw [(seat_mate j z) k,show (wall W Spin) (z,k) = Bays.install Spin z k from rfl,(seat_mate i z) k,(seat_mate i _).inter _ _,(seat_mate j _).inter _ _, Waist i j]; rw [he,map_neg]
private lemma anti_mark (h:i≠j){S:Finset G}{b:Bool}{x:FC G}(v:Sector S b x) :
 theta J (theta Q x)= (if b then (-1:ℂ) else 1) • theta Q (theta J x):=by
 have he(i j:Axis)(x:Ket G): theta (turnF i _ _) (theta (turnF j _ _) (create x))= -create (acts (turnF i _ _).val (acts (turnF j _ _).val x)):=by rw [theta_upV,theta_smul,theta_downV]; simp [smul_smul]
 induction v with
 | zero=> simp only [theta_zero,smul_zero]
 | one=> rw [theta_one,theta_one,theta_one]; simp -- tune
 | up k _=> rw [←create_put,he,he,turn_spin_A i j h,map_neg]; simp
 | down k _=> rw [takeF,theta_star,theta_star,theta_star,theta_star,← create_put,he,he,turn_spin_A i j h,map_neg]; simp
 | add _ _ p q=> rw [theta_add,theta_add,theta_add,theta_add,p,q,smul_add]
 | scale _ z p=>rw [theta_smul,theta_smul,theta_smul,theta_smul,star_star,p,smul_comm]
 | @mul a b _ _ x y h p=> rw [theta_mul,theta_mul,theta_mul,theta_mul,h,p]; cases a <;> cases b <;> simp -- tune
lemma past_veil (T:Finset Axis)(x:X): Rails.past T (Rails.past T x)=x:=by
 apply Prod.ext; · funext j v; simp only [Rails.past,shades_square]; split_ifs <;> simp
 funext v; exact congrArg x.2 (shades_square v T)
lemma pass_rect (x:X): past {i} (past {j} x)=past {j} (past {i} x):=by
 apply Prod.ext; · funext k y; simp only [Rails.past,Waist j i]; split_ifs <;> rfl
 funext y; exact congrArg x.2 (Waist j i y)
@[ext] theorem Badge.ext {Z W':Badge v B}(h: Z.label=W'.label): Z=W':= by cases Z; cases W'; congr
namespace Badge
variable (Z:Badge v B)(x: Locale v B)
def reflect (i:Axis)(Z:Badge v B): Badge v B := ⟨fun x:X=> theta (turnF i v B) (Z.label (Rails.past {i} x)), Girt.pole_w _ _ (theta_cont _) (Env.along (g:=fun x:X=> Rails.past {i} x) Z.env (past_cont _).measurable),fun x=> untheta _ (Z.state _)⟩
lemma thus : (Z.reflect i).label (Rails.past {i} x)=theta J (Z.label x):=by dsimp only [reflect]; rw [past_veil]
lemma back : (Z.reflect i).reflect i=Z:=by apply Badge.ext; funext x; unfold reflect; dsimp only; rw [past_veil,theta_twice _ (turn_squared i ..) (Z.state _)]
lemma one_r (i v B): reflect i (1:Badge v B)=1:=Badge.ext (funext fun x=> theta_one _)
lemma reflect_comm : (Z.reflect i).reflect j = (Z.reflect j).reflect i :=by -- parser
 by_cases h:j=i; · subst j; rfl
 apply Badge.ext; funext x; dsimp only [reflect]; rw [pass_rect i]; simpa only [Bool.false_eq_true,ite_false,one_smul] using anti_mark j i h (Z.state (past {j} (past {i} x)))
-- compose a finite set of copies in commuting group actions
abbrev walk (i:Axis) : Equiv.Perm (Badge v B):= ⟨reflect i,reflect i,(back i),(back i)⟩
lemma glance : Pairwise (fun i j:Axis=> Commute (walk (v:=v) (B:=B) i) (walk (v:=v) (B:=B) j)):=fun i j _=> (Equiv.ext (fun x:Badge v B=> Badge.reflect_comm j i x) : walk i * walk j = walk (v:=v) (B:=B) j * walk i)
def stencil (Z:Badge v B)(T: Finset Axis) := pal (Badge.walk (v:=v) (B:=B)) glance T Z
lemma stencil_at {T:Finset Axis}(p:i∉T): stencil Z (insert i T)= (stencil Z T).reflect i:=by
 unfold stencil; rw [pal_insert]; swap; · exact p
 rfl
lemma stencil_zero : stencil Z ∅=Z:=rfl
lemma stencil_one (T:Finset Axis): stencil (1:Badge v B) T=1:=by induction T using Finset.induction_on with | empty=> rfl | insert i s p ih=> rw [stencil_at (p:=p),ih,one_r]

def reflected (Z:Badge v B)(r:Rail δ):= Z.stencil (shade r)
lemma reflected_zero : reflected Z (0:Rail δ)=Z:=by unfold reflected; rw [show shade (0:Rail δ)=∅ from by ext; simp [shade], stencil_zero]
lemma reflected_one : reflected (δ:=δ) (1:Badge v B)= (fun _=>1):=funext fun _=> stencil_one _
end Badge
end YM.CF.Buffered.Region
#print axioms YM.CF.Buffered.Region.Badge.reflect_comm
