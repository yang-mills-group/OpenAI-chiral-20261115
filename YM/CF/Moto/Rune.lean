import YM.CF.Hove.Haven
import YM.CF.Haro.Fig
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.CF.Moto
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Stationary Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Fock Tulip Font Spire Nacre Ember Pec
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker MatrixOrder Classical
attribute [local instance] opCStarAlgebra
open Tap Hake Urn Yaw Levier Proa Rill
open Hove Haro
variable {n:Side}(o x y:Site n)(a b:Pal)(S T:Matrix (Single n) Kt ℂ)(P:Op (Single n))(k:ℕ)(g:SU.E)(r:Bool)(i:Axis)
def MarkPH (P:Op (Single n)):Prop:=∀ (g:SU.E)(x y:Site n),Commute (matPH P x y) (KinX g)
abbrev Noble(P:Dome):Prop:=(seedsP P ∧ ∀ g:SU.E,Commute P.1 (KinX g)∧ (∀ i,Commute (P.2.1 i) (KinX g))∧ ∀ i,Commute (P.2.2 i) (KinX g))
def hailV(x:Site n)(i:Kt): Single n:= ((x,i.1),i.2)
def nose(S:Matrix (Single n) Kt ℂ)(x:Site n):Pal:= Matrix.of fun i j=> S (hailV x i) j
lemma herz(f:Single n→ℂ):∑ i:Single n,f i=∑ i:Site n,∑ j:Kt,f (hailV i j):=by rw [Fintype.sum_prod_type]; simp_rw [Fintype.sum_prod_type]; rfl
lemma grantF : snapH S T P=∑ x:Site n,∑ y:Site n,(nose S x)ᴴ *matPH P x y * nose T y:=by
 let W(x:Site n)(y:Site n):Pal:=(nose S x)ᴴ *matPH P x y * nose T y
 have hz:= herz (n:=n)
 ext i j; change (Sᴴ*P*T) i j=(∑ x:Site n,∑ y:Site n, W x y) i j; rw [Matrix.mul_apply,hz]
 simp_rw [Matrix.mul_apply,hz,sum_mul]; conv_lhs=> arg 2; ext; rw [sum_comm (s:=(univ:Finset Kt))]
 rw [sum_comm]; simp_rw [Matrix.sum_apply]; refine sum_congr rfl fun x _=>sum_congr rfl fun y _=>?_ ; unfold W; rw [Matrix.mul_apply]; refine sum_congr rfl fun t _=>?_ ; rw [Matrix.mul_apply,sum_mul]; rfl
open Skye Precision Jet Scree
variable(X:Hub n)(F:InkD n){B:RG.BudgetPoint}{h v:ℝ}(p:PressB B X F h v)
abbrev boxM(U:Op (Single n))(x y:Prism.Rock n):Op SU.Slot:= Matrix.of fun i j=>U (x,i) (y,j)
include p
lemma worth_Φ : MarkPH (orbitPH (F 1)):=by
 intro g u z; let f(x y:SpinIdx):=CharM F (u,x) (z,y) 1; let V:= orbitPH (F 1)
 have hx(x): (gauge (fun _:Seat n=>g) (1:Pane n)) x=(1:Pane n) x:=by simp [Lattice.gauge]
 have hv(x y:SpinIdx): Commute (f x y) (mater g):=by
    have he:= char_g X _ p 1 (r:=(u,x)) (s:=(z,y)) (fun _=>g); rw [funext hx] at he; refine (Eq.trans (show f x y * mater g=(mater g*f x y * star (mater g))*mater g from congrArg (·*mater g) he) ?_ : f x y*mater g=mater g*f x y); rw [mul_assoc,show star (mater g)*_=1 from (matter g).property.1,mul_one]
 let T:=matPH V u z
 have hm:Commute T (KinX g):=by
    unfold Commute SemiconjBy; ext ⟨x,a⟩ ⟨y,b⟩; rw [Matrix.mul_apply, Matrix.mul_apply]; rw [Fintype.sum_prod_type,Fintype.sum_prod_type (fun l:SpinIdx ×Slot=> (KinX _) _ l * T l (y,b))]; rw [sum_eq_single y,sum_eq_single x]
    · simp only [KinX,Matrix.kronecker_apply,Matrix.one_apply_eq,one_mul]; exact Matrix.ext_iff.mpr ((hv x y).eq) a b
    · intro i _ h; simp [T,KinX,Matrix.one_apply,h,Ne.symm h]
    · simp
    · intro i _ h; simp [T,KinX,Matrix.one_apply,h,Ne.symm h]
    simp
 exact hm
omit p
lemma cap_c (p:MarkPH P)(x y:Prism.Rock n):Commute (boxM P x y) (mater g):=by
 obtain ⟨x,a⟩:=x; obtain ⟨y,b⟩:=y; let T:=matPH P x y; unfold Commute SemiconjBy; ext i j
 have he: (T*KinX g) (a,i) (b,j) = (KinX g * T) (a,i) (b,j):= Matrix.ext_iff.mpr (p g x y).eq _ _; rw [Matrix.mul_apply,Matrix.mul_apply,Fintype.sum_prod_type,Fintype.sum_prod_type (fun l:SpinIdx ×Slot=> KinX _ (a,i) l * T l (b,j))] at he; rw [sum_eq_single b,sum_eq_single a] at he
 · simp only [KinX,Matrix.kronecker_apply,Matrix.one_apply_eq,one_mul] at he; exact he
 · intro k _ h; simp [T,KinX,Matrix.one_apply,h, Ne.symm h]
 · simp
 · intro k _ h; simp [T,KinX,Matrix.one_apply,h, Ne.symm h]
 simp
-- notation. kin matter. slot = All.Trio. Includes color complex
local notation "K"=> KinX g
lemma folkP(M:Male)(i:Momentum):Commute (Tap.boot 1 M i) (KinX g):=by unfold Commute SemiconjBy KinX Tap.boot; rw [op_kron_mul,op_kron_mul,one_mul,mul_one,mul_one,one_mul]
lemma stake_M : Commute (baseF r) (KinX g):=by
 let M:Male:=⟨1,odd_one⟩
 cases r; swap; · rw [show baseF true = Tap.boot 1 M 0 from (boot_o _ _).symm]; exact folkP ..
 rw [show baseF false=1-Tap.boot 1 M 0 from (by unfold baseF; rw [boot_o]; simp)]; exact (Commute.one_left K).sub_left (folkP ..)
lemma sc_m(v:Pal)(a:ℂ)(p:Commute v K): Commute (a • v) K:=by unfold Commute SemiconjBy; rw [Matrix.smul_mul, p.eq,Matrix.mul_smul]
lemma state_u : Commute (ditF r i) (KinX g):=by
 let M:Male:=⟨1,odd_one⟩; let F(x):= Tap.boot 1 M (bout i x); have hv:=barox 1 le_rfl M i; have he:Commute (boom i) (KinX g):=(hv.mul_const (KinX g)).unique ((hv.const_mul (KinX g)).congr_of_eventuallyEq (Eventually.of_forall fun v=>(folkP g M (bout i v)).eq))
 unfold ditF; apply sc_m; cases r; exact he.neg_left; exact he
lemma com_p (p:MarkPH P) (hv:∀ x,Commute (nose S x) K)(hx:∀ x,Commute (nose T x) K) : Commute (snapH S T P) K:=by
 have hp:K*star K=1:=by unfold KinX; rw [op_star_kron,star_one,op_kron_mul,one_mul, (matter g).property.2,Matrix.one_kronecker_one]
 have hz:star K*K=1:=by unfold KinX; rw [op_star_kron,star_one,op_kron_mul,one_mul, (matter g).property.1,Matrix.one_kronecker_one]
 have hS(x):Commute (nose S x)ᴴ K:=by
    let A:=nose S x; have he:star A* star K=star K*star A:=by rw [←star_mul, ←star_mul,(hv x).eq]
    change star A*K= K* star A
    nth_rw 1 [show star A= K*star A* star K from (by rw [mul_assoc,he,←mul_assoc,hp,one_mul])]; rw [mul_assoc _ (star K),hz,mul_one]
 rw [grantF]; unfold Commute SemiconjBy; simp only [Matrix.sum_mul,Matrix.mul_sum]; exact sum_congr rfl (fun x _=> sum_congr rfl (fun y _=> ((hS x).mul_left (p g x y) |>.mul_left (hx y)).eq))
lemma leg_K(p:MarkPH P): Noble (jetsL o P):=by
 refine ⟨true_P ..,fun g=>?_⟩
 let K':=KinX g
 have hs(r:Bool)(x:Site n):Commute (nose (rampF r o) x) K':=by rw [show nose (rampF r o) x=(Rush.wind o (Lattice.lift (x-o))) • baseF r from rfl]; exact sc_m g _ _ (stake_M ..)
 have hv(r:Bool)(i:Axis)(x:Site n):Commute (nose (spanH r o i) x) K':=by rw [show nose (spanH r o i) x=(Rush.wind o (Lattice.lift (x-o))) • moonB r i (Lattice.lift (x-o)) from rfl]; exact sc_m g _ _ ((sc_m g _ _ (stake_M ..)).add_left (state_u ..))
 have hz(A:Pal)(p:Commute A K'): Commute (culm A) K':=((stake_M g false).mul_left p).mul_left (stake_M g true)
 exact ⟨com_p _ _ _ g p (hs _) (hs _),fun i=>hz _ (com_p _ _ _ g p (hv _ i) (hs _)),fun i=>hz _ (com_p _ _ _ g p (hs _) (hv _ i))⟩
end YM.CF.Moto
