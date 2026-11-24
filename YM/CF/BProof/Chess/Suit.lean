import YM.CF.BProof.Chess.Ground
/-! The monoid of variable length blocks based at 0. Mirror identity uses Keys
 (all-even) mode use of bounded Borel marks, not merely a local spin-coordinate rule. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Chess
open Function Filter Metric NormedSpace Finset Lattice Cube Bide Spire Bide.Half RG Fock Lat Skye Scree Tulip
open scoped Matrix.Norms.L2Operator Matrix Topology BigOperators InnerProductSpace Kronecker Classical
attribute [local instance] opCStarAlgebra
variable {N L:Side}{i:Axis}{s t h z w:ℕ}
variable {S T:Support (More N)} {F G:Obs N}
local instance (I : Type) [Fintype I] [DecidableEq I] : MeasurableSpace (Op I) := borel _
local instance (I : Type) [Fintype I] [DecidableEq I] : BorelSpace (Op I) := ⟨rfl⟩
lemma allowT (p:Allowed S F)(q:Allowed S G):Allowed S (F*G):=⟨Girt.kitE F G (·*·) continuous_mul p.bounded q.bounded, fun i j h=>congrArg₂ (·*·) (p.reads i j h) (q.reads i j h),fun i=>(p.modes_use i).mul (q.modes_use i)⟩ -- tune ·2
lemma allowI : Allowed S (1:Obs N):=⟨ ⟨ measurable_const,‖(1:FC (Single N))‖,fun _=> le_rfl⟩,fun _ _ _=>rfl,fun _=>.one⟩
@[ext] structure Scute (N L:Side)(i:Axis)(w:ℕ) where
 length:ℕ
 mark:Obs N
 permit: Allowed (span N L i length w) mark
namespace Scute
local notation "Skt"=> Scute N L i w
variable (x y z:Scute N L i w)
local notation "Δ_" a:max=> move (drive N L i a)
local notation "βt"=> move (Fixed.reflectSweep N i)
def vacant (N L:Side)(i:Axis)(w a:ℕ) : Scute N L i w:= ⟨a,1,allowI⟩
instance : One (Scute N L i w):=⟨vacant N L i w 0⟩
instance : Mul (Scute N L i w):=⟨fun x y=> ⟨x.length+y.length,x.mark*(move (drive N L i x.length) y.mark), allowT (mode_p x.permit (front N L i y.length)) (mode_p (movement y.permit rfl) (back N L i))⟩⟩
@[simp] lemma surge : (x*y).length=x.length+y.length:=rfl
@[simp] lemma slash : (x*y).mark=x.mark*move (drive N L i x.length) y.mark:=rfl
@[simp] lemma l_one : (1:Scute N L i w).length=0:=rfl
@[simp] lemma v_one : (1:Scute N L i w).mark=1:=rfl
lemma gather(s t:ℕ)(p:plainP F): (Δ_ s) ((Δ_ t) F)= move (drive N L i (s+t)) F:=by rw [dance _ _ p,drive_roll,add_comm t]
lemma moving_one(s:Sweep N): move s 1=1:= (move s).map_one
instance : Monoid (Scute N L i w) where
 mul_assoc x y z:=by
    apply Scute.ext; simp only [surge]; omega
    rw [slash,surge,slash,slash,slash,map_mul,gather _ _ (plain z.permit),mul_assoc]
 one_mul x:=by apply Scute.ext; rw [surge,l_one, zero_add]; rw [slash,v_one,l_one,drive₀,move_e (plain x.permit),one_mul]
 mul_one x:=by apply Scute.ext; rw [surge,l_one, add_zero]; rw [slash,v_one,moving_one,mul_one]
lemma lVac(t:ℕ): (vacant N L i w t).length=t:=rfl
lemma mVac(t:ℕ): (vacant N L i w t).mark=1:=rfl
lemma vacant_plus(a b:ℕ): vacant N L i w (a+b)=vacant N L i w a * vacant N L i w b:=by apply Scute.ext; rfl; rw [slash,mVac,mVac,mVac,moving_one,mul_one]
lemma commutes (v:field L (x*y).length≤(More N).val)(p:0<w): Commute x.mark (move (drive N L i x.length) y.mark):= x.permit.commute (movement y.permit rfl) (circular _ _ _ _ _ v p)
def bar: Scute N L i w:= ⟨x.length,(Δ_ x.length) (βt x.mark), mode_p (movement (movement x.permit rfl) rfl) (spin _ _ _ _)⟩
lemma bar_t : x.bar.mark= (Δ_ x.length) (βt x.mark):=rfl
lemma bar_l : x.bar.length=x.length:=rfl
lemma bar_b : bar (bar x)=x:=by
 apply Scute.ext; rfl
 let t:= Fixed.reflectSweep N i; let u:=drive N L i x.length
 change move u (move t (move u (move t x.mark)))=x.mark; simp only [dance _ _ (plain x.permit)]; rw [mul_assoc t u t,heel, ←mul_assoc t t u⁻¹, mTor N i,one_mul,inv_mul_cancel, move_e (plain x.permit)]
lemma bar_v(a:ℕ): bar (vacant N L i w a)=vacant N L i w a:=by apply Scute.ext; rfl; rw [bar_t,mVac,moving_one,moving_one]
lemma bar_mul(v:field L (x*y).length ≤ (More N).val)(e:0<w):bar (x*y)=bar y *bar x :=by
 apply Scute.ext; rw [bar_l,surge,surge,bar_l,bar_l,add_comm]
 rw [bar_t,slash,slash,(x.commutes y v e).eq,surge]; simp only [map_mul]; apply congrArg₂ (·*·)
 · rw [bar_t]; let V:=drive N L i x.length; let R:=Fixed.reflectSweep N i; let U:= drive N L i y.length
   have hz : V*R*(drive N L i (x.length+y.length))=R*U:=by rw [heel,←drive_roll,mul_assoc R, inv_mul_cancel_left] -- lhs unfold issue tune
   rw [dance _ _ (plain y.permit),dance _ _ (plain y.permit),dance _ _ (plain y.permit),hz]
 rw [bar_t,bar_l, gather _ _ (keys _ (plain x.permit)),add_comm]
-- commute at exact size or price rotation
lemma roof (p:home L x.length N):(Δ_ x.length) F= move (1:Sweep N) F:= by rw [homeP N L i p]
-- price propagation over monoid
variable {a b:ℝ}
lemma towerP (p:Paid x.mark a)(t:Paid y.mark b):Paid (x*y).mark (a*b):=by
 intro u; rw [slash,Pi.mul_apply]; refine (norm_mul_le ..).trans (mul_le_mul (p u) (normD t rfl u) (norm_nonneg _) ((norm_nonneg _).trans (p u))) -- careful mul_le_mul requires c or d?
lemma barCost (p:Paid x.mark a):Paid x.bar.mark a:=by rw [bar_t]; exact normD (normD p rfl) rfl
lemma vCost(b:ℕ) : Paid (vacant N L i w b).mark 1:=by intro u; exact le_of_eq norm_one -- requires Nontrivial
lemma pow_l(b:ℕ) : (x^b).length=x.length*b:=by induction b with|zero=>simp|succ b ih=>simp [pow_succ, mul_add,ih]
lemma repeat_cost (p:Paid x.mark a)(n:ℕ):Paid (x^n).mark (a^n):=by induction n with|zero=>rw [pow_zero,pow_zero]; exact vCost 0|succ n ih=>rw [pow_succ,pow_succ]; exact towerP _ _ ih p
end Scute
end YM.CF.BProof.Chess
