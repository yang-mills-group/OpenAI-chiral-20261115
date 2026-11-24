import YM.CF.Hove.Curb
import YM.CF.Haro.Weight
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Hove
set_option quotPrecheck false
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Stationary Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Fock Tulip Font Spire Nacre Ember Pec
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker MatrixOrder Classical
attribute [local instance] opCStarAlgebra
open Tap Hake Urn Yaw Levier Proa Rill

variable (j:ℕ)(p:4≤j)(e:Even j)
variable {c f:Side}(G:Ratio c f)(w:Odd G.count.val)(M:Male)(b:Bool)(o: Site c)(T:Script Male)(u:Use j G.count T)(d:List Axis)(ad:d.length+2≤j)
abbrev heel:=isle G (o,0)
abbrev Uρ(x:Cover):Stk G.count:= tub (coverlet b j G.count M.val d) x
abbrev portR(x:Cover)(i k:SpinIdx):= Uρ j G M b d x (0,i) (0,k)
include ad
lemma lipV (p:2 ≤ j):∃ C:ℝ,0<C∧∀{c f:Side}(G:Ratio c f),Odd G.count.val →∀(M: Male)(r s:SpinIdx),Cp 2 (fun x:Cover=>portR j G M b d x r s) (C*lace d.length G.count):=by
 obtain ⟨σ,C,h,v,H⟩:=pricelet b j (fun w:Male×Male=> w.1.val) (fun w=> w.2.val) (fun w=>w.1.property) (fun w=>w.2.property) (fun _=>0) d ad
 obtain ⟨A,hp,P⟩:= loan_h σ h; refine ⟨A*C,mul_pos hp v,fun {c f} G w M r s=>?_ ⟩; rw [mul_assoc]; exact P (H (⟨G.count,w⟩,M) r s)
local notation "Uχ"=> Uρ j G M b d
local notation "P'"=> Rush.cart c (Uρ j G M b d)
local notation "Y" D:max=> wingF j G w T M b (heel G o) D
variable (r s:Kt)(x y:Site c)
include e G w M T u
lemma ωY : (Y d) r (stickW x s)= P' (o,(0,r.1)) (x,(0,s.1))*(1:Op Slot) r.2 s.2:=by
 have he:merry G w T j b M d= Rush.cart c (Uρ j G M b d) ⊗ₖ (1: Op Slot):=by rw [merry,sticks j G.count w e (by omega) T u G rfl M]; exact pine_stencil j G.count w e (by omega) T u G rfl M b d ad
 unfold wingF fan; simp only [Matrix.of_apply, he]; let r₀:Kt:=r
 rw [show stickW (heel G o) r=switchG G ((o,(0,r.1)),r.2) from rfl]; unfold arch; rw [Matrix.of_apply, Equiv.symm_apply_apply]; rfl
variable (F:Cover→Pal)
def view_M : Matrix (Single c) Kt ℂ:= Matrix.of fun x i=> ζw o x*F (ox o x) (portB x) i
local notation "T'(" z ")" a:max k:max=> (Uρ j G M b d z (0,a) (0,k))
-- PAY & measure laws only plus χ
private lemma reedB (i k:Kt) (V:Site c→ℂ):
 (∑ x:Site c,(Y d) i (stickW x k)*V x)=∑' y: Cover,T'(y) i.1 k.1 * (Rush.wind o y* (1:Op Slot) i.2 k.2*V (o+wrap c y)):=by
 let Q(z:Site c)(y:Cover):= wagon c Uχ y (o,(0,i.1)) (z,(0,k.1)); let K(z:Site c)(y:Cover):= Q z y * (1:Op Slot) i.2 k.2 *V z
 have hx(x):Summable (K x):=((wagon_sum (furl j b d ad G w M) ..).mul_right _).mul_right _
 simp_rw [ωY j e G w M b o T u d ad]; unfold Rush.cart; simp only [Matrix.of_apply,←tsum_mul_right]; rw [←Summable.tsum_finsetSum (fun i _=>hx i)]; apply tsum_congr; intro x; rw [sum_eq_single (o+wrap c x)]; unfold K Q; rw [wagon_app, if_pos rfl]; ring; intro z _ hz; unfold K Q; simp only [wagon_app,if_neg (Ne.symm hz), zero_mul]; simp -- tune
local notation "κν"=> (lace d.length G.count)
local notation "v0"=> (view_M o F)
abbrev portS (i r s:Kt)(x:Cover):ℂ:= (1:Op Slot) i.2 r.2 * F x r s
def idealS : Pal:= Matrix.of fun i s=> ∑ r:Kt,∑' x:Cover,Uρ j G M b d x (0,i.1) (0,r.1)*portS F i r s x
local notation "µρ"=> idealS j G M b d F -- order
lemma splitting_m (i s:Kt) : ((Y d) * v0) i s= ∑ k:Kt,∑' x:Cover,T'(x) i.1 k.1* hill_q c o (portS F i k s) x:=by
 rw [Matrix.mul_apply,←Equiv.sum_comp (helix c).symm,Fintype.sum_prod_type, sum_comm]; apply sum_congr rfl; intro k _; let A(x:Site c):=(v0) (stickW x k) s; change ∑ x:Site c, (Y d) i (stickW x k)*A x= _
 rw [reedB j e G w M b o T u d ad i k]; apply tsum_congr; intro x; unfold A hill_q portS; simp only [view_M, ox, stickW,ζw,add_sub_cancel_left,Matrix.of_apply,portB]; ring -- lift(o+⋯)
variable(a W:ℝ)(h:0≤a)(hF:∀ i k:Kt, ∀ x:Cover,‖F x i k‖≤a*tweight 1 x)(hU:∀ i k:SpinIdx,Cp 2 (fun x:Cover=>Uρ j G M b d x (0,i) (0,k)) W){n:ℕ}(q:2*n<c.val)
local notation "Ψ"=> (Y d)
local notation "νd"=> µρ
include h hF hU q
lemma stamp_P : let X:=Ψ*v0; ‖X‖≤ Haro.ξP*(Fintype.card Kt*(a*W)) ∧ ‖X-idealS j G M b d F‖≤ Haro.ξP*(Fintype.card Kt*(2*a/(1+(n:ℝ))*W)):=by
 intro X; let P:=idealS j G M b d F; let f(i k:Kt)(x:Cover):= portR j G M b d x i.1 k.1
 let b'(i k s:Kt):= portS F i k s; let A(i k s:Kt):ℂ:=∑' x:Cover,f i k x*hill_q c o (b' i k s) x
 let K(i k s:Kt):ℂ:=∑' x:Cover,f i k x*b' i k s x
 have he(i k s:Kt) : ‖A i k s‖≤ a*W ∧ ‖A i k s-K i k s‖≤2*a/(1+(n:ℝ))*W:=by
    apply (turfL (hU ..) c o (portS F i k s) (fun x=> ?_) h q).2.2
    unfold portS; rw [Matrix.one_apply]; split; rw [one_mul]; exact hF _ _ _
    rw [zero_mul,norm_zero]; exact mul_nonneg h (tw_pos ..)
 have hh(i s:Kt): X i s=∑ k:Kt,A i k s:= splitting_m j e G w M b o T u d ad F i s
 have hl(i s:Kt): P i s=∑ k:Kt,K i k s:= rfl
 constructor
 · apply Haro.ζP; intro i s; rw [hh]; refine (norm_sum_le ..).trans ((sum_le_sum (fun k _=> (he i k s).1)).trans ?_); simp
 apply Haro.ζP; intro i k; change ‖X i k-P i k‖≤ _; rw [hh,hl, ←sum_sub_distrib]; refine (norm_sum_le ..).trans ((sum_le_sum (fun s _=> (he i s k).2)).trans ?_); simp
end YM.CF.Hove
