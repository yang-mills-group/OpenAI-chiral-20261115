import YM.CF.Hove.Point
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

variable (j:ℕ)(p:4≤j)(e:Even j)
variable {c f:Side}(G:Ratio c f)(w:Odd G.count.val)(M:Male)(b:Bool)(o: Site c)(T:Script Male)(u:Use j G.count T)(d:List Axis)(ad:d.length+2≤j)
local notation "B"=> baseF b
local notation "oA"=> (0:Site G.count)
local notation "V" s:max=> portR j G M b s
lemma binA (b:Bool): binV b ⊗ₖ (1:Op Slot)= baseF b:=by cases b; unfold baseF binV Fir.angle; simp; rfl; unfold baseF binV Fir.angle; simp; unfold bins; rw [sub_eq_add_neg _ Aop, Matrix.add_kronecker,Matrix.one_kronecker_one,op_kron_neg,sub_eq_add_neg] -- align
include p w
lemma view_P (a t:Axis)(i k:SpinIdx): let F(d:List Axis)(x):= portR j G M b d x i k; (∑' x,F [] x)=(lace 0 G.count:ℂ)*binV b i k∧ (∑' x,F [a] x)=0 ∧(∑' x:Cover,(x t:ℂ)*F [a] x)=if a=t then (lace 1 G.count:ℂ) * binV b i k else 0:=by
 intro F; let O:St G.count:= (0,i); let P:St G.count:= (0,k); let A:= Fir.paint b j G.count M.val 0
 have hp(d:List Axis)(s:d.length+2≤j)(u:Momentum)(t:u∈baseCube): Laurent.read (F d) u=A d u i k:=by
    have he:= (furl j b d s G w M).readK u t O P; apply he.trans; unfold A coverlet O P; simp only [c_app,ite_true]
 have he:0∈baseCube:=by simpa only [bout_zero] using bout_h 0 0 (by norm_num)
 have hm(d:List Axis)(s:d.length+2≤j):(∑' x,F d x)= A d 0 i k:=by simpa [Laurent.read] using hp d s 0 he
 obtain ⟨x,hx⟩:= aim_o b j p G.count M.val w M.property
 refine ⟨(hm [] (by simp; omega)).trans (congrFun (congrFun x i) k), (hm [a] (by simp; omega)).trans (congrFun (congrFun (hx a) i) k),?_⟩ -- tune
 obtain ⟨C,r,h⟩:= lipV j b [a] (by simp; omega) (by omega); have ht:=h G w M i k
 have he: HasDerivAt (fun x=>A [a] (bout t x) i k) _ 0:= op_deriv.mp (dusk_i b j p G.count M.val w M.property a t) i k
 have hh:= (show HasDerivAt (fun z=> Laurent.read (F [a]) (bout t z)) _ _ from (moments ht (by norm_num) t).2)
 have hv := hh.unique (he.congr_of_eventuallyEq (by filter_upwards [bout_v t] with i hi using hp [a] (by simp; omega) (bout t i) hi)); apply mul_left_cancel₀ Complex.I_ne_zero; rw [hv]; by_cases ht:a=t <;> simp [ht]
local notation "P'"=> Uρ j G M b
local notation "W"=> wingF j G w T M b (heel G o)
local notation "µ"=> idealS j G M b
lemma sun_v (F:Pal) (i:Axis): idealS j G M b [] (fun _=>F)=(lace 0 G.count:ℂ) • (B*F) ∧ idealS j G M b [i] (fun _=>F)=0:=by
 let C:=lace 0 G.count
 have ht (a):= view_P j p G w M b i 0 a
 constructor
 · ext r s; unfold idealS; simp only [Matrix.of_apply,portS, tsum_mul_right] -- tune
   simp_rw [show ∀ k,(∑' x:Cover,Uρ j G M b [] x (oA,r.1) (0,k))=(lace 0 G.count:ℂ)*binV b r.1 k from fun k=>(ht r.1 k).1]; rw [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,Finset.mul_sum]; rw [← binA]; apply sum_congr rfl; intro k _; rw [Matrix.kronecker_apply]; ring
 ext r s; unfold idealS; simp_rw [Matrix.of_apply, portS, tsum_mul_right]; simp_rw [show ∀ k,(∑' x:Cover,Uρ j G M b [i] x (oA,r.1) (0,k))=0 from fun k=>(ht r.1 k).2.1,zero_mul,sum_const_zero,Matrix.zero_apply]
lemma vita_q (a s:Axis): idealS j G M b [a] (moonB b s)= if a=s then (lace 1 G.count:ℂ) • B else 0:=by
 obtain ⟨C,r,h⟩:= lipV j b [a] (by simp; omega) (by omega); have ht:= h G w M
 let k:ℂ:=if a=s then lace 1 G.count else 0 -- coercion ℝ use!
 have he_ :((if a=s then (lace 1 G.count:ℂ) • B else 0)) = k • (B*B):=by split_ifs with e <;> simp [k,e,φ_sq]
 rw [he_]; ext i j'; unfold idealS; rw [Matrix.smul_apply, Matrix.mul_apply,smul_eq_mul, Finset.mul_sum,Matrix.of_apply]; apply sum_congr rfl; intro l _
 let F(x):= portR j G M b [a] x i.1 l.1; let T₁:= (1:Op Slot) i.2 l.2; change (∑' x:Cover,F x * portS (moonB b s) i l j' x)=_
 let L:= (lace 1 G.count:ℂ)
 have hp:= ht i.1 l.1; have hg:Summable (fun x:Cover=>(x s:ℂ)*F x):= (moments hp (by norm_num) s).1; have hv(x:Cover):F x*portS (moonB b s) i l j' x =(x s:ℂ)*F x*(T₁*B l j')+F x*(T₁ * ditF b s l j'):=by unfold portS moonB T₁; simp only [Matrix.smul_apply,Matrix.add_apply,smul_eq_mul]; ring
 have hw:(∑' x,F x)=0:= (view_P j p G w M b a s i.1 l.1).2.1; have he:(∑' x,(x s:ℂ)*F x)=k*binV b i.1 l.1:=by
    unfold k; rw [(show (∑' x,(x s:ℂ)*F x)=_ from (view_P j p G w M b a s i.1 l.1).2.2)]; split_ifs; rfl; exact (zero_mul _).symm
 simp_rw [hv]; rw [(hg.mul_right _).tsum_add (hp.falls.2.1.of_norm.mul_right _), tsum_mul_right,tsum_mul_right,hw,he,zero_mul,add_zero]; rw [show baseF b i l= binV b i.1 l.1 * T₁ from (by rw [←binA]; rfl)]; ring
end YM.CF.Hove
