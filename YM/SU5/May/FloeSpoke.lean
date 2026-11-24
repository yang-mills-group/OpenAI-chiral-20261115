import YM.Analysis.Nonnegative
import YM.SU5.May.FloeTwixt
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxSize 30000
set_option maxRecDepth 3000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.May.Arctic
open Function Filter Finset Fock Emu
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators ComplexOrder InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {J α:Type*} [LinearOrder J][Fintype J]
local notation "ι"=> Sum.inl
local notation "τ"=> Sum.inr
local notation "I"=>Complex.I
variable (p: J→ℂ) (x:J⊕J→J⊕J→ℂ)
def income (p:J→ℂ)(x:J⊕J→J⊕J→ℂ):Op J := Matrix.of fun i j=>Complex.I*p i*x (Sum.inl i) (Sum.inr j)
variable (q:∀ i,p i≠0)(r:∀ i j:J,p i*p j*x (Sum.inl i) (Sum.inl j)=star (x (Sum.inr i) (Sum.inr j)))(t:∀ i j:J,x (Sum.inr i) (Sum.inr j)= -x (Sum.inr j) (Sum.inr i))(h: 0 ≤ income p x)
def enroll (z:ℂ)(i j:J⊕J):ℂ:=x i j+ match i,j with| Sum.inl i, Sum.inr j => if i=j then -(z*Complex.I)*(p i)⁻¹ else 0| _,_=>0
local notation "K" => J ×ₗ Bool
local notation "T"=> income p x
private abbrev U (a : J)(b:Bool):=basisKet (toLex (a,b))
-- augment with epsilon. keep grants on BOTH orientation.Algebra.
private def fund(E:ℝ)(A:Op J)(i:J):Ket K:= (∑ j:J,A j i • U j false)+(E:ℂ) • U i true
private def price (E:ℝ)(i:J):Ket K:=∑ j:J, ((E:ℂ)⁻¹ *star (x (τ i) (τ j))) • U j true
variable (E:ℝ)(e:E≠0)(W:Op J)(L:income p x=star W*W)
local notation "Z" => enroll p x ((E:ℂ)^2)
include L q
private lemma fund_works(i j:J) : inner ℂ (fund E W i) (fund E W j) = income p (enroll p x ((E:ℂ)^2)) i j:=by
 change _=I*p i*(x _ _+ if i=j then -_*_ else 0)
 rw [mul_add,show I*p i*x (ι i) (τ j)=income p x i j from rfl,L,Matrix.mul_apply]; unfold fund
 simp_rw [inner_add_left,inner_add_right,sum_inner,inner_sum,inner_smul_left, inner_smul_right,basis_inner]; -- tune Sum double
 have ht(i j:J)(b c:Bool): U i b (toLex (j,c))=(if i=j∧b=c then 1 else 0):=by simp [U,basis_apply,eq_comm]; -- tune
 simp_rw [ht]; simp [Matrix.star_apply,mul_ite,ite_mul,Finset.sum_mul,eq_comm] -- likely needs case i=j
 split; swap; · rfl
 field_simp [q]; linear_combination (norm:=ring_nf) (E:ℂ)^2*Complex.I_mul_I
omit L q
include e in
private lemma price_bleed(i j:J): inner ℂ (price x E i) (fund E W j)= x (τ i) (τ j):=by
 unfold price fund; rw [inner_add_right]; simp_rw [sum_inner,inner_sum,inner_smul_right,inner_smul_left,basis_inner]
 have ht(i j:J)(b c:Bool): U i b (toLex (j,c))=(if i=j∧b=c then 1 else 0):=by simp [U,basis_apply,eq_comm]
 simp_rw [ht]; simp [mul_ite,ite_mul] -- tune
 field_simp

-- positivity routine ANY fixed fin labels even empty.SELL.Complex order at all
variable (F:α→ List J)
-- use explicit binders h due to L title.
-- sum-script relative.Real.Al.
local notation "H"=> Complex.I
def thaw (s t:List J) : ℂ:= (if s.length%2=0 then (1:ℂ) else Complex.I) * veil p s * runes x (pairOrder s t)
include L q r t e in
private lemma lapland (s t':List J) : thaw p (enroll p x ((E:ℂ)^2)) s t'= inner ℂ (chime (starve (fund E W) (price x E) p) (vacuum K) (s.map Sum.inr)) (chime (starve (fund E W) (price x E) p) (vacuum K) (t'.map Sum.inr)):= by
 refine quilt (fund E W) (price x E) p (enroll p x ((E:ℂ)^2)) q (fun i j=>?_) (fun i j=>?_) (fun i j=>?_) (fun i j=>(fund_works p x q E W L i j).symm) _ _
 · simpa [enroll] using r i j
 · simpa [enroll] using t i j
 simpa [enroll] using (price_bleed x E e W i j).symm
lemma smooth_thaw (z:ℕ→ J⊕J→J⊕J→ℂ)(h:∀ i j,Tendsto (fun k=>z k i j) atTop (𝓝 (x i j)))(a b:List J): Tendsto (fun k=>thaw p (z k) a b) atTop (𝓝 (thaw p x a b)):= Tendsto.const_mul _ (offer_v x _ h _)
variable [Fintype α](u:α→ℂ)
local notation "Wick(" z ")"=> ∑ i,∑ j, star (u i)*thaw p z (F i) (F j)*u j
include q r t h in
lemma wick_honoured : 0 ≤ ∑ i,∑ j, star (u i)*thaw p x (F i) (F j)*u j :=by
 set v:ℕ→ℝ:=fun i=> (↑(i+1:ℕ):ℝ)⁻¹ with hv; have hp:Tendsto v atTop (𝓝 0):=by apply tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1))) -- tune name
 have hz(i):v i≠0:=by unfold v; positivity
 let X(i:ℕ):=enroll p x ((v i:ℂ)^2); have he(i j:J⊕J):Tendsto (fun k=>X k i j) atTop (𝓝 (x i j)):=by
    cases i <;> cases j <;> unfold X enroll <;> simp only <;> try simp
    split_ifs; swap; · simp
    rename_i a b _
    set f:= fun y:ℝ=> x (ι a) (τ b) + -((y:ℂ)^2*I*(p a)⁻¹)
    change Tendsto (f ∘ v) _ _
    rw [← show f 0=x (ι a) (τ b) from (by dsimp only [f]; norm_num)]
    exact ((show Continuous f from (by unfold f; fun_prop)).continuousAt (x:=0)).tendsto.comp hp
 obtain ⟨A,B⟩:=CStarAlgebra.nonneg_iff_eq_star_mul_self.mp h
 refine ge_of_tendsto (f:=fun k:ℕ=> (Wick(X k))) (x:=atTop) (tendsto_finsetSum _ (fun i _=>tendsto_finsetSum _ fun j _=>((smooth_thaw p x X he ..).const_mul _).mul_const _)) (Eventually.of_forall fun i=>?_)
 let z(t:List J):= chime (starve (fund (v i) A) (price x (v i)) p) (vacuum K) (t.map Sum.inr)
 have hq: 0 ≤ inner ℂ (∑ j,u j • z (F j)) (∑ j,u j • z (F j)) := ⟨inner_self_nonneg (𝕜:=ℂ),(inner_self_im (𝕜:=ℂ) ..).symm⟩ -- tune
 rw [sum_inner] at hq; simp_rw [inner_sum,inner_smul_left,inner_smul_right,← show ∀ b c,thaw p (X i) b c=inner ℂ (z b) (z c) from fun b c=> lapland p x q r t (v i) (hz i) A B b c] at hq
 change 0≤ ∑ j,∑ k, star (u j)*thaw p _ _ _*u k
 apply le_trans hq; refine le_of_eq (Finset.sum_congr rfl fun j h=>Finset.sum_congr rfl fun k h=>?_); change star (u j) * (_*_)=_; ring
end YM.CF.May.Arctic
#print axioms YM.CF.May.Arctic.wick_honoured
