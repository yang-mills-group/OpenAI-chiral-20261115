import YM.CF.Fir.Hearth
import YM.CF.Fock.Quant
/-! Uniform free chiral history projector. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Fir
open Function Filter Lattice Laurent Bloch Next.Free Metric Finset Set WilsonFrame
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
abbrev Aop : Op SpinIdx := BZ.gPos
def zen (p:Momentum) := ∑ i,p i • (Complex.I • gammaOp i)
def bar (j:ℕ)(N:Side)(p:Momentum) : Op SpinIdx := (1/2:ℂ) • (1:Op SpinIdx)+(shell j N p-1/2) • grading + grading*zen (skin j N p)
lemma Adef : Aop=(1/2:ℂ) • (1+grading):=by rw [show (1/2:ℂ)=((1/2:ℝ):ℂ) by norm_num, BZ.ofReal_action]; rfl
lemma AOne : Aop*Aop=Aop := (BZ.atom 0).plusSq
lemma Aadj : star Aop=Aop := by rw [Adef,star_smul,star_add,star_one,gradingAdj.star_eq]; norm_num
lemma ordA : grading= (2:ℂ) • Aop-1 := by rw [Adef]; module
lemma zenT (p:BZ.Mom) : zen (tmap p) = BZ.symbolD p:=by unfold zen; simp_rw [tmap,BZ.ofReal_action]; rfl
lemma slashT (p:BZ.Mom) : zen (sine (tmap p))=BZ.slash p:=by unfold zen; simp_rw [sine,tmap,← Complex.ofReal_sin,BZ.ofReal_action]; rfl
lemma zenS (p:Momentum)(c:ℂ): zen (c • p)=c • zen p:=by simp only [zen,Pi.smul_apply,smul_eq_mul,Finset.smul_sum,smul_smul,mul_assoc]
lemma zenP (p q:Momentum): zen (p+q)=zen p+zen q:=by simp only [zen,Pi.add_apply,add_smul,Finset.sum_add_distrib]
lemma zenG (p:Momentum): grading*zen p = -(zen p*grading) := by
  unfold zen; rw [Matrix.mul_sum,Matrix.sum_mul,← sum_neg_distrib]; exact sum_congr rfl fun i _=> by simp only [Algebra.mul_smul_comm,Algebra.smul_mul_assoc, gradingSwap,smul_neg]
lemma zenA (p:Momentum): Aop*zen p=zen p*(1-Aop) := by rw [Adef]; simp only [Matrix.mul_smul,Matrix.smul_mul,mul_sub, add_mul, mul_add,mul_one,one_mul,zenG]; module
lemma zenAA (p:Momentum): (1-Aop)*zen p=zen p*Aop:=by rw [sub_mul,zenA,mul_sub,one_mul,mul_one]; abel
lemma zenSq (p:Momentum): zen p * zen p= -(prodM p p) • (1:Op SpinIdx):=by
  let z i:=p i • (Complex.I • gammaOp i)
  have he (s : Finset Axis): (∑ i∈s,z i)*(∑ i∈s,z i)= -(∑ i∈s,p i*p i) • (1:Op SpinIdx) := by
    induction s using Finset.induction_on with
    | empty=> simp
    | @insert i s hi ih=>
      rw [sum_insert hi,sum_insert hi, add_mul,mul_add,mul_add,ih,Matrix.mul_sum, Matrix.sum_mul]
      have h1 : z i * z i= -(p i*p i) • (1:Op SpinIdx):=by simp only [z, Matrix.mul_smul,Matrix.smul_mul,gammaOne,smul_smul]; ring_nf; simp
      rw [show ∑ j∈s,z j*z i= -∑ j∈s,z i*z j by
        rw [← sum_neg_distrib]; apply sum_congr rfl; intro j hj; simp only [z, Matrix.mul_smul,Matrix.smul_mul,gammaSwap j i (fun h=>hi (h ▸ hj)),smul_neg]; module, h1]; module
  exact he _
lemma zenStar (p:Momentum)(h:physical p): star (zen p)= -zen p:=by
  unfold zen; rw [star_sum,← sum_neg_distrib]; exact Finset.sum_congr rfl fun i _=> by rw [star_smul,star_smul, (gammaAdj i).star_eq, show star (p i)=p i from congr_fun h i, show star Complex.I= -Complex.I from Complex.conj_I,neg_smul, smul_neg]
@[simp] lemma zen_zero : zen 0=0:=by simp [zen]
variable (j:ℕ)(N:Side)(h:Odd N.val){p:Momentum}
@[simp] lemma bar_origin : bar j N 0=1-Aop:=by simp only [bar,skin_origin,zen_zero,mul_zero,add_zero,shell_origin, Adef]; module
lemma bar_side (hp:p∈ realCube zone): Aop*bar j N p=(shell j N p) • (Aop*(1+zen (mixL j N p))) ∧
    (1-Aop)*(1-bar j N p)= (shell j N p) • ((1-Aop)*(1+zen (mixL j N p))):=by
  rw [bar,skin_mix j N hp, zenS]; simp only [mul_add, Matrix.mul_smul, ← mul_assoc Aop, show Aop*grading=Aop from (BZ.atom 0).plusChir, Matrix.smul_mul]
  have he : ((1:Op SpinIdx)-Aop)*grading= -(1-Aop):=by rw [ordA]; simp only [mul_sub,Matrix.mul_smul,sub_mul,mul_one,one_mul,AOne]; module
  constructor
  · rw [mul_one]; module
  rw [mul_sub]; -- inspect
  simp only [mul_add,Matrix.mul_smul,← mul_assoc,he,mul_one, neg_mul, smul_neg]; module
lemma graphs_ne {v:Momentum}(h:physical v): 1+prodM v v≠0:=by
  rw [prodM_self v h]; norm_cast; have hh : 0≤∑ i:Axis,(v i).re^2:=sum_nonneg fun i _=> sq_nonneg _; linarith
lemma bar_full (hp:p∈realCube zone)(hg:p≠0)(hn : 1+prodM (mixL j N p) (mixL j N p)≠0):
    bar j N p=(shell j N p) • ((1-zen (mixL j N p))*Aop*(1+zen (mixL j N p))) ∧
    1-bar j N p=(shell j N p) • ((1-zen (mixL j N p))*(1-Aop)*(1+zen (mixL j N p))):=by
  let v := mixL j N p; let s := prodM v v; let Z:=zen v; let k:=shell j N p
  have hh:(k*s)=1-k:= eq_sub_of_add_eq (by rw [add_comm]; calc k+k*s=k*(1+s):=by ring
                                                             _ =1:= by change shell j N p*(1+s)=1; rw [shell_inv _ _ hp hg]; exact inv_mul_cancel₀ hn)
  have he:Z*Aop=(1-Aop)*Z := (zenAA v).symm
  have ht:Z*Aop*Z= -s • (1-Aop):=by rw [he,mul_assoc,show Z*Z= -s • 1 from zenSq v, Matrix.mul_smul,mul_one]
  change bar j N p=k • ((1-Z)*Aop*(1+Z)) ∧ _= k • ((1-Z)*(1-Aop)*(1+Z))
  have hx: bar j N p=k • ((1-Z)*Aop*(1+Z)) := by
    rw [bar,skin_mix j N hp,zenS]
    change (1/2:ℂ) • (1:Op SpinIdx)+(k-1/2) • grading+grading*(k • Z)=_
    rw [mul_add,mul_one,sub_mul,sub_mul,one_mul, ht,he,ordA]; simp only [Matrix.mul_smul,Matrix.smul_mul, sub_mul,one_mul]
    rw [smul_add, smul_sub k (Aop*Z),smul_smul k (-s),mul_neg,hh]; module
  refine ⟨hx,?_⟩; rw [hx,show (1-Z)*(1-Aop)*(1+Z)=(1+s) • (1:Op SpinIdx)-(1-Z)*Aop*(1+Z) by
    rw [mul_sub _ 1 Aop, mul_one,sub_mul _ ((1-Z)*Aop),sub_mul (1:Op SpinIdx) Z,one_mul,mul_add,mul_one,show Z*Z= -s • 1 from zenSq v]; module, smul_sub, smul_smul, mul_add k, hh]; module
lemma bar_frames (hp:p∈realCube zone)(hg:p≠0)(h:Odd N.val): bar j N p*bar j N p=bar j N p ∧ star (bar j N p)=bar j N p:=by
  let v:=mixL j N p; have hh:=graphs_ne (phys_mix j N h _ hp.1)
  rw [(bar_full j N hp hg hh).1, shell_inv _ _ hp hg];
  change ((1+prodM v v)⁻¹ • _)*_=_ ∧ _=_
  have he := zenSq v
  let k:= prodM v v; let Z:=zen v
  constructor
  · change ((1+k)⁻¹ • ((1-Z)*Aop*(1+Z))) * ((1+k)⁻¹ • ((1-Z)*Aop*(1+Z)))=_
    rw [Matrix.smul_mul,Matrix.mul_smul,mul_assoc ((1-Z)*Aop), ← mul_assoc (1+Z), ← mul_assoc (1+Z),show (1+Z)*(1-Z)=(1+k) • (1:Op SpinIdx) by
      rw [add_mul,one_mul,mul_sub,mul_one,show Z*Z= -k • 1 from he]; module]
    simp only [Matrix.smul_mul,Matrix.mul_smul,one_mul,← mul_assoc, mul_assoc (1-Z) Aop Aop,AOne,inv_smul_smul₀ hh,v,Z,k]
  simp only [star_smul,star_mul,star_add,star_one, Aadj,star_sub, zenStar _ (phys_mix j N h _ hp.1),star_inv₀,
    prodM_self _ (phys_mix j N h _ hp.1)]; simp [sub_eq_add_neg,mul_assoc]
end YM.CF.Fir
