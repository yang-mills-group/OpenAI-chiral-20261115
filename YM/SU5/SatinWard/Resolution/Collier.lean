import YM.SU5.SatinWard.Resolution.BeyondSea
import YM.CF.Matter.Mass
/-! # color multiplicities - commutant on the ACTUAL slot -/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 4000
noncomputable section
namespace YM.CF.Mezzo
open Function NormedSpace Lattice Finset Cube Lat Fock Tulip Peaks Drapes SU Ember
open Rush Scroll Paige Spire Fir Bloch Next.Free Dial ExTwo
open scoped Topology Matrix MatrixOrder Kronecker Classical BigOperators InnerProductSpace Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
local notation "T"=> Ten
local notation "𝕂"=> Op (Fin 5)
local notation "M"=> Op (Fin 3)
abbrev suite :Op Sheet:=Join.both 1 0
abbrev leaf :Op Sheet:=Join.both 0 1
lemma suitePlus : suite+leaf=1:=by ext (i|i) (j|j)<;>simp [suite,leaf,Join.both,Matrix.one_apply]
lemma starSuite:star suite=suite:=by rw [suite,Join.star_both,star_one,star_zero]
lemma starLeaf:star leaf=leaf:=by rw [leaf,Join.star_both,star_one,star_zero]
lemma cc_suite:cc suite=suite:=by ext (i|i) (j|j)<;>simp [suite,Join.both, Matrix.one_apply]; try rfl
lemma cc_leaf:cc leaf=leaf:=by ext (i|i) (j|j)<;>simp [leaf,Join.both, Matrix.one_apply]; try rfl
local notation "▪"=> Op Slot
abbrev sonnet (A B:M):▪:= A⊗ₖ suite+B⊗ₖ leaf
lemma firmSuite(A B:M)(i:E) : Commute (matter i).val (sonnet A B):=by
 have he(a b:M):Commute (matter i).val (a⊗ₖ suite):=by unfold Commute SemiconjBy; rw [matter_matrix,triple,each,suite,op_kron_mul,op_kron_mul,Join.both_mul,Join.both_mul]; simp
 have hh(a b:M):Commute (matter i).val (a⊗ₖ leaf):=by unfold Commute SemiconjBy; rw [matter_matrix,triple,each,leaf,op_kron_mul,op_kron_mul,Join.both_mul,Join.both_mul]; simp
 exact (he A A).add_right (hh B B)

lemma initial_jet : sonnet 1 1= 1:=by unfold sonnet; rw [←Matrix.kronecker_add,suitePlus,Matrix.one_kronecker_one]
lemma initial_flat: sonnet 0 0=0:=by simp [sonnet]
lemma coeffMul(A B C D:M):sonnet (A*C) (B*D)=sonnet A B * sonnet C D:=by
 have hx: Join.both (0:Op T) (0:𝕂)=0:=by simp [Join.both]
 unfold sonnet suite leaf; simp_rw [mul_add,add_mul,op_kron_mul,Join.both_mul,mul_zero,zero_mul,mul_one]; rw [hx]; simp
lemma coeffCC(A B:M):sonnet (cc A) (cc B)=cc (sonnet A B):=by unfold sonnet; rw [cc_add,op_cc_kron,op_cc_kron, cc_suite,cc_leaf]
lemma coeffStar(A B:M):sonnet (star A) (star B)=star (sonnet A B):=by unfold sonnet; rw [star_add,op_star_kron,op_star_kron, starSuite,starLeaf]
lemma coeffPlus(A B C D:M):sonnet (A+C) (B+D)=sonnet A B+sonnet C D:=by unfold sonnet; rw [Matrix.add_kronecker, Matrix.add_kronecker]; abel
lemma coeffScale(A B:M)(r:ℂ):sonnet (r • A) (r • B) = r • sonnet A B:=by unfold sonnet; rw [Matrix.smul_kronecker, Matrix.smul_kronecker, smul_add] -- tune
abbrev legC (q:Fin 3)(A:Sheet):Slot:=(q,A)
def ac:Sheet:=.inl ⟨(0,1),by decide⟩
def ab:Sheet:=.inr 0
abbrev passage (A:▪)(L K:Sheet): M:= A.submatrix (legC · L) (legC · K)
abbrev scrollW (A:▪) (i j:Fin 3): Op Sheet:= A.submatrix (legC i) (legC j)
lemma coeffJoint(A B:M):passage (sonnet A B) ac ac=A ∧ passage (sonnet A B) ab ab=B:=by constructor <;> ext i j<;> simp [passage, Matrix.submatrix_apply,legC,suite,leaf,ac,ab,Join.both,sonnet] -- tune
lemma rotorScroll(i:E): (matter i).val=(1:M)⊗ₖ each (fund i):=rfl
lemma scroll_l (B:Op Sheet)(C:▪)(i j:Fin 3): scrollW (((1:M)⊗ₖ B)*C) i j=B*scrollW C i j:=by
 ext p q; rw [scrollW,Matrix.submatrix_apply]; simp only [Matrix.mul_apply,legC,Matrix.kronecker_apply,Slot,Fintype.sum_prod_type,Matrix.one_apply,ite_mul,zero_mul,one_mul]; rw [sum_eq_single i]; swap; intro a _ h; simp [Ne.symm h]; swap; simp
 simp [scrollW,legC]
lemma scroll_r (B:Op Sheet)(C:▪)(i j:Fin 3): scrollW (C*((1:M)⊗ₖ B)) i j=scrollW C i j*B:=by
 ext p q; rw [scrollW,Matrix.submatrix_apply]; simp only [Matrix.mul_apply,legC,Matrix.kronecker_apply,Slot,Fintype.sum_prod_type,Matrix.one_apply,ite_mul,zero_mul,one_mul,mul_ite, mul_zero]; rw [sum_eq_single j]; swap; intro a _ h; simp [h]; swap; simp
 simp [scrollW,legC]
lemma scroll_receipt (C:▪)(i j:Fin 3)(g:E)(p:Commute C (matter g).val): Commute (scrollW C i j) (each (fund g)):=by
 unfold Commute SemiconjBy; rw [←scroll_l,←scroll_r]; exact congrArg (fun B=>scrollW B i j) p.eq
-- charge and diagonal probes
section
abbrev toneC :Sheet→ℕ:= Sum.elim (fun _=>2) (fun _=>4)
-- ± generator test within each colour irrep.Would rather exact orientation
-- issuer of indices
variable (α:Type*)(v:ℂ)
def peal (g:Bool):ℂ:=if g then -1 else 1
abbrev blastSign {α:Type} [DecidableEq α](a:α)(x:α):ℂ:=peal (decide (a=x))
variable {I:Type}[DecidableEq I][Fintype I]
def pealU (a:I):UNI I:=by
 let B:=Matrix.diagonal (blastSign a); refine ⟨B,?_⟩; apply Matrix.mem_unitaryGroup_iff.mpr; have hx : star B=B:=by
    ext i j; by_cases p:i=j <;> by_cases h:i=a <;> simp_all [B,Matrix.diagonal_apply,blastSign,peal,Ne.symm, apply_ite star,eq_comm]
 rw [hx,show B=_ from (rfl:B=Matrix.diagonal _),Matrix.diagonal_mul_diagonal]; ext i j; by_cases h:i=j<;>by_cases p:i=a<;>simp_all [blastSign,peal, Matrix.one_apply]; try rfl
lemma pealU_det(a:I): (pealU a).val.det= -1:=by
 let B:=Matrix.diagonal (blastSign a); change B.det=_; rw [Matrix.det_diagonal, Finset.prod_eq_single a]; simp [blastSign,peal]; all_goals simp +contextual [blastSign,peal,Ne.symm]

def siren(a b:F):E:=⟨pealU a*pealU b,(by change Matrix.det (_*_)=(1:ℂ); rw [Matrix.det_mul,pealU_det,pealU_det]; ring)⟩
abbrev pealTone(a b:F)(i:F):= blastSign a i * blastSign b i
lemma siren_at (a b:F): fund (siren a b)=Matrix.diagonal (pealTone a b):=Matrix.diagonal_mul_diagonal ..
abbrev beyond (a b x : F):Bool:= Bool.xor (decide (a=x)) (decide (b=x))
abbrev eitherB(a b:F):Sheet→Bool:= Sum.elim (fun z:Ten=> Bool.xor (beyond a b z.val.1) (beyond a b z.val.2)) (beyond a b)
lemma tangentU (x y: Bool) :peal (Bool.xor x y)=peal x*peal y:=by cases x <;>cases y<;> simp [peal]
lemma tideU (x:Bool): star (peal x)=peal x:=by cases x<;>simp [peal]
lemma peal_inj : Injective peal:=by intro x y h; cases x<;>cases y<;> first | rfl | norm_num [peal] at h
lemma siren_tap(a b:F):each (fund (siren a b))=Matrix.diagonal (peal ∘ eitherB a b):=by
 have ht(i:F):pealTone a b i= peal (beyond a b i):= (tangentU _ _).symm
 rw [each, siren_at, wedge_diag]; ext (x|x) (y|y)
 · by_cases p:x=y; subst y; simp only [Matrix.diagonal_apply_eq,Join.both,Matrix.fromBlocks_apply₁₁,Function.comp_apply, eitherB, Sum.elim_inl]; rw [ht, ht, tangentU (beyond a b x.val.1) (beyond a b x.val.2)]
   simp [Join.both,p,Matrix.diagonal_apply]
 · simp [Join.both,Matrix.diagonal_apply]
 · simp [Join.both, Matrix.diagonal_apply]
 by_cases p:x=y
 · subst y; rw [Join.both,Matrix.fromBlocks_apply₂₂,cc_apply,Matrix.diagonal_apply_eq,Matrix.diagonal_apply_eq, ht, tideU]; rfl
 simp [Join.both,p, Matrix.diagonal_apply]

lemma distinguish: ∀ q r:Sheet, q≠ r → ∃ a b:F, eitherB a b q ≠ eitherB a b r:=by decide +kernel -- maybe across sheet actually true for F5 (pair or one distinct, xor mod all-ones)
end
section
variable {I:Type*}[DecidableEq I][Fintype I]
-- Index shear
abbrev hair (g:Equiv.Perm I): Op I:= (1:Op I).submatrix g id
lemma hair_at(g:Equiv.Perm I)(i j:I): hair g i j= if g i=j then 1 else 0:=rfl
lemma hair_mul(g f:Equiv.Perm I):hair g*hair f=hair (g.trans f):=by
 ext i j; rw [Matrix.mul_apply]; simp_rw [hair_at]; rw [sum_eq_single (g i)]; swap; intro p _ h; simp [Ne.symm h]; swap; simp
 simp
lemma hair_one: hair (Equiv.refl I)=1:=by ext; rfl
lemma hair_t(g:Equiv.Perm I):star (hair g)=hair g.symm:=by
 ext i j; simp only [Matrix.star_apply,hair_at]; by_cases p:g.symm i=j; subst j; simp; have he:g j ≠ i:=fun q=>p (by rw [←q]; simp); simp [p,he]
def hairU (g:Equiv.Perm I):UNI I:=⟨hair g,by constructor<;> rw [hair_t, hair_mul]<;>simpa using hair_one⟩
lemma hairU_cc (g:Equiv.Perm I): cc (hair g)=hair g:=by ext i j; rw [cc_apply, hair_at]; split <;> simp
lemma hair_det (g:Equiv.Perm F): (hair g).det=(g.sign.val:ℂ):=by unfold hair; rw [Matrix.det_permute, Matrix.det_one, mul_one]
-- multiply all by sign so fit SU(5)
def signCap(g:Equiv.Perm F):ℂ:=(g.sign.val:ℂ)
lemma co_pay(g:Equiv.Perm F): signCap g=1 ∨ signCap g= -1:=by
 rcases Int.units_eq_one_or (g.sign) with h|h; all_goals simp [signCap,h]
def ticketPerm (g:Equiv.Perm F):E:=by
 let A:=signCap g • hair g; let p:UNI F:= ⟨A,by
   rcases co_pay g with h|h
   · rw [show A=hair g from by unfold A; rw [h,one_smul]]; exact (hairU _).property
   rw [show A= -hair g from by unfold A; rw [h,neg_smul,one_smul]]; refine ⟨?_,?_⟩ <;> simp only [star_neg,neg_mul,mul_neg,neg_neg]
   · exact (hairU g).property.1
   exact (hairU g).property.2 ⟩
 refine ⟨p,(show A.det=1 from ?_)⟩; unfold A; rw [Matrix.det_smul,hair_det g]; change signCap g^(Fintype.card (Fin 5))*signCap g=1; rcases co_pay g with h|h <;> norm_num [h]
-- health of this color spectrum at corresponding weights
lemma coast_perm(g:Equiv.Perm F): ∀ i:F,(each (fund (ticketPerm g))) (.inr i) (.inr (g i))≠0:=by
 intro i; unfold each; simp only [Join.both, Matrix.fromBlocks_apply₂₂, cc_apply]; rw [star_ne_zero]; change signCap g • hair g i (g i)≠0; rw [hair_at g,if_pos rfl,smul_eq_mul,mul_one]; rcases co_pay g with p|p<;>simp [p]
lemma coastS_perm(g:Equiv.Perm F)(i l:Ten)(h:g i.val.1=l.val.1)(e:g i.val.2=l.val.2):(each (fund (ticketPerm g))) (.inl i) (.inl l)≠0:=by
 unfold each; simp only [Join.both, Matrix.fromBlocks_apply₁₁,wedge_entry]; rw [show fund (ticketPerm g)=signCap g • hair g from rfl]; have hz:=l.property.ne; simp only [Matrix.smul_apply,hair_at g,h,e, if_pos rfl, if_neg hz,if_neg (Ne.symm hz), smul_eq_mul, mul_zero, mul_one, sub_zero]; rcases co_pay g with h|h<;>simp [h]
lemma accessShelf(p q:T):∃ g:Equiv.Perm F,g p.val.1=q.val.1∧g p.val.2=q.val.2:=by
 let f:=Equiv.swap p.val.1 q.val.1; have hz : f p.val.1=q.val.1:=by simp [f]
 have hx : f p.val.2≠q.val.1:=fun h=> p.property.ne (f.injective (hz.trans h.symm))
 refine ⟨f.trans (Equiv.swap (f p.val.2) q.val.2),?_⟩; simp only [Equiv.trans_apply,hz,Equiv.swap_apply_left,and_true]; exact Equiv.swap_apply_of_ne_of_ne (Ne.symm hx) q.property.ne

lemma peal_commutant(X:Op Sheet)(w:∀ i:E,Commute (each (fund i)) X) : X=Join.both (X ac ac • (1:Op Ten)) (X ab ab • (1:Op F)):=by
 let d:=fun i=> X i i; have hx:X=Matrix.diagonal d:=by
    ext a b; by_cases h:a=b; subst a; rw [Matrix.diagonal_apply_eq]
    rw [Matrix.diagonal_apply_ne _ h]; obtain ⟨g,f,u⟩:=distinguish a b h; obtain H:=(w (siren g f)).eq; rw [siren_tap] at H; have he:= Matrix.ext_iff.mpr H a b; rw [Matrix.diagonal_mul,Matrix.mul_diagonal,mul_comm (X a b)] at he; by_contra h; exact u (peal_inj (mul_right_cancel₀ h he))
 have h(v:E)(i j:Sheet)(p:each (fund v) i j≠0):d i=d j:=by
    obtain H:= (w v).eq; rw [hx] at H; apply mul_left_cancel₀ p; have he:=Matrix.ext_iff.mpr H i j; rw [Matrix.diagonal_mul,Matrix.mul_diagonal,mul_comm (d i)] at he; exact he.symm
 have hq(i:T):d ac=d (.inl i):= by obtain ⟨g,p,q⟩:=accessShelf ⟨(0,1),by decide⟩ i; exact h _ _ _ (coastS_perm g _ _ p q)
 have hk(i:F):d ab=d (.inr i):=by
    let g:Equiv.Perm F:=Equiv.swap 0 i; have ht:=h (ticketPerm g) _ _ (coast_perm g 0); simpa [ab,g] using ht
 nth_rw 1 [hx]; ext (i|i) (j|j)
 · by_cases h:i=j
   · subst j; simpa [Join.both] using (hq i).symm -- unfold d?
   simp [Join.both,h]
 · simp [Join.both]
 · simp [Join.both]
 by_cases p:i=j
 · subst j; simpa [Join.both] using (hk i).symm
 simp [Join.both,p]
lemma collaborations (X:▪) (p:∀ i:E,Commute (matter i).val X): X=sonnet (passage X ac ac) (passage X ab ab):=by
 have he(i j:Fin 3):= peal_commutant (scrollW X i j) fun g=> (scroll_receipt X i j g (p g).symm).symm
 ext ⟨i,a⟩ ⟨j,b⟩; change scrollW X i j a b= _; rw [he]; cases a <;> cases b <;> simp [Join.both,scrollW,passage,legC,sonnet,suite,leaf]
end
end YM.CF.Mezzo
