import YM.CF.Acorn.Duo
set_option autoImplicit false
noncomputable section
namespace YM.CF.Acorn
open Function Filter Matrix NormedSpace Finset Fock
open scoped Matrix.Norms.L2Operator Matrix Topology MatrixOrder BigOperators
attribute [local instance] opCStarAlgebra
variable {n:Type*}[LinearOrder n][Fintype n]

def liftL (A B:FC n) : FC n→L[ℂ] FC n:= (ContinuousLinearMap.mul ℂ (FC n)) A + (ContinuousLinearMap.mul ℂ (FC n)).flip B
def unitL (A:FC n) :FC n→L[ℂ] FC n:= liftL A (-A)
lemma basic_l (A B F:FC n): liftL A B F = A*F+F*B :=rfl
lemma unitt(A F:FC n): unitL A F=A*F-F*A:=by rw [unitL,basic_l, mul_neg]; rfl
lemma unit_der (A B C: FC n): unitL A (B*C) = unitL A B * C+B*unitL A C :=by rw [unitt,unitt,unitt]; noncomm_ring
lemma start_l(A B C D:FC n):liftL A B (C*D)=unitL A C*D+C*liftL A B D:=by rw [basic_l,basic_l,unitt]; noncomm_ring
lemma nilS(A:FC n)(h: UnitR A)(i:I n): unitL A (unitL A (pen i))=0:=by rw [unitt,unitt]; exact sub_eq_zero.mpr (h.stall i).eq
lemma read_sq(A X Y: FC n)(h:unitL A (unitL A X)=0)(g:unitL A (unitL A Y)=0): unitL A (unitL A (X*Y))= (2:ℂ) • (unitL A X*unitL A Y):=by simp only [unit_der,map_add,h,g,zero_mul,mul_zero,add_zero,zero_add,two_smul]
lemma unit_nil (A:FC n)(h:UnitR A)(K:Op (I n)): unitL A (unitL A (unitL A (mix K)))=0:=by
 unfold mix; simp_rw [map_sum,map_smul,read_sq A (pen _) (pen _) (nilS A h _) (nilS A h _),map_smul,unit_der, nilS _ h,zero_mul,mul_zero,add_zero,smul_zero,sum_const_zero]
lemma unit_negR (A:FC n)(h:UnitR A): UnitR (-A):=by
 refine ⟨fun i e=>by rw [neg_pow,h.exhaust i e,mul_zero],fun i=>?_⟩
 rw [show -A * pen i-pen i*(-A) = -(A*pen i-pen i*A) by rw [neg_mul,mul_neg]; abel]; exact (h.stall i).neg_left.neg_right

def sent (U: FC n→L[ℂ] FC n)(k:ℕ)(P:FC n) := ((k.factorial:ℂ)⁻¹) • ((U^k) P)
def drum (k:ℕ)(U:FC n):FC n:= ((k.factorial:ℂ)⁻¹) • U^k
lemma sent_calc(U:FC n→L[ℂ] FC n)(k:ℕ)(P:FC n): U (sent U k P)= (k+1:ℂ) • sent U (k+1) P:=by
 rw [sent,map_smul,sent, pow_succ']; change _ • ((U ∘L _) _) =_; rw [smul_smul,Nat.factorial_succ]; push_cast
 congr 1; have he : (k+1:ℂ)≠0:=by exact_mod_cast (by omega : k+1 ≠ 0)
 field_simp
@[simp] lemma sent_zero(U:FC n→L[ℂ] FC n)(x:FC n): sent U 0 x=x:=by simp [sent]
lemma walk_l(A B C D:FC n)(k:ℕ): sent (liftL A B) k (C*D) =∑ i∈ Finset.antidiagonal k, sent (unitL A) i.1 C * sent (liftL A B) i.2 D:=by
 induction k with
 | zero=>simp
 | succ k ih=>
  let U:=liftL A B; let f i:=sent (unitL A) i C; let g i:= sent U i D
  have he : (k+1:ℂ)≠0:=by exact_mod_cast (show k+1≠0 by omega)
  apply smul_right_injective _ he; change (k+1:ℂ) • sent (liftL A B) (k+1) _=_; rw [← sent_calc,ih,map_sum]; simp only [Finset.smul_sum]
  simp_rw [start_l,sent_calc]; rw [Finset.sum_add_distrib]
  change _ = ∑ i∈ Finset.antidiagonal (k+1),(k+1:ℂ) • (f i.1*g i.2)
  have hp (z:ℕ×ℕ)(h:z∈Finset.antidiagonal (k+1)) : (k+1:ℂ) • (f z.1*g z.2)= (z.1:ℂ) • f z.1*g z.2+f z.1*((z.2:ℂ) • g z.2):=by
     have hz : (z.1:ℂ)+z.2=(k+1:ℂ):=by exact_mod_cast (Finset.mem_antidiagonal.mp h)
     rw [← hz,add_smul,Algebra.smul_mul_assoc,Algebra.mul_smul_comm]
  rw [Finset.sum_congr rfl (fun i hi=> hp i hi),Finset.sum_add_distrib]; congr 1
  · rw [Finset.Nat.sum_antidiagonal_succ]; simp [f,g,U] -- tune orientation
  rw [Finset.Nat.sum_antidiagonal_succ']; simp [f,g,U]
lemma cash_d (A:FC n)(k:ℕ): A*drum k A=(k+1:ℂ) • drum (k+1) A:=by
  rw [drum,drum, Algebra.mul_smul_comm,pow_succ',smul_smul,Nat.factorial_succ]; push_cast; congr 1
  have he: (k+1:ℂ)≠0:=by exact_mod_cast (show k+1≠0 by omega)
  field_simp
lemma cash_b (A: FC n)(k:ℕ): drum k A*A=(k+1:ℂ) • drum (k+1) A:= by rw [←cash_d,drum, Algebra.smul_mul_assoc,Algebra.mul_smul_comm,← pow_succ,←pow_succ']
@[simp] lemma drum_zero (A:FC n): drum 0 A=1:=by simp [drum]
lemma duo_c (A B C:FC n)(k:ℕ): sent (liftL A B) k C=∑ i∈Finset.antidiagonal k, drum i.1 A*C*drum i.2 B:=by
 induction k with
 | zero=>simp
 | succ k ih=>
  let f i:=drum i A; let g i:=drum i B
  have he : (k+1:ℂ)≠0:=by exact_mod_cast (show k+1≠0 by omega)
  apply smul_right_injective _ he; change (k+1:ℂ) • sent (liftL A B) (k+1) _=_; rw [← sent_calc,ih,map_sum]; simp only [Finset.smul_sum]
  simp_rw [basic_l A B (drum _ _ * _ * _),← mul_assoc A,cash_d,mul_assoc (_ * C) _ B,cash_b]; rw [Finset.sum_add_distrib]
  let S:= Finset.antidiagonal (k+1); change _= ∑ i∈ S,(k+1:ℂ) • (f i.1*C*g i.2)
  have hp (z:ℕ×ℕ)(h:z∈Finset.antidiagonal (k+1)) : (k+1:ℂ) • (f z.1*C*g z.2)= (z.1:ℂ) • f z.1*C*g z.2+f z.1*C*((z.2:ℂ) • g z.2):=by
     have hz : (z.1:ℂ)+z.2=(k+1:ℂ):=by exact_mod_cast (Finset.mem_antidiagonal.mp h)
     rw [← hz,add_smul, Algebra.smul_mul_assoc,Algebra.smul_mul_assoc,Algebra.mul_smul_comm]
  rw [sum_congr rfl hp,sum_add_distrib]; congr 1
  · rw [Finset.Nat.sum_antidiagonal_succ]; simp [f,g]
  rw [Finset.Nat.sum_antidiagonal_succ']; simp [f,g]
lemma rotary (A:FC n)(h:nilX A)(k)(t:Fintype.card n≤k): ∑ i∈ range (k+1),drum i A=exp A:=by
 rw [exp_eq_tsum ℂ]; dsimp only; rw [tsum_eq_sum (s:=range (k+1))]; rfl
 intro i hi; rw [mem_range,not_lt] at hi; rw [h i (by omega),smul_zero]
lemma rotor {A B:FC n}(h:nilX A)(g:nilX B) (C:FC n) : exp A*C*exp B=∑ i∈range (2*Fintype.card n+1), sent (liftL A B) i C:=by
 let a:= Fintype.card n; let T (n):=range (n+1)
 rw [←rotary A h _ le_rfl,←rotary B g _ le_rfl, sum_mul,sum_mul_sum,← sum_product']; simp_rw [duo_c]; rw [← sum_biUnion]
 · let S:= (T (2*a)).biUnion fun i=>Finset.antidiagonal i; refine sum_subset ?_ ?_
   · rintro ⟨k,l⟩ ht; obtain ⟨u,v⟩:=mem_product.mp ht; apply mem_biUnion.mpr; refine ⟨k+l,mem_range.mpr ?_,by simp⟩; simp only [mem_range] at *; omega
   rintro ⟨i,j⟩ p h'; simp only [mem_product,not_and_or,mem_range,not_lt] at h'
   change drum i A*C*drum j B=0; unfold drum; rcases h' with v|v
   · have hk:Fintype.card n < i :=by omega
     rw [h i hk]; simp
   rw [g j (by omega), smul_zero, mul_zero]
 intro i _ j _ u; exact disjoint_left.mpr fun k h g=>u ((mem_antidiagonal.mp h).symm.trans (mem_antidiagonal.mp g))
lemma abyss (U:FC n→L[ℂ] FC n)(A:FC n){k:ℕ}(h:(U^k) A=0)(i : ℕ) (e:k ≤ i):sent U i A=0:=by rw [sent,show i=i-k+k by omega,pow_add]; change _ • ((U^(i-k)) ((U^k) A))=0; rw [h,map_zero,smul_zero]
lemma repel (A:FC n)(h:UnitR A)(i:I n): exp A *pen i * exp (-A)=pen i+(unitL A) (pen i):=by
 have hg := (rotor h.exhaust (unit_negR A h).exhaust (pen i)); rw [hg]
 have hx : Nonempty n:= ⟨i.2⟩; change ∑ k∈_, sent (unitL _) _ _=_
 rw [← sum_subset (s₁:=range 2) (Finset.range_mono ?_)] -- tune
 · simp [Finset.sum_range_succ,sent]
 · intro k _ h'; exact abyss (k:=2) (unitL A) (pen i) (by rw [pow_two]; exact nilS A h i) k (by simp only [Finset.mem_range, not_lt] at h'; exact h')
 have he : 0 < Fintype.card n:= Fintype.card_pos; omega
lemma cascade (A B:FC n)(K:Op (I n))(g: A+B=mix K)(k:ℕ)(h:UnitR A):
   (k+1:ℂ) • sent (liftL A B) (k+1) 1=∑ i∈(Finset.antidiagonal k).filter (fun i=> i.1 ≤ 2), sent (unitL A) i.1 (mix K) * sent (liftL A B) i.2 1:=by
 let X:=liftL A B; let y:= A+B; have ht: (liftL A B) (sent X k 1)=sent X k (mix K*1) :=by
   rw [mul_one, ←g,sent,sent,map_smul, show ∀ l,(liftL A B) ((X^l) 1)=((X^l) (A+B)) from ?_]
   intro l; rw [show A+B=X 1 by simp [X,basic_l]]; change (X*X^l) 1=(X^l*X) 1; rw [(Commute.refl X).pow_right l|>.eq]
 rw [←sent_calc,ht,walk_l]; apply Eq.symm; refine Finset.sum_subset (filter_subset ..) (fun i hi t=>?_); rw [mem_filter, Classical.not_and_iff_not_or_not] at t -- tune
 have he := unit_nil A h K
 rw [abyss (unitL A) (mix K) (k:=3) (by rw [pow_succ',pow_two]; exact he) i.1 ?_, zero_mul]; exact Nat.lt_of_not_ge (t.resolve_left (not_not.mpr hi))
end YM.CF.Acorn
