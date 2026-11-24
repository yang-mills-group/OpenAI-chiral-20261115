import YM.SU5.WakeFields.Postulator
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 350000
noncomputable section
--! Wick coupons at four billing slots. Perm identity generator (check kernel).
namespace YM.CF.Emu.SpinTable
open Finset Filter Fock Postulator
open scoped Matrix BigOperators
-- alpha color slot abstract. use Lean's dec. finite, no positivity needed.
variable {J V :Type*}[Fintype J][Fintype V][DecidableEq V]
variable (K:J→ J→ℂ)(X Y: V→V→ℂ)
abbrev Sig (J V:Type*) := J × V × Bool
-- component includes Spin factor
def entry (x y:J)(a b:V) :ℂ:= if a=b then K x y else 0
def germ (x y: Sig J V) : ℂ:= match x.2.2,y.2.2 with
 | true,false=> entry K x.1 y.1 x.2.1 y.2.1
 | false,true=> -entry K y.1 x.1 y.2.1 x.2.1
 | _,_=> 0

variable (p q m n:J)(a b i j u v:V)(h:∀ i, K i i=0)
abbrev hands (x:J)(a b:V): List (Sig J V):= [(x,b,true), (x,a,false)]
abbrev body4 (p q m n:J) (a b i j u v:V) := runes (germ K) (hands p a b ++ hands q i j ++ hands m u u ++ hands n v v)
abbrev body2 (p q:J) (a b i j:V) := runes (germ K) (hands p a b ++ hands q i j)
include h
lemma no_self : entry K p p a b=0:= by simp [entry,h]
lemma corporeal : body2 K p q a b i j= -(entry K p q b i*entry K q p j a):=by
 simp [body2,hands,readHead,picks,beside,cval,germ,no_self K _ _ _ h,empt]
omit h
def P1032 (K:J→ J→ℂ)(p q m n:J)(a b i j u v:V) :ℂ := entry K p q b i*entry K q p j a*entry K m n u v*entry K n m v u
def P2301 (K:J→ J→ℂ)(p q m n:J)(a b i j u v:V) :ℂ := entry K p m b u*entry K q n j v*entry K m p u a*entry K n q v i
def P3210 (K:J→ J→ℂ)(p q m n:J)(a b i j u v:V) :ℂ := entry K p n b v*entry K q m j u*entry K m q u i*entry K n p v a
def P1230 (K:J→ J→ℂ)(p q m n:J)(a b i j u v:V) :ℂ := entry K p q b i*entry K q m j u*entry K m n u v*entry K n p v a
def P1302 (K:J→ J→ℂ)(p q m n:J)(a b i j u v:V) :ℂ := entry K p q b i*entry K q n j v*entry K m p u a*entry K n m v u
def P2031 (K:J→ J→ℂ)(p q m n:J)(a b i j u v:V) :ℂ := entry K p m b u*entry K q p j a*entry K m n u v*entry K n q v i
def P2310 (K:J→ J→ℂ)(p q m n:J)(a b i j u v:V) :ℂ := entry K p m b u*entry K q n j v*entry K m q u i*entry K n p v a
def P3012 (K:J→ J→ℂ)(p q m n:J)(a b i j u v:V) :ℂ := entry K p n b v*entry K q p j a*entry K m q u i*entry K n m v u
def P3201 (K:J→ J→ℂ)(p q m n:J)(a b i j u v:V) :ℂ := entry K p n b v*entry K q m j u*entry K m p u a*entry K n q v i
include h
set_option maxHeartbeats 600000 in
lemma price4 : body4 K p q m n a b i j u v=
   P1032 K p q m n a b i j u v+P2301 K p q m n a b i j u v+P3210 K p q m n a b i j u v-P1230 K p q m n a b i j u v-P1302 K p q m n a b i j u v-P2031 K p q m n a b i j u v-P2310 K p q m n a b i j u v-P3012 K p q m n a b i j u v-P3201 K p q m n a b i j u v :=by
 unfold P1032 P2301 P3210 P1230 P1302 P2031 P2310 P3012 P3201
 simp [body4,hands,readHead,picks,beside,cval,germ,no_self K _ _ _ h,empt]; ring
omit h
abbrev rentOne (X:V→V→ℂ) := ∑ x:V,X x x
abbrev rentBoth (X Y:V→V→ℂ) := ∑ x:V,∑ i:V,X x i*Y i x
abbrev total (f:V→V→V→V→V→V→ℂ) := ∑ a:V,∑ b:V,∑ i:V,∑ j:V,∑ u:V,∑ v:V,X a b*Y i j*f a b i j u v
lemma unique (x:V) (f:V→ℂ)(t:∀ y,y≠x→f y=0){g:ℂ}(p:f x=g): ∑ y:V, f y=g:=(sum_eq_single_of_mem x (mem_univ _) (fun i _=> t i)).trans p

lemma billP1032 : total X Y (P1032 K p q m n)=rentBoth X Y*(Fintype.card V:ℂ)*(K p q*K q p*K m n*K n m):=by
  trans (∑ a:V,∑ b:V,∑ u:V,X a b*Y b a*(K p q*K q p*K m n*K n m))
  · unfold total
    apply sum_congr rfl; intro a _
    apply sum_congr rfl; intro b _
    apply unique b; · intro i t_k; apply sum_eq_zero; intro j _; apply sum_eq_zero; intro u _; apply sum_eq_zero; intro v _
                      simp only [P1032, entry]
                      split_ifs <;> (expose_names; grind only)
    apply unique a; · intro j t_k; apply sum_eq_zero; intro u _; apply sum_eq_zero; intro v _
                      simp only [P1032, entry]
                      split_ifs <;> (expose_names; grind only)
    apply sum_congr rfl; intro u _
    apply unique u; · intro v t_k
                      simp only [P1032, entry]
                      split_ifs <;> (expose_names; grind only)
    simp [P1032, entry]
  · unfold rentBoth; simp_rw [sum_mul]; simp [mul_assoc,mul_left_comm,mul_comm]

lemma billP2301 : total X Y (P2301 K p q m n)=rentOne X * rentOne Y*(K p m*K q n*K m p*K n q):=by
  trans (∑ a:V,∑ i:V,X a a*Y i i*(K p m*K q n*K m p*K n q))
  · unfold total
    apply sum_congr rfl; intro a _
    apply unique a; · intro b t_k; apply sum_eq_zero; intro i _; apply sum_eq_zero; intro j _; apply sum_eq_zero; intro u _; apply sum_eq_zero; intro v _
                      simp only [P2301, entry]
                      split_ifs <;> (expose_names; grind only)
    apply sum_congr rfl; intro i _
    apply unique i; · intro j t_k; apply sum_eq_zero; intro u _; apply sum_eq_zero; intro v _
                      simp only [P2301, entry]
                      split_ifs <;> (expose_names; grind only)
    apply unique a; · intro u t_k; apply sum_eq_zero; intro v _
                      simp only [P2301, entry]
                      split_ifs <;> (expose_names; grind only)
    apply unique i; · intro v t_k
                      simp only [P2301, entry]
                      split_ifs <;> (expose_names; grind only)
    simp [P2301, entry]
  · unfold rentOne; simp_rw [sum_mul,mul_sum,sum_mul]

lemma billP3210 : total X Y (P3210 K p q m n)=rentOne X * rentOne Y*(K p n*K q m*K m q*K n p):=by
  trans (∑ a:V,∑ i:V,X a a*Y i i*(K p n*K q m*K m q*K n p))
  · unfold total
    apply sum_congr rfl; intro a _
    apply unique a; · intro b t_k; apply sum_eq_zero; intro i _; apply sum_eq_zero; intro j _; apply sum_eq_zero; intro u _; apply sum_eq_zero; intro v _
                      simp only [P3210, entry]
                      split_ifs <;> (expose_names; grind only)
    apply sum_congr rfl; intro i _
    apply unique i; · intro j t_k; apply sum_eq_zero; intro u _; apply sum_eq_zero; intro v _
                      simp only [P3210, entry]
                      split_ifs <;> (expose_names; grind only)
    apply unique i; · intro u t_k; apply sum_eq_zero; intro v _
                      simp only [P3210, entry]
                      split_ifs <;> (expose_names; grind only)
    apply unique a; · intro v t_k
                      simp only [P3210, entry]
                      split_ifs <;> (expose_names; grind only)
    simp [P3210, entry]
  · unfold rentOne; simp_rw [sum_mul,mul_sum,sum_mul]

lemma billP1230 : total X Y (P1230 K p q m n)=rentBoth X Y*(K p q*K q m*K m n*K n p):=by
  trans (∑ a:V,∑ b:V,X a b*Y b a*(K p q*K q m*K m n*K n p))
  · unfold total
    apply sum_congr rfl; intro a _
    apply sum_congr rfl; intro b _
    apply unique b; · intro i t_k; apply sum_eq_zero; intro j _; apply sum_eq_zero; intro u _; apply sum_eq_zero; intro v _
                      simp only [P1230, entry]
                      split_ifs <;> (expose_names; grind only)
    apply unique a; · intro j t_k; apply sum_eq_zero; intro u _; apply sum_eq_zero; intro v _
                      simp only [P1230, entry]
                      split_ifs <;> (expose_names; grind only)
    apply unique a; · intro u t_k; apply sum_eq_zero; intro v _
                      simp only [P1230, entry]
                      split_ifs <;> (expose_names; grind only)
    apply unique a; · intro v t_k
                      simp only [P1230, entry]
                      split_ifs <;> (expose_names; grind only)
    simp [P1230, entry]
  · unfold rentBoth; simp_rw [sum_mul]

lemma billP1302 : total X Y (P1302 K p q m n)=rentBoth X Y*(K p q*K q n*K m p*K n m):=by
  trans (∑ a:V,∑ b:V,X a b*Y b a*(K p q*K q n*K m p*K n m))
  · unfold total
    apply sum_congr rfl; intro a _
    apply sum_congr rfl; intro b _
    apply unique b; · intro i t_k; apply sum_eq_zero; intro j _; apply sum_eq_zero; intro u _; apply sum_eq_zero; intro v _
                      simp only [P1302, entry]
                      split_ifs <;> (expose_names; grind only)
    apply unique a; · intro j t_k; apply sum_eq_zero; intro u _; apply sum_eq_zero; intro v _
                      simp only [P1302, entry]
                      split_ifs <;> (expose_names; grind only)
    apply unique a; · intro u t_k; apply sum_eq_zero; intro v _
                      simp only [P1302, entry]
                      split_ifs <;> (expose_names; grind only)
    apply unique a; · intro v t_k
                      simp only [P1302, entry]
                      split_ifs <;> (expose_names; grind only)
    simp [P1302, entry]
  · unfold rentBoth; simp_rw [sum_mul]

lemma billP2031 : total X Y (P2031 K p q m n)=rentBoth X Y*(K p m*K q p*K m n*K n q):=by
  trans (∑ a:V,∑ b:V,X a b*Y b a*(K p m*K q p*K m n*K n q))
  · unfold total
    apply sum_congr rfl; intro a _
    apply sum_congr rfl; intro b _
    apply unique b; · intro i t_k; apply sum_eq_zero; intro j _; apply sum_eq_zero; intro u _; apply sum_eq_zero; intro v _
                      simp only [P2031, entry]
                      split_ifs <;> (expose_names; grind only)
    apply unique a; · intro j t_k; apply sum_eq_zero; intro u _; apply sum_eq_zero; intro v _
                      simp only [P2031, entry]
                      split_ifs <;> (expose_names; grind only)
    apply unique b; · intro u t_k; apply sum_eq_zero; intro v _
                      simp only [P2031, entry]
                      split_ifs <;> (expose_names; grind only)
    apply unique b; · intro v t_k
                      simp only [P2031, entry]
                      split_ifs <;> (expose_names; grind only)
    simp [P2031, entry]
  · unfold rentBoth; simp_rw [sum_mul]

lemma billP2310 : total X Y (P2310 K p q m n)=rentBoth X Y*(K p m*K q n*K m q*K n p):=by
  trans (∑ a:V,∑ b:V,X a b*Y b a*(K p m*K q n*K m q*K n p))
  · unfold total
    apply sum_congr rfl; intro a _
    apply sum_congr rfl; intro b _
    apply unique b; · intro i t_k; apply sum_eq_zero; intro j _; apply sum_eq_zero; intro u _; apply sum_eq_zero; intro v _
                      simp only [P2310, entry]
                      split_ifs <;> (expose_names; grind only)
    apply unique a; · intro j t_k; apply sum_eq_zero; intro u _; apply sum_eq_zero; intro v _
                      simp only [P2310, entry]
                      split_ifs <;> (expose_names; grind only)
    apply unique b; · intro u t_k; apply sum_eq_zero; intro v _
                      simp only [P2310, entry]
                      split_ifs <;> (expose_names; grind only)
    apply unique a; · intro v t_k
                      simp only [P2310, entry]
                      split_ifs <;> (expose_names; grind only)
    simp [P2310, entry]
  · unfold rentBoth; simp_rw [sum_mul]

lemma billP3012 : total X Y (P3012 K p q m n)=rentBoth X Y*(K p n*K q p*K m q*K n m):=by
  trans (∑ a:V,∑ b:V,X a b*Y b a*(K p n*K q p*K m q*K n m))
  · unfold total
    apply sum_congr rfl; intro a _
    apply sum_congr rfl; intro b _
    apply unique b; · intro i t_k; apply sum_eq_zero; intro j _; apply sum_eq_zero; intro u _; apply sum_eq_zero; intro v _
                      simp only [P3012, entry]
                      split_ifs <;> (expose_names; grind only)
    apply unique a; · intro j t_k; apply sum_eq_zero; intro u _; apply sum_eq_zero; intro v _
                      simp only [P3012, entry]
                      split_ifs <;> (expose_names; grind only)
    apply unique b; · intro u t_k; apply sum_eq_zero; intro v _
                      simp only [P3012, entry]
                      split_ifs <;> (expose_names; grind only)
    apply unique b; · intro v t_k
                      simp only [P3012, entry]
                      split_ifs <;> (expose_names; grind only)
    simp [P3012, entry]
  · unfold rentBoth; simp_rw [sum_mul]

lemma billP3201 : total X Y (P3201 K p q m n)=rentBoth X Y*(K p n*K q m*K m p*K n q):=by
  trans (∑ a:V,∑ b:V,X a b*Y b a*(K p n*K q m*K m p*K n q))
  · unfold total
    apply sum_congr rfl; intro a _
    apply sum_congr rfl; intro b _
    apply unique b; · intro i t_k; apply sum_eq_zero; intro j _; apply sum_eq_zero; intro u _; apply sum_eq_zero; intro v _
                      simp only [P3201, entry]
                      split_ifs <;> (expose_names; grind only)
    apply unique a; · intro j t_k; apply sum_eq_zero; intro u _; apply sum_eq_zero; intro v _
                      simp only [P3201, entry]
                      split_ifs <;> (expose_names; grind only)
    apply unique a; · intro u t_k; apply sum_eq_zero; intro v _
                      simp only [P3201, entry]
                      split_ifs <;> (expose_names; grind only)
    apply unique b; · intro v t_k
                      simp only [P3201, entry]
                      split_ifs <;> (expose_names; grind only)
    simp [P3201, entry]
  · unfold rentBoth; simp_rw [sum_mul]

include h
abbrev total2 (f: V→V→V→V→ℂ):= ∑ a:V,∑ b:V,∑ i:V,∑ j:V,X a b*Y i j*f a b i j
lemma trace2 : total2 X Y (body2 K p q)=rentBoth X Y * (-(K p q*K q p)):=by
  unfold total2 rentBoth
  simp_rw [corporeal K p q _ _ _ _ h, sum_mul]; refine sum_congr rfl fun a _=> sum_congr rfl fun b _=>?_
  apply unique b
  · intro i v; apply sum_eq_zero; intro j _; simp [entry,v.symm]
  apply unique a
  · intro j v; simp [entry,v]
  simp [entry] -- maybe goals closed prematurely
lemma pure2 : (∑ u:V,∑ v:V, body2 K m n u u v v)= (Fintype.card V:ℂ) * (-(K m n*K n m)):=by
  have W(u:V): (∑ v:V,body2 K m n u u v v)= -(K m n*K n m):=by
    rw [sum_eq_single_of_mem u (mem_univ _)]; swap; · intro i _ v; rw [corporeal K m n _ _ _ _ h]; simp only [entry,if_neg v, mul_zero,neg_zero]; 
    rw [corporeal K m n _ _ _ _ h]; simp [entry]
  simp_rw [W]; simp

omit h
def realPlane (p q m n:J) := (K p q*K q m*K m n*K n p+K p q*K q n*K m p*K n m+K p m*K q p*K m n*K n q+K p m*K q n*K m q*K n p+K p n*K q p*K m q*K n m+K p n*K q m*K m p*K n q)
include h
lemma spinPlane (x:rentOne X=0) : (total X Y (body4 K p q m n))-(total2 X Y (body2 K p q))*(∑ u:V,∑ v:V, body2 K m n u u v v)= -rentBoth X Y * realPlane K p q m n:=by
 rw [show (total X Y (body4 K p q m n))=
    total X Y (P1032 K p q m n)+total X Y (P2301 K p q m n)+total X Y (P3210 K p q m n)-total X Y (P1230 K p q m n)-total X Y (P1302 K p q m n)-total X Y (P2031 K p q m n)-total X Y (P2310 K p q m n)-total X Y (P3012 K p q m n)-total X Y (P3201 K p q m n) from ?_]; swap; · unfold total; simp only [price4 K p q m n _ _ _ _ _ _ h,mul_sub,mul_add,sum_add_distrib,sum_sub_distrib]
 rw [billP1032,billP2301,billP3210,billP1230,billP1302,billP2031,billP2310,billP3012,billP3201,trace2 K X Y p q h,pure2 K m n h,x]; unfold realPlane; ring
#print axioms spinPlane
end YM.CF.Emu.SpinTable
