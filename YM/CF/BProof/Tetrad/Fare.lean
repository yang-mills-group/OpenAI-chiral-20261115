import YM.CF.BProof.Tetrad.Hue
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Tetra
open Function Finset List
open scoped BigOperators Classical

def fare (m n:ℕ) := 2*(m+n+2).choose (m+1)
@[simp] lemma fare0 (m:ℕ): fare 0 m= 2*(m+2):=by simp [fare]
lemma fare_sym (m n:ℕ) : fare m n=fare n m:=by unfold fare; rw [add_comm m n,Nat.choose_symm_of_eq_add (a:=m+1) (b:=n+1) (show n+m+2=m+1+(n+1) by omega)]
@[simp] lemma fares0(m:ℕ):fare m 0=2*(m+2):=by rw [fare_sym,fare0]
lemma fare_rec {m n:ℕ}(h:0 < m)(g:0 < n): fare m n= fare (m-1) n + fare m (n-1):=by
 rcases m with _|m; omega
 rcases n with _|n; omega
 unfold fare; simp only [Nat.add_one_sub_one]; rw [show m+1+(n+1)+2=m+(n+1)+2+1 by omega,show m+1+n+2=m+(n+1)+2 by omega,Nat.choose_succ_succ',mul_add]
lemma pay0 {x:Road}(h:¬ Line x): weight x=0:= clash false x h
lemma prev(x y:Road){N:ℕ}(k:x.length+y.length=N)(H:∀ m<N,∀ x y:Road,x.length+y.length=m→ pot false x y = weight x*weight y * fare x.length y.length):
 excerpt (fun l=>pot false l y) x = excerpt weight x*(weight y * fare (x.length-1) y.length)∧
 excerpt (pot false x) y = excerpt weight y*(weight x * fare x.length (y.length-1)):=by
 constructor
 · rw [← d_mul]; apply d_con; intro l p; rw [H (l.length+y.length) (by omega) l y rfl, show l.length= x.length-1 by omega]; ring
 rw [← d_mul]; apply d_con; intro l p; rw [H (x.length+l.length) (by omega) x l rfl, show l.length= y.length-1 by omega]; ring
lemma gap(x y:Road): pot false x y= weight x*weight y*fare x.length y.length:=by
 generalize hv:x.length+y.length=z
 induction z using Nat.strong_induction_on generalizing x y with| h n ih=>
   by_cases hx: Line x; swap; · rw [pay0 hx,zero_mul,zero_mul]; exact Finset.sum_eq_zero fun i _=> clash false _ fun s=>hx (smooth_p _ _ s).left_of_append
   by_cases hy: Line y; swap; · rw [pay0 hy,mul_zero,zero_mul]; exact Finset.sum_eq_zero fun i _=>clash false _ fun s =>hy ((smooth_p _ _ s).right_of_append).tail
   have hp:= payroll x y hx hy; obtain ⟨h1,h2⟩:=prev x y hv ih; rw [h1,h2] at hp
   by_cases he:x=[]
   · subst x; simp only [weight,w_nil] at *; cases y with
     | nil=> simp [pot,length_nil,fare,Finset.sum_const,singleW]
     | cons b y=>
       rw [←paid false _ (by simp) hy] at hp; simp only [d_nil,List.nil_append,zero_mul,Nat.zero_add, cons_ne_nil,if_false,if_true,fare0,length_nil,length_cons,Nat.add_one_sub_one,carryC, add_zero,one_mul] at hp ⊢; nlinarith only [hp]
   by_cases hf:y=[]
   · subst y; unfold weight at *; rw [←paid false _ he hx] at hp; have ht:x.length-1+1=x.length:=by have hl:=List.length_pos_of_ne_nil he; omega
     simp only [length_nil,w_nil,carryC,ite_true,if_neg he,add_zero,d_nil, zero_mul,fares0,List.append_nil, mul_one] at hp ⊢; nlinarith only [ht,hp]
   unfold weight at hp; rw [← paid false _ he hx,←paid false _ hf hy] at hp; simp only [carryC,if_neg he,if_neg hf] at hp
   have h(f1 f2 w A B K U:ℕ)(p:f1*(f2*A)+f2*(f1*B)+4*w=K+2*w+2*w)(u:U=A+B):K=f1*f2*U:=by
      rw [u,mul_add]
      calc
        _ = f1*f2*A + f2*f1*B:=by rw [mul_assoc,mul_assoc]; omega
        _ = _:=by ring
   exact h _ _ _ _ _ _ _ hp (fare_rec (length_pos_of_ne_nil he) (length_pos_of_ne_nil hf))

lemma pay2(a b:Tone):polar [a,b]=weight [a,b]:=by
 unfold polar weight; by_cases h:a=b; subst b; exact (unpaid true [] [] _).trans (unpaid false [] [] _).symm
 rw [paid true _ (by simp) (show smooth true [a,b] from by unfold smooth; simp [h,Ne.symm h]),paid false _ (by simp) (by simp [smooth,Line,h])]; simp only [d_cons,d_nil,singleW]
lemma gate(x:Road)(p:x≠[]) : pot true x []=6*weight x:=by
 generalize g:x.length = l
 induction l using Nat.strong_induction_on generalizing x with| h n ih=>
   by_cases hx:Line x; swap; · rw [pay0 hx,mul_zero]; exact Finset.sum_eq_zero fun i _=> clash true _ fun v=> hx (smooth_p _ _ v).left_of_append
   by_cases v:2≤x.length
   · rw [←enroll _ hx v]; rw [show excerpt _ x = _ from d_con (fun l=>pot true l []) (fun l=>weight l *6) x (fun l p'=>by rw [ih l.length (by omega) l (by intro h; subst l; simp_all; omega) rfl,mul_comm])]; rw [d_mul]; change excerpt (wage false) x*_ =_; rw [←paid false x p hx,mul_comm]
   obtain ⟨a,rfl⟩:= List.length_eq_one_iff.mp (show x.length=1 from by have ht:=length_pos_of_ne_nil p; omega) -- name tune
   rw [show pot true [a] []=pot false [a] [] from (Finset.sum_congr rfl fun b _=>pay2 a b),gap]; simp only [weight,length_cons,length_nil,w_nil,fares0]; rw [singleW]
end YM.CF.BProof.Tetra
