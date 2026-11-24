import YM.CF.Nacre.Rain
set_option autoImplicit false
noncomputable section
namespace YM.CF.Nacre
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Fock NormedSpace Lat Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Font Spire
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {n:Side}{m:ℕ}
def Teens {G:Gauge} (t: Site n)(u: fieldDir G n 1):fieldDir G n 1:= fun i=> u (i.1+t,i.2)
def SubMotion (t:Cover)(V: fieldDir group (More n) 1):fieldDir group (More n) 1:=Teens (duos n t) V
lemma lull(t:Cover)(x:HopK n)(A: fieldDir group (More n) 1)(p:PrizeX n):
 heat (terse x) (collect group (SubMotion t A)) p=heat (terse (rollH t x)) (collect group A) (pinP (2 • t) p):=by
 let f:= duos n t; let V:=collect group (SubMotion t A); let P:=collect group A; have he(u): V u=P (u.1+f,u.2):=rfl
 have hp (w: Walk)(x:Site (More n)):linkSum V x w=linkSum P (x+f) w:=by
    induction w generalizing x with
    | nil=>rfl
    | cons i w h=> rw [linkSum,linkSum,h,he,add_right_comm x f]; congr 1; rcases i with ⟨i,t|t⟩<;> simp only [Step.used,ite_true,Bool.false_eq_true,ite_false]; rw [add_sub_right_comm]
 cases p with
 | inl p=>exact hp ..
 | inr p=> rw [rolls]; exact hp ..
lemma dialback (P:Toy m n)(A:fieldDir group (More n) 1)(t:Cover)(h:Prints P): pyre P (SubMotion t A)=ZoneH (lagX t) (pyre P A):=by
 ext ⟨⟨x,i⟩,k⟩ ⟨⟨y,j⟩,l⟩; rw [limo]; let a:=(x,i); let b:=(y,j); let z:= Rush.wind x t*Rush.wind y t
 change _=z*∑ p, P (ramH t (a,k)) (ramH t (b,l)) p (fun j=>heat (terse (rollH t a)) (collect group A) (p j)); conv_rhs => rw [← Equiv.sum_comp (pinch (m:=m) t)];
 rw [mul_sum]; apply sum_congr rfl; intro p e; rw [h];
 change P _ _ _ (fun j=>heat (terse a) _ (p j))= z*(z*P _ _ _ (fun j=>heat _ _ (pinP (2 • t) (p j))))
 rw [←mul_assoc,show z*z=1 by unfold z; rw [mul_mul_mul_comm,Rush.wind, Rush.wind,fee_one,fee_one,one_mul],one_mul]; congr 1; ext1 j; exact lull t a A _

private lemma linkD(x y:Cover):pinch (m:=m) (n:=n) (x+y)= (pinch x).trans (pinch y):=by ext1 p; ext1 i; cases hr:p i with
 | inr a=> change pinP _ (p i) = pinP _ (pinP _ (p i)); rw [hr]; rfl
 | inl a=>
    change pinP _ (p i)=pinP _ (pinP _ (p i)); rw [hr]; change Sum.inl (a.1+wrap (More n) (2 • (x+y)),a.2) = (Sum.inl (a.1+wrap (More n) (2 • x)+ wrap (More n) (2 • y),a.2): PrizeX n); rw [smul_add,map_add,add_assoc]
private lemma wrapD {x y:Cover}(h:wrap n x=wrap n y): pinch (n:=n) (m:=m) x= pinch y:=by
 have hp: wrap (More n) (2 • x) = wrap (More n) (2 • y):=by
    have he (z:Cover): wrap (More n) (2 • z)=(assembly n).embed (wrap n z):=(Ratio.embed_wrap (assembly n) z).symm; rw [he x,h,he]
 unfold pinch pinP; rw [hp]
private def barA(x: Site n):Cover:=natural (-x)
def bro (i j: HopK n):HopK n:= rollH (barA i.1) j
lemma bar0(x:HopK n): bro x x=(0,x.2):=by simp [bro,rollH,barA,nat_true]
lemma barX(x y:HopK n)(t:Cover): bro (rollH t x) (rollH t y)=bro x y:=by
 unfold bro rollH; simp only [barA,nat_true,← sub_eq_add_neg,add_sub_add_right_eq_sub]
lemma barZ(x:HopK n)(t:Cover) (r:Trip m n): pinch (barA (rollH t x).1) (pinch t r)=pinch (barA x.1) r:=by
 change ((pinch t).trans (pinch (barA (rollH t x).1)) ) r=_; rw [← linkD]; suffices H:wrap n (t+barA (rollH t x).1)=wrap n (barA x.1) by rw [wrapD (m:=m) H]
 simp [barA,rollH,nat_true,add_comm x.1]

def humY(P:Toy m n) (x y:HopK n):ℂ:= jazzC x y*jazzC (bro x x) (bro x y)
def polish(P:Toy m n):Toy m n:=fun i j r=> humY P i.1 j.1 • P (bro i.1 i.1,i.2) (bro i.1 j.1,j.2) (pinch (barA i.1.1) r)
lemma sugar(P:Toy m n):Prints (polish P):=by
 rintro t ⟨x,i⟩ ⟨y,j⟩ r; let C:= P (bro x x,i) (bro x y,j) (pinch (barA x.1) r); let c:= jazzC (bro x x) (bro x y)
 unfold polish; change humY _ (rollH t x) (rollH t y) • P (bro (rollH t x) (rollH t x),_) (bro _ (rollH t y),_) (pinch (barA (rollH t x).1) (pinch t r))= _
 unfold humY; rw [barX,barX,barZ,verge,smul_smul, mul_assoc (_*_), show (ramH t (x,i)).1=rollH t x from rfl,barX]; rfl
lemma honored {D:ℝ}(a:ℝ)(P:Toy m n)(h:∀ i:Single n,i.1.1=0→ balance a P i≤ D)(i:Single n): balance a (polish P) i ≤ D:=by
 let t:= barA i.1.1
 obtain ⟨x,j⟩:=i; change Cover at t
 apply le_trans (b:=balance a P ((ramH t) (x,j))) (le_of_eq ?_) (h _ (by change (bro x x).1=0; rw [bar0]))
 unfold balance; conv_rhs=> rw [← Equiv.sum_comp (ramH t)]
 apply sum_congr rfl; rintro ⟨y,k⟩ _; conv_rhs=> rw [← Equiv.sum_comp (pinch (m:=m) t)]
 refine sum_congr rfl ?_; intro f h; rw [notx_t]
 change _*‖humY P x y • P (ramH t (x,j)) _ (pinch t f)‖=_; rw [norm_smul,show ‖humY P x y‖=1 by unfold humY; rw [norm_mul,monF,monF,one_mul],one_mul]; rfl
lemma ripples (P:Toy m n)(u:SpinIdx)(v:HopK n)(i j:Slot)(r:Trip m n):polish P ((0,u),i) (v,j) r=P ((0,u),i) (v,j) r:=by
 unfold polish humY; simp only [bar0]; change (jazzC (0,u) v*jazzC (0,u) (bro (0,u) v)) • P _ _ (pinch (barA (0:Site n)) r)= _; rw [show bro (0,u) v=v from Prod.ext (by simp [barA,bro,rollH,nat_true]) rfl, mon1,one_smul]; suffices H: pinch (barA (0:Site n)) r=r by rw [H]
 funext i; rcases hi:r i with f|f
 · change pinP _ (r i)= Sum.inl f; rw [hi,show barA (0:Site n)=0 by ext i; simp [barA,natural]]; simp [pinP]
 change pinP _ (r i)=_; rw [hi]; rfl
end YM.CF.Nacre
