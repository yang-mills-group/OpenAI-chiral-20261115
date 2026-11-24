import YM.CF.Scroll.Pent
set_option autoImplicit false
noncomputable section
namespace YM.CF.Scroll
open Function Filter Matrix NormedSpace Finset Fock Lat Lattice Rush Cube Next.Free Laurent Fir Bloch SU Drapes Peaks Dial Tulip
open scoped Matrix.Norms.L2Operator Matrix Topology MatrixOrder BigOperators Kronecker
attribute [local instance] opCStarAlgebra
variable {b r:Bool}{N P:Side}(a:Shape)(U:UNI SpinIdx)(t:ColorT b)(H: JetS a.s b r U)
lemma finger (d:Step)(X:Bkg N) (i j:Site N): tap (if d.neg then star (shift matter X (anticut N) d.dir) else shift matter X (anticut N) d.dir) i j= if j=i+d.vec then wind i (d.vec:Cover) • color matter (d.read X i) else 0:=by
 rcases d with ⟨d,h|h⟩; swap
 · change tap (star _) i j=if j=i+ -step d then wind i (-step d) • _ else 0; rw [tap_s]; by_cases H:j=i+-step d
   · rw [if_pos H]; set V:= (negDir d).read X i; have hx:j+step d=i:=by rw [H]; abel
     rw [←show wind j (step d)=wind i (-step d) from Eq.trans (invert_wx j (step d)) (by rw [wrap_step,hx])];
     rw [seam_eq]; change _= _ • color matter ((negDir d).read X i)
     rw [Step.neg_read,show i-step d=j by rw [H]; abel, color_inv]
     rw [show tap (shift matter X (anticut N) d) j i= hop matter X (anticut N) d j by ext; simp [shift,advance,tap,jump_apply,hx]]; simp [hop]
   rw [if_neg H]; ext; simp only [shift, tap,Matrix.star_apply,Matrix.submatrix_apply,jump_apply]; split; next p=> exact False.elim (H (by change j+step d=i at p; rw [←p]; abel))
   simp
 rw [show (Step.mk d false).vec=(step d:Cover) from rfl,seam_eq]; change tap (shift _ _ _ _) i j=if j=i+step d then seam _ _ _ • color matter (X (i,d)) else 0; by_cases e:j=i+step d <;> ext k l <;> simp_all [shift,tap,jump_apply,advance,eq_comm (a:=j),hop]
lemma flutes(x:Bkg (More N)) (i z) : links (stir t a x) (i,z)= t.lens (((posDir z).rotate a.s).read (links x) (a.mills N i)):=by
 let d:=(posDir z).rotate a.s; rw [show links _ _=travel (links (stir t a x)) i [posDir z] from by simp [travel]]
 rw [deep, levity,show d.read _ _=travel (links x) (a.mills N i) [d] by simp [travel], deep, a.nodex]; rfl
lemma lane_x (x:Site N) (Z:Cover)(M:Op (SpinIdx×Slot)):
 (milU a U t x).val * windX b (wind (a.mills N x) (a.s.act Z) • M) * star (milU a U t (x+wrap N Z)).val= wind x Z • sings b (spinQ U t) M:=by
 let V:=wind (a.mills N x) (a.s.act Z); let P:=x+wrap N Z
 have he (b:Bool): cSignX b V=V:=by cases b; rfl; exact fee_real _
 rw [win_c,he b]; unfold milU; simp only [star_smul,Matrix.mul_smul,Matrix.smul_mul, a.real_payA,smul_smul]
 let B:= (spinQ U t).val; rw [singT,twist_formula]; change ((_:ℂ)) • (B*windX b M * star B)=_;
 congr 1
 have hh :=footFee a x Z; change a.payA x*V= _ at hh
 linear_combination (norm:=ring) a.payA (x+wrap N Z)*hh+wind x Z*a.reflex (x+wrap N Z)
lemma starter_x(i:Axis)(x:Bkg (More N)): sings b (mealU a U t N) (if a.s.flip i then star (shift matter (links x) (anticut N) (a.s.perm i)) else shift matter (links x) (anticut N) (a.s.perm i))=shift matter (links (stir t a x)) (anticut N) i:=by
 let d:=(posDir i).rotate a.s; let R(d:Step)(y:Bkg N):Op (Model N):=if d.neg then star (shift matter y (anticut N) d.dir) else shift matter y (anticut N) d.dir
 let P:=R d (links x); let Q:=R (posDir i) (links (stir t a x))
 have he:d.neg= a.s.flip i :=by simp [d,posDir,Step.rotate]
 rw [← he]; change sings b (mealU a U t N) P=Q
 suffices h:∀ i j:Site N,tap (sings b (mealU a U t N) P) i j=tap Q i j from by ext ⟨i,X⟩ ⟨j,Y⟩; exact congr_fun (congr_fun (h i j) X) Y
 intro y z; let Z:=step i (S:=ℤ); have hz:(d.vec:Cover)= a.s.act Z:= Step.vec_rotate ..
 have hx:a.mills N (y+step i)=a.mills N y+d.vec:=by simp only [Shape.mills,d,Step.vec_rotate, Step.vec_pos,affine,Signed.act_add]; abel
 have hp : a.mills N z=a.mills N y+d.vec ↔ z=y+step i:=by rw [← hx]; exact a.mills_b.1.eq_iff
 unfold mealU; rw [tap_sg,show tap Q y z=_ from finger (posDir i) (links (stir t a x)) y z]; change (milU a U t y).val*windX b (tap P (a.mills N y) (a.mills N z))*star _=_; rw [show tap P _ _=_ from finger d (links x) (a.mills N y) (a.mills N z)]; by_cases p:z=y+step i; swap
 · rw [if_neg (fun l=> p (hp.mp l)),win_z,mul_zero,zero_mul,if_neg (show z≠y+(posDir i).vec from p)]
 rw [if_pos (hp.mpr p),if_pos (show z=y+(posDir i).vec from p), Step.pos_read,flutes, hz, show star (milU a U t z).val=star (milU a U t (y+wrap N Z)).val by rw [p,show wrap N Z=step i from wrap_step ..], lane_x]; unfold color; rw [wingK]; change wind y Z • (sings b U 1 ⊗ₖ _) = _; rw [singT,win_i,map_one,t.shore]; rfl
lemma swivel (N:Side)(X:Op SpinIdx): sings b (mealU a U t N) (spin N Slot X)=spin N Slot (sings b U X):=by
 let T:=mealU a U t N; suffices h:∀ x y:Site N,tap (sings b T (spin N Slot X)) x y=tap (spin N Slot (sings b U X)) x y from by ext ⟨x,p⟩ ⟨y,q⟩; exact congr_fun (congr_fun (h x y) p) q
 intro x y; have ht (X:Op SpinIdx)(x y:Site N): tap (spin N Slot X) x y= if x=y then X ⊗ₖ 1 else 0:= by ext p q; by_cases h:x=y <;> simp [spin,tap,jump_apply,h]
 unfold T mealU; rw [tap_sg,ht,ht]; by_cases h:x=y; swap; rw [if_neg h,if_neg (Tofu a N|>.injective.ne h),win_z,mul_zero,zero_mul]
 subst y; simp only [ite_true]; change sings b (milU a U t x) (X ⊗ₖ 1)=_; rw [wingM,wingK,singT b t.V,win_i,map_one]
include H
lemma shutH(x:Bkg (More N)): sings b (mealU a U t N) ((frame matter (links x) (anticut N)).H)=hush r ((frame matter (links (stir t a x)) (anticut N)).H):=by
 let X:=frame matter (links x) (anticut N); let Y:= frame matter (links (stir t a x)) (anticut N); let W:=mealU a U t N; let Z:=sings b W
 have he(i): Z (X.inc (a.s.perm i))=Y.inc i:=by
   have hK:Z (X.gamma (a.s.perm i))=hush (a.s.flip i) (Y.gamma i):=by rw [show Z (X.gamma _)=spin N Slot (sings b U _) from swivel .., H.cliff]; cases h:a.s.flip i; rfl; exact spin_neg ..
   have hx:=(starter_x a U t i x); cases h:a.s.flip i; simp only [h,Bool.false_eq_true,ite_false] at hx
   · rw [h] at hK
     unfold WilsonFrame.inc WilsonFrame.lap WilsonFrame.diff Z; simp only [singT,win_a,win_m,win_l,win_r,win_i,map_sub,map_mul,map_add,map_smul,map_one,win_s,map_star]; rw [show (twist W) (windX b (X.T _))=Y.T i from hx,show (twist W) (windX b (X.gamma _))=Y.gamma i from hK]
   simp only [h,ite_true] at hx; rw [h] at hK
   have hy: star (Z (X.T (a.s.perm i)))=Y.T i:=by
     unfold Z; rw [singT,← map_star,←win_s]; exact hx
   unfold WilsonFrame.inc WilsonFrame.lap WilsonFrame.diff Z; simp only [singT,win_a,win_m,win_l,win_r,win_i,map_sub,map_mul,map_add,map_smul,map_one,win_s,map_star]; rw [show (twist W) (windX b (X.T _))=star (Y.T i) from (star_eq_iff_star_eq.mp hy).symm,star_star, add_comm (star (Y.T i)), show star (Y.T i)-Y.T i= -(Y.T i-star (Y.T i)) by abel,smul_neg, show twist W _ = -(Y.gamma i) from hK,neg_mul_neg] -- tune
 have hp:Z X.chir=hush r Y.chir:=by rw [show Z X.chir=spin N Slot (sings b U grading) from swivel ..,H.grade]; cases r; rfl; exact spin_neg ..
 have ht:Z X.H0=Y.H0:=by simp only [Z, WilsonFrame.H0,singT,win_a,win_n,win_i,win_sum,map_one,map_add,map_sum,map_neg]; rw [← Equiv.sum_comp a.s.perm]; congr 1; apply sum_congr rfl; intro i _; exact he i
 unfold WilsonFrame.H; change sings b W (X.chir*X.H0)=hush r _; rw [singT,win_m,map_mul,show twist W (windX b X.chir)=_ from hp,show twist W (windX b X.H0)=_ from ht]; cases r; rfl; exact neg_mul ..
end YM.CF.Scroll
