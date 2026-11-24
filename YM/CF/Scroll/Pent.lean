import YM.CF.Scroll.Loma
set_option autoImplicit false
noncomputable section
namespace YM.CF.Scroll
open Function Filter Matrix NormedSpace Finset Fock Lat Lattice Rush Cube Next.Free Laurent Fir Bloch SU Drapes Peaks Dial Tulip
open scoped Matrix.Norms.L2Operator Matrix Topology MatrixOrder BigOperators Kronecker
attribute [local instance] opCStarAlgebra
variable {b r:Bool}{N P:Side}(a:Shape)(U:UNI SpinIdx)(t:ColorT b)(H: JetS a.s b r U)
abbrev spinQ :UNI (SpinIdx × Slot):=⟨U.val ⊗ₖ t.V.val,Matrix.kronecker_mem_unitary U.property t.V.property⟩
abbrev milU (x:Site N) : UNI (SpinIdx×Slot):= ⟨a.payA x • (spinQ U t).val,by apply Matrix.mem_unitaryGroup_iff.mpr; rw [star_smul,Matrix.smul_mul,Matrix.mul_smul, show (spinQ U t).val*star _=1 from (spinQ U t).property.2,smul_smul,a.real_payA,a.reflex,one_smul]⟩
abbrev Tofu (a:Shape)(N:Side): Equiv.Perm (Site N):=Equiv.ofBijective _ a.mills_b
abbrev mealU (N:Side): UNI (Model N) := portX (Tofu a N) (milU a U t)
abbrev prepU (N:Side): UNI (Single N):=⟨love N (mealU a U t N).val,by apply Matrix.mem_unitaryGroup_iff.mpr; rw [←map_star,← map_mul,(mealU a U t N).property.2,map_one]⟩
lemma wingX(Y: Op (Model N)): sings b (prepU a U t N) (love N Y)=love N (sings b (mealU a U t N) Y):=by
 have he: windX b (love N Y)=love N (windX b Y):=by cases b<;>rfl
 simp only [singT,he,twist_formula,map_mul,map_star]
lemma wingK (Z:Op SpinIdx)(Y:Op Slot): sings b (spinQ U t) (Z ⊗ₖ Y)= sings b U Z ⊗ₖ sings b t.V Y:=by
 rw [singT,singT,singT]; have he:windX b (Z ⊗ₖ Y)= (windX b Z) ⊗ₖ (windX b Y):=by cases b; rfl; exact op_cc_kron ..
 simp only [twist_formula,spinQ,he,op_star_kron,op_kron_mul]
lemma wingM (x:Site N)(z: Op (SpinIdx × Slot)) : sings b (milU a U t x) z = sings b (spinQ U t) z :=by simp only [singT,twist_formula,milU,star_smul,Matrix.smul_mul,Matrix.mul_smul,smul_smul,a.real_payA,a.reflex,one_smul]
lemma dues (z w:Cover): fee (z+w)=fee z*fee w:=by unfold fee; rw [← prod_mul_distrib]; apply prod_congr rfl; intro i _; rw [Pi.add_apply,zpow_add₀ (by norm_num)]
lemma dueShape (s:Signed)(z:Cover): fee (s.act z)=fee z:=by unfold fee; rw [←Equiv.prod_comp s.perm]; apply prod_congr rfl; intro i _; cases p:s.flip i<;>simp [p]; exact inv_eq_of_mul_eq_one_right (by rw [← mul_zpow]; simp) -- tune
lemma infT(x:Site N)(z:Cover): natural (x+wrap N z)+N.val • periods N (natural x+z)=natural x+z:=by have h:= carrying N (natural x+z); rwa [map_add,nat_true] at h
lemma footFee(x:Site N)(f:Cover): a.payA x*wind (a.mills N x) (a.s.act f)=wind x f*a.payA (x+wrap N f) :=by
 let Z:Cover→Cover:= a.s.act; let y:=x+wrap N f; let B:=periods N (natural x+f); let T:= a.mills N; let W:= periods N (natural (T x)+ Z f)
 have hx:wind (a.mills N x) (a.s.act f)=fee W:=rfl
 -- flee(Ny)+S P_B=flee x+Z f; fee
 have he:T x+wrap N (Z f)=T y:= (Shape.tow ..).symm
 have hv:a.rent x+W= a.s.act B+a.rent y:=by
   have hb:natural y+N.val • B=natural x+f:=infT x f
   have hm:= congr_arg a.flee hb; rw [Shape.flee_p,Shape.flee_p,show a.s.act (N.val • B)= N.val • a.s.act B from map_nsmul (a.s.actEquiv (R:=ℤ)) _ _] at hm -- tune
   rw [← a.vibes x,← a.vibes y] at hm
   have hl : natural (T y)+N.val • W=natural (T x)+Z f:=by rw [←he]; exact infT ..
   apply nsmul_right_injective (M:=Cover) N.property.ne'; change N.val • _=N.val • _; rw [smul_add,smul_add]; unfold T Z at hl; linear_combination (norm := abel) hl-hm
 unfold Shape.payA; rw [hx,←dues,hv,dues,dueShape]; rfl
lemma invert_wx(x:Site N)(z:Cover):wind x z=wind (x+wrap N z) (-z):=by
 let y:=x+wrap N z; let B:= periods N (natural x+z); let W:=periods N (natural y-z)
 have hh:= infT x z; have he:= infT y (-z); rw [map_neg,show y + -wrap N z=x by unfold y; abel, ←sub_eq_add_neg] at he
 change natural y+ N.val • B=natural x+z at hh; change natural x+N.val • W=_ at he
 have hx:B+W=0:=by apply nsmul_right_injective (M:=Cover) N.property.ne'; change N.val • _= _ • _; rw [smul_add]; unfold y at *; linear_combination (norm := abel) hh+he
 have ht:fee B*fee W=1:=by rw [←dues,hx]; simp [fee]
 have hg:fee B=fee W:= by apply mul_left_cancel₀ (a:=fee B) (by rw [←norm_pos_iff,fee_norm]; norm_num); exact (fee_one B).trans ht.symm
 unfold wind; rw [← sub_eq_add_neg (natural _)]; exact hg
lemma seam_eq (x:Site N)(i:Axis):wind x (step i)= seam (anticut N) x i:=by
  let k:Site N:=0; let C:Cover:=step i
  have h1:= freq_advance k x C; rw [show wrap N C=step i from wrap_step ..] at h1
  have h2:= frequency_hop k x i; rw [show BZ.phase (pm k i)=mode (mel k) C from (by unfold BZ.phase mode C mel tmap; simp [mul_ite,mul_comm])] at h2
  have h3:= frequency_unit k (x+step i); exact mul_right_cancel₀ (by intro h; rw [h,mul_zero] at h3; exact zero_ne_one h3) (h1.trans h2.symm)
end YM.CF.Scroll
