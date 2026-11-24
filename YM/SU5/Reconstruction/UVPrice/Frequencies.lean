import YM.SU5.Reconstruction.UVPrice.Walls
/-!
# Real Grid energy ports. faithful on bounded angular/energy window
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Roy
open Function Set Filter MeasureTheory Spectral Analysis Metric InnerProductSpace
open scoped Topology NNReal ENNReal ComplexOrder InnerProductSpace BigOperators
open YM.Multiplier Chirp CrossedFrame OS Semigroup Boundary Probe CF.Buffered.Afterglow.Tower MeshClock Germ SelectionAnalysis ConePrice Real Picket
variable {H : Hilbert} {a b : Axis} (S : OS.Semigroup H a)
variable (Γ: AddSubgroup ℝ)
structure Coupon (a: Axis) (Γ:AddSubgroup ℝ) where
 stamp : Axis→ Γ
 ground : 0≤ (stamp a:ℝ)
namespace Coupon
variable {Γ}
local notation "Q"=> Coupon a Γ
instance : Zero (Coupon a Γ):= ⟨⟨0, le_rfl⟩⟩
abbrev dt (q: Coupon a Γ) : ℝ≥0:= Real.toNNReal (q.stamp a:ℝ)
abbrev displacement (q: Coupon a Γ) : Cross a := diameter (face q.stamp)
def cash(z: Coupon a Γ): H.Op:= S.E z.dt*S.U z.displacement
def receipt (p:E4)(q: Coupon a Γ):ℂ:= (favor a q.dt p:ℂ)*plane p q.displacement.val
lemma firm (z:Q) : Registers S.ℚmeasure (fun p:E4=> receipt p z) (cash S z):= (costT S z.dt).times (costU S z.displacement)
@[fun_prop] lemma durable (q:Q):Continuous (fun x:E4=> receipt x q):=by unfold receipt plane; fun_prop
@[fun_prop] lemma allC : Continuous (fun x:E4=> (receipt x: Coupon a Γ→ℂ)):= continuous_pi (durable)
variable (q:Coupon a Γ)
lemma receipts_add (x y:E4)(p:0≤x a)(h:0≤y a): receipt (x+y) q= receipt x q * receipt y q:= by
 unfold receipt favor plane; rw [show (x+y) a=x a+y a from rfl,max_eq_right (add_nonneg p h),max_eq_right p,max_eq_right h,mul_add,Real.exp_add,inner_add_left]; push_cast; rw [add_mul,Complex.exp_add]; ring
lemma amount (x:E4): ‖receipt x q‖ = favor a q.dt x:= by rw [receipt,norm_mul,plane_norm,Complex.norm_real,Real.norm_of_nonneg (favorL ..).1.le, mul_one]
@[simp] lemma no (x:E4): receipt x (0:Coupon a Γ) = 1:= by
 have p: dt (0:Q)=0:= by change (0:ℝ).toNNReal=0; simp
 have u: (0:Q).displacement=0:= by apply Subtype.ext; change (WithLp.toLp 2 _)-_=(0:E4); ext i; change 0 - _= (0:ℝ); simp [face]; intro; rfl
 rw [receipt,p,u]; simp [plane,favor]
noncomputable def ray (a:Axis)(p:Γ)(h:0 ≤ (p:ℝ)): Coupon a Γ:=⟨Pi.single a p,by simpa⟩
lemma ray_time (p:Γ)(h:0≤ (p:ℝ)): (ray a p h).dt = (p:ℝ).toNNReal:=by unfold dt ray; simp
lemma ray_space (p:Γ)(h:0≤ (p:ℝ)): (ray a p h).displacement = 0:= by
 apply Subtype.ext; unfold displacement diameter face; change WithLp.toLp 2 _ - _• basis a=(0:E4); ext i; by_cases v:i=a <;> simp [v,ray,Pi.single_apply] -- tune
lemma ray_receipts (p:Γ)(h:0≤ (p:ℝ))(x:E4): receipt x (ray a p h) = favor a (p:ℝ).toNNReal x := by rw [receipt,ray_time,ray_space]; simp [plane]
noncomputable def still (a b:Axis)(t:b≠a)(p:Γ) : Coupon a Γ:= ⟨Pi.single b p, by simp [t.symm]⟩
lemma still_reads (p:Γ)(t:b≠a)(y:E4): receipt y (still a b t p)= Complex.exp ((p:ℝ)*(y b:ℂ)*Complex.I):= by
 have h:(still a b t p).displacement.val=(p:ℝ) • basis b:= by
    unfold displacement diameter; change WithLp.toLp 2 _ - _• basis a=_; ext i; by_cases v:i=a
    · subst i; simp [still,face,t.symm]
    by_cases u:i=b<;>simp [still,face,t.symm,u]
 rw [receipt,h]; unfold dt; rw [show ((still a b t p).stamp a:ℝ)=0 from by simp [still,t.symm]]; rw [plane,real_inner_smul_right,innerB]; simp [favor]
noncomputable def twice (q: Coupon a Γ) := ray a (q.stamp a + q.stamp a) (show 0≤ _ from add_nonneg q.ground q.ground)
lemma squared (x:E4): ‖receipt x q‖^2 = (receipt x q.twice).re:= by
 rw [amount,twice,ray_receipts]; simp only [dt,favor,Complex.ofReal_re,AddSubgroup.coe_add,Real.coe_toNNReal _ (add_nonneg q.ground q.ground), Real.coe_toNNReal _ q.ground, neg_add_rev,add_mul,Real.exp_add,pow_two]
-- faithfulness for low energy-no alias. through turns
variable (d:Dense (Γ:Set ℝ)) {x y:E4}(p:0≤x a)(v:0≤y a)(h:(receipt x:Coupon a Γ→ℂ)=receipt y)
include d p v h
lemma fixed_at : x a=y a:=by
 obtain ⟨t,g,z⟩:=d.exists_mem_open (U:=Ioi (0:ℝ)) isOpen_Ioi nonempty_Ioi
 let w:Γ:= ⟨t,g⟩; let q:= ray a w (by linarith [ (show 0 < t from z)] : (0:ℝ)≤ t)
 have he : favor a q.dt x = favor a q.dt y:= by simp only [← amount]; rw [congr_fun h] -- tune
 unfold favor q at he; rw [ray_time,max_eq_right p,max_eq_right v,Real.exp_eq_exp,Real.coe_toNNReal _ (show 0≤ (w:ℝ) from (mem_Ioi.mp z).le)] at he; exact mul_left_cancel₀ (neg_ne_zero.mpr (mem_Ioi.mp z).ne') he -- sign
omit p v in
lemma cross_at (t:b≠a) : x b=y b:=by
 let F(x:E4)(i:ℝ) := Complex.exp ((i:ℂ)*(x b:ℂ)*Complex.I)
 have ht:F x=F y:=by
   apply d.denseRange_val.equalizer (show Continuous (F x) by unfold F; fun_prop) (show Continuous (F y) by unfold F; fun_prop)
   funext s; exact Eq.trans (still_reads (s:Γ) t x).symm (Eq.trans (congr_fun h _) (still_reads s t y))
 by_contra z; let e := Real.pi/(x b-y b); have he:e*(x b-y b)=Real.pi:= div_mul_cancel₀ _ (sub_ne_zero.mpr z)
 have hy:=congr_fun ht e; unfold F at hy
 have hp: Complex.exp ((π:ℂ)*Complex.I)=1:=by
    rw [←he]; push_cast -- shape
    rw [mul_sub,sub_mul,Complex.exp_sub,hy]; exact div_self (Complex.exp_ne_zero _)
 rw [Complex.exp_pi_mul_I] at hp; norm_num at hp
lemma no_alias:x=y:=by
 ext1 i; by_cases e:i=a; · subst i; exact fixed_at d p v h
 exact cross_at d h e
end Coupon
end YM.Roy
