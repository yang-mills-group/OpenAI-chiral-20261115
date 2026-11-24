import YM.SU5.Selected.Chene.Creme
import YM.SectorNext.VACUUM_NORMALIZATION.Scheme
set_option autoImplicit false
noncomputable section
namespace YM.Chene.Trunk
open Function Filter Matrix Lattice Tree SectorNext.Vacuum.FlatTree Finset Next.Rank.Axial Pad Precision Exterior
open scoped Topology BigOperators Matrix
variable {c f : Side}(g:Ratio c f)

abbrev circle(n:Side):=Face (Per n)

def petals (n:Side): circle n≃ Body 2 n:= Equiv.prodCongr (Equiv.refl _) plaqEquiv
@[simp] lemma petalEq (n:Side)(x:circle n): petals n x=(x.1,plaquette x.2):=rfl
@[simp] lemma pinchK (n:Side)(x:Site n)(i:Axis): (wheel n).symm (x,coord i)=(x,i):= (wheel n).symm_apply_apply (x,i)

-- choose Pin axis actual cycle positions. not frame-dependent outside normalization.
def song {T:Type*}[AddCommGroup T] (x:circle c)(v: Reed c→T) : T:=
    let i:=x.2.val.1; let j:=x.2.val.2; v (x.1+step i,j)-v (x.1,j)-(v (x.1+step j,i)-v (x.1,i))

def curl (T: Type*) [CommRing T] (c:Side) : Matrix (circle c) (Reed c) T:= of fun x j=> song x (fun i=>(1:Matrix _ _ T) i j)

theorem curl_applyZ {T: Type*} [CommRing T](v:Reed c→T)(x:circle c) : (curl T c*ᵥ v) x=song x v:=by
 unfold curl song mulVec dotProduct; simp_rw [Matrix.of_apply,sub_mul, sum_sub_distrib]; exact congrArg (song x) (Matrix.one_mulVec v)
lemma liftCurl (c:Side): realM (curl ℤ c)= curl ℝ c:=by ext i j; simp [realM,curl,song,Matrix.one_apply]
lemma exterior_curl (c:Side): curl ℝ c=(d 1 c).submatrix (petals c) (wheel c):=by
 apply Matrix.ext_iff_mulVec.mpr; intro v; rw [submatrix_mulVec_equiv]; funext i; rw [curl_applyZ]; simp [d_plaquettes,song,Function.comp]
lemma curl_climb (v:Site c→ℝ): curl ℝ c *ᵥ climb v=0:=by
 funext x; unfold climb; rw [curl_applyZ]; unfold song; simp only [add_right_comm x.1 (step x.2.val.1) (step x.2.val.2),Pi.zero_apply]; abel
lemma curl_root (k:Site c→Site f): curl ℝ c * realM (press k)=0:=by apply Matrix.ext_iff_mulVec.mpr; intro v; rw [←mulVec_mulVec,liftPress, speedZ,curl_climb,zero_mulVec]

-- line positions and torus cycles
def lineK (n:Side) (a:Axis)(x:Per n): Site n:=fun i=> if a=i then x else 0
lemma line_next (n:Side)(a:Axis)(x:Per n): lineK n a x+step a=lineK n a (x+1):=by ext i; by_cases e:a=i <;> simp [lineK, *,eq_comm]
lemma line_prev(n:Side)(a:Axis): lineK n a (-1) = -step a:=by ext i; by_cases e:a=i <;> simp [lineK, *,eq_comm]

def pin (T:Type*)[CommRing T](c:Side): Matrix Axis (Reed c) T:= of fun a i=> ∑ x :Per c,(1:Matrix _ _ T) (lineK c a x,a) i
theorem pin_apply {T:Type*}[CommRing T](v: Reed c→T)(a:Axis) : (pin T c *ᵥ v) a=∑ x:Per c,v (lineK c a x,a):=by
 unfold mulVec dotProduct pin; simp_rw [Matrix.of_apply,sum_mul]; rw [sum_comm]; apply sum_congr rfl; intro x _; exact congrFun (Matrix.one_mulVec v) _
lemma liftPin (c:Side): realM (pin ℤ c)=pin ℝ c:=by ext i j; simp_rw [realM,Matrix.map_apply,pin,Matrix.of_apply,map_sum]; simp [Matrix.one_apply]
lemma rail {T:Type*}[CommRing T](v:Site c→T): pin T c *ᵥ climb v=0:=by
 funext i; rw [pin_apply]; unfold climb; simp_rw [line_next,Finset.sum_sub_distrib]; change _-_=(0:T); exact sub_eq_zero.mpr (Equiv.sum_comp (Equiv.addRight (1:Per c)) (fun x=>v (lineK c i x))).symm
lemma pin_angle (c:Side){f:Side}(p:Site c→Site f) : pin ℝ c * realM (press p)=0:= by apply Matrix.ext_iff_mulVec.mpr; intro v; rw [←mulVec_mulVec,liftPress,speedZ,rail,zero_mulVec]

def wind(c:Side): Matrix (Reed c) Axis ℝ:= of fun i j=> (c.val:ℝ)⁻¹ * (1:Matrix Axis Axis ℝ) i.2 j
lemma wind_emit(v:Axis→ℝ)(i:Reed c) : (wind c *ᵥ v) i=(c.val:ℝ)⁻¹*v i.2:=by
 unfold wind mulVec dotProduct; simp_rw [Matrix.of_apply, _root_.mul_assoc,← mul_sum]; rw [show ∑ j,(1:Matrix Axis Axis ℝ) i.2 j *v j=v i.2 from congrFun (Matrix.one_mulVec v) _]
lemma hard_positive (c:Side): (0:ℝ)<c.val:= Nat.cast_pos.mpr c.property
lemma pin_wind (c:Side): pin ℝ c * wind c=1:=by
 apply Matrix.ext_iff_mulVec.mpr; intro v; rw [←mulVec_mulVec,one_mulVec]; funext i; rw [pin_apply]; simp_rw [wind_emit]; rw [sum_const,card_univ,Fintype.card_congr (Equiv.refl (Per c)),ZMod.card,nsmul_eq_mul,←_root_.mul_assoc, mul_inv_cancel₀ (hard_positive c).ne',_root_.one_mul] -- tune
lemma relieve (c:Side): curl ℝ c * wind c=0:=by apply Matrix.ext_iff_mulVec.mpr; intro i; rw [← mulVec_mulVec,zero_mulVec]; funext v; rw [curl_applyZ]; simp [song,wind_emit]

def pasture(g : Matrix (Body 2 c) (Body 2 c) ℝ) : Matrix (Reed c) (Reed c) ℝ:= (K g).submatrix (wheel c) (wheel c)
local notation "C"=> curl ℝ c
lemma flat_t (g : Matrix (Body 2 c) (Body 2 c) ℝ) : Cᵀ*g.submatrix (petals c) (petals c)*C=pasture g:=by
 rw [exterior_curl,transpose_submatrix,submatrix_mul_equiv,submatrix_mul_equiv]; rfl -- tune
lemma pasture_symm (g : Matrix (Body 2 c) (Body 2 c) ℝ)(p:gᵀ=g): (pasture g)ᵀ=pasture g:=by rw [←flat_t,transpose_mul,transpose_mul,transpose_submatrix,p,transpose_transpose, Matrix.mul_assoc]
lemma pasture_r (g : Matrix (Body 2 c) (Body 2 c) ℝ): pasture g * wind c=0:=by rw [←flat_t,Matrix.mul_assoc (_*_ ) C,relieve,Matrix.mul_zero]
lemma pasture_g (g : Matrix (Body 2 c) (Body 2 c) ℝ) {p:Site c→Site f} : pasture g *realM (press p)=0:=by rw [←flat_t,Matrix.mul_assoc (_*_ ) C,curl_root,Matrix.mul_zero]

end YM.Chene.Trunk
