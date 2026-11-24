import YM.CF.BPress.Magnets
import YM.CF.BPress.EmbedCost
import YM.CF.BPress.Chord
import YM.UVNext.FREE_STRESS_CERTIFICATE.Color

/-! `eq:B-mood` Lie algebra triple with NORMALIZED inner product. Actual h-lifts (`chosen`,
move by right multiplication by inverse gauge), no branch replacement of nearest point. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Mag
open Function Filter Set SU Gauge LocalH
open scoped Topology ContDiff BigOperators NNReal Matrix.Norms.Frobenius InnerProductSpace
attribute [local instance] frobInner
abbrev Hue := PiLp 2 (fun _ : Fin 3 => group.Color)
def magnet : Hue := WithLp.toLp 2 ![group.ad (generator 0) (generator 1),group.ad (generator 0) (generator 2),group.ad (generator 1) (generator 2)]
lemma base_colors : group.colorMat (magnet 0)= Z ∧ group.colorMat (magnet 1)= -Y ∧ group.colorMat (magnet 2)= X:= by
  have he (i j) : group.colorMat (group.ad (generator i) (generator j))= ![X,Y,Z] i * ![X,Y,Z] j - ![X,Y,Z] j * ![X,Y,Z] i := by rw [group.colorMat_ad,generator_eq,generator_eq]; rfl
  refine ⟨(he 0 1).trans xy,(he 0 2).trans (show X*Z-Z*X= -Y by rw [← zx]; abel),(he 1 2).trans yz⟩
def spin (z : E) (H : Hue) : Hue := WithLp.toLp 2 fun i=> group.adjoint z (H i)
lemma spin_at (z : E) (H : Hue) (i) : spin z H i=group.adjoint z (H i):= rfl
@[simp] lemma spin_one (H : Hue) : spin 1 H=H:= by ext i j; rw [spin_at,group.adjoint_one]
lemma spin_seq (x y : E) (H : Hue) : spin x (spin y H)=spin (x*y) H:= by ext i j; rw [spin_at,spin_at,spin_at,group.adjoint_mul]
lemma spin_dist (z : E) (H K : Hue) : dist (spin z H) (spin z K)=dist H K:= by
  apply sq_eq_sq₀ dist_nonneg dist_nonneg |>.mp; rw [dist_eq_norm,dist_eq_norm,PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_congr rfl; intro i _; change ‖group.adjoint z (H i)-group.adjoint z (K i)‖^2=‖H i-K i‖^2; rw [←map_sub,group.norm_adjoint]
lemma spin_cent (i : Fin 5) (H : Hue) : spin (center i) H=H:= by
  apply PiLp.ext; intro j; apply group.colorMat_injective; rw [spin_at,group.mat_adjoint,Gauge.conjugate]
  have h (A : group.Mat) : group.mat (center i)*A=A*group.mat (center i):=by rw [mat_center]; simp
  rw [h,mul_assoc,group.mat_mul_star,mul_one]
lemma stab {z : E} : spin z magnet=magnet ↔ ∃ i, z=center i:= by
  constructor
  · intro h; rw [←center_test]; have hz(i:Fin 3) : (group.colorMat (magnet i))*group.mat z= group.mat z * (group.colorMat (magnet i)):= by
      have he : spin z magnet i=magnet i:=congrArg (fun H : Hue=>H i) h -- tune
      rw [spin_at] at he; conv_lhs=> rw [← he]; rw [group.mat_adjoint,Gauge.conjugate,mul_assoc,group.mat_star_mul,mul_one]
    have hx:=hz 1; have he:=hz 2; -- fund vs group.mat
    -- make type explicit
    change (show Op F from group.colorMat (magnet 2))*fund z=fund z*(show Op F from group.colorMat (magnet 2)) at he
    change (show Op F from group.colorMat (magnet 1))*fund z=fund z*(show Op F from group.colorMat (magnet 1)) at hx
    rw [base_colors.2.2] at he; rw [base_colors.2.1,neg_mul,mul_neg] at hx; exact ⟨he,neg_injective hx⟩
  · rintro ⟨i,rfl⟩; exact spin_cent ..
def paint (x : E) : Hue:= spin x magnet
def picture (x : group.Color) := paint (group.lieExp x)
@[simp] lemma picture_zero : picture 0=magnet:= by simp [picture,paint]

lemma spin_cont : Continuous (fun x : E × Hue=> spin x.1 x.2) := by
  refine (PiLp.continuous_toLp 2 (fun _ : Fin 3=>group.Color)).comp (f:=fun x : E × Hue=> fun i=>group.adjoint x.1 (x.2 i)) (continuous_pi ?_)
  intro i
  change Continuous (fun x : E × Hue=>group.projectColor (group.mat x.1*group.colorMat (x.2 i)*star (group.mat x.1)))
  refine group.projectColor.continuous_of_finiteDimensional.comp (((group.continuous_mat.comp continuous_fst).mul (group.colorMat.continuous_of_finiteDimensional.comp ?_)).mul ((group.continuous_mat.comp continuous_fst).star))
  exact (PiLp.continuous_apply ..).comp continuous_snd
lemma paint_cont : Continuous paint:= spin_cont.comp (f:=fun x : E=>(x,magnet)) (continuous_id.prodMk continuous_const)
lemma picture_diff : ContDiff ℝ ω picture := by
  let L:=PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3=>group.Color)
  refine L.symm.contDiff.comp (f:=fun x : group.Color=> fun i=> group.adjoint (group.lieExp x) (magnet i)) (contDiff_pi.mpr (fun i=>?_))
  change ContDiff ℝ ω fun x:group.Color=> group.projectColor (group.mat (group.lieExp x)*group.colorMat (magnet i)*star (group.mat (group.lieExp x)))
  refine group.projectColor.toContinuousLinearMap.contDiff.comp ((group.exp_jet.mul contDiff_const).mul ?_)
  exact ((show _ ≃L[ℝ] _ from starL ℝ).contDiff).comp group.exp_jet
lemma picture_injD : Injective (fderiv ℝ picture 0):=by
  let L:= fderiv ℝ picture 0; apply (LinearMap.ker_eq_bot.mp ?_ : Injective L.toLinearMap); rw [LinearMap.ker_eq_bot']; intro x h; change L x=0 at h
  have g: HasDerivAt (fun t : ℝ=> picture (t • x)) (L x) 0:=
    HasFDerivAt.comp_hasDerivAt (l:=picture) (f:=fun t:ℝ=>t • x) (0:ℝ) (by rw [zero_smul]; exact (picture_diff.differentiable (by simp) _).hasFDerivAt) (by simpa using (hasDerivAt_id' (0:ℝ)).smul_const x) -- tune
  have he(i:Fin 3) : group.colorMat (magnet i)*group.colorMat x=group.colorMat x*group.colorMat (magnet i):= by
    let V : Hue →L[ℝ] group.Color:= (ContinuousLinearMap.proj i).comp (PiLp.continuousLinearEquiv 2 ℝ _).toContinuousLinearMap
    have u : V (L x)=group.ad x (magnet i):= (V.hasFDerivAt.comp_hasDerivAt _ g).unique (YM.UVNext.FreeStress.adjoint_derivative x (magnet i))
    rw [h,map_zero] at u; exact (sub_eq_zero.mp ((group.colorMat_ad ..).symm.trans ((congrArg group.colorMat u.symm).trans (map_zero _)))).symm
  have hX:= he 2; have hY:=he 1; let X' : Op F := group.colorMat x
  have h1 : X*X'=X'*X:= by rw [base_colors.2.2] at hX; exact hX
  have h2 : Y*X'=X'*Y:= by rw [base_colors.2.1] at hY; exact neg_inj.mp ((neg_mul ..).symm.trans ((show -Y*X'=X'*-Y from hY).trans (mul_neg ..)))
  apply group.colorMat_injective; rw [map_zero]; exact Mag.trace_commutant h1 h2 (Thera.league.mp (group.colorMat_mem _)).2
end YM.CF.BPress.Mag
