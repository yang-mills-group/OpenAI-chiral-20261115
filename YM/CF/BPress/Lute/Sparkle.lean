import YM.CF.BPress.Spin.Hue
import YM.CF.Sods.Verd
/-! VolumeB-marker eq:B-Gz. Angle spectrum in principal cut. Buy radius price with slack using exact $45$ color construction. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Lute
open Function Finset Filter NormedSpace InnerProductSpace SU SU.Pair Spin Spin.Paint Lattice Fock Complex
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker InnerProductSpace ContDiff
attribute [local instance] opCStarAlgebra
variable {J K : Type*}[Fintype J][DecidableEq J][Fintype K][DecidableEq K]
-- angle units radians
local notation "π"=>Real.pi
abbrev χ:=BZ.phase
@[simp] lemma χ_zero:χ 0=1:=by simp [χ,BZ.phase]
lemma χ_add (x y:ℝ):χ (x+y)=χ x*χ y:=by simp [χ,BZ.phase,add_mul, exp_add]
@[simp] lemma χ_cc (x:ℝ): star (χ x)=χ (-x):=by simp [χ,BZ.phase, ← exp_conj]
@[simp] lemma χ_norm(x:ℝ):‖χ x‖=1:=norm_exp_ofReal_mul_I _
lemma sumχ(x:ℝ):χ x+χ (-x)=2*(Real.cos x:ℂ):=by simp only [χ,BZ.phase,Complex.exp_mul_I, ←Complex.ofReal_cos, ← Complex.ofReal_sin]; rw [Real.cos_neg,Real.sin_neg,Complex.ofReal_neg]; ring
-- inject exp for principals
lemma coverχ {x y:ℝ}(h:|x|<π)(g:|y|<π)(u:χ x=χ y):x=y:=by
 have ht:=Complex.exp_inj_of_neg_pi_lt_of_le_pi ?_ ?_ ?_ ?_ u; exact Eq.trans (by simp) (Eq.trans (congrArg Complex.im ht) (by simp)) -- inference?
 · simpa using (abs_lt.mp h).1
 · simpa using (abs_lt.mp h).2.le
 · simpa using (abs_lt.mp g).1
 simpa using (abs_lt.mp g).2.le
lemma χ_ball{t x:ℝ}(h:|x|<π)(p:t∈Set.Icc (0:ℝ) 1): ‖χ (t*x)-(χ (x/2))*(Real.cos (x/2):ℂ)‖<1:=by
 let b:=x/2; let c:=Real.cos b; let v:=t*x-b; let k:ℂ:=c; have hb : |v| ≤ |b|:=by
    have he : |2*t-1| ≤ 1:=by obtain ⟨p,h⟩:=p; rw [abs_le]; constructor <;> linarith
    rw [show v=(2*t-1)*b from by unfold v b; ring,abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) he
 have hc: |b|<π/2:=by rw [show b=x/2 from rfl,abs_div,abs_of_pos (show (0:ℝ)<2 by norm_num)]; linarith
 have ht:0<c:=Real.cos_pos_of_mem_Ioo (abs_lt.mp hc); have hv:c≤Real.cos v:=by
    have he(x:ℝ):Real.cos |x|= Real.cos x:=abs_cases x|>.elim (fun p=>by rw [p.1]) fun p=>by rw [p.1,Real.cos_neg]
    unfold c; rw [←he v,←he b]; exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (hc.le.trans (half_le_self Real.pi_pos.le)) hb
 change ‖χ (t*x)-χ b*k‖<1; rw [show t*x=b+v from by unfold v; ring,χ_add,←mul_sub, norm_mul,χ_norm,one_mul]
 have Hre(y:ℝ): (χ y).re=Real.cos y:=by simp [χ,BZ.phase]
 have H:= Complex.normSq_eq_norm_sq (χ v-k); have hu:=Complex.normSq_sub (χ v) k -- name tune
 rw [hu] at H; clear hu; rw [Complex.normSq_eq_norm_sq, χ_norm] at H; unfold k at H; norm_num [Complex.mul_re,Hre, Complex.normSq_eq_norm_sq,Real.norm_eq_abs] at H; nlinarith

def spectralC(U:UNI J)(f:J→ℂ): Op J:= twist U (Matrix.diagonal f)
def rotationU(U:UNI J)(f:J→ℝ)(t : ℝ):= spectralC U (fun i=>χ (t*f i))
lemma spectralC_diag_exists [Nonempty J](X:Op J)(p:X∈unitary (Op J)): ∃ U f, X=spectralC U f:=by
 -- exact diagonalization of commuting selfadjoints
 let A:=Sods.fro true X; let B:=Sods.fro false X; have hu:= p.1; have hv:= p.2
 have ht:Commute A B:= by
    -- fro_f small on itself reuse ∴ commute
    let U : UNI J:=⟨X,p⟩
    have he:= Sods.fro_f U _ (Sods.fro_f U _ (Switch.fromCommute (Commute.refl U.val)) true |>.symm) false
    change ‖B*A-A*B‖ ≤0 at he; exact (sub_eq_zero.mp (norm_le_zero_iff.mp he)).symm
 obtain ⟨U,f,u⟩:= spectral_exists A (Sods.fresh true X); let G:=twist (star U) B; let a:=Matrix.diagonal (fun i=>(f i:ℂ))
 have hc:Commute a G:=by rw [u] at ht; have hx:=ht.map (twist (star U)); rwa [spectral,twist_inv] at hx
 have he:Sods.Bl f G:=by
    intro i j p; have hp:=Matrix.ext_iff.mpr hc.eq i j; rw [Matrix.diagonal_mul,Matrix.mul_diagonal,mul_comm (G i j)] at hp; exact (mul_eq_zero.mp (show _*G i j=0 from (sub_mul ..).trans (sub_eq_zero.mpr hp))).resolve_left (sub_ne_zero.mpr (ofReal_injective.ne p))
 obtain ⟨W,d,w,H⟩:=Sods.dozen he (show IsSelfAdjoint G from (Sods.fresh false X).map _)
 have hx : X=A+Complex.I • B:= Sods.mix_g ⟨X,p⟩; let C (i):ℂ:=f i+Complex.I*d i
 have hk:B=twist U G:=by unfold G; nth_rw 1 [←star_star U]; exact (twist_inv (star U) B).symm
 have hb: twist W a=a:= Sods.invite id W w
 have ha:A=spectral (U*W) f:=by rw [u,←twist_spectral]; unfold spectral; rw [hb]
 refine ⟨U*W,C,?_⟩; rw [hx,ha,hk,H,twist_spectral,spectral,spectral, ←Sods.twink,←map_add,spectralC]; congr; ext i j; by_cases h:i=j <;> simp [C,h]; -- tune
lemma rot_unit [Nonempty J](U:UNI J)(f:J→ℝ)(t:ℝ):rotationU U f t∈unitary (Op J):=by
 have hp:Matrix.diagonal (fun i=>χ (t*f i)) ∈ unitary (Op J):= Sods.mojo (fun i=>t*f i)
 exact ((unitary _).mul_mem ((unitary _).mul_mem U.property hp) (star U).property)
lemma rot_add(U:UNI J)(f:J→ℝ)(t u:ℝ): rotationU U f (t+u)=rotationU U f t*rotationU U f u:=by
 unfold rotationU spectralC; rw [←map_mul,Matrix.diagonal_mul_diagonal]; simp [add_mul,χ_add]
@[simp] lemma rot_0(U:UNI J)(f:J→ℝ): rotationU U f 0=1:=by simp only [rotationU,zero_mul,χ_zero,spectralC]; rw [show Matrix.diagonal (fun _:J=> (1:ℂ))=1 from rfl,map_one]
lemma twist_T(U:UNI J)(f:J→ℂ) : (spectralC U f).det=∏ i,f i:=by unfold spectralC; rw [twist_formula,Matrix.det_mul,Matrix.det_mul,mul_right_comm,_root_.mul_comm U.val.det,←Matrix.det_mul, U.property.1,Matrix.det_one,one_mul, Matrix.det_diagonal]
lemma rot_det(U:UNI J)(f:J→ℝ)(t:ℝ): (rotationU U f t).det=χ (t*∑ i,f i):=by rw [rotationU,twist_T,χ, BZ.phase, Finset.mul_sum, Complex.ofReal_sum,Finset.sum_mul,Complex.exp_sum]; rfl
lemma mat_smooth {n:WithTop ℕ∞}{E : Type*}[NormedAddCommGroup E][NormedSpace ℝ E](f:E→Op J)(x:E) (h:∀ i j, ContDiffAt ℝ n (fun x=> f x i j) x): ContDiffAt ℝ n f x:= by
 let L : (J→J→ℂ) ≃ₗ[ℝ] Op J:={toFun:=Matrix.of,invFun:=Matrix.of.symm,left_inv:=Matrix.of.left_inv,right_inv:=Matrix.of.right_inv,map_smul':=fun _ _=>rfl,map_add':=fun _ _=>rfl}
 refine ((L.toContinuousLinearEquiv (𝕜:=ℝ)).contDiff.contDiffAt).comp (f:=fun x i j=>f x i j) x (contDiffAt_pi.mpr (fun i=>contDiffAt_pi.mpr (h i)))
lemma rot_smooth(U:UNI J)(f:J→ℝ): ContDiff ℝ ⊤ (rotationU U f):=by
 rw [contDiff_iff_contDiffAt]; intro x; unfold rotationU spectralC; simp_rw [twist_formula]; have ht:ContDiffAt ℝ (⊤:WithTop ℕ∞) (fun t:ℝ=>Matrix.diagonal fun i=> χ (t*f i)) x:=by apply mat_smooth; intro i j; by_cases h:i=j; simp only [h,Matrix.diagonal_apply_eq]; refine (Complex.contDiff_exp (𝕜:=ℝ)).contDiffAt.comp x (f:=fun t:ℝ=> ((t*f j:ℝ):ℂ)*Complex.I) ((Complex.ofRealCLM.contDiff.contDiffAt.comp x (f:= fun t:ℝ=> t*f j) (by fun_prop)).mul contDiffAt_const); simp [h]; fun_prop
 exact (contDiffAt_const.mul ht).mul contDiffAt_const
-- buy no wrap iff. ensures symmetry after any functional calculus phase. need only Twist x with principal phase equal.
lemma shift_diag(U:UNI J)(f k:J→ℂ)(B: Op J)(h:∀ i j,f i=f j → k i=k j)(p:spectralC U f*B=B*(spectralC U f)ᵀ) : spectralC U k*B=B*(spectralC U k)ᵀ:=by
 let A(g:J→ℂ) : Op J:=spectralC U g; let V:=ccU U; have he(g:J→ℂ) : (A g)ᵀ=twist V (Matrix.diagonal g):=by
    unfold A spectralC; rw [show (twist U _)ᵀ= cc (star (twist U (Matrix.diagonal g))) by simp [cc], ←map_star, cc_twist,cc, star_star,Matrix.diagonal_transpose]
 let C:=star U.val*B*V.val; have hx(g:J→ℂ) : A g*B=B*(A g)ᵀ ↔ Commute (Matrix.diagonal g) C:=by
    let d:=Matrix.diagonal g; rw [he]; unfold Commute SemiconjBy C A spectralC; rw [twist_formula,twist_formula]; constructor
    · intro p; have hp:=congrArg (fun x=> star U.val*x*V.val) p; simp only [mul_assoc] at hp ⊢; rw [← mul_assoc (star U.val), U.property.1,one_mul, V.property.1,mul_one] at hp; exact hp
    intro h; have hp:=congrArg (fun x=> U.val*x*star V.val) h; simp only [mul_assoc] at hp ⊢; rw [← mul_assoc V.val,V.property.2,mul_one,mul_assoc V.val, ←mul_assoc U.val (star U.val),U.property.2,one_mul] at hp; exact hp
 apply (hx k).mpr; unfold Commute SemiconjBy; ext i j; rw [Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm (C i j)]; by_cases t:f i=f j; · rw [h i j t]
 have he : C i j=0:=by
    have he:=Matrix.ext_iff.mpr ((hx f).mp p).eq i j; rw [Matrix.diagonal_mul,Matrix.mul_diagonal,mul_comm (C i j)] at he; contrapose! t; exact mul_right_cancel₀ t he -- wrong contra neg aim
 rw [he,mul_zero,mul_zero]

-- principal display certificate. used at Γ, Σ (proof each finite).
structure Swing {J:Type*}[Fintype J][DecidableEq J](U:Op J)(s:ℝ):Prop where
 curve :∃ (W:UNI J) (f:J→ℝ), U=rotationU W f 1∧(∀ i, |f i| < π) ∧ ∑ i,f i=s
end YM.CF.BPress.Lute
