import YM.CF.BPress.Spin.Grading
import YM.CF.BPress.Spin.Tilt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
/-! Free identity compression via paying temporal difference. Keep real-part PSD order.
 'Diff contrast of one plane-wave sector.' -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Spin
open Function Filter NormedSpace Finset Lattice Laurent Bloch Lat Sifting Fock Fir Nacre Scroll Thera Tulip Tenant Ember SU SU.Pair Cube Rush Dial Next.Free Quad
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker InnerProductSpace
attribute [local instance] opCStarAlgebra
namespace Blank
variable {N:Side}
def scalarP (U:Op (HopK N)): Op (Single N):=U ⊗ₖ (1:Op Slot)
def lens (A: Momentum→ Op SpinIdx)(N:Side) := scalarP (plates N A)
lemma l_one : lens (fun _=>(1:Op SpinIdx)) N=1:=by rw [lens,piles1,scalarP,Matrix.one_kronecker_one]
lemma l_star (A:Momentum→Op SpinIdx): star (lens A N)=lens (fun p=>star (A p)) N:=by rw [lens,scalarP, op_star_kron,star_one,pilesS]; rfl
lemma l_sub (A B:Momentum→Op SpinIdx) : lens A N -lens B N=lens (fun p=> A p-B p) N:=by simp only [lens,←pilesM]; unfold scalarP; simp only [sub_eq_add_neg,Matrix.add_kronecker,op_kron_neg]
lemma l_mul (A B:Momentum→Op SpinIdx): lens A N*lens B N=lens (fun p=>A p*B p) N:=by unfold lens scalarP; rw [op_kron_mul,pilesP,mul_one]
lemma l_scale (A:Momentum→Op SpinIdx)(a:ℝ): a • lens A N=lens (fun p=>a • A p) N:=by
 have he: a • plates N A=plates N fun p=> a • A p:=by unfold plates; rw [←map_smul]; congr 1; ext ⟨i,b⟩ ⟨j,c⟩; by_cases h:i=j <;> simp [Rush.mark,jump_apply,h]
 unfold lens scalarP; rw [← he]; exact (Matrix.smul_kronecker _ _ _).symm
lemma block_m (f g:Site N→ Op SpinIdx)(h:∀x,f x≤g x): jump (Equiv.refl _) f≤ jump (Equiv.refl _) g:=by
 choose b hb using fun x=> CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (sub_nonneg.mpr (h x)); apply sub_nonneg.mp; rw [←jump_sub];
 let A:=jump (Equiv.refl _) b; have he x:g x-f x=star (b x)*b x:= hb x -- tune
 rw [show jump (Equiv.refl _) (g-f)=star A*A by unfold A; rw [jump_star,jump_mul, Equiv.refl_symm,Equiv.refl_trans]; exact congrArg (jump _) (funext he)]; exact star_mul_self_nonneg _
lemma lens_m (A B: Momentum→Op SpinIdx)(h:∀ x:Site N, A (mel x)≤B (mel x)) : lens A N ≤lens B N:= kron_one (twist_mono _ (block_m _ _ h)) Slot

-- identify vacuum spin strips exactly.
variable (N) (u:Bool)
def cup (u:Bool):Finset SpinIdx:=if u then plusHalf else plusHalfᶜ
lemma lid:angle u=cutM (cup u):=by unfold cup angle; rw [Adef,←raising]; cases u <;> simp [dim_cut]
def tenureX:= univ.filter fun i: Single N=> i.1.2 ∈ cup u
def tenureP :=cutM (tenureX N u)
lemma t_comp:tenureP N true=tickA N:=by
 change _=love N (cutM (upperP N)); ext ⟨⟨x,i⟩,s⟩ ⟨⟨y,j⟩,q⟩;
 by_cases h:x=y <;> by_cases k:i=j <;> by_cases g:s=q <;> simp [tenureP,cup,cutM,loveAt,unityP,helix,upperP,tenureX,h,k,g]
lemma t_lamp: tenureP N u=lens (fun _=>angle u) N:=by
 unfold lens; rw [pilesV,lid]; ext ⟨⟨x,i⟩,s⟩ ⟨⟨y,j⟩,q⟩; by_cases h:x=y <;> by_cases k:i=j <;> by_cases g:s=q <;> simp [tenureP,cup,cutM,tenureX,h,k,g,scalarP,jump_apply]

variable (j:ℕ) (M:Jill.Male)(h:1≤j)
def sideP(u:Bool){I:Type*}[Fintype I][DecidableEq I](A:Op I):=if u then A else 1-A
include h in
lemma nativeP : sideP u (spar j M (1:Bkg (More N)))=lens (bent u j M.val) N:=by
 rw [spar,profile_trivial]; change skewE j M u N 1=lens _ N; rw [skew_flat j h,cart_traded (cBar j M.val u h M.property)]; rfl
-- time layer advance, literal anticut.
abbrev isi : Cover:=step 0
def advanceW (N:Side): Op (Single N):= scalarP (wagon N (fun _=>1) isi)
abbrev phase (p:Momentum):= mode p isi
abbrev δM (p:Momentum): Op SpinIdx:= 1-phase p • 1
def deltaX:=1-advanceW N
lemma advance_lens : advanceW N=lens (fun p=> phase p • 1) N:=by
 let d(p:Momentum):Op SpinIdx:=phase p • 1; let F:= wagon N (fun _=> (1: Op SpinIdx)) isi; let A:=overU N SpinIdx; apply congrArg scalarP (show F=plates N d from ?_); suffices F*A.val=A.val*Rush.mark N d by rw [plates,twist_formula, ←this, mul_assoc]; change F=F*(A.val*star A.val); rw [A.property.2,mul_one]
 ext ⟨x,b⟩ ⟨k,i⟩
 change (F*A.val) _ _=(A.val*Rush.mark N d) _ _
 let P:=mel k; let f(y:HopK N):ℂ:=mode P (natural y.1)*((1:Op SpinIdx) y.2 i/normF N)
 have he(y:HopK N): A.val y (k,i)=f y:= four_id ..
 have ht(x y:SpinIdx): (1:Op SpinIdx) x y=if x=y then 1 else 0:= Matrix.one_apply ..
 rw [Matrix.mul_apply]; simp_rw [he]; rw [show ∑ k:HopK N,F (x,b) k*f k= (F*ᵥ f) (x,b) from rfl, single_load (mode_fee k) b (fun y:SpinIdx=> (1:Op SpinIdx) y i/normF N) (fun _=>1) isi x]; unfold A; simp only [Matrix.mul_apply,Matrix.one_mulVec,Fintype.sum_prod_type,four_id,Rush.mark,jump_apply,Equiv.refl_apply]
 simp [Matrix.one_apply,ite_div,mul_ite,ite_mul,d]; unfold phase; split <;> ring -- tune
lemma δ_lens : deltaX N=lens δM N:=by
 unfold deltaX; rw [advance_lens,←l_one,l_sub]

include h in
lemma glens : ∃ c:ℝ,0<c ∧ ∀ (M:Jill.Male)(N:Side)(x:Site N), c*‖pm x‖^2≤ ‖shell j M.val (mel x)‖:=by
 let I:= Σ _ : Jill.Male, Σ N: Side, Site N; let x(i:I) := pm i.2.2; have hx(k:I) : ‖x k‖≤Real.pi:= (pi_norm_le_iff_of_nonneg Real.pi_pos.le).mpr fun i=> abs_le.mpr ⟨(pm_zone k.2.2 i).1.le,(pm_zone ..).2⟩
 let t: Ember.Tax I:=⟨fun i=> ‖x i‖,Real.pi,fun i=> norm_pos_iff.mpr (pm_nonzero i.2.2),hx⟩
 obtain ⟨c,h,H⟩:=Jill.court j h (t:=t) (fun i=>i.1) x (fun _=>rfl) hx; exact ⟨c,h,fun i n k=> H ⟨i,n,k⟩⟩
lemma realLens (x:Site N): shell j M.val (mel x)=(‖shell j M.val (mel x)‖:ℂ):= Jill.express j (pm x) M.val (base_subset_realCube zone_pos (mel_h x)) M.property
lemma phase_lens (x:Site N): ‖(1:ℂ)-phase (mel x)‖≤ ‖pm x‖:=by
 unfold phase mode isi; rw [norm_sub_rev]; unfold mel; have he: (∑ i, tmap (pm x) i *((step (0:Axis) : Cover) i:ℂ))= (pm x 0:ℂ):=by simp [Lattice.step_apply,tmap] -- tune order
 rw [he]; exact Real.norm_exp_I_mul_ofReal_sub_one_le.trans (norm_le_pi_norm ..)
lemma cube_law (x:Site N) : let A:=angle u; let B:=bent u j M.val (mel x); let J:= A*(1+Fir.zen (mixL j M.val (mel x))); A*B*A= (‖shell j M.val (mel x)‖:ℝ) • A:=by
 intro A B J; let X:=cutM (cup u); have hx:IsStarProjection A:=by unfold A; rw [lid]; exact cutM_idp _
 unfold A B; rw [aspect u j M.val (base_subset_realCube zone_pos (mel_h x)),Matrix.smul_mul]; nth_rw 1 [realLens N j M x]
 rw [mul_assoc (angle u), add_mul,one_mul,zenAngle,mul_add, ←mul_assoc (angle u),Fock.Porth hx,zero_mul,add_zero,hx.isIdempotentElem.eq]; ext; simp [Complex.real_smul,A]
lemma cube_sq (x:Site N): let P:=angle u; let B:=δM (mel x)* P; star B*B = ‖(1:ℂ)-phase (mel x)‖^2 • P:= by
 intro P B; let z:=phase (mel x); have hp:IsStarProjection P:=by unfold P; rw [lid]; exact cutM_idp _
 rw [show B=(1-z) • P by unfold B δM; rw [sub_mul,Matrix.smul_mul, one_mul,sub_smul,one_smul],star_smul,hp.isSelfAdjoint,Matrix.smul_mul,Matrix.mul_smul,hp.isIdempotentElem.eq,smul_smul]
 have ht(a:ℂ):star a*a=((‖a‖^2:ℝ):ℂ):=by rw [mul_comm, Complex.ofReal_pow]; exact inner_self_eq_norm_sq_to_K (𝕜:=ℂ) a -- tune
 rw [ht]; ext; simp [Complex.real_smul,z] -- tune
include h in
theorem blank_difference : ∃ c:ℝ,0<c ∧ ∀ N (M:Jill.Male) (u:Bool), let A:= sideP u (spar j M (1:Bkg (More N))); let P:=tenureP N u; c • (star (deltaX N*P) * (deltaX N*P)) ≤ P*A*P := by
 obtain ⟨c,f,p⟩:= glens j h; refine ⟨c,f,fun N M u=>?_⟩; intro A P; unfold P A; rw [nativeP N u j M h,t_lamp,δ_lens,l_mul,l_star,l_mul,l_mul,l_mul,l_scale]
 apply lens_m; intro x; rw [cube_law N u j M x, cube_sq N u x,smul_smul]
 apply smul_le_smul_of_nonneg_right ((mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (phase_lens N x) 2) f.le).trans (p M N x)) (by rw [lid]; exact IsStarProjection.nonneg (cutM_idp _)) -- tune
end Blank
end YM.CF.BPress.Spin
