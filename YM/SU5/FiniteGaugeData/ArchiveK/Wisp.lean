import YM.SU5.FiniteGaugeData.Largo.Duet
import YM.Space.Configurations
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Window.ArchiveK
open Function Filter Lattice Metric Complex Finset Laurent Next.Free Bloch Fir Lat MeasureTheory Fock Rush Largo WithLp
open scoped Topology BigOperators Pointwise ENNReal Matrix Matrix.Norms.L2Operator MatrixOrder InnerProductSpace ComplexOrder Kronecker
attribute [local instance] opCStarAlgebra
/- Wisp.H. Cover continuous real scalar tool E one coords. T quantities discharge convol. -/
section spatial
variable (x y:E4) (p q:Space3)
local notation "ℙ" => E4 ≃ₗᵢ[ℝ] E4
-- radial definitions
abbrev emitX(a : Cover):E4:= toLp 2 fun i=> (a i:ℝ)
@[simp] lemma emit_axis(a : Cover)(i:Axis): emitX a i=a i:= rfl
lemma emit_in : Injective emitX:=fun i j p=> funext (fun a=> Int.cast_injective (α:=ℝ) (congrArg (fun x:E4=> x a) p))
@[simp] lemma emit_sub (a b:Cover) : emitX (a-b)=emitX a-emitX b:=by apply PiLp.ext; intro i; simp
@[simp] lemma emit_add (a b:Cover) : emitX (a+b)=emitX a+emitX b:=by apply PiLp.ext; intro i; simp
@[simp] lemma emit_neg (a:Cover): emitX (-a)= -emitX a:= by apply PiLp.ext; intro i; simp
@[simp] lemma emit_origin : emitX 0=0:= by apply PiLp.ext; intro i; simp
lemma pis (x y:E4): inner ℝ x y=∑ i:Axis, x i*y i:=by rw [PiLp.inner_apply]; apply Finset.sum_congr rfl; intro i _; rw [RCLike.inner_apply]; simp [mul_comm]
-- Pair-kin; choose Le.
def rectX : WithLp 2 (Space3 × ℝ) ≃ₗᵢ[ℝ] E4 where
 toFun p:= position p.fst p.snd
 invFun p:= WithLp.toLp 2 (spatial p,time p)
 right_inv p:= position_eta _
 left_inv p:= by apply WithLp.ofLp_injective 2; apply Prod.ext; exact spatial_position p.fst p.snd; exact time_position p.fst p.snd
 map_add' p q:=by apply PiLp.ext; intro i; fin_cases i <;> rfl
 map_smul' p q:= by apply PiLp.ext; intro i; fin_cases i <;> rfl
 norm_map' p:= by
    rw [←sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), WithLp.prod_norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2]; rw [Fin.sum_univ_castSucc]; rfl -- full Fin.snoc not definally
local notation "P" p:max t:max=> WithLp.toLp 2 (p,t)
def upright (G:E4 ≃ₗᵢ[ℝ] E4): Space3×ℝ ≃ᵐ E4 := ((MeasurableEquiv.toLp 2 (Space3×ℝ)).trans rectX.toMeasurableEquiv).trans G.toMeasurableEquiv
lemma upmarket (G:E4 ≃ₗᵢ[ℝ] E4): MeasurePreserving (upright G) volume volume:= G.measurePreserving.comp (rectX.measurePreserving.comp (WithLp.volume_preserving_toLp _ _))
def seedX (G:ℙ)(p:Space3):= upright G (p,0)
def sailX (G:ℙ):= upright G (0,1)
@[simp] lemma up_G (G:ℙ)(p:Space3×ℝ) : upright G p= G (position p.1 p.2):= rfl
lemma line_G(G:ℙ)(p:Space3×ℝ): upright G p=seedX G p.1+p.2 • sailX G:=by
    rw [up_G]; unfold seedX sailX; rw [up_G,up_G,←map_smul,←map_add]; -- refine congrArg G ?_
    apply congrArg G; apply PiLp.ext; intro i; refine Fin.lastCases ?_ (fun j=> ?_) i; change p.2=(0:ℝ)+p.2 • (1:ℝ); simp; simp [position]
lemma norm_xray(p:Space3)(u:ℝ): ‖position p u‖^2= ‖p‖^2+u^2:=by change ‖rectX (P p u)‖^2=_; rw [LinearIsometryEquiv.norm_map, WithLp.prod_norm_sq_eq_of_L2]; change ‖p‖^2+‖u‖^2= _; rw [Real.norm_eq_abs, sq_abs]
@[simp] lemma seed_size(G:ℙ) : ‖seedX G p‖=‖p‖:=by unfold seedX; rw [up_G,LinearIsometryEquiv.norm_map,←sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),norm_xray]; simp
@[simp] lemma sail_size(G:ℙ) : ‖sailX G‖=1:=by unfold sailX; rw [up_G,LinearIsometryEquiv.norm_map,←sq_eq_sq₀ (norm_nonneg _) zero_le_one,norm_xray]; simp
lemma kv (p q:Space3)(x y:ℝ) : inner ℝ (position p x) (position q y)= inner ℝ p q+x*y:=by rw [show position p x=rectX (P p x) from rfl, show position q y=rectX (P q y) from rfl, LinearIsometryEquiv.inner_map_map, WithLp.prod_inner_apply]; change _+inner ℝ x y=_; simp [mul_comm]
lemma sail_zero(G:ℙ) : inner ℝ (seedX G p) (sailX G)=0:=by unfold seedX sailX; rw [up_G,up_G,LinearIsometryEquiv.inner_map_map, kv]; simp
@[fun_prop] lemma seed_cont(G:ℙ) : Continuous (seedX G):=by change Continuous (fun p:Space3=> G (rectX (P p 0))); fun_prop
abbrev brushQ(p:E4): Momentum:= Fir.tmap p.ofLp
lemma spendQ(p:E4) : pass (brushQ p)=((‖p‖^2:ℝ):ℂ):=by rw [EuclideanSpace.real_norm_sq_eq]; unfold brushQ pass; push_cast; rfl
@[fun_prop] lemma brush_safe : Continuous brushQ := by unfold brushQ Fir.tmap; fun_prop
abbrev coastE(x:ℝ) :ℂ := Complex.exp (Complex.I*x)
@[fun_prop] lemma contCoastE : Continuous coastE:=by unfold coastE; fun_prop
lemma surfK (p:E4)(x:Cover): mode (brushQ p) x=coastE (inner ℝ p (emitX x)):=by rw [pis]; simp only [mode,coastE,brushQ, Fir.tmap, emit_axis,ofReal_sum, ofReal_mul, ofReal_intCast]
@[simp] lemma coast_pay(v:ℝ) : ‖coastE v‖=1:=by simp [coastE,Complex.norm_exp]
@[simp] lemma coast_inv(v:ℝ): star (coastE v)=coastE (-v):=by unfold coastE; simp only [Complex.star_def, ←Complex.exp_conj,map_mul, conj_I, conj_ofReal]; rw [ofReal_neg,mul_neg,neg_mul]
@[simp] lemma coast_zero : coastE 0=1:=by simp [coastE]
lemma coast_add(v w:ℝ) : coastE (v+w)=coastE v*coastE w:=by simp [coastE,mul_add,Complex.exp_add]
@[simp] lemma coast_dual(v:ℝ): coastE (-v)*coastE v=1:=by rw [←coast_add,neg_add_cancel,coast_zero]
@[simp] lemma coast_inv'(v:ℝ): (coastE v)⁻¹=coastE (-v):=by rw [←eq_inv_of_mul_eq_one_left (coast_dual v)]; -- tune
lemma arm_abs (x:E4)(i:Axis): |x i| ≤ ‖x‖:= by rw [← YM.basis_inner i x]; simpa [YM.basis_norm] using abs_real_inner_le_norm (YM.basis i) x
lemma one_arm (x:E4):∃ i:Axis, ‖x‖ ≤ 2* |x i|:= by
 by_contra! h; have he:= Finset.sum_lt_sum_of_nonempty (s:=@univ Axis _) univ_nonempty (f:=fun i:Axis=>4*(x i)^2) (g:=fun _=> ‖x‖^2) (fun i _=> by
     have ht:= pow_lt_pow_left₀ (h i) (show 0≤2* |x i| from by positivity) (n:=2) (by norm_num)
     rw [mul_pow, sq_abs] at ht; linarith only [ht]); rw [←mul_sum,← EuclideanSpace.real_norm_sq_eq x,sum_const,card_univ,Fintype.card_fin] at he; exact (not_lt_of_ge (le_of_eq (by norm_num))) he
lemma abject(a:ℕ)(u:Cover)(t:u∈ Lattice.box a): ‖emitX u‖ ≤ 2*a:= by obtain ⟨i,h⟩:= one_arm (emitX u); apply h.trans; gcongr; rw [emit_axis]; rw [abs_le]; obtain ⟨v,w⟩:= box_test.mp t; norm_cast; exact ⟨v i,w i⟩
lemma hinder(a:ℕ)(u:Cover)(p:u∉ Lattice.box a) : (a:ℝ) < ‖emitX u‖:= by
 by_contra! h; apply p (box_test.mpr ?_); have he(i:Axis): -(a:ℤ) ≤ u i∧ u i ≤ a:= by have hv:= abs_le.mp ((arm_abs (emitX u) i).trans h); simp only [emit_axis] at hv; exact_mod_cast hv
 exact ⟨fun i=> (he i).1,fun i=> (he i).2⟩
end spatial
open Measure
lemma zero_free {X:Type*} [NormedAddCommGroup X][Borel' : MeasurableSpace X][BorelSpace X](μ:Measure X)[NullSingletonClass μ]: ∀ᵐ x:X ∂μ,x≠0:= ae_iff.mpr (by simp)
#print axioms seed_size
end YM.CF.Window.ArchiveK
