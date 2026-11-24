import YM.CF.Spire.Jot
import YM.CF.Thera.Lawn
import YM.RG.Block
set_option autoImplicit false
noncomputable section
namespace YM.CF.Reef
open Function Filter NormedSpace Fock SU Spire Lattice RG
open scoped Topology Matrix.Norms.Frobenius InnerProductSpace
attribute [local instance] Gauge.frobInner
abbrev Ox:=group.Color
abbrev qG:group.El ≃* group.El:= polarT true
lemma mat_g(x): group.mat (qG x)=cc (group.mat x):=rfl
lemma q0(x): qG (qG x)=x:=by apply group.mat_injective; rw [mat_g,mat_g,cc_cc]
lemma cold(x): group.price (qG x)=group.price x:=by simp [Gauge.price,mat_g,Matrix.trace, Matrix.diag,Complex.re_sum]
lemma cool(x): group.chord (qG x)=group.chord x:=by rw [← sq_eq_sq₀ (group.chord_nonneg _) (group.chord_nonneg _),Gauge.chord_price,Gauge.chord_price,cold]
def chill:group.Mat→ₗᵢ[ℝ]group.Mat where
 toFun:=cc
 map_add':=cc_add
 map_smul':= by intro b x; ext; simp -- tune
 norm_map' x:=by
    rw [←sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),Gauge.frob_sq,Gauge.frob_sq]
    change (cc x * star (cc x)).trace.re=_
    rw [← cc_star, ← cc_mul]; simp [Matrix.trace, Matrix.diag,Complex.re_sum]
private lemma bubble(x:group.Mat)(p:x∈group.lie):cc x∈group.lie:=by obtain ⟨p,h⟩:=Thera.league.mp p; apply Thera.league.mpr; constructor; rw [←cc_star,p, cc_neg]; rw [cc,Matrix.trace_transpose,Matrix.star_eq_conjTranspose, Matrix.trace_conjTranspose,h, star_zero]
def frolic: Ox→ₗᵢ[ℝ]Ox where
 toLinearMap:= group.projectColor ∘ₗ chill.toLinearMap ∘ₗ group.colorMat
 norm_map' x:=by
    apply mul_left_cancel₀ group.colorScale_pos.ne'; rw [←Gauge.colorMat_norm,←Gauge.colorMat_norm]; change ‖group.colorMat (group.projectColor (cc _))‖=_; rw [group.colorMat_project_self (bubble _ (group.colorMat_mem _))]; exact chill.norm_map _
lemma fizz(g): group.colorMat (frolic g)= cc (group.colorMat g):= group.colorMat_project_self (bubble _ (group.colorMat_mem _))
lemma fiz2(g): frolic (frolic g)=g:=group.colorMat_injective (by rw [fizz,fizz,cc_cc])
lemma mat_f (x): frolic (group.projectColor x)=group.projectColor (cc x):=by
 symm; apply group.colorMat_injective; rw [Gauge.colorMat_project,fizz,Gauge.colorMat_project]; apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (bubble _ (group.colorMat_project _ ▸ group.colorMat_mem (group.projectColor x)))
 intro w hw; have he: inner ℝ (chill (x-group.lie.starProjection x)) (chill (cc w))=0:=by rw [chill.inner_map_map]; exact Submodule.starProjection_inner_eq_zero _ _ (bubble _ hw)
 rw [show chill (cc w)=w from cc_cc w,map_sub] at he; exact he
lemma swing(g):group.curvature (qG g)= frolic (group.curvature g):=by rw [Gauge.curvature,Gauge.curvature,← map_inv qG, mat_g,mat_g,mat_f, show cc ((1/2:ℝ) • _)=_ from ?_]; exact map_smul chill _ _ |>.trans (by change _ • chill _= _; rw [map_sub]; rfl) -- tune
lemma dip(g c): frolic (group.adjoint g c)=group.adjoint (qG g) (frolic c):=by apply group.colorMat_injective; rw [fizz,group.mat_adjoint,group.mat_adjoint,fizz]; simp [Gauge.conjugate, cc_mul,mat_g] -- tune
lemma mat_cc(x): chill (exp x)=exp (chill x):=by
 letI : NormedAlgebra ℚ group.Mat := NormedAlgebra.restrictScalars ℚ ℂ _; let F: group.Mat →+* group.Mat:=⟨⟨⟨chill,cc_one⟩,cc_mul⟩,cc_zero,cc_add⟩
 exact map_exp F chill.continuous _
lemma cool_a(v): group.lieExp (frolic v)=qG (group.lieExp v):= group.mat_injective (by rw [mat_g,Gauge.mat_lieExp,Gauge.mat_lieExp,fizz]; exact (mat_cc _).symm)
lemma icyC:Continuous qG:=by
 let H:= group.continuous_mat.isClosedEmbedding group.mat_injective
 rw [H.isEmbedding.continuous_iff]; exact chill.continuous.comp group.continuous_mat
end YM.CF.Reef
