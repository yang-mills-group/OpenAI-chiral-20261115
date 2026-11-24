import YM.SU5.FiniteGaugeData.Mirage.Velour
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Calculus.Deriv.Star
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxSize 20000
set_option maxHeartbeats 440000
noncomputable section
namespace YM.CF.Window.Mirage
open Function Filter Lattice Cube Metric Complex Finset Laurent Next.Free Bloch Fir Lat MeasureTheory Fock Rush
open scoped Topology BigOperators Pointwise ENNReal Matrix Matrix.Norms.L2Operator MatrixOrder InnerProductSpace ComplexOrder Kronecker
open Scroll Spire Peaks Tap Tenant Tulip Buffered Fock.Brique Window.Brique Largo
attribute [local instance] opCStarAlgebra
set_option quotPrecheck false
variable {N X:Side}{s r d w j:ℕ}{a C:ℝ}{σ τ:Window.Family}{S T U:Finset Cover}
local notation "Μ"=> Single N
local notation "Κ"=> FC (Single N)
open SU Dial Cascade Scree
private lemma billed (f g:ℂ→ℂ)(F:Differentiable ℂ f)(G:Differentiable ℂ g)(h:f 0=1)(t:g 0=1): ∃ z:ℂ, ‖z‖=1 ∧ 1/2 < ‖f z*g (star z)‖:=by
 by_contra! x; let k(z:ℂ):= star (g (star z)); let H:= f*k; have he:Differentiable ℂ k:=by
    intro z; change DifferentiableAt ℂ (star ∘ g ∘ (starRingEnd ℂ)) z; rw [differentiableAt_star_conj_iff]; exact G _
 let U:=Metric.ball (0:ℂ) 1; have hu:DiffContOnCl ℂ H U:= (F.mul he).diffContOnCl; have hx:= norm_le_of_forall_mem_frontier_norm_le (U:=U) (C:=1/2) isBounded_ball hu ?_ (subset_closure (by simp [U] : (0:ℂ)∈U)) -- syntax
 have ht:H 0=1:=(by simp [H,k,h,t]); have hd: ‖H 0‖ ≤ (1:ℝ)/2:=hx; rw [ht,norm_one] at hd; norm_num at hd
 intro i hi; unfold H k; simp only [Pi.mul_apply,norm_mul, norm_star, Function.comp_apply]; simp_rw [U, frontier_ball (0:ℂ) (by norm_num:(1:ℝ)≠0), mem_sphere_zero_iff_norm] at hi; exact (_root_.norm_mul (f i) (g (star i))).ge.trans (x i hi) -- orientation.

section T
variable (L:Mark N→ₗ[ℂ]ℂ)
variable {o1 o2: Site (More N)}{U V T S:Support (More N)}(p:Corset U T o1)(q:Corset V S o2)(τ:Window.Family)
def conspire {o:Site (More N)}{U T:Support (More N)}(p:Corset U T o) : FC (Single N) →ₗ[ℂ] Mark N where
 toFun := cargo p 1
 map_add' i j:= by ext1 x; unfold cargo; simp [map_add]
 map_smul' a u:= by ext1 x; unfold cargo; simp [flipsP,twist_scalar] -- tune
@[simp] lemma conspire_one {o:Site (More N)}{U T:Support (More N)}(p:Corset U T o): conspire p 1=1 := by funext x; change (cargo p 1 _) x=1; rw [cargo]; simp
-- if bought EVERY rotation independently, RIGHT average over root, get matter component
abbrev discord (f g:Mark N) := L (f*g)-L f*L g
lemma stirring (f: Mark N): ∃ A : Mark N →ₗ[ℂ]ℂ, (∀ x,A x= discord L f x):= ⟨L.comp (LinearMap.mul ℂ _ f) - L f • L,fun _=>rfl⟩
lemma stir_left(f: Mark N): ∃ A : Mark N→ₗ[ℂ]ℂ, ∀ x,A x=discord L x f:=by
 let A:= L.comp (LinearMap.mulRight ℂ f); -- tune
 refine ⟨A-L f • L,fun x=>?_⟩; unfold discord; change _-L f*L x=_; rw [mul_comm (L f)]; rfl
variable (F G:ℂ → FC (Single N))
open scoped Classical
-- Will extract covariance between F(z) and an exact single Chord term Y from G(\bar z)-1, nonzero. F here covariant on itself & throughout. Covers `price H`.
lemma against (v:Differentiable ℂ F)(w:Differentiable ℂ G)(H:L 1=1)(f:F 0=1)(g:G 0=1) (h:∀ (z:ℂ),‖z‖=1→∀ e:SU.E, ‖L (conspire p (F z)*conspire q (orbitB (G (star z)) e))‖ ≤ 1/2) (M: Finset (Single N))(Q:Support (More N))(P:∀ z:ℂ, Receipt σ τ Q M (G z-1)): -- U conflict! actual Right lower support? make A
 ∃ (z:ℂ),‖z‖=1 ∧ ∃ l:List (Single N),l≠[] ∧ l.Nodup ∧ l.toFinset⊆ M ∧ ∃ A: FC (Single N), Chord σ τ N Q (spotted l) A ∧ discord L (conspire p (F z-1)) (conspire q A)≠0 ∧ ∀ i:SU.E,orbitB A i=A:=by
 let X:= (L.comp (conspire p)).toContinuousLinearMap; let Y:= ((L.comp (conspire q)).comp (centB N)).toContinuousLinearMap; obtain ⟨z,v,e⟩:= billed (X∘ F) (Y ∘ G) (X.differentiable.comp v) (Y.differentiable.comp w) (by unfold X; rw [comp_apply,f]; change L (conspire p 1)=_; rw [conspire_one,H]) (by unfold Y; rw [comp_apply,g]; change L (conspire q (centB N 1))=_; rw [cent_one,conspire_one,H])
 let A:= conspire p (F z); let Z:= G (star z); let U₀:=centB N Z; let W: FC (Single N)→L[ℝ]ℂ:= ((L.comp ((LinearMap.mul ℂ _ A).comp (conspire q))).toContinuousLinearMap).restrictScalars ℝ; have he: ‖L (A * conspire q U₀)‖ ≤ 1/2:=by
    change ‖W (centB N Z)‖ ≤ _; have hx:W (centB N Z)=_ := (W.integral_comp_comm (orbit_integrable Z)).symm; -- IntegralMeasure
    rw [hx]; exact (norm_integral_le_of_norm_le (integrable_const (μ:=SU.group.probHaar) _) (Eventually.of_forall (h z v))).trans_eq (by simp) -- function type maybe no
 have hg: discord L A (conspire q U₀)≠0:=fun k=> not_lt_of_ge he ((sub_eq_zero.mp k).symm ▸ (show 1/2 < ‖L A * L (conspire q U₀)‖ from e)); -- direction
 let T:= conspire p (F z-1); obtain ⟨C,u⟩:= stir_left L (conspire q U₀); obtain ⟨B,t⟩:= stirring L T; let X:=B.comp (conspire q); have hp: X (centB N (Z-1))≠0:=by
    unfold X; rw [map_sub]; change B _ ≠_; rw [map_sub, map_sub, cent_one,conspire_one,t,show B 1=0 from (t _).trans (by unfold discord; rw [mul_one,H,mul_one,sub_self]),sub_zero, ←u, show T=A-1 from (by unfold T A; rw [map_sub, conspire_one]),map_sub, show C 1=0 from (u _).trans (by unfold discord; rw [one_mul,H,one_mul,sub_self]),sub_zero, u]; exact hg
 obtain ⟨t',x',p',g',A',h',y',z'⟩:= (P (star z)).buys X hp; exact ⟨z,v,t',x',p',g',A',h', fun z=> y' ((t (conspire q A')).trans z), z'⟩
end T
end YM.CF.Window.Mirage
