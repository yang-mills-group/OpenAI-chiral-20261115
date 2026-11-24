import YM.CF.BPress.Lute.Music
/-! one-parameter principals & cost radius. lifting square path will use half angles. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Lute
open Function Finset Filter NormedSpace InnerProductSpace SU SU.Pair Spin Spin.Paint Lattice Fock Complex Tile Join Metric
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker InnerProductSpace ContDiff Classical
attribute [local instance] opCStarAlgebra
local notation "π"=>Real.pi
namespace Music
variable (k:Fin 5)
abbrev groupX:= (tune_price k).curve.choose
abbrev pricesX:= (tune_price k).curve.choose_spec.choose
lemma all : wave k* star basis=rotationU (groupX k) (pricesX k) 1∧(∀ i,|pricesX k i|<π)∧∑ i, pricesX k i=0:= (tune_price k).curve.choose_spec.choose_spec
def hopper:=rotationU (groupX k) (pricesX k)
def tap(u:ℝ):=hopper k u*basis
lemma smooth_h : ContDiff ℝ ⊤ (hopper k):=rot_smooth ..
lemma smooth_t : ContDiff ℝ ⊤ (tap k):=(smooth_h k).mul contDiff_const
lemma undock : wave 0=basis:=by rw [wave,Mag.center_zero, inv_one,Paint.turn_one]
@[simp] lemma open_t : tap k 0=basis:=by rw [tap,hopper,rot_0,one_mul]
@[simp] lemma close_t : tap k 1=wave k:=by rw [tap, hopper,← (all k).1,mul_assoc,basis_acts.gate.1,mul_one]
lemma special_h(u:ℝ):hopper k u ∈ unitary (Op Slot)∧(hopper k u).det=1:=by refine ⟨rot_unit ..,?_⟩; rw [hopper,rot_det,(all k).2.2,mul_zero,χ_zero]
lemma cong_basis (u:ℝ): hopper k u*basis=basis*(hopper k u)ᵀ:=by
 let f:=pricesX k; let U:=groupX k; let A:=basis; let h:=(all k).2.1; refine shift_diag U (fun i=>χ (1* f i)) _ A ?_ ?_; intro i j g; rw [one_mul,one_mul] at g; have he:f i=f j:= coverχ (h i) (h j) g; rw [show pricesX k i=_ from he]
 have he:(tap k 1)ᵀ=tap k 1:=by rw [close_t]; exact (wave_s k).triangle
 change hopper k 1*basis=_; rw [←show tap k 1=hopper k 1*basis from rfl,←he, tap,Matrix.transpose_mul,basis_acts.triangle]; rfl
lemma half_cong (u:ℝ): hopper k (u/2)*basis*(hopper k (u/2))ᵀ=tap k u:=by rw [tap,mul_assoc,← cong_basis,← mul_assoc, hopper,←rot_add, add_halves]
lemma payoff (u:ℝ): Spin.Sym (tap k u):=by
 unfold tap; obtain ⟨t,b⟩:= special_h k u; refine ⟨?_ , (unitary _).mul_mem t basis_acts.gate,?_⟩; rw [Matrix.transpose_mul,basis_acts.triangle,←cong_basis]; rw [Matrix.det_mul,b, basis_acts.traceX,mul_one]
@[simp] lemma rot_idle(u:ℝ): hopper 0 u=1:=by
 let U:=groupX 0; let f:=pricesX 0; have hf:spectralC U (fun i=>χ (f i))=1:=by have he:= (all 0).1; rw [undock, basis_acts.gate.2, rotationU] at he; simpa using he.symm
 have ht:Matrix.diagonal (fun i=>χ (f i))=1:= (twist U).injective (hf.trans (map_one _).symm)
 have hu: ∀ i, f i=0:=fun i=>coverχ ((all 0).2.1 i) (by simpa using Real.pi_pos) (by have hg:=Matrix.ext_iff.mpr ht i i; simpa using hg)
 change rotationU U f u=_; unfold rotationU spectralC; simp_rw [hu,mul_zero, χ_zero, show Matrix.diagonal (fun _:Slot=>(1:ℂ))=(1:Op Slot) from rfl, map_one]
@[simp] lemma tap_idle(u:ℝ):tap 0 u=basis:=by rw [tap,rot_idle,one_mul]
-- any t; and family budget
def till := spectralC (groupX k) (fun i=>χ (pricesX k i/2)*(Real.cos (pricesX k i/2):ℂ))*basis
lemma bill (a:ℝ)(p:a∈Set.Icc (0:ℝ) 1): ‖tap k a-till k‖<1:=by obtain ⟨m,rfl,x⟩:= Swing.weights (groupX k) (pricesX k) (all k).2.1 a p; unfold tap till; rw [←sub_mul]; rw [CStarRing.norm_mul_coe_unitary _ (⟨basis,basis_acts.gate⟩:UNI Slot)]; exact x
lemma bought : ∃ r0 :ℝ,0<r0∧ r0 <1 ∧ ∀ k:Fin 5,∀ u∈Set.Icc (0:ℝ) 1, ‖tap k u-till k‖ ≤ r0:=by
 let s:ℝ:=1; let A:=Set.Icc 0 s; have ht:A.Nonempty:=⟨0, by simp [A,s]⟩; let f(k)(u):=‖tap k u-till k‖; choose t x T using fun k:Fin 5=> isCompact_Icc.exists_isMaxOn ht ((smooth_t k).continuous.sub continuous_const).norm.continuousOn
 obtain ⟨i,v,H⟩:= Set.exists_max_image Set.univ (fun k=>f k (t k)) (Set.toFinite _) Set.univ_nonempty -- tune
 refine ⟨max (1/2) (f i (t i)), lt_max_of_lt_left one_half_pos, max_lt (by norm_num) (bill i _ (x i)), fun k u p=>?_⟩; exact ((T k p).trans (H _ trivial)).trans (le_max_right ..); -- tune
end Music
end YM.CF.BPress.Lute
#print axioms YM.CF.BPress.Lute.Music.payoff
