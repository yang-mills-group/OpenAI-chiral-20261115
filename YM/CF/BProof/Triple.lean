import YM.CF.BProof.Centers
import YM.CF.BProof.Chord
import YM.CF.BProof.Taylor

/-! Lie immersion of eq:B-mood. Work on triple Lie norm, with the *inverse* conjugation
convention on the fitted frame. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Mag
open Function SU NormedSpace Matrix Filter Metric Set
open scoped Matrix Matrix.Norms.Frobenius Topology ContDiff NNReal InnerProductSpace

abbrev Triple := PiLp 2 (fun _ : Fin 3 => Lie)
local notation "M" => group.mat
local notation "A" => group.colorMat
local notation "E'" => group.lieExp

def B0 : Triple := WithLp.toLp 2 magnetic

def turn (k : E) (x : Triple) : Triple := WithLp.toLp 2 (fun i=> group.adjoint k (x i))
lemma turn_eq (k : E) (x : Triple) (i : Fin 3) : turn k x i=group.adjoint k (x i) := rfl
lemma turn_mul (k l : E) (x : Triple) : turn (k*l) x=turn k (turn l x) := PiLp.ext fun i => group.adjoint_mul k l _
@[simp] lemma turn_id (x : Triple) : turn 1 x=x := PiLp.ext fun i => group.adjoint_one _
lemma turn_sub (k : E) (x y : Triple) : turn k (x-y)=turn k x-turn k y := PiLp.ext fun i=> map_sub (group.adjoint k) _ _
lemma turn_norm (k : E) (x : Triple) : ‖turn k x‖=‖x‖ := by
 rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2]
 congr 1; ext1 i; exact congrArg (fun x : ℝ=>x^2) (group.norm_adjoint k (x i))
lemma turn_inj (k:E) : Injective (turn k) := by
 intro x y h; have he:= congrArg (turn k⁻¹) h; rwa [← turn_mul,←turn_mul,inv_mul_cancel,turn_id,turn_id] at he

lemma turn_cont : Continuous (fun x : E × Triple=>turn x.1 x.2) := by
 unfold turn; apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => Lie)).comp -- tune
 apply continuous_pi
 intro i
 let P (x : E × Triple) :=A (x.2 i)
 have he:Continuous P:= group.colorMat.continuous_of_finiteDimensional.comp (by fun_prop)
 let h:Continuous (fun x : E×Triple => M x.1) := group.continuous_mat.comp continuous_fst
 exact group.projectColor.continuous_of_finiteDimensional.comp ((h.mul he).mul (Continuous.star h))

def orbit (k : E) := turn k⁻¹ B0
lemma orbit_cont : Continuous orbit:= by
 unfold orbit; change Continuous ((fun x : E × Triple=>turn x.1 x.2) ∘ (fun x : E=>(x⁻¹,B0)))
 exact turn_cont.comp (by fun_prop)
@[simp] lemma orbit_one : orbit 1=B0 := by simp [orbit]
lemma orbit_move (a k : E) : turn a (orbit k)=orbit (k*a⁻¹) := by simp [orbit,turn_mul]
lemma orbit_center (i : Fin 5) (k : E) : orbit (center i*k)=orbit k := by
 apply turn_inj (center i); unfold orbit
 rw [←turn_mul,center_comm i k, _root_.mul_inv_rev, ← _root_.mul_assoc,mul_inv_cancel,_root_.one_mul]
 rw [←turn_mul,center_comm i k⁻¹,turn_mul]
 congr 1; exact PiLp.ext fun j => ((adjoint_center _).mpr ⟨i,rfl⟩ j).symm

theorem fiber (k l : E) : orbit k=orbit l ↔ ∃ i, l=center i*k := by
 constructor
 · intro h; have he:= congrArg (turn l) h; unfold orbit at he; rw [←turn_mul,←turn_mul,mul_inv_cancel,turn_id] at he
   obtain ⟨i,hi⟩:= (adjoint_center (l*k⁻¹)).mp fun j=> congrArg (fun x : Triple => x j) he
   refine ⟨i,?_⟩; rw [←hi]; group -- tune tactic name collisions
 rintro ⟨i,rfl⟩; rw [orbit_center]

def patch (x : Lie) := turn (E' x) B0
lemma patch_zero : patch 0=B0 := by simp [patch]
lemma patch_s : ContDiff ℝ ω patch := by
  apply (contDiff_piLp 2).mpr
  intro i
  exact group.projectColor.toContinuousLinearMap.contDiff.comp
    ((group.exp_jet.mul (f:=fun x : Lie => M (E' x)) (g:=fun _ => A (magnetic i)) contDiff_const).mul
      ((starL ℝ : group.Mat ≃L[ℝ] group.Mat).contDiff.comp group.exp_jet))

lemma immersion : Injective (fderiv ℝ patch 0) := by
 apply (injective_iff_map_eq_zero _).mpr
 intro v hv
 let L:=A v
 have hP : HasDerivAt (fun t : ℝ=>patch (t • v)) 0 0 := by
   have h:HasDerivAt (fun t : ℝ=>t • v) v 0:=by simpa using (hasDerivAt_id' (0:ℝ)).smul_const v
   rw [← hv]; exact HasFDerivAt.comp_hasDerivAt 0 (by simpa using (patch_s.differentiable (by simp) 0).hasFDerivAt) h
 let U (t:ℝ):= M (E' (t • v))
 have he:HasDerivAt U L 0:= by unfold U; simp_rw [group.mat_lieExp,map_smul]; simpa using! hasDerivAt_exp_smul_const (A v) (0:ℝ)
 have hm(i) : L * A (magnetic i)=A (magnetic i)*L := by
   let a:= A (magnetic i); have hp:= ((he.mul_const a).fun_mul (he.star))
   have hx : HasDerivAt (fun t:ℝ=>A (patch (t • v) i)) 0 0 := by
     convert group.colorMat.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt _ ((PiLp.proj 2 _ i : Triple →L[ℝ] Lie).hasFDerivAt.comp_hasDerivAt 0 hP) using 1
     all_goals first|rfl|simp
   have h(t:ℝ) : A (patch (t • v) i)=U t*a*star (U t) := group.mat_adjoint ..
   simp_rw [h] at hx
   have hg := hp.unique hx; rw [show U 0=1 by simp [U], show star L= -L from group.colorMat_skew v] at hg
   simpa [sub_eq_add_neg,add_eq_zero_iff_eq_neg] using hg
 obtain ⟨w,hw⟩:= commutant L (by have h:=hm 2; simp [magnetic,X,group.colorMat_project_self lie_x] at h; exact h) (by have h:=hm 0; simp [magnetic,X,group.colorMat_project_self lie_z] at h; exact h)
 change L = w • (1:group.Mat) at hw
 have ht : Matrix.trace L=0:= (Thera.league.mp (group.colorMat_mem v)).2; rw [hw] at ht
 rw [Matrix.trace_smul,Matrix.trace_one,Fintype.card_fin] at ht; change w*(↑(5:ℕ):ℂ)=0 at ht; have hz : w=0:=by simpa using ht
 rw [hz,zero_smul] at hw; exact group.colorMat_injective (hw.trans (map_zero _).symm)
end YM.CF.BProof.Mag
