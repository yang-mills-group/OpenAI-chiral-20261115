import YM.Push.LOOP_COEFFICIENT.Color
import YM.CF.Thera.Jolt
import YM.CF.Matter.Anomaly

/-!
# Matter and color intertwiners in U1

Work with the actual single defining group, `SU.matter`. Fix its tangent
normalization and determine the representation matrices over Complex. No
claim about anomaly-cancellation, the overall cutoff or its elections here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction
open CF Function Set Matrix Finset
open scoped Topology Matrix Matrix.Norms.Frobenius Kronecker BigOperators
namespace Matter
abbrev F := CF.SU.F
abbrev Ten := CF.SU.Ten
abbrev Sheet := CF.SU.Sheet
abbrev E := CF.SU.E
abbrev Slot := CF.SU.Slot
abbrev V := Op F
abbrev U := Op Sheet
abbrev C := SU.group.Color
abbrev G := SU.group

def adj (u : E) := G.adjoint u
abbrev H : C →ₗ[ℝ] V := G.colorMat
abbrev blockRep (u : E) := SU.each (SU.fund u)
/-- Trace over defining five. -/
def sl : Submodule ℂ V := LinearMap.ker (Matrix.traceLinearMap F ℂ ℂ)
lemma payable (x : V) : x∈sl ↔ x.trace=0 := Iff.rfl
def adact (u : E) (x : sl) : sl := ⟨SU.fund u*x.val*star (SU.fund u), by
  rw [payable,Matrix.trace_mul_cycle, show star (SU.fund u)*SU.fund u=1 from u.val.property.1,one_mul]; exact x.property⟩

/-- Complexified generator: `-Aᵀ`, not `cc A`, on conjugate fundamental. -/
def repX (A : V) := CF.Join.both (ExTwo.gen A) (-A.transpose)

lemma charges (x : C) : H x∈sl := (CF.Thera.league.mp (G.colorMat_mem x)).2

def core (x : C) : sl := ⟨H x, charges x⟩
lemma agrees (x : C) : repX (H x) = SU.sheetD (H x) := by
  unfold repX SU.sheetD
  rw [cc,show star (H x) = -(H x) from G.colorMat_skew x]; simp


lemma hero (u : E) (x : C) : core (adj u x) = adact u (core x) :=
  Subtype.ext (G.mat_adjoint u x)

-- Differentiate actual tangent path in SU. Distinguish L2 from gauge Frobenius norm
-- in these deriv proofs. Follows equivalent norm representations only along ℝ here.
def march (x : C) (t : ℝ) := G.lieExp (t • x)
lemma fund_value (x : C) : march x 0=1 := by simp [march]
lemma differ (x : C) : HasDerivAt (fun t=>SU.fund (march x t)) (H x) 0 := by
  let p : ℝ→C := fun z=>z • x
  change HasDerivAt (fun z=>G.mat (G.lieExp (p z))) _ _
  simp only [p,G.mat_lieExp,map_smul]; simpa using! hasDerivAt_exp_smul_const (G.colorMat x) (0:ℝ)
lemma matter_d (x : C) : HasDerivAt (fun t=>blockRep (march x t)) (SU.sheetD (H x)) 0 := by
  have hp := differ x
  have e₀ : SU.fund (march x 0)=1:=by rw [fund_value,SU.fund_one]
  have ht := SU.eachD (f:=fun t=>SU.fund (march x t)) e₀ hp
  exact ht

lemma turns (u : E) (x : C) : SU.fund u*H x=H (adj u x)*SU.fund u := by
  change G.mat u *G.colorMat x=G.colorMat (G.adjoint u x)*G.mat u
  rw [G.mat_adjoint]; unfold Gauge.conjugate; rw [mul_assoc (G.mat u * _), G.mat_star_mul,mul_one]

lemma direction (u : E) (x : C) : blockRep u*repX (H x)=repX (H (adj u x))*blockRep u := by
  -- g-compatible directly by tensor formula; use Q on first block
  rw [repX,repX,blockRep,CF.SU.each, Join.both_mul, Join.both_mul]
  congr 1
  · refine ExTwo.q_inj ?_
    rw [← Matrix.mul_assoc,← ExTwo.wedgeTensor,← Matrix.mul_assoc,ExTwo.gen_tensor,
      Matrix.mul_assoc,ExTwo.gen_tensor,Matrix.mul_assoc,← ExTwo.wedgeTensor,
      ← Matrix.mul_assoc,← Matrix.mul_assoc]; congr 1
    unfold ExTwo.current
    rw [mul_add,add_mul,ExTwo.kr_mul,ExTwo.kr_mul,ExTwo.kr_mul,ExTwo.kr_mul,one_mul,mul_one,turns]
  let A := SU.fund u
  have he := turns u x
  have hp := congr_arg cc he; rw [cc_mul,cc_mul] at hp
  have hv c : -transpose (H c)=cc (H c) := by rw [cc,show star (H c) = -(H c) from G.colorMat_skew c]; simp
  rw [hv,hv]; exact hp

/-- Primitive generation block commutation, applied later separately for
 every generation matrix. -/
def pure (v : Op Sheet) : Prop := ∀ i, blockRep i*v=v*blockRep i

def action (g : C →ₗ[ℝ] Op Sheet) : Prop := ∀ u x, blockRep u*g x=g (adj u x)*blockRep u

lemma point (X : C →ₗ[ℝ] Op Sheet) (h : action X) (a b : C) :
    X (G.ad a b) = repX (H a)*X b-X b*repX (H a) := by
  have l:= (matter_d a).mul_const (X b)
  let T (b : C) := X.toContinuousLinearMap
  have r:= (((T b).hasFDerivAt.comp_hasDerivAt 0 (YM.Push.Loops.adjoint_rate (a:=a) b)).fun_mul (matter_d a))
  -- rewrite derivative along conjugates
  unfold T at r
  simp only [Function.comp_def] at r
  change HasDerivAt (fun t=> X (adj (march a t) b)*blockRep (march a t)) _ _ at r
  rw [show (fun t=>X (adj (march a t) b) * blockRep (march a t)) = (fun t=>blockRep (march a t)*X b) from funext fun t=> (h (march a t) b).symm] at r
  have hp := r.unique l
  rw [agrees]; -- identity at t=0
  simp [blockRep,fund_value,SU.fund_one,SU.each_one] at hp
  exact eq_sub_of_add_eq hp

lemma centers (v : Op Sheet) (p : pure v) (a : C) : repX (H a)*v=v*repX (H a) := by
  rw [agrees]
  have h := (matter_d a).const_mul v
  have e:= (matter_d a).mul_const v
  exact e.unique (by
    change HasDerivAt (fun t=>blockRep (march a t)*v) _ _; rw [show (fun t=>blockRep (march a t)*v) = (fun t=>v*blockRep (march a t)) from funext fun i => p _]; exact h)
end Matter
end YM.GaugeFieldConstruction
