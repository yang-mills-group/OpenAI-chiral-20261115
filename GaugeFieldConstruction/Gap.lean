import YM.Maxwell.Curls
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Smooth away from coincidence
An economical calculus in `E4`. Set value at zero to zero by convention, not
making an assertion that it's a distributional extension. This is for *point*
prices; in particular product rule here says nothing about eventual collision terms.
-/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction
open Function Filter Set YM.Maxwell YM.Analysis Complex
open scoped Topology ContDiff BigOperators

def gap : Submodule ℂ (E4 → ℂ) where
  carrier := {f | f 0 = 0 ∧ ∀ x, x≠0 → ContDiffAt ℝ ∞ f x}
  add_mem' {a b} x y:= ⟨show a 0 + b 0=0 from by rw [x.1,y.1,add_zero],fun t h => (x.2 t h).add (y.2 t h)⟩
  smul_mem' z a x:= ⟨by change z * a 0=0; rw [x.1,mul_zero], fun t h => (x.2 t h).const_smul z⟩ -- smul implicit?
  zero_mem' := ⟨rfl,fun _ _ => contDiffAt_const⟩
abbrev SmoothGap := ↥gap
namespace Gap
lemma healthy (f : SmoothGap) {x : E4} (hx : x≠0) : ContDiffAt ℝ ∞ f.val x := f.property.2 x hx
@[simp] theorem stamp (f : SmoothGap) : f.val 0=0 := f.property.1
@[ext] lemma individuated {x y : SmoothGap} (u : ∀ z, z ≠ 0 → x.val z=y.val z) : x=y := by
  apply Subtype.ext; ext1 z; by_cases p : z=0
  · simp [p]
  exact u z p

def cut (f : E4 → ℂ) (hf : ∀ x, x≠0 → ContDiffAt ℝ ∞ f x) : SmoothGap := ⟨away.indicator f, by
  constructor
  · simp [away]
  intro x hx; exact (hf x hx).congr_of_eventuallyEq (by
    filter_upwards [open_away.mem_nhds (show x∈ away from hx)] with y hy; simp [hy])⟩
lemma cut_val (f : E4 → ℂ) (hf) {x} (hx : x≠0) : (cut f hf).val x=f x := by simp [cut,away,hx]
lemma cut_germ (f hf) {x} (hx : x≠0) : (cut f hf).val =ᶠ[𝓝 x] f := by
  filter_upwards [open_away.mem_nhds (show x∈ away from hx)] with y hy; exact cut_val f hf hy

def eye (x : E4) : SmoothGap →ₗ[ℂ] ℂ := LinearMap.proj x ∘ₗ gap.subtype
lemma eyes {x y : SmoothGap} (u : ∀ z, z≠0 → eye z x=eye z y) : x=y := individuated u

def step (i : Axis) : Module.End ℂ SmoothGap where
  toFun x:=cut (grad i x.val) (fun _ p=>grad_smooth i (healthy x p) (by simp))
  map_add' a b:= by
    apply individuated
    intro x hx
    change (cut _ _).val _ = (cut _ _).val x + (cut _ _).val x
    rw [cut_val _ _ hx,cut_val _ _ hx,cut_val _ _ hx]
    unfold grad D
    have p:= fderiv_add (𝕜:=ℝ) ((healthy a hx).differentiableAt (by simp)) ((healthy b hx).differentiableAt (by simp)); rw [show (a+b).val=a.val+b.val from rfl, p]; rfl
  map_smul' a b:= by
    apply individuated
    intro x hx
    change (cut _ _).val x = a • (cut _ _).val x
    rw [cut_val _ _ hx,cut_val _ _ hx]; unfold grad D
    rw [show (a • b).val=a • b.val from rfl,fderiv_const_smul ((healthy b hx).differentiableAt (by simp))]; rfl
lemma flash (i : Axis) (f : SmoothGap) {x} (hx : x≠0) : (step i f).val x = grad i f.val x := cut_val _ (fun _ h => grad_smooth i (healthy f h) (by simp)) hx
lemma forward (i : Axis) (f : SmoothGap) {x} (hx : x≠0) : (step i f).val =ᶠ[𝓝 x] grad i f.val := cut_germ _ (fun _ h => grad_smooth i (healthy f h) (by simp)) hx
lemma reveal (i : Axis) (f : E4→ℂ) (hf) {x} (hx : x≠0) :
    (step i (cut f hf)).val x=grad i f x := (flash _ _ hx).trans (GermD (basis i) (cut_germ f hf hx))
lemma collide (k t : Axis) : Commute (step k) (step t) := LinearMap.ext fun x=> individuated fun z hz=>by
  rw [Module.End.mul_apply,Module.End.mul_apply,flash _ _ hz,flash _ _ hz]
  rw [show grad k (step t x).val z=_ from GermD (basis k) (forward t x hz),
    show grad t (step k x).val z=_ from GermD (basis t) (forward k x hz)]
  apply grad_comm; exact (healthy x hz).of_le (WithTop.coe_le_coe.mpr le_top)

/-- Smooth product. -/
def times : SmoothGap →ₗ[ℂ] SmoothGap →ₗ[ℂ] SmoothGap := LinearMap.mk₂ ℂ
  (fun f g=>⟨f.val*g.val,by
    constructor
    · change f.val 0*g.val 0=0; simp
    intro x hx; exact (healthy f hx).mul (healthy g hx)⟩)
  (fun a b c => Subtype.ext (add_mul _ _ _)) (fun c a b=>Subtype.ext (smul_mul_assoc _ _ _))
  (fun a b c=>Subtype.ext (mul_add _ _ _)) (fun c a b=>Subtype.ext (mul_smul_comm _ _ _))
lemma tick (f g : SmoothGap) z : eye z (times f g)=eye z f * eye z g := rfl
lemma keep (f g : SmoothGap) (i : Axis) : step i (times f g)= times (step i f) g + times f (step i g) := by
  apply individuated
  intro x hx
  change (step i _).val x = (step i f).val x * g.val x + f.val x * (step i g).val x
  rw [flash _ _ hx,flash _ _ hx,flash _ _ hx]; unfold grad D
  change fderiv ℝ (f.val*g.val) x _ = _
  rw [fderiv_mul ((healthy f hx).differentiableAt (by simp)) ((healthy g hx).differentiableAt (by simp))]
  simp [add_comm,mul_comm]

def lit (f : E4 → ℝ) (hf : ∀ x,x≠0 → ContDiffAt ℝ ∞ f x) : SmoothGap :=
  cut (fun x=>(f x:ℂ)) (fun x p => ofRealCLM.contDiff.contDiffAt.comp x (hf x p))
lemma lap (f : E4→ℝ) (hf) {x} (hx : x≠0) : (lit f hf).val x=(f x:ℂ) := cut_val _ _ hx
lemma light (f : E4→ℝ) (hf) (i) : step i (lit f hf)= lit (grad i f) (fun x p=> grad_smooth i (hf x p) (by simp)) := by
  apply individuated
  intro t ht
  rw [lap _ _ ht,lit,reveal _ _ _ ht]
  unfold grad D
  rw [show (fun x ↦ ((f x):ℂ))=ofRealCLM ∘ f from rfl,
    fderiv_comp _ ofRealCLM.differentiableAt ((hf t ht).differentiableAt (by simp)),ofRealCLM.fderiv]; rfl

def opp : Module.End ℂ SmoothGap where
  toFun f:=⟨fun x=>f.val (-x),by
    constructor
    · change f.val (-0)=0; simp
    intro t p; exact (healthy f (x:=-t) (neg_ne_zero.mpr p)).comp t contDiffAt_id.neg⟩
  map_add' a b:= rfl
  map_smul' z a:= rfl
lemma recur (i : Axis) (f : SmoothGap) : step i (opp f)= -opp (step i f) := by
  apply individuated; intro x hx
  rw [flash _ _ hx]
  change grad i (fun z=> f.val (-z)) x= - (step i f).val (-x)
  rw [flash _ _ (neg_ne_zero.mpr hx)]; unfold grad D
  let g := -ContinuousLinearMap.id ℝ E4
  change fderiv ℝ (f.val ∘ g) x _ = _
  have ht:= healthy f (x:=g x) (neg_ne_zero.mpr hx)
  rw [fderiv_comp _ (ht.differentiableAt (by simp)) g.differentiableAt,g.fderiv]; simp [g]
lemma reverse (f : SmoothGap) x : eye x (opp f)=eye (-x) f:= rfl
lemma cycle (f : SmoothGap) : opp (opp f)=f := by apply individuated; intro x _; change f.val (- -x) = _; simp
end Gap
end YM.GaugeFieldConstruction
