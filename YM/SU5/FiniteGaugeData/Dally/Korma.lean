import YM.SU5.FiniteGaugeData.Dally.Apso
import YM.SU5.FiniteGaugeData.Dally.Galleon
/-!
 # Ward paper and b-axis angular drive
 -/
noncomputable section
open Metric Filter Function WithLp
open scoped Topology NNReal ENNReal InnerProductSpace
set_option autoImplicit false
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin.Galleon
namespace Dai
open _root_.YM Dally Gem Leal Leal.Breve Celeritas Land Mist OS OS.Semigroup Flute Apso Mink
variable {K : Axis → Hilbert} (W : ∀ i : Axis, OS.Semigroup (K i) i)
    {ι : Type} (G : Canopy (K timeAxis) ι) (ω : ∀ i, (K i).space) (A : Tribe G)
variable {n : ℕ} (u : Fin n → ι) (w : Palette G u)
variable (b : SpaceAxis) (x : Points n) (t s : ℝ)
local notation "ₜ" => timeAxis
local notation "Π₁" => Palette G u
local notation "e" => Ray.fromAxis b

def cruze (r : SO) := turnO r.val x
def wheelR (t : ℝ) := cruze x (Rho b t)
def staff (r : SO) : Palette G u := fun i=> (G.P (u i)).E r (w i)
def vane (t : ℝ) : Palette G u := staff G u w (Rho b t)
@[simp] lemma cruze_zero : cruze x 1=x:= Luna x
@[simp] lemma cruze_more (p q : SO) : cruze (cruze x q) p=cruze x (p*q):=Lynx x p q
@[simp] lemma staff_zero : staff G u w 1=w:= funext fun i=> by rw [staff,map_one]; rfl
@[simp] lemma staff_more (p q : SO) : staff G u (staff G u w q) p=staff G u w (p*q) := funext fun i=> by unfold staff; rw [map_mul]; rfl
@[simp] lemma wheel_zero : wheelR b x 0=x:= by simp [wheelR]
@[simp] lemma vane_zero : vane G u w b 0=w:= by simp [vane]
lemma wheel_more : wheelR b (wheelR b x s) t = wheelR b x (t+s) := by rw [wheelR,wheelR,cruze_more,Rho_more]; rfl
lemma vane_more : vane G u (vane G u w b s) b t = vane G u w b (t+s):= by simp [vane,staff_more,Rho_more]
lemma wheel_entry (i : Fin n) : wheelR b x t i= circleB (Ray.fromAxis b) t (x i) := rfl
def agent (i : Fin n) (a : Axis) : Points n := points <| Pi.single i (basis a)
@[simp] lemma agent_entry (i j : Fin n) (a : Axis) : agent i a j = if i=j then basis a else 0 := by
  simp [agent, Pi.single_apply,eq_comm]
def stride : (Points n) →L[ℝ] (Points n) :=
  let L := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => E4))
  let f : (Points n) →L[ℝ] (Fin n → E4) := ContinuousLinearMap.pi (fun i => (road (Ray.fromAxis b)).comp
    ((ContinuousLinearMap.proj (R:=ℝ) i).comp L.toContinuousLinearMap))
  L.symm.toContinuousLinearMap.comp f
lemma stride_entry (i : Fin n) : stride b x i=road (Ray.fromAxis b) (x i):=rfl
lemma hubcap (y : E4) : road (Ray.fromAxis b) y = y timeAxis • basis b.castSucc - y b.castSucc • basis timeAxis := by
  simp only [road, _root_.sub_apply, ContinuousLinearMap.smulRight_apply,
    Mink.clockL_at, Ray.alongL_at, Ray.onAxis]
  rw [show position (Ray.fromAxis b).val 0=basis b.castSucc from ?_]; rfl
  apply ext_by
  · rw [spatial_position]; apply PiLp.ext; intro j; simp [Ray.fromAxis, spatial, basis_eq, eq_comm]
  rw [time_position]; simp [time,ear b]
lemma payout : stride b x = ∑ i, ((x i ₜ) • agent i b.castSucc - (x i b.castSucc) • agent i ₜ) := by
  apply PiLp.ext; intro i
  rw [stride_entry, ofLp_sum, Finset.sum_apply, Finset.sum_eq_single i]
  · simp only [PiLp.sub_apply, PiLp.smul_apply, agent_entry, ↓reduceIte]; exact hubcap b _
  · intro j hj u; simp [u]
  · simp
def spanθ := points fun i => (Ray.fromAxis b).scalesT (x i)
lemma pulley : wheelR b x = fun t => x + Real.sin t • stride b x + (Real.cos t - 1) • spanθ b x := by
  funext t; apply PiLp.ext; intro i; rw [wheel_entry]; simp [circleB,stride_entry,spanθ]
lemma engineC : AnalyticAt ℝ (wheelR b x) t := by
  rw [pulley]
  exact (analyticAt_const.add (Real.analyticAt_sin.smul analyticAt_const)).add
    ((Real.analyticAt_cos.sub analyticAt_const).smul analyticAt_const)
lemma ostensible : ContinuousSMul ℝ (Points n) := by
  exact IsBoundedSMul.continuousSMul
attribute [local instance] ostensible
lemma engineR : HasDerivAt (F:=Points n) (𝕜:=ℝ) (wheelR b x) (stride b x) 0 := by
  rw [pulley]
  simpa only [Real.cos_zero, Real.sin_zero, neg_zero, zero_add, add_zero, one_smul, zero_smul]
    using! (((hasDerivAt_const 0 x).add ((Real.hasDerivAt_sin 0).smul_const (stride b x))).add
      (((Real.hasDerivAt_cos 0).sub_const 1).smul_const (spanθ b x)))
lemma engineP : AnalyticAt ℝ (vane G u w b) t := by
  apply analyticAt_pi_iff.mpr
  intro i
  let P := G.P (u i)
  let Q (z : ℂ) := P.link (Ray.fromAxis b) z (w i)
  have S : AnalyticAt ℂ Q (t:ℂ) := ((ContinuousLinearMap.apply ℂ (colorP P.amount) (w i)).analyticAt _).comp (P.ink (Ray.fromAxis b) _)
  apply AnalyticAt.congr (f:=Q ∘ Complex.ofRealCLM) (S.restrictScalars.comp (Complex.ofRealCLM.analyticAt _))
  exact Eventually.of_forall fun s=> (DFunLike.congr_fun (P.base (Ray.fromAxis b) s) _).symm

def plumeP := deriv (vane G u w b) 0
lemma engineD : HasDerivAt (vane G u w b) (plumeP G u w b) 0 := (engineP G u w b 0).differentiableAt.hasDerivAt
lemma portStaff (r : SO) : sailK G u (staff G u w r)=G.stampE r (sailK G u w):=rfl
#print axioms engineC
#print axioms engineR
#print axioms payout
#print axioms engineP
end Dai
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin.Galleon
