import ExactRunning.Step.Separation

/-!
# Comparing joint to fine

`X.zFlex r x y` is joint cost at independent probes: x coarse background,
`lead` of y joint background. `reduced`: second-order simplification
to incoming (plus constant) when taking coarse background predicted
by joint (`x=fore(y)`, tangentially `x=castLow(y)`; `zFore`). Contrast
`separated` on the diagonal (zLaw).
-/


set_option linter.unusedSectionVars false
noncomputable section
namespace ExactRunning
open YM Stationary Lattice Laurent Bloch RG
open Function Filter Finset Matrix
open scoped BigOperators ContDiff Topology ComplexConjugate Matrix

open Exterior Wilson Precision
open Tree

namespace BlockTie
variable {G : Gauge} {E I : Pylon G} {m : Side} {X : BlockTie E I}


variable (X)
def fore (m : Side) (y : Link G m) := content (X.Z m (X.lead m y))
def castLow (m : Side) := fderiv ℝ (X.fore m) 0
abbrev lift0 (m : Side) := uniformM (G:=G) (X.W m)

def zFlex (r : ℝ) (x y : Link G m) := X.zCost r (X.lead m y) (input G m x)
def zFore (m : Side) (r : ℝ) := fun y => X.zFlex r (X.castLow m y) y
def k_const (m : Side) (r : ℝ) :=
    (1/2) * ((ridge r).cut m (Entry G)).cutlog (X.kcoin m)
def pullIn (m : Side) (r : ℝ) :=
    epCost (X.back r) E.p E.r ∘ input G (X.up m) ∘ X.lift0 m

lemma lead_first (y : Link G m) :
    (X.lead m y).1=input G (X.up m) (X.lift0 m y) := rfl

lemma prophecies :
    Army (X.Z m ∘ X.lead m) 0 :=
  X.lead_lit.ribbons X.branches _ (by rw [X.lead_zero]; rfl)
lemma prophet_zero : (X.Z m ∘ X.lead m) 0=1 := by rw [Function.comp_apply,X.lead_zero,X.Z_zero]
lemma fore_zero : X.fore m 0=0 := by rw [fore,X.lead_zero,X.Z_zero,content_one]
lemma fore_smooth : ContDiffAt ℝ ω (X.fore m) 0 :=
  X.prophecies.logL X.prophet_zero

variable {X}
lemma read_flex {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (r : ℝ) (q k : Y → Link G m) (h : ContinuousAt k 0) (h0 : k 0 = 0) :
    (fun z => X.zEnergy r (q z,X.plait (k z)))=ᶠ[𝓝 0]
      fun z=> X.zFlex r (q z) (k z) := by
  have hb := ((show Tendsto (X.lead m) (𝓝 0) (𝓝 1) from X.lead_zero ▸ X.lead_lit.cont.tendsto).comp
    (show Tendsto k (𝓝 0) (𝓝 0) from h0 ▸ h.tendsto)).eventually extend_retract
  exact hb.mono fun z hz => congr_arg (fun b=> X.zCost r b (input _ _ (q z))) hz

private lemma z_forecast {r : ℝ} (h : X.ZSafe m r) :
    Tandem 2 (X.zFore m r) (fun y => X.zFlex r (X.fore m y) y) := by
  let A := X.castLow m
  let f (u : Link G m → Link G m) := fun y=> ((u y,X.plait y):Point G m (X.up m))
  have hp : Progress (f A) (f (X.fore m)) := by
    have hf := X.plait_analytic (m:=m)
    have hv := (hf.differentiableAt (by simp)).hasFDerivAt
    refine ⟨A.contDiff.contDiffAt.prodMk hf,X.fore_smooth.prodMk hf,
       Prod.ext (map_zero A) X.plait_zero,Prod.ext X.fore_zero X.plait_zero,?_⟩
    exact ((A.hasFDerivAt.prodMk hv).fderiv).trans
      (((X.fore_smooth.differentiableAt (by simp)).hasFDerivAt.prodMk hv).fderiv.symm)
  exact (hp.quadratic (X.z_flat h)).congr
    (X.read_flex r A id continuousAt_id rfl)
    (X.read_flex r (X.fore m) id continuousAt_id rfl)

lemma sector_fit {b : ℝ → Joint G m (X.up m)} {r : ℝ}
    (h : Fit (X.together r m) (X.together r m) (fun t => X.full (b t) (X.Z _ (b t))))
    (he : ∀ᶠ t in 𝓝 0, X.Witness (b t)) :
    Fit ((ridge r).cut m (Entry G)) ((X.back r).cut (X.up m) (Entry G))
      (fun t => X.sectors (b t)) := by
  let P := (ridge r).cut m (Entry G)
  have ht : Fit (X.bCut r m) P (fun t=> (X.prospectus (b t))ᵀ) := by
    refine (h.pick12.neg.mul ((Fit.coin P X.kernel.penalty).inv
      (show (X.kcoin m).det ≠ 0 from X.kcoin_unit.ne_zero))).congr ?_
    filter_upwards [he] with t hh
    rw [X.full_price hh,toBlocks_fromBlocks₁₂,neg_neg,
      Matrix.mul_assoc]
    change (X.prospectus (b t))ᵀ * (X.kcoin m * (X.kcoin m)⁻¹)=_
    rw [Matrix.mul_nonsing_inv _ X.kcoin_unit,Matrix.mul_one]
  refine (ht.tr.mul (Fit.clip _ _).tr).congr ?_
  filter_upwards [he] with t hh
  rw [transpose_transpose,X.prospectus_eq hh]
  simp [transpose_fromCols, fromCols_mul_fromRows]

theorem reduced {r : ℝ} (h : X.ZSafe m r)
    (w : X.Railings r m)
    (x : Link G m) (hx : (ridge r).repeats x)
    (hv : (X.back r).repeats (X.lift0 m x)) (hc : (ridge r).repeats (X.castLow m x)) :
    Touch (fun t => X.zFore m r (t•x))
       (fun t => X.pullIn m r (t•x) + X.k_const m r) := by
  let z t := (t:ℝ) • x
  let b t := X.lead m (z t)
  let C t := X.fore m (z t)
  let v t := X.Z m (b t)
  have ho : z 0=0 := zero_smul ..
  have e : deriv C 0=X.castLow m x :=
    (Push.side _ (X.fore_smooth.differentiableAt (by simp)) x).deriv
  have hz : ContDiffAt ℝ ω z 0 := by unfold z;fun_prop
  have ht : Tendsto z (𝓝 0) (𝓝 0) := ho ▸ hz.continuousAt.tendsto
  have v0 : v 0 = 1 := by unfold v b; rw [ho,X.lead_zero,X.Z_zero]
  have hh0 : (b 0).1=1 := by unfold b; rw [ho,X.lead_zero]; rfl
  have hh : (fun t => input G m (C t)) =ᶠ[𝓝 0] v := ht.eventually
    ((X.prophet_zero ▸ X.prophecies.cont.tendsto :
      Tendsto (X.Z m ∘ X.lead m) _ (𝓝 1)).eventually content_encodes)
  have hC : ContDiffAt ℝ ω C 0 := ContDiffAt.comp (g:=X.fore m) _ (ho.symm ▸ X.fore_smooth) hz
  have H := w hx (z:=C) (by unfold C;rw [ho,X.fore_zero]) (hC.differentiableAt (by simp)) (by rw [e];exact hc)
  have hi := ht.eventually (X.witness_lit X.lead_lit (b:=X.lead m) (by rw [X.lead_zero]; rfl))
  have hu := sector_fit (b:=b) (H.full.congr (hh.mono fun t h => congr_arg (X.full (b t)) h)) hi
  have hm := H.front.congr (hh.mono fun t h => show _ = mail (v t) from congr_arg mail h)
  have hf : Fit ((X.back r).cut _ (Entry G)) ((X.back r).cut _ (Entry G)) (fun t => epMat E.p E.r (b t).1) :=
    ((X.back r).ticket_fit_line (granaryG (E.endpoint.ticket _)) hv).congr <|
    Eventually.of_forall fun t=> by dsimp only [b,Function.comp_apply,z];rw [X.lead_first,map_smul]
  have he := Det.log_predicted hu hm hf (Fit.coin _ _)
    (Fit.coin_unit _ X.penalty).ne_zero
    (by rw [v0]; exact (tonic_cut_unit (ridge r) _ h.2).ne_zero)
    (by rw [hh0];exact (E.endpoint.unit (D:=X.back r) h.2 _).ne_zero)
  have hb : Fit ((X.back r).cut _ (Entry G)) ((X.back r).cut _ (Foot G))
       (fun t=> mail (b t).1) := H.fine
  refine ((z_forecast h).pre hz ho).touch.trans
     ((he.sub (Touch.refl ((hb.tr.mul hb).cutdet_cont.log (by
       rw [hh0];exact (tonic_cut_unit (X.back r) _ h.2).ne_zero)))).congr ?_ ?_)
  · filter_upwards [hi,hh] with t j q
    change _ = X.zCost r (b t) (input G m (C t))
    have q : input G m (C t)=X.Z m (b t) := q
    rw [q,zCost,X.vibrant_equal (show X.Witness (b t) from j), sub_right_comm];rfl
  exact Eventually.of_forall fun t => by
    dsimp only
    nth_rw 1 [add_comm]
    rw [add_sub_assoc,add_comm]
    rfl
end BlockTie
end ExactRunning
