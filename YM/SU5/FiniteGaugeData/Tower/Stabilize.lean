import YM.SU5.FiniteGaugeData.Tower.Sitting
import YM.SU5.FiniteGaugeData.Tower.ProductPay
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K" => tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(s:ℕ)
/-!
# Stabilize the entire conditional-link law against upper perturbations on
protected charts

Whole-torus total variation between these conditional *backward* transition
measures, no sign assertion on their inputs in the history and no Poklot
claim that native Gibbs readings vary little with a link. Use per-step on W
held (still integrated with the **signed amplitude** on W).
-/
open Tree Push.GridApprox Stencil Tenant
variable (S:Finset Cover)(P:Patch)(Z:KernelChoices)(p:P.Branches Z SU.group){X:Type*}(c f:Side)(h:(More f).val=(More c).val*P.L.val)(V:X→LinksC)
local notation "B"=> fixedStep P Z (fun _:Unit=>c) (fun _:Unit=>f) (fun _:Unit=>h) ()
local notation "W" x:max=> Satin.graft S f (V x)
local notation "πS"=> sensitive P Z S c f h
local notation "πE"=>hitEdges c (πS)
local notation "μ"=> prior SU.group (More c)
local notation "T"=> P.FrameTag

def patchFee (P:Patch)(S:Finset Cover):ℝ:=(Fintype.card P.FrameTag+Fintype.card Axis*2)*(S.card*(Lattice.box (Push.GridApprox.reach P)).card)
lemma patchFee_n(P:Patch)(S:Finset Cover):0≤patchFee P S:=by unfold patchFee; positivity

-- control all relevant factors including mass and *all* predictor noise
-- conditionals (actual hard branches, exact chosen likelihood laws)
include p
lemma stabilization (x y:X)(β:ℝ)(ε:ℝ)(q:0≤ε)(a:
 ∀ i∈ sensitive P Z S c f h, ∀ t:T, ‖perSite B (W x) i t-perSite B (W y) i t‖≤ ε)(b:
 ∀ i∈hitEdges c (sensitive P Z S c f h), ∀ t: Seat c→ T, ∀ r:SU.E, ‖perLink B β (W x) t i r-perLink B β (W y) t i r‖≤ε):
 (∫ i: Pane c, ‖(B).density β (W x) i-(B).density β (W y) i‖∂μ) ≤ patchFee P S * ε:=by
 let m(w:X)(i: Seat c)(t:T):=perSite B (W w) i t
 let F(w:X)(i: Seat c→T):ℝ:=∏ j, m w j (i j)
 let G(w:X)(t:Seat c→T)(i:Edge (Seat c))(j:SU.E):= perLink B β (W w) t i j
 let u(w:X)(t:Seat c→T)(i:Pane c):=∏ j: Edge (Seat c),G w t j (i j)
 have hm(w i t):0≤ m w i t:= (site_bound P Z p (fun _:Unit=>c) (fun _:Unit=>f) (fun _:Unit=>h) () (W w) i t).1
 have Hm(w i): ∑ t,m w i t=1:=P.frameMass_sum p _
 have hF(w i):0≤ F w i:= prod_nonneg (fun j _=>hm w j _)
 have hg(w t i j):0≤ G w t i j:= link_lower P Z p c f h (W w) _ _ _ _
 have H(w t i):0≤u w t i:= prod_nonneg fun i _=>hg w t i _
 have hc(w t i):Continuous (G w t i):= perLink_cont ..
 have hz(w t):Continuous (u w t):= continuous_finsetProd _ (fun i _=> (hc _ _ _).comp (continuous_apply _))
 have hz'(e:Pane c→ℝ)(t:Continuous e):Integrable e μ:= t.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
 have uT(w t i): ∫ b, G w t i b∂ SU.group.probHaar=1:= perLink_mass ..
 have Ut(w t): ∫ b,u w t b∂μ=1:= by unfold u prior; rw [integral_fintype_prod_eq_prod]; simp_rw [uT]; simp
 have ht(w):∑ i,F w i=1:=by unfold F; rw [←Fintype.prod_sum]; simp_rw [Hm]; simp
 have pm: (∑ i:Seat c→T, ‖F x i-F y i‖) ≤ (Fintype.card P.FrameTag:ℝ)*((πS).card*ε) := by
    refine (discursive (m x) (m y) (hm x) (hm y) (Hm x) (Hm y) (πS) (fun i t=>funext fun v=> affected_site S P Z p c f h V x y t v)).trans ?_ -- Hm overextend
    exact (sum_le_sum (fun i v=> sum_le_sum (fun j _=> a i v j))).trans_eq (by simp_rw [Finset.sum_const,card_univ, nsmul_eq_mul]; ring)
 have pk(t:Seat c→T): (∫ i:Pane c, ‖u x t i-u y t i‖∂μ) ≤ ((πE).card:ℝ)*ε:=by
    refine (sparse_int SU.group.probHaar (G x t) (G y t) (hg x t) (hg y t) (hc x t) (hc y t) (uT x t) (uT y t) (πE) (fun i z=> funext fun k=> affected_link S P Z p c f h V x y z t k β)).trans ?_
    rw [←nsmul_eq_mul,←Finset.sum_const (s:=πE)]; refine sum_le_sum fun i z=>?_ ; exact (integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _=> norm_nonneg _)) (integrable_const ε) (Filter.Eventually.of_forall (b i z t))).trans_eq (by simp)
 let F₀(w:X):Pane c→ℝ:=(B).density β (W w)
 have sf(w:X)(i:Pane c): F₀ w i=∑ t:Seat c → T,F w t * u w t i:= density_parts ..
 let l(i:Seat c→T)(k:Pane c):ℝ:= ‖F x i-F y i‖*u x i k+F y i* ‖u x i k-u y i k‖
 have he(i:Pane c): ‖F₀ x i-F₀ y i‖≤∑ j:Seat c→T,l j i:=by
    rw [sf,sf,←Finset.sum_sub_distrib]; apply (norm_sum_le ..).trans; refine Finset.sum_le_sum fun j _=> ?_; let x':= u x j i; let y':= u y j i; let t:= F y j
    have h':F x j*x'-t*y'=(F x j-t)*x'+t*(x'-y'):=by ring
    rw [h']; apply (norm_add_le ..).trans_eq; rw [norm_mul,norm_mul,Real.norm_of_nonneg (show 0≤x' from H ..),Real.norm_of_nonneg (show 0≤t from hF ..)]
 have hm'(t:Seat c→T):Integrable (fun i:Pane c=> ‖F x t-F y t‖*u x t i) μ:=hz' _ (continuous_const.mul (hz ..))
 have hz₀(t:Seat c→T):Integrable (fun i:Pane c=> F y t*‖u x t i-u y t i‖) μ:=hz' _ (continuous_const.mul (((hz x t).sub (hz y t)).norm))
 have hl(i:Seat c→T):Integrable (l i) μ:= (hm' i).add (hz₀ i)
 refine (integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _=> norm_nonneg _)) (integrable_finsetSum _ (fun i _=> hl i)) (Filter.Eventually.of_forall he)).trans ?_
 rw [integral_finsetSum _ (fun i _=> hl i)]
 have hμ(t:Seat c→T): (∫ i,l t i∂μ) ≤ ‖F x t-F y t‖+F y t*((πE).card*ε):=by
    unfold l; rw [integral_add (hm' t) (hz₀ t),integral_const_mul,integral_const_mul,Ut,mul_one]; exact add_le_add_right (mul_le_mul_of_nonneg_left (pk t) (hF y t)) _ -- right adds? add_le_add_left? recent convention
 refine (Finset.sum_le_sum (fun t _=> hμ t)).trans ?_
 rw [Finset.sum_add_distrib,←sum_mul,ht,one_mul]
 have s' : ((πS).card:ℝ) ≤ (S.card:ℝ)*(Lattice.box (Push.GridApprox.reach P)).card := by exact_mod_cast sensitive_count S P Z c f h
 have e' : ((πE).card:ℝ) ≤ (S.card:ℝ)*(Lattice.box (Push.GridApprox.reach P)).card * Fintype.card Axis*2:= le_trans (Nat.cast_le.mpr (hit_count c (πS))) (by push_cast; gcongr)
 unfold patchFee; apply le_trans (add_le_add_left pm _)
 calc
    _ ≤ (Fintype.card P.FrameTag:ℝ)*((S.card*(Lattice.box (Push.GridApprox.reach P)).card)*ε)+S.card*(Lattice.box (Push.GridApprox.reach P)).card*Fintype.card Axis*2*ε:=by gcongr
    _= _:=by ring

end YM.CF.Buffered.Afterglow.Tower
#print axioms YM.CF.Buffered.Afterglow.Tower.stabilization
