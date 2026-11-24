import YM.SU5.Reconstruction.Cashier.Target
import YM.SU5.Reconstruction.Cashier.Engineer
/-! # New small norm estimate on ALL Frames

$LowBack$. Explicit ε of frame suppression, indices of torus positions grow
along that history path NOT lottery x re-election from Another grant. Main
steps require op-NORM limit (successor of compact transfer). True application
in later modules. So this criterion is about to be SPENT in this very law.
-/
set_option quotPrecheck false
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6000
set_option maxHeartbeats 490000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.SlabMark.Bankroll
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
local notation "L₀"=>Λ.R.L.val
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(s:ℕ)
open SatinVerification Tapestry PhaseChoice
variable (G:GroundExtension (i:=i) (k:=k) (E:=E) Y H)(j:Axis) (C:Arena Y H G.history.circuit j 0 false)(w:ℕ)
  (S:Finset Cover)(t:Between (tent Y H) j 0 (ruler Λ.block*w) S)(hw:0<w)
local notation "uM"=> (L₀^(s+1-s)*w)
local notation "Wh"=>wingspan Λ l S
local notation "B"=>allBox Y H V G j S s C w t hw
local notation "Bb"=>allBox Y H V G j (wingspan Λ l S) (s+1) C (uM) (escalatesPlace Y H j S s w t hw).1 (escalatesPlace Y H j S s w t hw).2
local notation "T"=>PhaseChoice.transfer Y H G S s
variable {F:Swatch (wingspan Λ l S)}
lemma arrival (f:Swatch S) : B f=Bb (T f):=by -- note notation issue (B)
 let y:=toEntry Y H j false S s w t (allHues Y H S f); let y':=furnished Y H s G.history j false w y (s+1) (by omega)
 have he:y'.val.val=render Wh K (T f):=by
    change stream Y H G.refine s (s+1-s) (render S K f)=_
    rw [show s+1-s=1 from by omega]; exact transferred ..
 exact (refined_box Y H V s G.history G.clipped j false C w y hw (s+1) (by omega)).trans (box_chart Y H V G j Wh (s+1) C uM _ _ (T f) he)

-- tiny in OPERATOR norm.
lemma retire_clock : Real.sqrt rate<1/128:= by
 have hv: Real.sqrt rate=Real.exp (-256):=by
    apply Real.sqrt_eq_iff_mul_self_eq pennies.le (Real.exp_pos _).le |>.2 -- name
    unfold rate; rw [←Real.exp_add]; norm_num
 rw [hv,Real.exp_neg]
 have he:128 < Real.exp 256:=by linarith [Real.add_one_le_exp 256]
 simpa [one_div] using one_div_lt_one_div_of_lt (by norm_num : (0:ℝ)<128) he
variable (f:ℕ→ Swatch S)(a₀:ℝ)(h:∀i, ‖f i‖≤a₀)(p: Rolls Y H s G (fun i=>render S (tent Y H) (f i)) w)
section subsidy
variable {φ:ℕ→ℕ}(v:Tendsto φ atTop atTop)(e:Tendsto (fun i=>PhaseChoice.transfer Y H G S s (f (φ i))) atTop (𝓝 F))
include v e p h
lemma resolution_small: ‖Bb F‖ ≤ Real.sqrt rate:=by
 let hL:=escalatesPlace Y H j S s w t hw; let h₀:ℝ:= spread S*a₀ + 1; have hev:0≤a₀:=(norm_nonneg _).trans (h 0); have ht:0<h₀:=by unfold h₀; positivity
 have hf(k:ℕ):pay (render S K (f k)) h₀:= fun m x=> ((rendered_price Y H S (f k)) m x).trans (le_trans (mul_le_mul_of_nonneg_left (h k) (by positivity)) (le_add_of_nonneg_right (by positivity)))
 let g:= toEntry Y H j false (wingspan Λ l S) (s+1) (uM) hL.1 (allHues Y H _ F)
 change ‖boxOp Y H V (s+1) G.history G.clipped j false C uM g hL.2‖ ≤ _
 apply engineered Y H V _ G.history j false C _ g G.clipped hL.2 rate pennies
 unfold Evaluator
 have hg:g.val.val=render (wingspan Λ l S) K F:=rfl
 rw [hg,show (uM:ℕ)= (L₀*w:ℕ) from by rw [show s+1-s=1 from by omega,pow_one]]
 exact landed Y H V s j w S t hw G f v e h₀ ht hf p -- binder inspect
end subsidy
variable (c:∀ j:Axis,Arena Y H G.history.circuit j 0 false)(th:∀j:Axis,Between (tent Y H) j 0 (ruler Λ.block*w) S)
include h p
lemma tend_small : ∀ᶠ i in atTop, ∀ j:Axis, ‖allBox Y H V G j S s (c j) w (th j) hw (f i)‖ < 1/128:=by
 refine Filter.eventually_all.mpr fun j =>?_ -- 'j' shadow notation B (fixed)
 let X:= allBox Y H V G j S s (c j) w (th j) hw
 let Z:=allBox Y H V G j (wingspan Λ l S) (s+1) (c j) (uM) (escalatesPlace Y H j S s w (th j) hw).1 (escalatesPlace Y H j S s w (th j) hw).2
 by_contra! hl -- eventual not? pushes to exists with negation
 have hy:∃ᶠ i in atTop,(1:ℝ)/128 ≤ ‖X (f i)‖:=by simpa [X] using hl
 obtain ⟨ψ,g,τ⟩:=extraction_of_frequently_atTop hy; let A:=closure ((⇑(T)) '' Metric.closedBall 0 a₀)
 have ht:IsCompact A:=(compact_resolution Y H V G S s).isCompact_closure_image_closedBall _
 have hx(i:ℕ):T (f (ψ i))∈ A:= subset_closure (Set.mem_image_of_mem _ (mem_closedBall_zero_iff.mpr (h (ψ i))))
 obtain ⟨a,H₁,b,b',α⟩:=ht.tendsto_subseq hx
 let θ:=ψ ∘ b; have he:= (g.comp b').tendsto_atTop
 have hB:Tendsto (fun i=> X (f (θ i))) atTop (𝓝 (Z a)):=by
    rw [show (fun i=> X (f (θ i)))=(fun i=> Z (T (f (θ i)))) from funext (fun i=>arrival Y H V s G j (c j) w S (th j) hw _)]
    exact ((Z.continuous.tendsto a).comp α)
 have ht:(1:ℝ)/128 ≤ ‖Z a‖:= ge_of_tendsto' hB.norm (fun i=> τ (b i))
 exact not_lt_of_ge ht ((resolution_small Y H V s G j (c j) w S (th j) hw f a₀ h p he α).trans_lt retire_clock)
end YM.CF.Buffered.Afterglow.Tower.SlabMark.Bankroll
#print axioms YM.CF.Buffered.Afterglow.Tower.SlabMark.Bankroll.tend_small
