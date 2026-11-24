import YM.CF.Cloak.Arch
import YM.CF.Rill.Oboe
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Cloak
open Siete
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG PhysicalNext.JointLoad Heir Next.Foundations AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree Esti
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD
open Ac
variable {c f:Side}(S:StepData c f){r v:ℕ}
open CF.Jet
local notation "G"=> SU.group
variable {S}{n:ℕ}{θ a b m x t w K C d:ℝ}
variable {K': Teller G}{A B:Stores S}{T:Tube G S}{V:Config G c}{U:Config G f}{k:S.Choices}{q:Chi}{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][Nonempty E]{x':E}
open AnalyticBridge.Annulus1AD Push.SectorMeasure.Oriented Pressure.Tube
variable {O:Stores S}{F: Forest S.ratio}{Y:LinkArray G (Frozen A x F)}{z:LogArray G (Active A x F)}{β Q γ D L M s:ℝ}{J:ChartRatio G}{P:Patch}
open Forge Reine Rill
open Rill
structure Vista {g:Side}{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E](U:E→ Config G g)(x:E)(t C σ:ℝ)(A:Finset (Cell g))(n:ℕ)(q:Chi) (f n':ℝ): Prop where -- f' marker
 pot{k:ℕ}(hk:k≤4)(V:RG.Atom G k)(i:Site g): Allows n (lush_k q V A t i ∘ U) x (f*t^k*V.budget σ) ∧ ( (∀ l:Cell g,l∉A→ Pressure.toll (U x) l ≤ t) → Allows n (peer_k V A t i ∘ U) x (f*t^k*V.budget σ)) ∧ ∀ p: Clip,Allows n (sleeve V A p i t∘ U) x (f*V.budget σ)
lemma priceInk (n:ℕ)(C σ:ℝ)(hs:0<σ) :∃ D:ℝ,0≤D∧∀ i:ℕ, priceK n (rateN i) C ≤ D*Real.exp (σ*i):=by
 -- direct exp. pow ≤ n! * exp ; t_i linear. pad C.v.
 let p:ℝ:=2*50^4*Fintype.card PlaqAxes; let f:= (n.factorial:ℝ); let E:=Real.exp (n*C); let g:=σ/(1+p); let D:= f^2*E*g⁻¹^n*Real.exp σ
 have hh:0≤p:=by unfold p; positivity
 have hg:0<g:=by unfold g; positivity
 refine ⟨D,by unfold D; positivity,fun i=>?_⟩; let w(i:ℕ):ℝ:=1+(rateN i:ℝ); have hx:0 ≤ w i:=by unfold w; positivity
 have hy: g*w i ≤ σ+σ*i:=by
    unfold w rateN g; push_cast; have hw : p * i +p=2*(i+1:ℝ)*50^4*(Fintype.card PlaqAxes:ℝ):=by unfold p; ring -- tune coercion
    norm_num at hw; rw [←hw]; field_simp; nlinarith only [mul_nonneg hh (show 0≤(i:ℝ) by positivity),mul_nonneg hs.le (show 0 ≤ (i:ℝ) by positivity)]
 have ht : w i^n≤ f*g⁻¹^n*(Real.exp σ*Real.exp (σ*i)):=by
    rw [←Real.exp_add]; have h: (g*w i)^n/f ≤ Real.exp (σ+σ*i):=(Real.pow_div_factorial_le_exp _ (mul_nonneg hg.le hx) n).trans (Real.exp_monotone hy); have he:0<f:=by unfold f; positivity
    rw [div_le_iff₀ he,mul_pow] at h; rw [mul_right_comm,inv_pow,←div_eq_mul_inv,le_div_iff₀ (pow_pos hg _)]; linarith
    
 apply le_trans (mul_le_mul_of_nonneg_left ht (show 0 ≤ f*E by unfold f E; positivity)); unfold D; apply Eq.le; ring
end YM.CF.Cloak
