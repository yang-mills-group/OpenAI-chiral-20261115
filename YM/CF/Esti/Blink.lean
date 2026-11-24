import YM.CF.Esti.Pal
import YM.CF.Vol.Celt
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Psalm.Baton
import YM.CF.Palot.End
import YM.CF.Appel.Sat
import YM.Next.FLUCTUATIONS.Grants
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Folio.Wind
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Esti
open Siete
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG PhysicalNext.JointLoad Heir Next.Foundations AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
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
lemma Lento.piece{f:ℝ→ℝ}(h:Lento f) (n:ℕ)(C:ℝ):Lento (Jet.composeCost n C ∘ f):=((Lento.sun _).times (((Lento.sun 1).plus h).power n)) -- tune
lemma Lento.sco{f:ℝ→ℝ}(h:Lento fun x=> (f x)⁻¹): Lento (fun x=>2/(f x)^2) :=by
 simp_rw [div_eq_mul_inv, ← inv_pow]; exact (Lento.sun _).times (h.power 2)
lemma Lento.ledge(P:Side)(v:ℝ):Lento (fun x=>(v*fiery G x P)⁻¹):=by simp_rw [mul_inv_rev]; exact (Lento.tuff P).times (Lento.sun _)
open Pressure.Stores
abbrev dusk(j:ℕ)(P:Patch):ℝ:=4*(footprint (j+125)*epoch P.L)
lemma dust(j:ℕ): (latticeFieldEstimates O j x:ℝ)=dusk j S.patch* O.shares * plow x^4:=by unfold dusk latticeFieldEstimates plow fulg; simp only [Nat.cast_mul,plot_rel]; push_cast; ring
lemma dusk_pos (P:Patch)(n:ℕ): 4 ≤ dusk n P:=by
 have hh : (1:ℝ)≤epoch P.L:=by exact_mod_cast (show 1 ≤ epoch P.L from by unfold epoch; omega)
 apply le_trans _ (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hh (footprint_pos _).le) (by norm_num : (0:ℝ) ≤ 4)); unfold footprint; nlinarith [pow_le_pow_left₀ (show (0:ℝ) ≤ 1 by norm_num) (show 1≤ 2*((n+125:ℕ):ℝ)+1 by linarith [Nat.cast_nonneg (α:=ℝ) (n+125)]) 4] -- tune natcast
lemma cardS (P:Patch)(d:ℝ→ℝ)(n:ℕ)(g:ℝ)(h:Lento d)(p:0<g): ∀ᶠ x in atTop, ∀{c f:Side}(S:StepData c f), S.patch=P →∀ O:Stores S, ∀ k:ℕ,k ≤ latticeFieldEstimates O n x→ |d x|^k ≤ Real.exp (g*(Scales.p G P.L x)^2*O.shares):=by
 filter_upwards [lentA P.L d h 4 g p (dusk n P) (by linarith [dusk_pos P n])] with x hx c f S p O k l; exact hx _ _ ((Nat.cast_le (α:=ℝ).mpr l).trans_eq ((dust n).trans (by rw [p]))) -- tune
end YM.CF.Esti
