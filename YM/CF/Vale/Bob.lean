import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Pane.Null
import YM.CF.Vale.Oak
/-! A convenient bootstrap vacuum with a strict-admissibility-scale cutoff. Its gauge term is still plaquette-local (including the translation of its CP symmetrization). Finite-lattice choice; no claim on reflection positivity of the overlap weighting. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Vale
open Function Filter Lattice Laurent Bloch Wilson Precision RG Next.Free Work.F08 Craft Pressure Stationary Tree Reef Hom AnalyticBridge.LocalGaussianLaws MeasureTheory Finset Gauge
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.Frobenius Classical
local notation "G5"=> SU.group
open PhysicalNext.Repeat WilsonStartup
variable {n:Side}{e:ℝ}{K:Teller G5}{P:Patch}{R:ChartRatio G5}{W:Postal}
-- cost inChannels under mask
abbrev ren(B:Clip)(U:Config G5 n):= energy U - ∑ i:Pressure.Cell n, Design.bulk B*residual G5 i U
def basicP(B:Clip)(U:Config G5 n):= (ren B U + ren B (echo U))/2
lemma rename (p:Clip)(hp:p.direct ≤1)(V:Config G5 n):mainTerm p (Design.top G5 p) V=ren p V:=by
 let U:= Design.top G5 p
 have he(i:Signed): quadratic p U (pull i 0 V)+uncut U.cubic (pull i 0 V)+uncut U.quartic (pull i 0 V)= ren p (pull i 0 V):=by linarith only [Design.principal_top p (pull i 0 V) hp] -- abbrev
 have ht(i:Signed): ren p (pull i 0 V)=ren p V:=by
    unfold ren; rw [energy_pull V]; simp_rw [← residual_send]; congr 1; exact Equiv.sum_comp (Equiv.ofBijective _ ⟨Face.injective_send i (0:Site n), Finite.injective_iff_surjective.mp (Face.injective_send ..)⟩) (fun v:Pressure.Cell n=> Design.bulk p * residual G5 v V)
 unfold mainTerm; change Patch.average (fun s:Signed=> quadratic p U _ + uncut U.cubic _ + uncut U.quartic _)=_; simp_rw [he,ht]; simp only [Patch.average,sum_const,card_univ,nsmul_eq_mul,←mul_assoc,inv_mul_cancel₀ (show (↑(Fintype.card Signed):ℝ)≠0 by positivity),one_mul] -- tune
lemma plainB (p:Clip)(hp:p.direct ≤ 1)(q:BudgetPoint)(b:ℝ)(V:Config G5 n)(h:flags q.threshold V=∅): let T:=solvent (Design.top G5 p); T.inChannels p q b V=b*basicP p V:=by
 obtain ⟨C,hC,H⟩:= Design.bound_arbitrary p G5 hp 1 (by norm_num); let R:=Design.top G5 p; intro T; have ht : Precision.loop R V=0:=by
    unfold Precision.loop; have he(i:Signed): uncut R.loop (pull i 0 V)=0:=by unfold R Design.top uncut; simp [Atom.unmasked,Atom.poly, Design.extractAtom] -- tune
    simp_rw [he]; simp [Patch.average]
 rw [Pane.crystalline _ _ _ _ _ h,show T=solvent R from rfl,splits (H _ le_rfl _ (le_refl 0)),show Precision.loop (solvent R) V=0 from ht,add_zero,show mainTerm p R V=_ from rename p hp V,show mainTerm p R (echo V)=_ from rename p hp _]; rfl
end YM.CF.Vale
