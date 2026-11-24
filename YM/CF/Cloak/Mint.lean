import YM.CF.Cloak.Frame
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
open Vol Pressure.Tube
variable (S) (A:Stores S)(x w:ℝ)
def Mowed (U:Config G f)(V: Config G c):Prop:= (∀ i∉A.costs,Pressure.toll U i ≤ fiery G x S.patch.L/2)∧ A.flags=RG.flags (temp x) V
variable {S A x}
lemma mowed (M: Monk G S)(J:Tube G S)(p e s:ℝ)(q:Chi)(R:ChartRatio G)(l:ℕ)(p₀:M.key.flags=RG.flags (temp x) M.V)(h:ψ J x M q p l e R w s≠0)(ht:0<fiery G x S.patch.L) : Mowed S M.key x (M.sent x J q p l e) M.V :=by
 let a:=M.sent x J q p l e; have he:(∏ i:Cell f,tokenF M.key q x a i)≠0:= left_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul (right_ne_zero_of_mul h)))
 refine ⟨fun i g=>?_ ,p₀⟩; have hp:=Finset.prod_ne_zero_iff.mp he i (mem_univ i); apply ((profile_charged _ _ _ (by change 0<fiery G x S.patch.L/4; positivity) _ hp (SU.group.chord_nonneg _)).2 g).le.trans; change 2*(fiery G x S.patch.L/4) ≤ _; linarith
lemma mowed_f(Z:Signed)(p:Mowed S A x U V) (i:Cell f)(h:i∉(turnStore Z A).costs): Pressure.toll (pull Z 0 U) i ≤ fiery G x S.patch.L/2:= (show Pressure.toll (pull Z 0 U) i=Pressure.toll U (Face.send Z 0 i) from Face.send_price U i Z 0 SU.group.chord SU.group.chord_inv fun i k=>SU.group.chord_conj k i).trans_le (p.1 _ (mt (costs_turn ..).2 h))
lemma mowed_c(Z:Signed)(p:Mowed S A x U V)(i:Cell c)(h:i∉traceZ (turnStore Z A).flags): Pressure.toll (pull Z 0 V) i ≤ temp x:= by
 by_contra! t
 have hz:i.1∈(turnStore Z A).flags:=(flag_turn ..).2 (p.2.symm ▸ (exact_turn ..).1 ((flags_spec ..).mpr ⟨i,Work.E01.base_touched _,t⟩)); exact h (mem_filter.mpr ⟨mem_univ _,hz⟩)
lemma shipP (s:ℝ)(U:Config G f)(b:Finset (Cell f))(p:Clip)(i:Site f)(ht:0 ≤ s)(h:∀ x∉b,Pressure.toll U x ≤ s): PathData.kept p s i U ↔ pers b p s U i:= by
 apply Iff.symm (persR b p s U i ht ?_); intro j t; by_contra hz; apply t.not_ge; exact (h j hz).trans (le_mul_of_one_le_right ht (Real.one_le_exp (by have :=p.radius_pos; positivity)))
lemma dimX(V:Atom G r)(U:Config G f)(p:BudgetPoint)(i:Site f): (dimA V).placed p U i=0:=by unfold RG.Atom.placed; simp [RG.masked,dimU]
lemma exteriorL(k:ℕ)(P:ℕ→RG.Atom G r)(U: Config G f)(X:BudgetPoint) {σ C:ℝ}(p:0<σ)(hp:SumBudget (fun i=>(P i).budget σ) C)(i:Site f): PathData.atomSeries P X U i=PathData.atomSeries (haste k P) X U i+PathData.atomSeries (batch P k) X U i:=by
 have he(u): (P u).placed X U i=(haste k P u).placed X U i+(batch P k u).placed X U i:=by
    unfold Vol.batch Newt.haste Newt.farther; dsimp only; split <;> simp [dimX]
 unfold PathData.atomSeries; simp_rw [he]; apply Summable.tsum_add; exact (PathData.atom_dominated _ X i (half_pos p) (pastA P p hp k)).summable U; exact (PathData.atom_dominated _ X i p (barn hp k)).summable U
end YM.CF.Cloak
