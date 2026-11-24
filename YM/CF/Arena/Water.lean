import YM.CF.Arena.Vale
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Arena
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace Matrix Kronecker
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Push.Uniform (curve Slope tint partSpace meetVar)
open AnalyticBridge.Annulus1AD AnalyticBridge.SectorAffine Oriented Esti Vol Bloch Exterior Jet
open RG Forge Cay Slate Rel
local notation "G"=> SU.group
variable {c f:Side}{S:StepData c f}{T:Tube SU.group S}{F:Forest S.ratio}{q:Chi}{s:Signed}{l n:ℕ}{x d β C D σ m:ℝ}{P:Tab S}{V:Config SU.group c}
open Cube
section currents
variable {R p:ℕ}
abbrev DirP(c:Side):= Site c→Site c→ SpaceX G c
def dict(Q:DirP c)(i:Site c): SpaceX G c:= (∑ j,Q j i)-(∑ j,Q i j)
lemma dict_p (X Y:DirP c)(i:Site c):dict (X+Y) i=dict X i+dict Y i:=by unfold dict; simp only [Pi.add_apply,sum_add_distrib]; abel
lemma river {k:Site c}{F:SpaceX G c}(ht:Travel k n p R R σ C F)(hp:0<σ)(hk:p ≤ n):∃ M:DirP c,(∀ i j,M i j≠0→ separation i j≤ R)∧ (∀ i j,CakeF (M i j) i R n σ C ∧ cFoot p (satX (M i j))) ∧∀ i, Sean k F i= dict M i:=by
 obtain ⟨P,X,hX,hC,hS,H,hf⟩:=ht.profit; let M(i j:Site c):= stroll k i (P (i-j)); refine ⟨M,?_,?_,?_⟩
 · intro i j h; have hp:= hS (i-j) (fun v=>h (by unfold M; rw [v,zero_a])); rw [separation_comm, ← separation_translate j i (-j),add_neg_cancel]; simpa only [← sub_eq_add_neg] using hp -- tune should direction
 · intro i j; obtain ⟨hP,hQ,h⟩:=H (i-j); have hx:=tide k i hP; have h0:‖(0:InputZ G c)‖<σ:=by rw [norm_zero]; exact hp
   exact ⟨hx.under le_rfl le_rfl ((single_le_sum (fun i _=>hX i) (mem_univ _)).trans hC),prism_food k i h (((hP.ledger _ h0).order hk).smooth) (((hx.ledger _ h0).order hk).smooth)⟩
 intro i; rw [hf]; unfold dict M; rw [←Equiv.sum_comp (Equiv.addLeft i) (fun j=>stroll k j (P (j-i))), ← Equiv.sum_comp ((Equiv.neg _).trans (Equiv.addLeft i)) (fun j=>stroll k i (P (i-j)))]; simp only [Equiv.coe_addLeft,add_sub_cancel_left,add_sub_cancel_right,Equiv.trans_apply]; change stroll k i _= (∑ x,stroll k (i+x) (P x)) - ∑ x:Site c, stroll k i (P (i- (i+ -x))) -- tune signs
 have hh {f g:SpaceX G c}(i:Site c): stroll k i (f-g)=stroll k i f-stroll k i g:=funext fun a=> mul_sub ..
 rw [Rel.stint]; simp_rw [hh,sum_ride k _ (0:Salt c G)]; simp [Finset.sum_sub_distrib]
end currents
end YM.CF.Arena
