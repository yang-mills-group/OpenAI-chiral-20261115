import YM.CF.Atala.Bingo
import YM.CF.Hive.High
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Atala
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
variable {G:Gauge}{c f:Side}{S:StepData c f}{r v l:ℕ}{w x β d:ℝ}{q:Chi}{T:Tube G S}
open CF.Forge
open Cube Lat
attribute [local instance] opCStarAlgebra
variable (S){A:Stores S}{U V:Config SU.group f}{k:ℕ}{X: Finset (Hos S r)}{e:ℝ}
lemma view_g (i:Site f)(l:Lattice.Walk)(j p:Site f)(v:j∈visits i l)(x:p∈visits i l):separation j p ≤2*l.length:=by
 have h:= Shapes.visits_dist i j l v; have hp:=Shapes.visits_dist i p l x; have ht:= separation_triangle j i p; rw [separation_comm j i] at ht; omega
lemma safe_y (D:ℕ)(h:∀ i:Bond f,S.ratio.parent i.1∉A.dome D → V i=U i)(p:D+30 ≤ r)(w:X ⊆ blip S A r) (hp:Guard U e)(h₁:Guard V e):Guard (valve S U V X D) e:=by
 let q:=valve S U V X D
 have hu {t:Type}[DecidableEq t][Fintype t](B:SU.E→* UNI t)(v:PlaqBound B U e)(x:PlaqBound B V e): PlaqBound B q e:=by
    intro a i j k; let l:=square i j; let R:Support f:= (visits a l).toFinset; have hx:R=R:=rfl
    have hk(Y Z:Config SU.group f)(p:Agrees R Y Z): travel Y a (square i j)= travel Z a (square i j):= travel_local a _ _ _ (fun i h j=>p i (List.mem_toFinset.mpr h) (List.mem_toFinset.mpr j)) -- tune
    rcases virgin S A U V D h X w R (fun i f j g=>by have he:=view_g a l i j (List.mem_toFinset.mp f) (List.mem_toFinset.mp g); have hv:l.length=4:=rfl; omega) with g|g; rw [hk _ _ g]; exact v a i j k
    rw [hk _ _ g]; exact x a i j k
 exact ⟨hu _ hp.1 h₁.1,hu _ hp.2 h₁.2⟩
lemma valve_h(U V:Config G f)(x:ℕ): valve S U V (∅:Finset (Hos S r)) x=U:=by funext; simp [valve]
end YM.CF.Atala
