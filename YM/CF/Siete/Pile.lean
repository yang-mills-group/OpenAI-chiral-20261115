import YM.CF.Siete.Site
import YM.CF.Appel.Cube
import YM.CF.Neige.Walk
set_option autoImplicit false
noncomputable section
namespace YM.CF.Siete
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG PhysicalNext.JointLoad Heir Next.Foundations AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Precision Tree Push.SectorMeasure
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
variable {G:Gauge}{c f:Side}{P:Teller G}{S: StepData c f}{F: Forest S.ratio}{A:Stores S}{x d:ℝ}{X:Support f}{T:Tube G S}{Y:Support c}{I:Type}[Fintype I][DecidableEq I]
variable (T) (M:Museum F x A X Y I)(β:ℝ)(k:S.Choices)(q:Chi)(d:ℝ)(l:ℕ)(B:Config G f)(Z:LogArray G (Active A x F))
variable (g:Site c→G.El)
def traceU(V:Config G c): Prices G I:= (realP β T F A V k x l q d (Folio.leaf A F x B) Z-Offset.mean T x k A F q d (Folio.leaf A F x B) V) ∘ M.colorSeat G
abbrev recent(V:Config G c) : Config G f:= fieldU β T F A V k x l q d (Folio.leaf A F x B) Z
lemma recent_p (V:Config G c) : Agrees (inspected X) (recent T β k q d l B Z V) (M.received k T q d 1 V B (traceU T M β k q d l B Z V)) :=by
 intro i p u
 by_cases h:i∈F.trunks; · exact (F.on_tree _ ⟨i,h⟩).trans (F.on_tree _ ⟨i,h⟩).symm
 let a: Active A x F:= ⟨⟨i,h⟩, M.admits p u⟩
 obtain ⟨t,h⟩:= M.covers a p u; change F.drape _ a.val.val=F.drape _ a.val.val; rw [F.off_tree,F.off_tree]
 unfold Next.SectorChange.returned thaw; rw [freeze_regular,freeze_regular,release,release,Museum.deposited, ← h,M.seat.injective.extend_apply, one_smul]; congr 2; ext j; unfold traceU; simp -- tune
 change (_:ℝ)=_ + (_- _); exact (add_sub_cancel ..).symm
def atoms(V:Config G c): Directions G f:= M.extra g 1 (traceU T M β k q d l B Z V)
lemma obtain_s (b:Folio.Bulletin x P T) {p:Site c} (t:Museum.Station Y x p) (V:Config G c) (U:Directions G c)(h:AgreeNear id p (Heir.reach x) (Lattice.gauge g V) (increment 1 U))(i:Bond f)(hi:i.1∈ inspected X)(hx:i.1+step i.2∈ inspected X)(hs:separation p (S.ratio.parent i.1)≤7*(1+radiusB x))(sw:Bool): sounds T F x k sw (U,atoms T M β k q d l B Z g V) i=gauge (fun i=> G.lieExp (φ T F sw U i)) (gauge (g∘ S.ratio.parent) (recent T β k q d l B Z V)) i:=by
 -- rewrite via heard
 rw [atoms,M.heard g 1 b hi hx t hs sw _ _ h]; unfold Lattice.gauge; rw [recent_p T M β k q d l B Z V i hi hx]
end YM.CF.Siete
