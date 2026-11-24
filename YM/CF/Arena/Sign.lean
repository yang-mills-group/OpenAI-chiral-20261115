import YM.CF.Arena.Paid
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
variable {K:Teller G}
open AnalyticBridge.GaussianFieldAlignment Tensor Orthogonal PhysicalNext.OrderedAffine2B.SymRows Channels Locations
abbrev dial(S:StepData c f)(s:Signed)(b:Site c)(P:Tab S): Tab S:=⟨Locations.forest s b P.1,Channels.ticket s b P.2⟩
def clue(S:StepData c f)(s:Signed)(b:Site c)(A:Monk G S): Monk G S:=⟨book s b A.key,Locations.forest s b A.park,Channels.ticket s b A.k,pull s b A.V,pull s (S.ratio.embed b) A.U,Tensor.lifting (fiber s b A.V S) (diagram s b S) A.z⟩
section
variable (x:ℝ)(S:StepData c f)(s:Signed)(b:Site c)(A:Monk G S)
lemma gen : (clue S s b A).bush x=rollY s b x A.key A.park (A.bush x):= by funext i; change pull s (S.ratio.embed b) A.U i.val.val=_; rw [read_back]; rfl
lemma spike (a: Prices SU.group (Active A.key x A.park)): let F:=clue S s b A; let R:= calendar x A.key A.park s b; let U:= fiber s b A.V S; landed x F.key F.park F.V (F.bush x) (Orthogonal.move (onBond U) R.onKey a)=pull s (S.ratio.embed b) (landed x A.key A.park A.V (A.bush x) a):=by
 intro F R U; rw [show F.bush x= _ from gen x S s b A]; let Y:= A.bush x; let W:=rollY s b x A.key A.park Y; let c:=Orthogonal.move (onBond U) R.onKey a; let h(i):=F.U i; let H:= landed x A.key A.park A.V Y a; let K:= landed x F.key F.park F.V W c; change K=pull s (S.ratio.embed b) H; ext1 i
 let u:= sendEdge s (S.ratio.embed b) i; by_cases hx:i∈ F.park.trunks
 · have hv:u∈ A.park.trunks:= (trunk_map s b ..).mp hx -- tune
   rw [read_back,show K i=1 from F.park.on_tree _ ⟨i,hx⟩, show H (sendEdge s (S.ratio.embed b) i)=1 from A.park.on_tree _ ⟨u,hv⟩]; split <;> simp
 let v:F.park.Free:=⟨i,hx⟩; let q:= Locations.free s b A.park v; unfold K H; rw [read_back]
 change F.park.drape _ v.val= if s.flip i.2 then (A.park.drape _ q.val)⁻¹ else A.park.drape _ q.val; rw [F.park.off_tree,A.park.off_tree]; unfold Next.SectorChange.returned thaw; have hh':chill F.key x F.park v ↔ chill A.key x A.park q:= chill_map s b .. -- tune
 by_cases he:chill F.key x F.park v
 · let g: Frozen F.key x F.park:= ⟨v,he⟩; let K: Frozen A.key x A.park:=Locations.frozen s b A.key A.park x g; rw [show v=g.val from rfl, show q= K.val from rfl,freeze_held,freeze_held]; rfl
 let g:Active F.key x F.park:= ⟨v,he⟩; let D: Active A.key x A.park:= R.onKey g; rw [show v=g.val from rfl,show q=D.val from rfl,freeze_regular,freeze_regular]; let y:=tape a D; unfold release; have hp:tape c g= U i y:= move_tape .. -- tune
 change SU.group.lieExp (tape c g) * replica S.ratio F.V i=if s.flip i.2 then (SU.group.lieExp y * replica S.ratio A.V u)⁻¹ else SU.group.lieExp y * replica S.ratio A.V u; rw [hp,show replica S.ratio F.V= _ from Locations.replica_move (S:=S) s b A.V,Channels.read_back]; change SU.group.lieExp (Channels.scatter s (S.ratio.embed b) (replica S.ratio A.V) i y) * (if s.flip i.2 then ((replica S.ratio A.V) u)⁻¹ else _)= if s.flip i.2 then _ else _
 unfold Channels.scatter; split -- tune
 next t=> change SU.group.lieExp (-SU.group.adjoint ((replica S.ratio A.V u)⁻¹) y) * _=_; rw [SectorChange.exp_negative,SectorChange.exp_adjoint]; unfold u; group
 next t=> rfl
end
end YM.CF.Arena
