import YM.CF.Cloak.TintA
import YM.Further.ROOTED_INTERACTING_REMAINDER.Vault
import YM.CF.Cloak.Wear
import YM.CF.Cloak.Mint
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
open Vol Cay Slate
variable {l:ℕ}{M:Monk G S}{s':ℝ}
open Further.RootedInteractingRemainder Precision Next.SectorChange
variable (S) in
lemma sail_g (b:ℕ)(e:Bond c)(p W:ℝ)(U:Config G f)(V:Config G c)(A:Stores S)(he:A.flags= RG.flags p V)(h: e.1 ∉ A.dome b)(hQ: 0≤p)(hv:S.patch.Branches S.kernel G)(hu:∀ i:Bond f,separation e.1 (S.ratio.parent i.1)≤ predReach S.patch → ∃ u:SU.group.El,U i=u*replica S.ratio V i∧SU.group.chord u≤W)(hW:0≤W)(hp:2*(predReach S.patch+1)< c.val)(hx:predReach S.patch+1≤b) (k:S.Choices): let d:= (16:ℝ)*(2*((predReach S.patch+1:ℕ):ℝ)+1)^5*Fintype.card PlaqAxes*p; Pressure.wire (S.prediction U k) V e≤ d+ Vault.farePrice S.patch S.kernel*(4*(W+d)):=by
 intro d; obtain ⟨g,hg⟩:=Work.E08.axial_patch e.1 V (predReach S.patch) (predReach S.patch+1) le_rfl hp p hQ (fun y l i=>by
       by_contra! t; apply never_c h (show y∈ A.place from mem_union_right _ (he.symm ▸ (flags_spec ..).mpr ⟨(y,i),Work.E01.base_touched _,t⟩))|>.not_ge (l.trans hx))
 let X:= Lattice.gauge g V; let z:=constantGauge g S.ratio; let Z:= Lattice.gauge z U; let E(i:Bond f):Prop:= separation e.1 (S.ratio.parent i.1) ≤ predReach S.patch; let A'(i):= if E i then Z i else 1; have hd:0≤ d:=by unfold d; positivity
 have hh(i:Bond f)(t:E i): SU.group.chord (Z i)≤ W+d:=by
    obtain ⟨u,l,v⟩:=hu _ t; have he(Z):=SU.group.chord_triangle (z i.1*u*(z i.1)⁻¹) Z; let P:= replica S.ratio X; have hp:Z i=z i.1*u*(z i.1)⁻¹ * P i:=by
       unfold P X; rw [←copied S.ratio S.patch.odd_side]; unfold Z Lattice.gauge; rw [l]; unfold z; group
    rw [hp]; refine (he _).trans (add_le_add ((SU.group.chord_conj _ _).le.trans v) ?_); unfold P Precision.replica; split
    next => rw [SU.group.chord_one]; exact hd
    next => exact hg _ t
 have he(i): SU.group.chord (A' i)≤W+d:=by unfold A'; split; exact hh _ ‹_›; next x=>rw [SU.group.chord_one]; exact add_nonneg hW hd
 have hm:= Vault.prediction_good S A' k (4*(W+d)) (by positivity) (fun i _=> show SU.group.chord (A' i)≤ _ from (he _).trans (Eq.le ?_)) e -- tune
 · rw [←wire_gauge g]; have hp:S.prediction Z k= Lattice.gauge g (S.prediction U k):=by funext i; unfold Z; rw [Esti.gauge_t G S i hv]; simp [z,constantGauge,Lattice.gauge,S.ratio.embed_parent] -- tune unfold gauge too deep!
   unfold Pressure.wire; rw [←hp,prediction_near_eq hv Z A' k e (fun i v=> (if_pos (show E i from v)).symm)]; refine (SU.group.chord_triangle ..).trans (add_le_add (hg e (by simp)) ((SU.group.chord_inv _).le.trans hm)) -- tuning
 ring
lemma fieldP(T:Tube G S)(M:Monk G S)(i:Bond f)(a W:ℝ)(ht:0≤a)(ha:0≤W)(p:0<β)(h:S.ratio.parent i.1∉M.key.dome ((l+62)*radiusB x))(hd:1000≤radiusB x)(hp:∀ u:SU.group.Color,‖u‖≤a→SU.group.chord (SU.group.lieExp u)≤ W)(hg:∀ u:Active M.key x M.park,u.val.val=i→‖M.rich x T q d l β u‖ ≤ a): ∃ z:SU.group.El,M.sent x T q d l β i=z*replica S.ratio M.V i∧SU.group.chord z≤ W:=by
 by_cases t:i∈M.park.trunks
 · have hx: M.sent x T q d l β i=1:=M.park.on_tree _ ⟨i,t⟩; refine ⟨1,hx.trans ?_, SU.group.chord_one.le.trans ha⟩; rw [one_mul]; exact (if_pos (M.park.trunk_internal t)).symm
 let j:M.park.Free:=⟨i,t⟩; let u:Active M.key x M.park:=⟨j,?_⟩; swap
 · intro v; apply h; refine Atala.dome_u (Atala.driftK S i (d:=10*radiusB x) v) ?_; rw [separation_self]; simp_rw [Nat.add_mul]; omega
 exact ⟨_, clear_physical x M.key M.park M.V (M.bush x) (M.fuel x T q d l β) u,hp _ (hg _ rfl)⟩
end YM.CF.Cloak
