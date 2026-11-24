import YM.CF.Tarn.Loops
import YM.CF.Cloak.Seat
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
section orient
variable (T:Tube G S)(U:Config G f)(V:Config G c)(s:Signed)(A:Stores S)(q:Chi)(F W:BudgetPoint)(x α β:ℝ)
open Vol
local notation "u₀"=> pull s 0 U
local notation "V'"=> pull s 0 V
local notation "a₀"=> (turnStore s A).costs
local notation "t₀"=> F.threshold
local notation "r₀"=> Stores.till x
local notation "u"=>S.patch.L.val
local notation "H₀"=>r₀/u
local notation "s₀"=>W.threshold
local notation "Q₀"=>traceZ (turnStore s A).flags
variable {U V F W A x}{K:Teller G} (p:Mowed S A x U V)(hp:K.Funds S T)(hf: F.threshold=fiery G x S.patch.L)(h:W.threshold=temp x)(hu:0< F.threshold)
open Cay Slate Vol
include p
variable {q}
lemma flakeF (J:ℕ→RG.Atom G r)(y:Site f)(hv:(s.act (S.ratio.parent y))∉A.dome (taxM x))(pV:v ≤ Stores.till x)(hf:F.threshold=fiery G x S.patch.L) : PathData.atomSeries (batch J v) F u₀ y=gplot (batch J v) u₀ y:=by
 have hz:∀ i∈RG.flags F.threshold u₀,S.ratio.parent i∈(turnStore s A).place:=by
    rw [hf]; intro i t; obtain ⟨p',e,g⟩:= (RG.flags_spec ..).mp t
    have he:p'∈(turnStore s A).costs:=by
       by_contra h; apply g.not_ge; exact (mowed_f _ p _ h).trans (half_le_self (temp_nonneg _)) -- tune fiery
    exact (planted_owns ..).mpr ⟨Sum.inl (.inl p'),he, mem_image_of_mem _ e⟩
 have hQ:S.ratio.parent y∉ (turnStore s A).dome (v+10):=fun t=>hv ((dome_turn ..).1 (AnalyticBridge.Annulus1AD.farther (by unfold taxM; omega) t)) -- hv originally yaw change? tune
 refine tsum_congr fun i=> ?_; unfold batch; split
 next h=>
    apply masked_eq; apply Finset.disjoint_left.mpr; intro z w l
    have hh:=Push.AbsoluteSums.Paths.where_slot y (J i).leg z ((Push.AbsoluteSums.Paths.atom_foot y (J i)) ▸ w); apply Nat.not_lt_of_ge ?_ (never_c hQ (hz z l)); have he:= hh.trans h; have ht:= Work.E04.parent_separation S.ratio y z; omega
 simp only [dimX,dimU]
include hf h hu
lemma pearl_z (q:Chi)(i:Along S)(j:ℕ)(he:taxM x ≤ j*radiusB x)(ht:spanC T x)(v:i∈rush x A s j): heatR T U V s A q F W x α i=Tarn.TaleX T x α V' u₀ i:=by
 let D:= (turnStore s A); have hV: RG.flags s₀ V'⊆D.place:=by rw [h]; intro x t; exact mem_union_right _ ((flag_turn ..).mpr (p.2.symm ▸ (exact_turn ..).1 t))
 have hv:= (mem_filter.mp v).2; rcases i with (i|i|i|i)|i|i
 · rfl
 · rfl
 · change s.act i.1∉_ at hv; have hx:i.1∉D.dome (radiusB x):=fun t=>hv ((dome_turn ..).1 (AnalyticBridge.Annulus1AD.farther (by unfold taxM at he; omega) t))
   refine congrArg (-α *·) ?_; rw [stilt T s p h]; have hx' :0≤ s₀:= h.symm ▸ temp_nonneg _
   have hP: king ∅ T.down T.low r₀ S.patch.L.val s₀ V' i=crown T.down T.low r₀ S.patch.L.val s₀ V' i:=crownK _ _ _ _ _ _ _ _ hx' (supplies_n _ _ _ hx' (h.symm ▸ ht) _ _ fun _ t=> never_c hx (hV t)) (Or.inr (reign hV i fun v=>hx (halo_subset _ _ v)))
   apply hP.symm.trans; exact (kin_q _ S.patch.L.property _ _ _ _ _).trans (kin_q _ S.patch.L.property _ _ _ _ _).symm
 · rfl
 · rw [heatR, spice s q p hf hu]; change _=gplot _ _ _; exact flakeF s p _ _ (fun v=>hv (AnalyticBridge.Annulus1AD.farther he v)) le_rfl hf -- tune args
 change -visit _ _ _ _ _ i = - gplot _ V' i; rw [spliceV s p h]; congr 1
 let B:=T.down.loop; change PathData.atomSeries (batch B H₀) W V' i=gplot _ _ _; refine tsum_congr fun j=>?_; unfold batch; split
 next h=>
    have ht: i∉D.dome r₀:=fun v'=>hv ((dome_turn ..).mp (AnalyticBridge.Annulus1AD.farther (by unfold taxM at he; omega) v'))
    apply masked_eq; apply Finset.disjoint_left.mpr; intro a v g
    have he:separation i a≤ r₀:= (Push.AbsoluteSums.Paths.where_slot i (B j).leg a ((Push.AbsoluteSums.Paths.atom_foot i (B j)) ▸ v)).trans (h.trans (Nat.div_le_self ..)); exact (never_c ht (hV g)).not_ge he
 simp only [dimX,dimU]
end orient
end YM.CF.Cloak
