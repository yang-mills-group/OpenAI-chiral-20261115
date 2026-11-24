import YM.CF.Sour.Calm
import GaugeFieldConstruction.Tellur
import GaugeFieldConstruction.Sunkist
set_option quotPrecheck false
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Rill
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
variable {c f:Side}{S:StepData c f}{r v l:ℕ}{w x β d:ℝ}{q:Chi}
open CF.Forge
open AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Matrix
local notation "G"=>SU.group
open Err
variable {M N:Monk G S}{e b w K t:ℝ} {U V:Config G c}{E F:Support c} {T:Tube G S}
open Cube Lat Tulip Peaks Fock Jet Branch Urn Levier Drapes Tenant
attribute [local instance] opCStarAlgebra
variable {N:Side}
set_option synthInstance.maxSize 20000
open Sour Vow
local notation "SS"=> More N
open Pressure
namespace CreekX
variable {H:Scree.Loom N}{t d:ℝ}{k:ℕ}{X S:Support (More N)}{P:RG.BudgetPoint}{D Z:Support (More N)}{U W: Skye.Orbit N}(u:Roof N t d k H)(p:P.threshold ≤ t)(hp:halo (cipherK k) D ⊆ X)(hg:halo (k+22) S⊆ X)
def sandQ (k:ℕ)(S D:Support (More N)):=halo (k+10) S ∪ halo (2*k+20) D
def nozzle (k:ℕ)(S D:Support (More N))(t:ℝ)(U:Pane N):Prop:=sandQ k S D∩RG.flags t U⊆D
include hp hg
lemma march : halo 12 (sandQ k S D) ⊆ X :=by
 intro y g; obtain ⟨x,T,q⟩:=halo_spec.mp g
 rcases Finset.mem_union.mp T with h|h
 · obtain ⟨j,r,v⟩:=halo_spec.mp h; exact hg (halo_spec.mpr ⟨j,r,le_trans (separation_triangle j x y) (by omega)⟩)
 exact hp (ql D k (halo_spec.mpr ⟨x,h,q⟩))
-- need include hp hg since p omitted by Lean
lemma march_1 : sandQ k S D⊆ X:=Subset.trans (halo_subset _ _) (march hp hg)
lemma trench_f (f:Agrees X U.1 W.1): nozzle k S D t U.1↔ nozzle k S D t W.1:=by
 have e:=flags_agree t U.1 W.1 (sandQ k S D) (agrees_mono f (Finset.coe_subset.mpr ((Yaw.touchK _).trans (march hp hg))))
 unfold nozzle; rw[e]
include u
lemma sailsZ (h:nozzle k S D t U.1)(v:nozzle k S D t W.1)(f:Agrees X U.1 W.1)(x:Set.EqOn U.2 W.2 X): Agrees S (H U) (H W):=by
 let Q:=halo (2*k+20) D; let T:=sandQ k S D
 have he:halo 12 Q ⊆ X:=Subset.trans (ql D k) hp; have hv: Q⊆ X:= (halo_subset 12 _).trans he
 have a:IceK H S T Q D k t:=⟨Finset.subset_union_left,Finset.subset_union_right,subset_rfl⟩
 have hQ:= blink u a h v (agrees_mono f (Finset.coe_subset.mpr he)) (fun i h=>x (hv h))
 intro j s l; have m:= hQ j s; split_ifs at m; exact m; exact m.1.trans ((f _ (hg (halo_subset _ _ s)) (hg (halo_subset _ _ l))).trans m.2.symm)
omit hp hg
lemma sailsEmpty (h:nozzle k S ∅ t U.1): Agrees S (H U) U.1:=by
 intro i q v; apply u.lamp
 apply Finset.disjoint_left.mpr; intro j p z; exact Finset.notMem_empty j (h (Finset.mem_inter.mpr ⟨Finset.mem_union_left _ (halo_spec.mpr ⟨_,q,(separation_comm ..).trans_le ((Atala.win_r z).trans (by omega))⟩),p⟩)) -- namespace
-- gauge & mirrors
omit u
lemma nozzle_meter : MeasurableSet {U:Orbit N|nozzle k S D t U.1}:=by
 apply measurable_fst (t:={A:Pane N|nozzle k S D t A})
 suffices e:{U:Pane N| nozzle k S D t U}= ⋃ Q:↥(Finset.univ.filter (fun Q:Support (More N)=>sandQ k S D ∩ Q⊆D)), {x:Pane N|RG.flags t x=Q.val} by rw[e]; exact MeasurableSet.iUnion (fun i=>RG.flags_measurable_eq t i.val)
 ext x; constructor
 · intro p; apply Set.mem_iUnion.mpr; exact ⟨⟨_,Finset.mem_filter.mpr ⟨Finset.mem_univ (RG.flags t x),p⟩⟩,rfl⟩
 intro v; obtain ⟨Q,h⟩:=Set.mem_iUnion.mp v; change nozzle k S D t x; unfold nozzle; rw [show RG.flags t x=Q.val from h]; exact (Finset.mem_filter.mp Q.property).2
lemma gz (g:Seat N→ SU.E):nozzle k S D t (Lattice.gauge g U.1)↔nozzle k S D t U.1:=by unfold nozzle; rw[gauge_flags]
include hp hg p
lemma payz (l: pingS P.threshold (X\D) U.1): nozzle k S D t U.1:= fun _ h=> debt U.1 _ _ _ _ p l (Finset.mem_inter.mpr ⟨march_1 hp hg (Finset.mem_inter.mp h).1,(Finset.mem_inter.mp h).2⟩) -- tune

local notation "Sz"=> fun i:tangD N=> ((pressQ P Z U.1 i,U.2):Orbit N)
variable (vZ:D⊆ Z)(pZ:cipherK k ≤5*P.B)(ht:3 ≤ P.B)
include u vZ pZ ht
lemma nozzle_port {e:Pressure.Bond SS}(he:e.1∈ S)(g:pingS P.threshold (X\D) U.1): (fun i:tangD N=>H (Sz i) e) =ᶠ[𝓝 0] fun i => pressQ P Z (H U) i e:=by
 let Q:=halo (2*k+20) D; let T:=sandQ k S D
 filter_upwards [Vow.tick (Y:=Z) g] with i t'
 let W':= Sz i; have hy:halo 12 Q ⊆ halo (5*P.B) D:= Subset.trans (ql D k) (Corona.halo_mono pZ le_rfl)
 have hl:= blink u (show IceK H S T Q D k t from ⟨Finset.subset_union_left,Finset.subset_union_right,subset_rfl⟩) (payz (U:=U) p hp hg g) (payz (U:=W') p hp hg t') (agrees_mono (Taxi.wakeV _ vZ i) (Finset.coe_subset.mpr hy)) (fun _ _=>rfl) e he
 split_ifs at hl with l
 · change H W' e= _; rw [← hl]; unfold pressQ gyrate Function.comp increment; rw [steadyB,if_neg ?_]; simp; intro h; apply Finset.disjoint_left.mp ((Finset.mem_filter.mp h).2) (Finset.mem_insert_self ..) (Corona.halo_mono ?_ vZ l); unfold cipherK at *; omega
 change H W' e=_; rw [hl.2]; change pressQ _ _ _ _ _=_; unfold pressQ gyrate Function.comp increment; rw [hl.1]
end CreekX
end YM.CF.Rill
