import YM.CF.Sour.Breeze
import YM.CF.Sour.Penny
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
lemma debt (U:Pane N)(x t:ℝ)(X D:Support SS)(p:x ≤ t)(s:pingS x (X\D) U): X∩RG.flags t U ⊆ D:=by
 intro i l; by_contra h; obtain ⟨v,w⟩:=mem_inter.mp l; obtain ⟨j,g,k⟩:= (flags_spec ..).mp w; have he:= s j fun h'=>disjoint_left.mp h' (mem_sdiff.mpr ⟨v,h⟩) g; exact (not_lt_of_ge (he.trans_le p).le) k
abbrev cipherK(k:ℕ):=2*k+32
lemma ql(D:Support SS)(k:ℕ):halo 12 (halo (2*k+20) D) ⊆ halo (cipherK k) D:=by
 intro j t; obtain ⟨x,v,p⟩:=halo_spec.mp t; obtain ⟨y,u,q⟩:=halo_spec.mp v; exact halo_spec.mpr ⟨y,u,(separation_triangle y x j).trans (by unfold cipherK; omega)⟩
variable {H:Scree.Loom N}{t d:ℝ}{k:ℕ}{X:Vow.Aura N}{P:RG.BudgetPoint}{D Z:Support (More N)}{U W: Skye.Orbit N}(u:Roof N t d k H)(p:P.threshold ≤ t)(hp:halo (cipherK k) D ⊆ X.val)(g:U.1∈σX P X D)
variable (Y:Support (More N))(hg:halo (k+10) Y⊆ X.val)
local notation "Qx"=>halo (2*k+20) D
local notation "Lc"=>σX P X D
include u g p hp hg
lemma poli (v:W.1∈σX P X D)(f:Agrees X.val U.1 W.1)(x:Set.EqOn U.2 W.2 X.val): Agrees Y (H U) (H W):=by
 let Q:=halo (2*k+20) D; have he:halo 12 Q⊆X.val:=Subset.trans (ql D k) hp; have hv:Q⊆ X.val:= (halo_subset 12 _).trans he
 have hQ:= blink (E:=Y) u (show IceK H Y X.val Q D k t from ⟨hg,hv,subset_rfl⟩) (debt U.1 _ _ _ _ p g.1) (debt W.1 _ _ _ _ p v.1) (agrees_mono f (Finset.coe_subset.mpr he)) (fun i h=> x (hv h))
 intro j s t; have hm:= hQ j s; split_ifs at hm; exact hm; exact hm.1.trans ((f _ (hg (halo_subset _ _ s)) (hg (halo_subset _ _ t))).trans hm.2.symm)
omit g hp
lemma fern(V:Pane N)(v:V∈σX P X D)(i:Bond SS)(g:i.1∈Y)(l:D=∅)(τ:Ids N): H (V,τ) i= V i:=by
 apply u.lamp; refine disjoint_left.mpr fun j p' x=>?_ ; have hw: j∈X.val:= hg (halo_spec.mpr ⟨i.1,g,(separation_comm ..).trans_le ((Atala.win_r x).trans (by omega))⟩); exact notMem_empty j (l ▸ debt V _ _ _ _ p v.1 (mem_inter.mpr ⟨hw,p'⟩))
local notation "Sz"=> fun i:tangD N=> ((pressQ P Z U.1 i,U.2):Orbit N)
variable (vZ:D⊆ Z)(pZ:cipherK k ≤5*P.B)(ht:3 ≤ P.B)
include g vZ pZ ht hp
lemma portA {e: Pressure.Bond SS}(he:e.1∈Y) : (fun i:tangD N=>H (Sz i) e) =ᶠ[𝓝 0] fun i => pressQ P Z (H U) i e:=by
 let Q:=halo (2*k+20) D; have hx:Q⊆ X.val:= (halo_subset 12 _).trans (Subset.trans (ql D k) hp)
 filter_upwards [Vow.tick (Y:=Z) g.1] with i t
 let W' := Sz i; have hy:halo 12 Q ⊆ halo (5*P.B) D:= Subset.trans (ql D k) (Corona.halo_mono pZ le_rfl)
 have hl:= blink (E:=Y) u (show IceK H Y X.val Q D k _ from ⟨hg,hx,subset_rfl⟩) (debt U.1 _ _ _ _ p g.1) (debt W'.1 _ _ _ _ p t) (agrees_mono (Taxi.wakeV _ vZ i) (Finset.coe_subset.mpr hy)) (fun _ _=>rfl) e he
 split_ifs at hl with l
 · change H W' e= _; rw [← hl]; unfold pressQ gyrate Function.comp increment; rw [steadyB,if_neg ?_]; simp; intro h; apply disjoint_left.mp ((mem_filter.mp h).2) (mem_insert_self ..) (Corona.halo_mono ?_ vZ l); unfold cipherK at *; omega
 change H W' e=_; rw [hl.2]; change pressQ _ _ _ _ _=_; unfold pressQ gyrate Function.comp increment; rw [hl.1]
end YM.CF.Rill
