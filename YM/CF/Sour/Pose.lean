import YM.CF.Stax.Flow
import YM.CF.Salt.Ruin
import YM.CF.Taxi.Amp
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Sour
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
variable {n:Side}
local notation "SA"=> Seat n
local notation "VX"=> Aura n
local notation "Hk"=> hook SA
open Hake Jet Sault Stax
variable (P:BudgetPoint)(δ:ℕ)
abbrev Firing(n:Side):=Orbit n→FC (Dwell n)
abbrev σX (X:Aura n)(D:Support (More n)):= litres P.threshold X.val D
abbrev Slip (X:Aura n)(D:Support (More n)):= (pillar (G:=SU.group) X.val (open_l P.threshold X.val D)).choose
abbrev gloss(X:Aura n)(D:Support (More n))(V:Orbit n):Orbit n:=(Slip P X D V.1,V.2)
abbrev coll_T (X:Aura n)(D:Support (More n))(m:Firing n)(V:Orbit n):FC (Dwell n):=if Gates (σX P X D) X.val V.1 then m (gloss P X D V) else 0
local instance loreM (I:Type)[Fintype I][DecidableEq I]:MeasurableSpace (Op I):=borel _
local instance loreN(I:Type)[Fintype I][DecidableEq I]:BorelSpace (Op I):=⟨rfl⟩
structure Crate(X:Aura n)(D:Support (More n))(Y:Aura n)(m:Firing n):Prop where
 cog:Measurable m
 body:∀ V:Orbit n,Sector (camp Y.val) false (m V)
 same:∀ i j:Orbit n,i.1∈σX P X D → j.1 ∈ σX P X D→ Agrees X.val i.1 j.1→ Set.EqOn i.2 j.2 X.val →m i=m j
 gauge:∀ i:Orbit n,∀ t:Seat n→SU.E, i.1∈σX P X D → m (Lattice.gauge t i.1, threadG t i.2)=sauce false false (tradew n t) (m i)
local notation "SP" P:max X:max D:max=> σX P X D
local notation "Te" P:max X:max D:max m:max=> coll_T P X D m
namespace Crate
variable {P δ}{X Y Z:Aura n}{D:Support (More n)}{m:Firing n}(h:Crate P X D Y m)
include h
lemma lit(V:Orbit n):Sector (camp Y.val) false (coll_T P X D m V):=by unfold coll_T; split; exact h.body _; exact Sector.zero _
lemma virtue :Measurable (coll_T P X D m):=by
 have ht:=h.cog; unfold coll_T; apply Measurable.ite (measurable_fst ((year_s _ (open_l ..)).measurableSet)); exact ht.comp ((((pillar (G:=SU.group) X.val (open_l P.threshold X.val D)).choose_spec.1).comp measurable_fst).prodMk measurable_snd); exact measurable_const
lemma latch(V W:Orbit n)(r:Agrees X.val V.1 W.1)(p:Set.EqOn V.2 W.2 X.val) : coll_T P X D m V=coll_T P X D m W:=by
 let F:= SP P X D; have hv: Gates F X.val V.1↔Gates F X.val W.1:= ⟨fun ⟨i,q,u⟩=>⟨i,q,fun a t v=> (r _ t v).symm.trans (u a t v)⟩,fun ⟨i,q,u⟩=>⟨i,q,fun a t v=> (r _ t v).trans (u a t v)⟩⟩
 unfold coll_T; rw [hv]; split_ifs with x; swap; · rfl
 let A:=V.1; let B:= W.1; obtain ⟨hx,he⟩:=(pillar X.val (open_l (n:=n) P.threshold X.val D)).choose_spec.2 V.1; obtain ⟨ht,hv'⟩:=(pillar X.val (open_l (n:=n) P.threshold X.val D)).choose_spec.2 W.1 -- tune _
 exact h.same _ _ (he (hv.mpr x)) (hv' x) (fun a t v=> (hx a t v).symm.trans ((r _ t v).trans (ht a t v))) p
lemma pointV (V:Orbit n)(p: V.1 ∈ σX P X D):coll_T P X D m V=m V:=by
 have hφ:Gates (σX P X D) X.val V.1:=⟨_,p,fun _ _ _=>rfl⟩; rw [coll_T,if_pos hφ]; obtain ⟨w,v⟩:=(pillar X.val (open_l P.threshold X.val D)).choose_spec.2 V.1; exact (h.same _ (gloss P X D V) p (v hφ) w fun _ _=>rfl).symm
lemma tanG (V:Orbit n)(t:Seat n→ SU.E): coll_T P X D m (Lattice.gauge t V.1, threadG t V.2)= sauce false false (tradew n t) (coll_T P X D m V):=by
 by_cases u:Gates (σX P X D) X.val V.1; swap
 · unfold coll_T; rw [if_neg u,if_neg ?h,sauce,singT,win_z,map_zero]; case h=> exact mt (Salt.monk t P.threshold X.val D V.1).mp u
 obtain ⟨i,v,p⟩:=u; let U:Orbit n:=(i,V.2); let Z:= fun (U:Orbit n)=> ((Lattice.gauge t U.1, threadG t U.2):Orbit n)
 rw [h.latch V U p (fun _ _=>rfl), h.pointV U v, ←h.gauge U t v]; exact (h.latch (Z V) (Z U) (Skye.tied _ V.1 i t t p (fun _ _=>rfl)) (fun _ _=>rfl)).trans (h.pointV (Z U) ((Salt.glowF t P.threshold X.val D i).mpr v))
end Crate
abbrev Bag(n:Side):=Aura n→Firing n
abbrev Rail (h:ℝ)(r:Finset (Dwell n)):=h^r.card
local notation "Pn"=>More n
open Hake
structure Marque (P:BudgetPoint)(X Y: Aura n)(D:Support (More n))(m:Firing n)(h C:ℝ):Prop extends Crate P X D Y m where
 vet:∃ v:Finset (Dwell n)→Finset (Dwell n)→ℝ, (∀ i j,0 ≤ v i j)∧ (∀ j:Finset (Dwell n), (∑ i:Finset (Dwell n),Rail h i*v i j) ≤ C*Rail h j) ∧ ∀ V:Orbit n,V.1∈ σX P X D →∀ Z:Support (More n),D⊆Z→∀ i j:Finset (Dwell n),Pence P.order (fun y:tangD n=>m (pressQ P Z V.1 y,V.2) i j) 0 (v i j)
-- constructor loan.ops at Flag lower policy letter stamp; universal q.
end YM.CF.Sour
