import YM.CF.Vow.Loge
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Vow
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
variable{n:Side} {P: BudgetPoint}{x y a b h c d:ℝ}{k m:ℕ}
local notation "DN"=>tangD n
local notation "E'"=>SU.group
variable {X D Y Z:Support (More n)}{U:Pane n}
local notation "Ink" n=> Hake.Raid (Dwell n)
-- mask interactions from Polar expenses: non-flag gas & erosion AND Omittance. use mined. canonical choose D unique local. β support shifts.
open Rue Trees Ursell
abbrev Cusp(n:Side):= Aura n→Support (More n)→ Copy n
variable (P:BudgetPoint){F:Pax n}(K U':Cusp n)(V:Orbit n)
abbrev hailV (D:Support (More n))(K:Cusp n)(V: Orbit n): Aura n→ Cipher n:= fun i=>K i (D∩ i.val) V
abbrev keyL (P: BudgetPoint)(K:Cusp n)(F:Pax n)(V:Orbit n): Aura n→ Cipher n:= fun i=> if Disjoint (flags P.threshold V.1) i.val then F i V else hailV (flags P.threshold V.1) K V i
abbrev gemB (D:Support (More n))(K U:Cusp n)(T:Finset (Palot.Duo (More n))) (H:Palot.Crowd (Site (More n))):Copy n:= fun V=>Palot.jewel D (hailV D K V) (hailV D U V) T H
abbrev lumpD (Q: Finset (Palot.Duo (More n))) (D:Support (More n))(S:Aura n):Prop:= beatB Q=beamH S.val∧ mine D Q -- implicit
lemma gear_v (D:Support (More n))(T:Finset (Palot.Duo (More n)))(S:Aura n):gemB D K U' T (beamH S.val)= if lumpD T D S then (∏ i∈ T.toLeft,K i (D∩i.val)) * ∏ i∈ T.toRight,U' i (D∩i.val) else 0:=by
 by_cases h:lumpD T D S; swap; · rw [if_neg h]; exact funext fun V=> if_neg h
 rw [if_pos h]; funext V; unfold gemB Palot.jewel; rw [if_pos h]; simp only [Pi.mul_apply,Finset.prod_apply]; let f:=hailV D K V; let w:= hailV D U' V
 have ht:= prod_disjSum T.toLeft T.toRight (Sum.elim f w); rw [Palot.joinP] at ht; exact ht
lemma gem_Z (D:Support (More n))(T:Finset (Palot.Duo (More n)))(H:Palot.Crowd (Site (More n))) : gemB D K U' T H V= jewel D (hailV D K V) (hailV D U' V) T H:=rfl
abbrev glowV(K U':Cusp n): Cusp n:=fun i D=> if D⊆ i.val then mintF (gemB D K U') (beamH i.val) else 0
variable(X:Aura n)
local notation "W_"=> flags P.threshold V.1
lemma sway_g (D:Support (More n))(x:Aura n)(i:Finset (Palot.Duo (More n)))(p:beatB i=beamH x.val) : mine D i ↔ mine (D∩x.val) i:=by
 let N:=x.val; have hq: Stilo.bay (beatB i)= N:= p ▸ bay_beam _; unfold Palot.mine; change _↔ _∧raisedH (D∩N) _∧_; rw [hq,inter_assoc, inter_self]; suffices h: raisedH (D∩N) i.toLeft ↔ raisedH D i.toLeft by rw [h]
 constructor
 · exact fun u j v p=> u j v (Disjoint.mono_right inter_subset_left p)
 intro u j v; have ht:= u j v; obtain ⟨k,h,i⟩:= not_disjoint_iff.mp ht; exact not_disjoint_iff.mpr ⟨_,h,mem_inter.mpr ⟨i,hq ▸ Palot.seam_b _ _ v h⟩⟩ -- tune stray ;
lemma gran_v (D:Support (More n))(T:Finset (Palot.Duo (More n)))(X:Aura n): gemB D K U' T (beamH X.val)=gemB (D∩X.val) K U' T (beamH X.val):=by
 by_cases h:beatB T=beamH X.val; swap; · funext V; unfold gemB Palot.jewel; rw [if_neg fun l=>h l.1,if_neg fun l=>h l.1]
 have ht:= Palot.rim_beat (T:=T); rw [h,bay_beam] at ht; have hu(i:Aura n)(v:i.val ⊆ X.val): (D∩X.val)∩i.val =D∩i.val:=by exact inter_assoc .. |>.trans (congrArg (D∩·) (inter_eq_right.mpr v))
 rw [gear_v,gear_v]; unfold lumpD; rw [sway_g D X T h]; split_ifs with k; swap; · rfl -- tune
 refine congrArg₂ (·*·) (prod_congr rfl ?_) (prod_congr rfl ?_) <;> intro i w
 rw [hu i fun a p=> ht ▸ mem_union_left _ (show a∈ robe T.toLeft from mem_biUnion.mpr ⟨_,w,p⟩)]
 rw [hu i fun a p=> ht ▸ mem_union_right _ (show a∈ robe T.toRight from mem_biUnion.mpr ⟨_,w,p⟩)]
lemma pulpit(D: Support (More n))(X:Aura n): glowV K U' X (D∩X.val) V= jack D (hailV D K V) (hailV D U' V) X:=by
 unfold glowV jack; rw [if_pos inter_subset_right]; unfold mintF; rw [Finset.sum_apply]; apply sum_congr rfl; intro i _; rw [←gran_v K U' D i X,gem_Z]
-- flag/D armor
structure ArmsK (P:BudgetPoint)(K:Cusp n)(Q:Aura n→Support (More n)→ℝ)(h:ℝ):Prop where
 price (i:Aura n)(D:Support (More n)):D.Nonempty→D⊆i.val→Medal P i.val D (K i D) h (Q i D)
 claim (i:Aura n)(D:Support (More n)):D.Nonempty→D⊆i.val→Firm P i.val D (K i D)
end YM.CF.Vow
