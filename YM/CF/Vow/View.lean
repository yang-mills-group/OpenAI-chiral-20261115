import YM.CF.Vow.Grow
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
open Rue Trees
variable {F G: Pax n}{K:Cusp n}{f g: Copy n}
variable (U: Orbit n)
def march (P:BudgetPoint) (o:Aura n)(f:Copy n)(U:Orbit n):= if pingS P.threshold o.val U.1 then f U else 0
abbrev paysS (Y:Aura n)(f:Copy n): Pax n:= Pi.single Y f
lemma emberT(p:BudgetPoint)(S:Aura n)(f:Copy n): coldE p (paysS S f) U=march p S f U:=by
 unfold coldE march paysS; rw [sum_filter]; rw [sum_eq_single S]; · rw [Pi.single_eq_same]
 · intro i _ g; rw [Pi.single_eq_of_ne g]; split <;> rfl
 simp
abbrev raceB (P:BudgetPoint)(x:Aura n): Set (Orbit n):={U|pingS P.threshold x.val U.1}
lemma march_f (s: FleetS P.threshold U.1)(x:Aura n)(F:Copy n) : march P x F U=if Disjoint (flags P.threshold U.1) x.val then F U else 0:=by
 unfold march; split_ifs with u v v <;> try rfl
 · exact False.elim (v (ping_le u).symm)
 exact False.elim (u ((shoreK _ _ s _).1 v.symm))
local notation "Ω"=> flags P.threshold U.1
-- purely regular shift on common scope.L. Two stencils not nested. define transfer sign birth +/- .
def flick(x:Aura n)(F:Copy n)(D:Support (More n)): Copy n:= if Disjoint D x.val then F else 0
abbrev chasmR(x:Aura n)(F: Support (More n)→ Copy n): Cusp n:= Pi.single x F
lemma shade_t (p:BudgetPoint)(x:Aura n)(F: Support (More n)→ Copy n) : fuelV p (chasmR x F) U= if fuelH (flags p.threshold U.1) x then F (flags p.threshold U.1∩x.val) U else 0:=by
 unfold fuelV; rw [sum_filter, sum_eq_single x]; · rw [chasmR, Pi.single_eq_same]
 · intro i _ t; unfold chasmR; rw [Pi.single_eq_of_ne t]; split <;> rfl
 simp
abbrev stroke(x y z:Aura n)(f g:Copy n):Cusp n:= chasmR z (fun t=> flick x f t-flick y g t)
lemma amends(x y z:Aura n)(p:x.val⊆z.val)(v:y.val⊆ z.val)(h: ∀ (u:Orbit n), pingS P.threshold z.val u.1 → f u=g u)(u: FleetS P.threshold U.1): march P y g U+fuelV P (stroke x y z f g) U=march P x f U:=by
 have hp(s: Aura n)(F: Copy n)(p:s.val⊆z.val):flick s F (Ω∩z.val) U=march P s F U:=by
    unfold flick; rw [march_f U u]; split_ifs with g v v; rfl
    · obtain ⟨i,x,y⟩:= Finset.not_disjoint_iff.mp v; exact False.elim (Finset.disjoint_left.mp g (mem_inter.mpr ⟨x,p y⟩) y)
    · exact False.elim (g (Disjoint.mono_left inter_subset_left v))
    rfl
 unfold stroke; rw [shade_t]; split
 · rw [Pi.sub_apply, hp x f p,hp y g v]; abel
 rename_i w; unfold fuelH at w; have ht:= (shoreK _ _ u _).mp (not_not.mp w); rw [march,if_pos (grow_b v ht),march,if_pos (grow_b p ht), add_zero]; exact (h _ ht).symm
lemma flick_M (x z:Aura n)(p:x.val⊆z.val)(t:0≤h)(v:Medal P x.val ∅ f h d) (D:Support (More n)):Medal P z.val D (flick x f D) h d:=by -- tune d
 unfold flick; split; rename_i q
 · apply v.stretchB p (empty_subset D); intro i w; simp only [sdiff_empty] at w; exact mem_sdiff.mpr ⟨p w,fun k=> Finset.disjoint_left.mp q k w⟩
 exact Medal.zeroT.big (v.wage t)
lemma prizes0 (n:Side) (P:BudgetPoint)(U:Orbit n): fuelV P 0 U=0:=by simp [fuelV]
lemma toast(k K':Cusp n): fuelV P (k+K') U= fuelV P k U + fuelV P K' U:=by simp [fuelV,sum_add_distrib]
lemma tunes {I:Type*}(V:I→ Cusp n)(i: Finset I): fuelV P (∑ j∈i,V j) U=∑ j∈i,fuelV P (V j) U:=by induction i using Finset.induction_on with | empty=> rw [sum_empty,sum_empty]; exact prizes0 n P U | insert i s t ih=> rw [sum_insert t,toast,ih,sum_insert t]
lemma migrate {I:Type*} (S:I→Aura n)(G:I→Support (More n) → Copy n)(N:Finset I)(w:I→ℝ)(p:D.Nonempty)(t:∀ i∈ N,∀ (D:Support (More n)),D.Nonempty→D⊆ (S i).val→ Medal P (S i).val D (G i D) h (w i))(x:Aura n)(v:D⊆x.val): Medal P x.val D ((∑ i∈N,chasmR (S i) (G i)) x D) h (∑ i∈ N, if S i=x then w i else 0):=by
 simp only [Finset.sum_apply]; apply Medal.sumP; intro i u; by_cases g:S i=x; · subst x; rw [if_pos rfl, chasmR,Pi.single_eq_same]; exact t i u D p v
 rw [if_neg g,chasmR,Pi.single_eq_of_ne (Ne.symm g)]; exact Medal.zeroT
-- irregular scalarβ source transfer: if arbitrary REAL law L.A uses unknown δtheta labels,$B shares
--  unconditionally on any V. use notation `Slab X D ηc` costs apply.
end YM.CF.Vow
