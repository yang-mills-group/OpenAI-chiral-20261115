import YM.SU5.Interaction.Kerosene.KernelBond
set_option autoImplicit false
set_option maxHeartbeats 700000
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
open Stax Larch Bake Ione Mew Cadre Rive
variable {I:Type}[Fintype I][LinearOrder I](F: Mew.Key I→ Cusp n)(s: I→ Seat n)(K:Mew.Key I→ Rinse (Seat n) (Copy n))
open Palot
-- Rune Key Hush at lit and ALL tag requests for outputs, River; don't need asym certificates here.
structure CoalKey (s:I→Seat n)(F:Mew.Key I→ Cusp n) : Prop where
 hush(X:Aura n) (D:Support (More n)):D⊆ X.val→ Hush s X.val (fun z:Key I=>F z X D)
 clean (z): z∈hill I → Turf (fun i:Aura n=> F z i ∅)
 money (X:Aura n)(D:Support (More n)): D⊆ X.val→∀ y, River fun z:Key I=> F z X D y
structure Riches (s:I→Seat n)(K:Mew.Key I→ Rinse (Seat n) (Copy n)) : Prop where
 clean (z): z∈hill I→∀ (X Y:Aura n),Y.val⊆X.val→∀ F: Copy n,(∀ (V:Orbit n)(U: Ids n),F V=F (V.1,U))→∀ (V:Orbit n)(U:Ids n), K z X ∅ Y F V=K z X ∅ Y F (V.1,U)
 money(X Y:Aura n)(D: Support (More n)):D⊆X.val→ Y.val⊆ X.val→ ∀ Q: Mew.Key I→ Copy n, (∀ V:Orbit n,River fun z=> Q z V)→ ∀ (V:Orbit n),River fun z=> K z X D Y (Q z) V
 poise(X Y:Aura n)(D: Support (More n)):D⊆X.val→ Y.val⊆ X.val→ Hush s X.val (fun z:Key I=> K z X D Y)
variable (g:Riches s K)(u: CoalKey s F)
abbrev damp (K:Cusp n):= fun i:Aura n=> K i ∅
include g u
lemma coalSurf : CoalKey s fun z:Key I=> volta (K z) (F z) :=by
 let R:= fun i:Key I=> Stoke (K i) (F i); let v(X Y:Aura n)(D:Support (More n))(G:hook (Seat n))(z:Key I):= K z X D Y (∏ j∈G,F z j (D∩j.val)); let VoltaR (z):=volta (K z) (F z)
 have hh(X:Aura n)(D:Support (More n))(i): VoltaR i X D= F i X D+∑ Y:Aura n,∑ G∈drum X Y D,v X Y D G i:= rfl
 refine ⟨?_,fun z p X V H=> ?_,?_⟩
 · intro X D d i u₁ j u₂ hp; exact congrArg₂ (·+·) (u.hush X D d i u₁ j u₂ hp) (show Stoke (K i) (F i) X D=Stoke (K j) (F j) X D from by
     unfold Stoke; refine sum_congr rfl fun Y _=>sum_congr rfl fun G e=>?_ ; let f:= (drum_p ..|>.mp e).2.2; rw [show K i X D Y=K j X D Y from g.poise _ _ _ d (f ▸ subset_union_left) i u₁ j u₂ hp]; apply congrArg; exact prod_congr rfl fun l z=> u.hush _ _ inter_subset_right i u₁ j u₂ (fun k w=> hp k (f ▸ (subset_union_right (coneL z w))))) -- unfold Stoke may fail Expected elaboration
 · change VoltaR z X ∅ V=VoltaR z X ∅ (V.1,H); rw [hh,Pi.add_apply,Pi.add_apply,show F z X ∅ V=_ from u.clean z p X V H, Finset.sum_apply,Finset.sum_apply]; apply congrArg (fun x:Cipher n=>F z X ∅ (V.1,H)+x); refine sum_congr rfl fun Y _=>?_ ; rw [Finset.sum_apply,Finset.sum_apply]; apply sum_congr rfl; intro i v'; refine g.clean z p X Y ((drum_p ..|>.mp v').2.2 ▸ subset_union_left) _ (fun V H=>?_ ) V H; rw [Finset.prod_apply, Finset.prod_apply]; apply prod_congr rfl; intro i _; rw [empty_inter]; exact u.clean z p i V H
 intro X D h V; change River fun z:Key I=> VoltaR z X D V; simp_rw [hh,Pi.add_apply,Finset.sum_apply]; refine dub_V (u.money X D h V) (tick_sum _ _ (fun Y _=> tick_sum _ _ (fun G giv=>?_))); refine g.money X Y D h ((drum_p ..|>.mp giv).2.2 ▸ subset_union_left) (fun z:Key I=>∏ j∈G,F z j (D∩j.val)) (fun V=>?_ ) V; simp_rw [Finset.prod_apply]; exact cost_R _ _ (fun i _=> u.money i _ inter_subset_right V)
omit g
variable {J:Type*}(b0:List J)(U:J→ Mew.Key I→ Rinse (Seat n) (Copy n))(p:∀ i∈ b0,Riches s (U i))
include p
lemma coalWood : CoalKey s fun z:Key I=> woodBar (fun i:J=>U i z) b0 (F z) := by
 induction b0 generalizing F with
 | nil=> exact u
 | cons i j ih=> exact ih (fun z:Key I=>volta (U i z) (F z)) (coalSurf F s (U i) (p i (by simp)) u) (fun i v=>p i (List.mem_cons_of_mem _ v))
omit p
variable (Γ L:ℝ)(q:0 ≤ L)(t:0 < Γ)(w:0<d)(pQ:degreePrice P.B Γ d <1)(hp:1 ≤ h)(C:Key I→ Tape (A:=Seat n))(r:∀ i∈hill I,Reservoir h d m P (F i) (C i) Γ L) (T0:Ids n)
include q t w pQ hp r
lemma coalRoad :
 (∀ i:Aura n,Hush s i.val (fun z=>clearZone P (F z) i)) ∧(∀ i:Aura n,∀ v:Orbit n,River (fun z=> clearZone P (F z) i v)) ∧(∀ i:Scree.Hub n,Hush s i.val.2 (fun z=>cast_E (clearZone P (F z)) T0 i))∧(∀ i:Scree.Hub n,∀ v,River (fun z=>cast_E (clearZone P (F z)) T0 i v))∧(∀ i:Force n,Hush s i.val.1.val.2 (fun z=>budgetR (clearWarp P (F z)) i))∧ ∀ i:Force n,∀ v,River (fun z=>budgetR (clearWarp P (F z)) i v):=by
 let Q(z:Key I):=damp (F z)
 have hF(i:Aura n): Hush s i.val (fun z=>clearZone P (F z) i):= lore_H Q P s (fun i=>u.hush i ∅ (empty_subset _)) i
 have hr j (k:j∈hill I):= ΩRank _ (C j) L Γ (r j k) w q t pQ hp
 have hu(i:Aura n)(v): River (fun z=> clearZone P (F z) i v):= lore_Y Q P hp (fun i v=>u.money i ∅ (empty_subset _) v) (fun z=> (fun i=>C z i ∅)) (add_nonneg q w.le) hr (fun i z j=> ((r i z).frame j ∅ (empty_subset _)).merit) ((ready_pos _ _ (hr 0 roots)).le) pQ i v
 refine ⟨hF,hu,fun i z t b l v=> ?_,fun i v=> ?_,fun i z t b l v=> ?_,fun i v=> ?_⟩
 · exact congrArg (fun v: Copy n=> bassH (lagE i) • fun x:Pane n=> v (x,T0)) (hF (lagE i) z t b l v)
 · exact bScale _ (hu (lagE i) (v,T0)) (bassH (lagE i))
 · exact congrArg (fun v:Copy n=> bassH _ • v) (moto_H (P:=P) F (fun _=>0) s u.hush (fun _ _ _ _ _ _ _ _=>rfl) (lordD i) (extraD i) z t b l v)
 exact bScale _ (moto_R P F (fun _=>0) u.money (fun _ _ _ _=>zeroR _) hu _ _ _) (bassH _)
end YM.CF.Vow
#print axioms YM.CF.Vow.coalRoad
