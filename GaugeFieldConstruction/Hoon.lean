import GaugeFieldConstruction.Aeaea
import YM.CF.Yaw.Viv
import GaugeFieldConstruction.Plaid
import GaugeFieldConstruction.Corbie
/- Gauge average phase extensions. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 320000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.XGarden
open Function Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG WilsonStartup Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical
open Buffered Buffered.Region FlightFlux Fluxim Work Tensor
open Fock Tulip Lat Spire Phase Cube Scroll Paige Vault Phase Spire Branch
open Push.SectorMeasure
attribute [local instance] opCStarAlgebra
variable {n:Side}
namespace MastTin
open Shield Echo Ledger Jet Salt Pastry Hake Urn Levier Hive Nacre Rush Peaks
local notation "GS"=>SU.group
open Next.SectorChange.Motion Ione
open TableF.Lenten TableF.Lenten.Housing TableF.Lenten.Layout
open Haro
open scoped YM.CF.Mew
variable {p:BudgetPoint} (o:Skye.Seat n)
-- nongauge Hot support label
open Roots GJ Mew Wosk
open Tenant Push.AbsoluteSums Trees
variable {P:BudgetPoint}{K J B I:Type}[LinearOrder I][Fintype I] {h:ℝ}
variable (σ:I→ Seat n)(e:Vulcan I n)(x:Scree.Hub n)
-- allocate average over roots in monomial, incl singleton.
def marksY (L:ℕ)(P:BudgetPoint)(T:Finset I) : Finset (Scree.Hub n):=Finset.univ.filter fun u=> T=e.keys.toFinset ∧ Roots.ψS σ e.keys ∧ u.val.2=SpacePad L P σ e ∧u.val.1 ∈ T.image σ
lemma issue_mono {L:ℕ}{T:Finset I}(U:Linca P σ e)(Y:x∈ marksY σ e L P T): e.seat⊆ x.val.2 ∧ x.val.1∈e.seat ∧ T.image σ ⊆ e.seat:=by
 obtain ⟨r,p,q,h⟩:= (mem_filter.mp Y).2; have hf:T.image σ ⊆e.seat:=by intro i w; obtain ⟨k,v,rfl⟩:=mem_image.mp w; rw [r,List.mem_toFinset] at v; exact U.stamp.port _ v
 rw [q]; exact ⟨subset_union_left,hf h,hf⟩
lemma fullΥ (L:ℕ)(P:BudgetPoint)(U:Linca P σ e)(h: ψS σ e.keys)(w:e.keys≠[]): (marksY σ e L P e.keys.toFinset).Nonempty:=by
 have hh: e.keys.toFinset.Nonempty:=by contrapose! w; cases u:e.keys; exact rfl; simp [u] at w
 obtain ⟨i,t⟩:=hh; let o:=σ i; let S:Scree.Hub n:=⟨(o,SpacePad L P σ e),mem_union_left _ (U.stamp.port i (List.mem_toFinset.mp t))⟩; exact ⟨S,mem_filter.mpr ⟨mem_univ _,rfl,h,rfl,mem_image_of_mem _ t⟩⟩
lemma fleet_Α {F:InkD n}{c:ℝ} (g:BitCost P x F h c)(v:ℂ): BitCost P x (v • F) h (‖v‖*c):=by -- bind
 obtain ⟨C,p,t,w⟩:=g.worth; refine ⟨fun i j u=> congrArg (v • ·) (g.term i j u),fun i=>(g.fit i).smul _, measurable_const.smul g.measureV,(fun i=> ‖v‖*C i),fun i=>mul_nonneg (norm_nonneg _) (p i),fun U p Z=>?_,?_⟩
 · let y:tangD n→ℂ:= fun i=> crumb (F (increment U i)).val Z
   change Signs P _ _ _; have he: (fun i:tangD n=> crumb ((v • F) (increment U i)).val Z)=v • y:=funext fun i=>crumb_scale ..
   rw [he]; exact Mew.grade_unit _ _ (t U p Z)
 rw [show (∑ i:Finset (Dwell n),tariff P x.val.1 h i*(‖v‖* C i))= _ from (show _= ‖v‖* (∑ i:Finset (Dwell n),tariff P x.val.1 h i*C i) from ?_)] -- tune
 exact mul_le_mul_of_nonneg_left w (norm_nonneg _)
 simp_rw [mul_left_comm (tariff _ _ _ _),←mul_sum]
variable (L:ℕ)(P:BudgetPoint)(T:Finset I)
local notation "cℓ"=> marksY σ e L P T
abbrev exp_Plate(S:Finset (Scree.Hub n)):ℝ:= (↑S.card : ℝ)⁻¹
def LexS: InkD n:= if x∈ cℓ then ((exp_Plate cℓ:ℝ):ℂ) • PinInk e else 0
abbrev waiveP (h:ℝ):=base_E e P h e.seat.card
def Lex_B (h:ℝ):ℝ:=if x∈ cℓ then exp_Plate cℓ*waiveP e P h else 0
#print Lex_B
lemma Lex_P (h:ℝ)(U:Linca P σ e): BitCost P x (LexS σ e x L P T) h (Lex_B σ e x L P T h):=by
 unfold LexS Lex_B; by_cases v:x∈ cℓ; swap; · simp_rw [if_neg v]; exact fee_blank
 rw [if_pos v,if_pos v]; let t:=issue_mono σ e x U v; have p:=fleet_Α x (fleeting (h:=h) σ e x U e.seat.card t.1 ?_) ((exp_Plate cℓ:ℝ):ℂ); rw [Complex.norm_real,Real.norm_of_nonneg (by unfold exp_Plate; positivity)] at p; exact p; exact fun i h=>halo_spec.mpr ⟨x.val.1,mem_singleton_self _,(U.grave.lim _ t.2.1 _ h).le⟩
def entryS (Q:Boke n I)(T:Finset I)(x:Scree.Hub n): InkD n:= Lee Q (fun e=>LexS σ e x L P T)
def entryW (Q:Boke n I)(h:ℝ)(T:Finset I)(x:Scree.Hub n): ℝ:=Lee Q fun e=>Lex_B σ e x L P T h
lemma entry_budget(Q:Boke n I)(h:ℝ)(v:CostP σ P Q): BitCost P x (entryS σ L P Q T x) h (entryW σ L P Q h T x):=by induction Q with | nil=>exact fee_blank | cons i L ih=> unfold entryS entryW; rw [consA,consA]; exact add_b (Lex_P _ _ _ _ _ _ _ (v _ List.mem_cons_self)) (ih fun j t=>v j (List.mem_cons_of_mem _ t))
end MastTin
end YM.CF.XGarden
end
