import GaugeFieldConstruction.Ei
import GaugeFieldConstruction.Plush
import GaugeFieldConstruction.Uber
set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 140000
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
-- nongauge Hot support label
open Roots GJ Mew Wosk
open Tenant Push.AbsoluteSums Trees
open Sour Sour.SliceRoof
set_option maxHeartbeats 240000
variable (I:Type)[LinearOrder I][Fintype I]
open SeasonH
variable (σ:I→Seat n)(V:Support (More n))(A:Pane n) (M:I→ Boke n I)(F:Fork n I)(r:ℝ)(v:stabH F)
variable (t:Finset I)(e:Vulcan I n)(S:Hubber n)(Q:Boke n I)
-- raw Lattice supports.Z cut zeta
namespace MintB
open Fren
open Rue Py.Rate.Pitching.Focus.CoeffArc Py.Rate.Pitching.Focus
variable (P:BudgetPoint)(m:ℕ)(x:Scree.Hub n)
-- sum all.E representation
lemma Grant_Υ (p:CostP σ P Q)(v:buried Q):
 (∑ x:Scree.Hub n, entryS σ m P Q t x)=(∑ S:Hubber n,cacheS I σ t S Q):=by
 induction Q with
 | nil=> simp [entryS,cacheS,pre_g,skimQ,Lee]
 | cons i Q h=>
    let T:= (p i (List.mem_cons_self)); let U:= (v i List.mem_cons_self)
    simp_rw [show ∀ x,entryS σ m P (i::Q) t x=LexS σ i x m P t+entryS σ m P Q t x from fun _=>consA ..]; rw [sum_add_distrib,h (fun i t=>p i (List.mem_cons_of_mem _ t)) (fun i t=>v i (List.mem_cons_of_mem _ t))]; by_cases p:Incζ I σ t i
    · have he(Y:Hubber n):cacheS I σ t Y (i::Q)=(if Y=i.seat then PinInk i else 0)+cacheS I σ t Y Q:=by unfold cacheS pre_g skimQ; rw [List.filter_cons,if_pos (decide_eq_true p),List.filter_cons]; by_cases u:Y=i.seat; rw [if_pos (by simpa using u.symm),if_pos u]; exact consA ..; rw [if_neg u,if_neg (by simpa using Ne.symm u),zero_add]
      rw [Finset.sum_congr rfl (g:=fun Y=> (if Y=i.seat then PinInk i else 0)+cacheS I σ t Y Q) (fun Y h=>he Y)] -- rw finds which side? tune
      rw [sum_add_distrib, sum_ite_eq', if_pos (mem_univ _)]; apply congrArg (·+_); have hk:i.keys.toFinset=t:=p.1; have ht:(marksY σ i m P t).Nonempty:=hk ▸ fullΥ _ _ _ _ T p.2 U; unfold LexS; rw [← Finset.sum_filter,show univ.filter (fun v=>v∈marksY σ i m P t)=_ from filter_mem_eq_inter.trans (univ_inter _)] -- tune
      rw [sum_const, exp_Plate, ←Nat.cast_smul_eq_nsmul ℂ,smul_smul]; push_cast; rw [mul_inv_cancel₀ (by exact_mod_cast (ne_of_gt ht.card_pos)), one_smul] -- tune D.a
    simp_rw [Lex_blank I σ t i _ _ _ p]; simp only [sum_const_zero,zero_add]; unfold cacheS pre_g skimQ; simp [p]
def registerT (σ:I→Seat n)(L:ℕ)(P:BudgetPoint)(Q:Boke n I) :Key I→RegBudget n:=fun z=> WritV σ (entryS σ L P Q) z
lemma cash_D (V:Pane n)(h:∀ X, pingS P.threshold X V)(Q:Boke n I)(u:CostP σ P Q)(t:buried Q): Kin σ (fun z:Key I=> exponentL P (registerT I σ m P Q z) V) (disks I univ V Q):=by
 let F(S:Finset I):= ∑ x:Scree.Hub n,entryS σ m P Q S x V; let G:= Fluid σ F; have he:(fun z:Key I=> exponentL P (registerT I σ m P Q z) V) = G:=by
    funext z; simp_rw [exponentL,numbE]; simp_rw [Set.indicator_of_mem ((show ∀ X:Support (More n), V∈{U|pingS P.threshold X U} from fun X=>h X|> (fun x=>x)) _)]; -- cannot discharge h. tune
    unfold registerT G Fluid F WritV; simp_rw [Finset.sum_apply, Pi.smul_apply, smul_sum]; rw [sum_comm]
 rw [he]; refine ⟨(tip_bank _ _ (fun i _=>lift_b i (F i))).1,γRise_P _ _ _, fun i k=>?_⟩; rw [show tipI G i= _ from Fluid_p σ F k,Disk_version I σ _ V Q i k]; unfold F; rw [←Finset.sum_apply, Grant_Υ I σ _ Q P m u t,Finset.sum_apply]; simp -- tune Param order
#print axioms cash_D
end MintB
end MastTin
end YM.CF.XGarden
end
