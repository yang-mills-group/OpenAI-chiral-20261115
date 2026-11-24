import GaugeFieldConstruction.Epis
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
abbrev bSalt (p:BudgetPoint)(j:ℕ):ℝ:=((1+(j:ℝ))^p.power*preFoot p j)
abbrev bagP (x:RankU n):Finset (Dwell n):= x.elim ∅ (fun u=>{u.1,u.2})
abbrev bagS (x:RankU n):ℂ:= x.elim 1 fun u=> parity u.1 ({u.2}:Finset (Dwell n))
abbrev uttR(x:RankU n):FC (FinV n):=(upperW x).val
abbrev disR(x:RankU n):Prop:=∀ i,x=some i→i.1≠ i.2
lemma FineVT (x:RankU n)(S:Support (More n))(h:∀i,x=some i→Ekm n i.1∈ S ∧Ekm n i.2∈S):Flour (camp S) (uttR x):=by
 rcases x with _|⟨b,i⟩; exact Flour.grainE; let P:=h _ rfl; exact Flour.putPut _ (mem_filter.mpr ⟨mem_univ _,P.1⟩) (mem_filter.mpr ⟨mem_univ _,P.2⟩)
lemma duoR (x:RankU n):‖bagS x‖=1:=by rcases x with _|v; exact norm_one; simp [bagS,parity]
lemma ticket_R (x:RankU n)(p:disR x): poke (bagP x)=bagS x • uttR x:=by
 rcases x with _|⟨i,j⟩; · simp only [bagS,Option.elim_none,one_smul]; exact Poly.tag_void _
 have he:i∉ ({j}:Finset (Dwell n)):=by simpa using p _ rfl -- tune projection
 exact (Poly.tag_any _ _ _ he).trans (by rw [Poly.tag_once]; rfl)
lemma chip_R(x:RankU n)(p:disR x)(y:Finset (Dwell n)): crumb (uttR x) y= if y=bagP x then (bagS x)⁻¹ else 0:=by
 have hp:bagS x≠0:=norm_ne_zero_iff.mp (by rw [duoR]; exact one_ne_zero)
 rw [show uttR x=(bagS x)⁻¹ • poke (bagP x) from (by rw [ticket_R x p,smul_smul,inv_mul_cancel₀ hp,one_smul]),crumb_scale,Pastry.chip]; split <;>simp
lemma chronos (U:Linca P σ e)(M:ℕ)(g:e.seat⊆ x.val.2)(p:e.seat ⊆ halo M ({x.val.1}:Support (More n)))(q:disR e.val):BitCost P x (PinInk e) h (tariff P x.val.1 h (bagP e.val)*(e.won*preFoot P M)):=by
 let S:=bagP e.val; let L:= e.won*preFoot P M; let T:= (U.stamp).micro; have he:0≤L:= mul_nonneg T.1 (by unfold preFoot; positivity)
 let H:=PinInk e
 refine ⟨fun i j v=>congrArg (· • upperW e.val) (T.2.2.1 _ _ (agrees_mono v g)),fun v=>(FineVT e.val x.val.2 fun i v=>⟨g (U.legs i.1 i.2 v).1,g (U.legs i.1 i.2 v).2⟩).smul _,T.2.1.meas.smul measurable_const, Pi.single S L,fun i=>by rw [Pi.single_apply]; split; exact he; exact le_rfl,fun A W r=> ?_,?_⟩
 · let z:tangD n→ℂ:=fun k=>crumb (PinInk e (increment A k)).val r; have ht(k:tangD n): z k=e.amt (increment A k)*crumb (uttR e.val) r:=crumb_scale ..; by_cases v:r=S
   · subst r; rw [Pi.single_eq_same]; let u:tangD n→ℂ:= e.amt∘ increment A; let a:=(bagS e.val)⁻¹; change Signs P x.val.1 z L; rw [show z=(a • u) from funext fun i=>by rw [ht i,chip_R e.val q S,if_pos rfl,mul_comm]; rfl]
     have hx: ‖a‖=1:=by rw [show a=(bagS e.val)⁻¹ from rfl,norm_inv,duoR]; simp
     have hu:pingS P.threshold e.seat A:=fun i w=> W i fun p=>w (disjoint_of_subset_left g p)
     have hg: Signs P x.val.1 u L:= halo_price x.val.1 _ T.2.2.1 (T.2.2.2 _ hu) p
     let ny:=Mew.grade_unit a _ hg; rw [hx,one_mul] at ny; exact ny
   change Signs _ _ z _; rw [Pi.single_eq_of_ne v,show z=fun _=>0 from funext fun i=> by rw [ht,chip_R _ q,if_neg v,mul_zero]]; exact Prism.hail norm_zero.le
 apply le_of_eq; rw [sum_eq_single S]; rw [Pi.single_eq_same]; intro i _ h; rw [Pi.single_eq_of_ne h,mul_zero]; simp
lemma tariff_R (x:RankU n)(o:Seat n)(p:BudgetPoint)(h:ℝ)(t:disR x)(m:ℕ)(u:∀ i,x=some i→ separation o (Ekm n i.1)≤ m ∧ separation o (Ekm n i.2) ≤ m):tariff p o h (bagP x)≤(1+(m:ℝ))^p.power*Lite h x:=by
 rcases x with _|⟨i,j⟩
 · change tariff p _ _ ∅≤ _*1; unfold Scree.tariff endL; simp; try exact one_le_pow₀ (le_add_of_nonneg_right (Nat.cast_nonneg _))
 let Q:=bagP (n:=n) (some (i,j)); have hv:i≠j:= t _ rfl
 have he:Q.card=2:=by simp [Q,bagP,hv] -- defeq tune
 have hx:endL o Q ≤ m:=by
    apply Finset.sup_le; intro l w; rcases mem_insert.mp w with rfl|g; exact (u _ rfl).1 -- tune
    rw [mem_singleton.mp g]; exact (u _ rfl).2
 change tariff p _ _ Q ≤ _; unfold Scree.tariff; rw [he]; exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (add_le_add_right (Nat.cast_le.mpr hx) _) _) (sq_nonneg _)
def base_E (a: Vulcan I n)(p:BudgetPoint)(h:ℝ)(m:ℕ):ℝ:= Lite h a.val*(a.won*bSalt p m)
lemma base0_E (P:BudgetPoint)(h:ℝ)(U:Linca P σ e)(m:ℕ):0≤ base_E e P h m:=mul_nonneg (costsE ..) (mul_nonneg U.stamp.micro.1 (by unfold bSalt preFoot; positivity))
lemma fleeting (U:Linca P σ e)(M:ℕ)(g:e.seat⊆x.val.2)(p:e.seat⊆halo M ({x.val.1}:Support (More n))):BitCost P x (PinInk e) h (base_E e P h M):=by
 by_cases q:disR e.val; swap
 · 
   have hx: upperW e.val=0:=by
      rcases he:e.val with _|⟨i,j⟩
      · exact False.elim (q (fun u g=>by rw [he] at g; contradiction))
      by_cases h:i=j; · subst j; exact Subtype.ext (put_sq i)
      refine False.elim (q ?_); intro u g; rw [he] at g; rw [←Option.some.inj g]; exact h
   rw [show PinInk e=0 from funext fun i=> by simp [PinInk,hx]]; exact bitΩ fee_blank (base0_E _ _ _ _ U M)
 apply bitΩ (chronos σ e x U M g p q)
 have ht: ∀ i, e.val=some i→ separation x.val.1 (Ekm n i.1)≤ M ∧ separation x.val.1 (Ekm n i.2) ≤ M:=by
    intro i q; have he:=U.legs i.1 i.2 q; have hx(y:Seat n)(u:y∈e.seat):separation x.val.1 y ≤ M:=by obtain ⟨i,s,v⟩:=halo_spec.mp (p u); rwa [mem_singleton.mp s] at v
    exact ⟨hx _ he.1,hx _ he.2⟩
 refine (mul_le_mul_of_nonneg_right (tariff_R e.val _ P h q M ht) (mul_nonneg U.stamp.micro.1 (by unfold preFoot; positivity))).trans_eq ?_; unfold base_E bSalt; ring
#print axioms fleeting
end MastTin
end YM.CF.XGarden
end
