import GaugeFieldConstruction.Bayon
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
open Roots Mew Wosk
abbrev FinV(n:Side):= LeanV (Single n)
abbrev Ekm(n:Side)(i:FinV n):Seat n:= aptK i.2
abbrev LoreM(n:Side)(I G:Type):= Lem I (Seat n) G (Pane n)
abbrev Boke(n:Side)(I:Type):= Book0 I (Seat n) (FinV n) (Pane n)
variable {I G A B:Type}[LinearOrder I][Fintype I]
variable (ι:I→Seat n)(P:BudgetPoint)
variable (e:LoreM n I G)
structure Kingf (p:BudgetPoint) (ι:I→Seat n) (g:LoreM n I G) : Prop where
  micro : Micro p g.seat g.amt g.won
  port :∀ i∈ g.keys,ι i∈ g.seat
abbrev Γ0 (p:BudgetPoint):ℝ:=2^p.order
lemma micro_mc {S:Hubber n}{t u: Pane n→ℂ}{c d:ℝ}(p:Micro P S t c)(q:Micro P S u d):Micro P S (t*u) (Γ0 P*c*d):=by
 let L:=ContinuousLinearMap.mul ℝ ℂ; refine ⟨mul_nonneg (mul_nonneg (by unfold Γ0; positivity) p.1) q.1,?_,fun x y v=>congrArg₂ (· * ·) (p.2.2.1 _ _ v) (q.2.2.1 _ _ v),fun i t=>?_⟩
 · obtain ⟨C,g⟩:= p.2.1.cost; obtain ⟨D,h⟩:= q.2.1.cost; exact ⟨p.2.1.meas.mul q.2.1.meas,C*D,fun i=>(norm_mul_le ..).trans (mul_le_mul (g i) (h i) (norm_nonneg _) ((norm_nonneg _).trans (g i)))⟩
 have he:=(p.2.2.2 i t).bilinear L (q.2.2.2 i t) (ContinuousLinearMap.opNorm_mul_le ..); rw [mul_one] at he; exact he -- tune
lemma scene_W (g:LoreM n I B)(h:Kingf P ι e)(p:Kingf P ι g)(i:A): Kingf P ι (joint e g (Γ0 P) i):= ⟨micro_mc P (micro_spin h.micro subset_union_left) (micro_spin p.micro subset_union_right),fun i t=> (List.mem_append.mp t).elim (fun t=>Finset.mem_union_left _ (h.port _ t)) (fun k=> Finset.mem_union_right _ (p.port _ k))⟩ -- V' undefined
lemma mer_k (h:Kingf P ι e): Kingf P ι (merP e):=by
 refine ⟨?_, h.port⟩; have hp:= micro_ms h.micro (-1:ℂ); rw [norm_neg,norm_one,one_mul,neg_one_smul] at hp; exact hp
lemma leaf_k (i:G):Kingf P ι (leaf (B:=Pane n) i):=by
 refine ⟨⟨zero_le_one,Env.compact continuous_const,fun _ _ _=>rfl,fun j p=> allows_const _ (Eq.le (show ‖(1:ℂ)‖=1 from norm_one))⟩,fun i t=>?_⟩; simp [leaf] at t -- tune
structure Linca (P:BudgetPoint)(ι:I→Seat n)(e:LoreM n I (Option (FinV n × FinV n))):Prop where
 stamp : Kingf P ι e
 legs : puffQ (Ekm n) e
 grave : Grove (Tenant.terr _) e.seat

-- strong radial stamp incl empty support.Footprint connectivity.
abbrev Fork (n:Side)(I:Type):= FinV n→ FinV n→Toil I (Seat n) (Pane n)
structure Fort (P:BudgetPoint)(F:Fork n I):Prop where
  size : stabH F
  mist : darkH F
  day :∀ i j,∀ v∈ F i j,Micro P v.seat v.amt v.won ∧Grove (Tenant.terr _) v.seat ∧ Ekm n i ∈ v.seat ∧ Ekm n j∈ v.seat
abbrev Subter (i:FinV n)(g:LoreM n I (FinV n)):= Kingf P ι g∧ (g=leaf i ∨ Ekm n i ∈ g.seat ∧ Ekm n g.val∈ g.seat ∧ Grove (Tenant.terr _) g.seat)
def CostP (B:Boke n I): Prop:=∀ e∈ B,Linca P ι e
variable (F: Fork n I)(Q: Boke n I)(u: Fort P F)(z:CostP ι P Q)
local notation "Kℓ"=>Γ0 P
local notation "Φ"=>Ekm n
local notation "Geo"=>Grove (Tenant.terr (More n))
include u
lemma κFoam (i j:FinV n)(v:Lem I (Seat n) Unit (Pane n))(t:v∈ F i j):Kingf P ι v:=⟨(u.day i j v t).1, by rw [u.size i j v t]; simp⟩
lemma feasibility (i:FinV n)(v:Lem I (Seat n) (Option (FinV n×FinV n)) (Pane n))(p:Linca P ι v)(e: LoreM n I (FinV n))(w:e∈ feint F Kℓ i v): Subter ι P i e:=by
 unfold feint at w; cases g:v.val with
 | none=>simp [g] at w
 | some j=>
    obtain ⟨j,k⟩:= j; have hp:= p.legs _ _ g; simp only [g,Option.elim_some,List.mem_append,List.mem_map] at w; cases w with
    | inl w=> obtain ⟨q,h,rfl⟩:=w; let Tη:= (u.day i j q h).2; exact ⟨scene_W ι P v q p.stamp (κFoam ι P F u i j q h) k,Or.inr ⟨Finset.mem_union_right _ Tη.2.1,Finset.mem_union_left _ hp.2,p.grave.unite Tη.1 hp.1 Tη.2.2⟩⟩
    | inr w=> obtain ⟨q,h,rfl⟩:=w; let Tη:= (u.day i k q h).2; exact ⟨mer_k ι P (joint v q Kℓ j) (scene_W _ _ _ _ p.stamp (κFoam ι P F u i k q h) j), Or.inr ⟨Finset.mem_union_right _ Tη.2.1,Finset.mem_union_left _ hp.1,p.grave.unite Tη.1 hp.2 Tη.2.2⟩⟩
include z
lemma ΘMeter (i:FinV n)(e)(v:e∈ frond F Kℓ Q i):Subter ι P i e:=by
 obtain v|v:=List.mem_cons.mp v
 · subst e; exact ⟨leaf_k ι P i,Or.inl rfl⟩
 obtain ⟨i,u',w⟩:=List.mem_flatMap.mp v; exact feasibility _ _ F u _ _ (z _ u') _ w
lemma Fiscal(e:LoreM n I (Option (FinV n× FinV n)))(g:Linca P ι e): CostP ι P (growL F Kℓ Q e):=by
 intro v t; unfold growL at t; cases C:e.val with
 | none=> rw [C] at t; exact List.mem_singleton.mp t ▸ g
 | some X=>
    obtain ⟨i,j⟩:=X; rw [C] at t; obtain ⟨k,q',rfl⟩:=List.mem_map.mp t; have he:=g.legs i j C
    rcases List.mem_append.mp q' with h|h
    · obtain ⟨b,vb,V⟩:=List.mem_flatMap.mp h; obtain ⟨w,w₀,rfl⟩:=List.mem_map.mp V
      have hx:=ΘMeter _ _ F Q u z i b vb; have hh:= ΘMeter _ _ F Q u z j w w₀
      refine ⟨scene_W _ _ _ _ g.stamp (scene_W _ _ _ _ hx.1 hh.1 _) _,?_,?_⟩
      · intro k l q
        change some (b.val,w.val)=_ at q; obtain ⟨rfl,rfl⟩:=Prod.mk.inj (Option.some.inj q); exact ⟨hx.2.elim (fun v=>Finset.mem_union_left _ (by rw [v]; exact he.1)) (fun w=> Finset.mem_union_right _ (Finset.mem_union_left _ w.2.1)),hh.2.elim (fun v=> Finset.mem_union_left _ (by rw [v]; exact he.2)) (fun v=> Finset.mem_union_right _ (Finset.mem_union_right _ v.2.1))⟩
      change Geo (e.seat ∪ (b.seat∪ w.seat)); rw [←Finset.union_assoc]; have hp: Geo (e.seat∪ b.seat):=by rcases hx.2 with H|H; rw [H,show (leaf (I:=I) (J:=Seat n) (B:=Pane n) i).seat=∅ from rfl, Finset.union_empty]; exact g.grave; exact g.grave.unite H.2.2 he.1 H.1
      rcases hh.2 with H|H
      · rw [H,show (leaf (I:=I) (J:=Seat n) (B:=Pane n) j).seat=∅ from rfl,Finset.union_empty]; exact hp
      exact hp.unite H.2.2 (Finset.mem_union_left _ he.2) H.1
    obtain ⟨b,vb,v⟩:= List.mem_flatMap.mp h; obtain ⟨Y,t₀,rfl⟩:= List.mem_map.mp v; have hv:= ΘMeter ι P F Q u z j b vb
    let S':=(u.day i b.val Y t₀)
    refine ⟨scene_W _ _ _ _ g.stamp (scene_W _ _ _ _ hv.1 (κFoam ι P F u i b.val Y t₀) _) _,fun x y h=>by change none=some (x,y) at h; contradiction,?_⟩
    change Geo (e.seat∪ (b.seat∪ Y.seat)); have hh : Geo (e.seat∪ Y.seat):=g.grave.unite S'.2.1 he.1 S'.2.2.1; rcases hv.2 with H|H
    · rw [H,show (leaf (I:=I) (J:=Seat n) (B:=Pane n) j).seat=∅ from rfl,Finset.empty_union]; exact hh
    rw [Finset.union_comm b.seat,←Finset.union_assoc]; exact hh.unite H.2.2 (Finset.mem_union_left _ he.2) H.1
omit z
lemma FiscalK (X:I→Boke n I)(L:List I)(p:∀ i∈ L,CostP ι P (X i)):CostP ι P (Keeps F Kℓ X L):=by
 induction L with
 | nil=> intro i t; simp [Keeps] at t
 | cons i L h=>
    intro j v; let A:= h fun j w=> p j (List.mem_cons_of_mem _ w); cases List.mem_append.mp v with| inl w=>exact A j w| inr t=> obtain ⟨k,s,h⟩:=List.mem_flatMap.mp t; exact Fiscal ι P F (Keeps F Kℓ X L) u A k (p i List.mem_cons_self k s) j h
#print axioms FiscalK
end MastTin
end YM.CF.XGarden
end
