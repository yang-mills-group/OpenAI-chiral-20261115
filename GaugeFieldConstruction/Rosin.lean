import GaugeFieldConstruction.Tornador
set_option autoImplicit false
set_option maxRecDepth 5500
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
namespace ArtCart
open Buffered Lifted Girt Skye Window Vale
variable (x:Cover)(d:ℕ)
lemma starlet(z:Cover):∃ i:Cover,z=nodeC i↔ ∃ j:Cover,z=nodeC j:=by classical by_cases h:∃ j:Cover,z=nodeC j; obtain ⟨j,t⟩:=h; exact ⟨j,fun u=>⟨j,u⟩,fun _=>t⟩; exact ⟨0,fun u=>⟨_,u⟩,fun u=>(h u).elim⟩
abbrev starElem(z:Cover):= (starlet z).choose
lemma node_cone {u v: Cover}: nodeC u=nodeC v↔u=v:=(show Injective nodeC from fun i j h=> nsmul_right_injective (M:=Cover) (show (2:ℕ)≠0 from by norm_num) (add_right_cancel h)).eq_iff
abbrev ridge(x:Cover)(d:ℕ):= ((cartO x d).image starElem).filter (fun i=>nodeC i ∈cartO x d) -- finite support pool
variable {d x}
lemma ridge_spec(i:Cover): i∈ridge x d ↔ nodeC i∈cartO x d:=by
 unfold ridge; rw [mem_filter]; refine ⟨And.right,fun h=> ⟨?_,h⟩⟩; refine mem_image.mpr ⟨nodeC i,h,node_cone.mp ?_⟩; exact ((starlet (nodeC i)).choose_spec.mpr ⟨i,rfl⟩).symm
-- all node/Seams cover projections
variable (n)
lemma node_lift (i:Cover)(a:Site n)(h:wrap (More n) i=node a) : ∃ x:Cover,i=nodeC x ∧ wrap n x=a:=by
 let q:=natural a; let k:=More n; have hv: wrap k (nodeC q)=node a:=Eq.trans (node_of _ _).symm (congrArg _ (Rush.nat_true a)); let V:= Rush.periods k i - Rush.periods k (nodeC q); have hf:i=nodeC q+k.val • V:=by
    have hK:= carrying k (nodeC q); have he:= carrying k i; rw [show wrap k i=wrap k (nodeC q) from h.trans hv.symm] at he; unfold V; rw [smul_sub]; linear_combination (norm:=abel) he.symm+hK
 let x:= q+n.val • V; have hp: i=nodeC x:=by unfold x nodeC; rw [smul_add,add_right_comm _ _ (1:Cover),← smul_comm n.val,←mul_smul]; exact hf -- tune
 refine ⟨x,hp,Tenant.needle (Eq.trans (node_of n x) (hp ▸ h))⟩ -- tune
-- vocabulary on d box: slots with ferm sites in ridge. pack in paper.
abbrev mort (x:Cover)(d:ℕ) := (ridge x d) × SpinIdx × SU.Slot -- coe Sort syntax
abbrev jungle (x:Cover)(d:ℕ):Type:= Option (Bool× mort x d × mort x d)
abbrev hereF(i:mort x d):Single n:= ((wrap n i.1.val,i.2.1),i.2.2)
abbrev hereV {x:Cover}{d:ℕ}(n:Side)(i:jungle x d):Wa n:= i.map fun ⟨b,k,l⟩=> (b,hereF n k,hereF n l)
lemma hereD (i:mort x d): node (hereF n i).1.1 =wrap (More n) (nodeC i.1.val):=node_of ..
variable {n}
lemma hereN(d:ℕ)(w: d<n.val):Injective (hereF (x:=x) (d:=d) n):=by
 rintro i j h; have he(i:mort x d): nodeC i.1.val∈cartO x d:= (ridge_spec _).1 i.1.property; refine Prod.ext ?_ (congrArg (fun i:Single n=> (i.1.2,i.2)) h)
 apply Subtype.ext; apply node_cone.mp; apply cart_I d w (he i) (he j); rw [←hereD,←hereD,h] -- Hove.port tune
lemma hereI (w:d<n.val):Injective (hereV (d:=d) (x:=x) n):= Option.map_injective (fun _ _ e=> Prod.ext (congrArg (fun x:Pairs n=> x.1) e) (Prod.ext (hereN _ w (congrArg (fun x:Pairs n=> x.2.1) e)) (hereN _ w (congrArg (fun x: Pairs n=> x.2.2) e)))) -- tune
lemma here_Q (i:mort x d)(w:d<n.val): aptK (hereF n i) ∈knotX x d n:=by
 change node (hereF n i).1.1 ∈ _; rw [hereD,←cart_T w]; exact mem_image_of_mem _ ((ridge_spec _).1 i.1.property)
lemma here_H (i:Single n)(w:d<n.val)(h:aptK i∈ knotX x d n):∃ j:mort x d,hereF n j=i:=by
 rw [← cart_T w] at h; obtain ⟨j,u,v⟩:= mem_image.mp h; obtain ⟨k,rfl,K⟩:= node_lift n j i.1.1 v; refine ⟨(⟨k,(ridge_spec _).2 u⟩,i.1.2,i.2),?_⟩; unfold hereF; rw [K]
lemma here_all (i:Wa n)(w:d<n.val)(h: DomainP (knotX x d n) i): ∃ j:jungle x d,hereV n j=i:= by
 rcases i with _|⟨b,u,v⟩; exact ⟨none,rfl⟩; obtain ⟨l,e⟩:=here_H u w h.1; obtain ⟨j,f⟩:=here_H v w h.2; exact ⟨some (b,l,j),by simp [hereV,e,f]⟩ -- tune
lemma hereDom (i:jungle x d)(w:d<n.val): DomainP (knotX x d n) (hereV n i):=by cases i with|none=>trivial|some p=>exact ⟨here_Q _ w,here_Q _ w⟩
lemma here_cost (i:jungle x d)(v:ℝ)(r:Side): papW n v (hereV n i)=papW r v (hereV r i):=by cases i <;>rfl
-- phases
variable (n)
def feeV(i:jungle x d):ℂ:= i.elim 1 fun ⟨_,j,k⟩=> winding n j.1.val * winding n k.1.val
lemma winding_Q(i:mort x d): ‖winding n i.1.val‖=1:=fee_norm _
lemma feeV_n (i:jungle x d): ‖feeV n i‖=1:=by rcases i with _|⟨b,k,l⟩; exact norm_one; change ‖_*_‖= _; rw [norm_mul,winding_Q,winding_Q,one_mul]
lemma feeV_S (i:jungle x d):star (feeV n i)=feeV n i:=by rcases i with _|⟨b,k,l⟩; exact star_one _; change star (_*_)= _*_; rw [star_mul,show star (winding n l.1.val)=_ from fee_real _, show star (winding n k.1.val)=_ from fee_real _,mul_comm]; rfl
lemma feeV_U(i:jungle x d):feeV n i*feeV n i=1:=by rcases i with _|⟨b,k,l⟩; exact one_mul _; change _*_*(_*_)=1; rw [mul_mul_mul_comm (winding _ _),show winding n k.1.val * winding n k.1.val=1 from fee_one _,one_mul,show winding n l.1.val*winding n l.1.val=1 from fee_one _]
abbrev Psu (x:Cover)(d:ℕ):= jungle x d→ LinksC→ ℂ
abbrev Pvi(x:Cover)(d:ℕ)(A:Paper n): Psu x d:= fun i V=> feeV n i * A (hereV n i) (snake x V)
-- linear realization, works at any host (even collisions). multiply by indicator later.
def pR {x:Cover}{d:ℕ}(A:Psu x d):Paper n:=∑ i:jungle x d,isolate (hereV n i) (fun V=> feeV n i * A i (onC n V))
lemma pR_K {x:Cover}{d:ℕ}(A:Psu x d)(w:d<n.val)(i:jungle x d): pR n A (hereV n i)=fun V=> feeV n i * A i (onC n V):=by rw [pR,Finset.sum_apply]; simp [isolate, Pi.single_apply,(hereI w).eq_iff]
lemma pR_Z {x:Cover}{d:ℕ}(A:Psu x d)(w:d<n.val)(i:Wa n) (u:¬ DomainP (knotX x d n) i): pR n A i=0:=by
 unfold pR; rw [Finset.sum_apply]; apply sum_eq_zero; intro j _; simp only [isolate,Pi.single_apply]; split; next h=> exact (u (h.symm ▸ hereDom j w)).elim
 rfl
lemma pR_S {x:Cover}{d:ℕ}(V: Paper n)(w:d<n.val)(h:∀ i:Wa n,¬ DomainP (knotX x d n) i→V i=0):pR n (Pvi n x d V)=V:=by
 funext i; by_cases u:DomainP (knotX x d n) i; swap; · rw [pR_Z n _ w i u,h i u]
 obtain ⟨j,rfl⟩:= here_all i w u; rw [pR_K n _ w]; funext v; unfold Pvi; rw [porch w,←mul_assoc,feeV_U,one_mul]
end ArtCart
end MastTin
end YM.CF.XGarden
end
