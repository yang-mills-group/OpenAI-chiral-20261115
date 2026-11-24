import GaugeFieldConstruction.HarborM
import GaugeFieldConstruction.Liaison
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 340000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Scree.Ing
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree
open Skye Scree Vow Hake Jet Fock
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Peaks
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
section gas
variable {α β ι M:Type*} [Fintype ι][Fintype β] [DecidableEq β] [Fintype α]
variable (w:ι→β)(t:β→Finset α)(f:ι→M)
variable (V:Finset β)
local notation "F"=>fun j=> (univ:Finset ι).filter fun i=> w i=j
variable [CommSemiring M]
noncomputable def PourUp (w:ι→β)(f:ι→M):β→M:=fun j=>∑ i:ι with w i=j,f i
private lemma pours : (∏ j∈V,PourUp w f j)=∑ s∈ ((univ:Finset (Finset ι)).filter (fun s:Finset ι=>s.image w=V∧Set.InjOn w (s:Set ι))), ∏ i∈s,f i:=by
 unfold PourUp; rw [Finset.prod_sum]; let A:= V.pi F
 let g (p:∀ (i:β), i∈V→ι):= V.attach.image fun j=>p j.val j.property
 have h {p}(u:p∈A){i:β}(t:i∈V): w (p i t)=i:=(mem_filter.mp (Finset.mem_pi.mp u i t)).2
 have he {p} (u:p∈A)(i:ι): i∈ g p ↔ ∃ t:w i∈V, p (w i) t = i:=by
    constructor
    · intro v; obtain ⟨⟨j,k⟩,z,rfl⟩:= mem_image.mp v; dsimp only
      have hx:=h u k; simp [hx,k]
    rintro ⟨k,hh⟩; exact mem_image.mpr ⟨⟨w i,k⟩,mem_attach ..,hh⟩
 let d:Finset (Finset ι):=univ.filter (fun s=> s.image w=V∧ Set.InjOn w (s:Set ι))
 have hd {s}:s∈d↔s.image w=V ∧ Set.InjOn w s:=by simp [d]
 apply sum_bij (fun a h=>g a)
 · intro i v; apply hd.mpr; constructor
   · ext j; constructor
     · intro q; obtain ⟨x,z,rfl⟩:=mem_image.mp q; exact ((he v x).mp z).choose
     intro jv; exact mem_image.mpr ⟨i j jv,mem_image.mpr ⟨⟨j,jv⟩,mem_attach ..,rfl⟩,h v jv⟩
   intro x v' y y' ht
   obtain ⟨t,x'⟩:=(he v x).mp v'; obtain ⟨z,y'⟩:=(he v y).mp y'; exact x'.symm.trans ((congrArg (fun j:↥V=>i j.val j.property) (show (⟨_,t⟩:↥V)=⟨_,z⟩ from Subtype.ext ht)).trans y')
 · intro x v y t a; funext i hi; let j:=x i hi; have hg:w j=i:=h v hi
   have hz:j∈g x:= mem_image.mpr ⟨⟨i,hi⟩,mem_attach ..,rfl⟩
   obtain ⟨l,o⟩:= (he t j).mp ((a ▸ hz) : j∈g y); exact o.symm.trans (congrArg (fun i:↥V=>y i.val i.property) (show (⟨_,l⟩:↥V)=⟨_,hi⟩ from Subtype.ext hg))
 · intro b s; obtain ⟨e,t⟩:=hd.mp s; choose x p q using fun (j:β)(u:j∈V)=> mem_image.mp ((e ▸ u): j∈ b.image w) -- rw tune
   have v:x∈A:=Finset.mem_pi.mpr fun j t=>mem_filter.mpr ⟨mem_univ _,q j t⟩
   refine ⟨x,v,?_⟩; ext i; rw[he v i]; constructor
   · rintro ⟨d,h⟩; exact h ▸ p (w i) d -- dependent anchor h may loop
   intro hi; have h:w i∈V:=e ▸ mem_image_of_mem w hi
   exact ⟨h,t (p _ h) hi (q _ h)⟩
 intro i v
 unfold g; rw [prod_image]; intro x u y t a; exact Subtype.ext ((h v x.2).symm.trans ((congrArg w a).trans (h v y.2)))

end gas
section ion
variable {n:Side}{α β:Type*}[Fintype α]
variable (z:α→Force n){S:Support (More n)}
abbrev plateI (z:α→Force n)(i:α) :Support (More n):=(z i).val.1.val.2
abbrev sealI (z:α→Force n)(i:α) :Support (More n):=(z i).val.2
def walls (J:Finset α):= J.biUnion (plateI z)
def til (J:Finset α):= J.biUnion (sealI z)
structure PriceI (Z:Support (More n))(J:Finset α):Prop where
 zone : (J:Set α).Pairwise fun a b=> Disjoint (plateI z a) (plateI z b)
 covers : til z J= Z
local notation "Pζ"=> PriceI z
variable {P: BudgetPoint}{U:Orbit n}{A:Finset α}{v:α → Copy n}{V:Support (More n)}
lemma PriceI.inject (g:Pζ V A):Set.InjOn z A:=fun i k j t h=>by
 by_contra e; have v:=g.zone k t e; unfold plateI at v; beta_reduce at v; rw [h] at v; exact disjoint_left.mp v (z j).val.1.property (z j).val.1.property
-- band support for every occupied pack
lemma PriceI.foot (g:Pζ V A){i:α}(p:i∈A):plateI z i∩ V = sealI z i:=by
 ext x; rw [mem_inter]; constructor
 · rintro ⟨u,t⟩; rw [←g.covers] at t; obtain ⟨j,k,h⟩:=mem_biUnion.mp t; by_cases e:i=j; · rw [e]; exact h
   exact False.elim (disjoint_left.mp (g.zone p k e) u ((z j).property.2 h))
 intro u; exact ⟨(z i).property.2 u,g.covers ▸ mem_biUnion.mpr ⟨i,p,u⟩⟩
lemma PriceI.flip (J:Finset (Force n))(u:Set.InjOn z A)(h:A.image z=J):Pζ S A ↔ PriceI (id:Force n→Force n) S J:=by
 rw[←h]; have ht:til (id:Force n→Force n) (A.image z)=til z A:=by
    ext i; simp[til,sealI]
 constructor
 · intro H; refine ⟨?_,ht.trans H.covers⟩; intro a v b t d; obtain ⟨x,y,rfl⟩:=mem_image.mp v; obtain ⟨i,b,rfl⟩:=mem_image.mp t; exact H.zone y b (fun e=> d (congrArg _ e))
 intro H; refine ⟨?_,ht.symm.trans H.covers⟩; intro a v b t d; exact H.zone (mem_image_of_mem z v) (mem_image_of_mem z t) (fun e=>d (u v t e))

include z in
lemma pricePack (K:Support (More n)){M:Type*}[CommSemiring M](f:α→M) :
 (∑ i:Finset (Force n) with PriceI (id:Force n → Force n) K i, ∏ j∈ i,PourUp z f j)=∑ i:Finset α with Pζ K i,∏ j∈i,f j:=by
 simp_rw[pours]; let S:= (univ:Finset (Finset (Force n))).filter (fun i=>PriceI (id:Force n→Force n) K i)
 rw [sum_sigma'] -- tune
 let σ:=S.sigma (fun J=>univ.filter (fun L:Finset α=>L.image z= J ∧ Set.InjOn z L))
 apply sum_bij (fun i h=> i.snd)
 · rintro ⟨i,v⟩ h; obtain ⟨a,u,b⟩:= And.intro (mem_sigma.mp h).1 (mem_filter.mp (mem_sigma.mp h).2).2
   exact mem_filter.mpr ⟨mem_univ _,(PriceI.flip z i b u).mpr (mem_filter.mp a).2⟩
 · rintro ⟨i,x⟩ u ⟨j,y⟩ v h; dsimp only at h; subst x
   have he:= (mem_filter.mp (mem_sigma.mp u).2).2.1; have hx:=(mem_filter.mp (mem_sigma.mp v).2).2.1
   rw[show i=j from he.symm.trans hx]
 · intro i h; have p:=(mem_filter.mp h).2; have t:=p.inject _; exact ⟨⟨i.image z,i⟩,mem_sigma.mpr ⟨mem_filter.mpr ⟨mem_univ _, (PriceI.flip z _ t rfl).mp p⟩,mem_filter.mpr ⟨mem_univ _,rfl,t⟩⟩,rfl⟩
 rintro ⟨i,x⟩ u; rfl
local notation "K0"=> flags P.threshold U.1
lemma fueled_split (h:Rue.FleetS P.threshold U.1):fueled P (PourUp z v) U=∑ i:Finset α with Pζ K0 i,∏ j∈i, v j U:=by
 unfold fueled; rw [←sum_filter, ← pricePack z _ (fun i=>v i U)]
 let Q(i:Finset (Force n)):= coverF P i U.1∧ Set.PairwiseDisjoint (↑i) (fun x=> (x: Force n).val.1.val.2)
 let F₀ := PourUp z v
 have he(i:Finset (Force n)):Q i ↔ PriceI id K0 i:=⟨fun p=>⟨p.2,p.1⟩,fun p=>⟨p.covers,p.zone⟩⟩
 change (∑ i∈ (univ:Finset _).filter Q, ∏ j∈i, clamp P j (F₀ j) U)=_
 rw [filter_congr (p:=Q) (q:=fun i=>PriceI id K0 i) fun i _=> he i]
 apply sum_congr rfl; intro i t; apply prod_congr rfl; intro j p
 have ht:= (show PriceI (id:Force n→Force n) K0 i from (mem_filter.mp t).2).foot id p
 have hv: boundF j P U.1:= (Rue.shoreK P.threshold U.1 h _).1 (disjoint_left.mpr (fun {x} k U'=>by
    obtain ⟨a,b⟩:= mem_sdiff.mp k; apply b; change _∈sealI id (j:Force n); rw [←ht]; exact mem_inter.mpr ⟨a,U'⟩))
 unfold clamp; rw [if_pos hv]; unfold F₀ PourUp; simp only [Finset.sum_apply]
end ion
end YM.CF.Scree.Ing
end
