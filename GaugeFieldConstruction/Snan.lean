import GaugeFieldConstruction.Tondra
/- Incidence Majorant -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Fock.Wosk
open Pastry Function Set Metric MeasureTheory NormedSpace Filter Finset
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Roots Mew Roots.GJ
variable {I J O V B W G:Type}[LinearOrder I][Fintype I][DecidableEq J][LinearOrder G][Fintype G]
variable (ι:G→J)(a b h r:ℝ)(U:G→ G→Toil I J B)(c d:ℝ)(p:FumedH a b ι U c d)(q:Book0 I J G B)(D:ℝ)(t:Puffion ι q)(s:MajorZ a b h q D)
variable (hr:0≤r)(ha:0≤a)(hb:0≤b)(ht:1≤h)
local notation "WG"=>weightV a b
local notation "WX"=>bil a b
variable (hD:0≤D)(hC:0≤c)
include p hr t
lemma tooth_s (i j:G): OpenB (toothW U r q i j) ∧∀ v∈toothW U r q i j,∀ i' j',v.val=some (i',j')→ (ι i'∈v.seat ∨ i'=i)∧(ι j'∈v.seat∨j'=j):=by
 let L:=frond U r q i; let T:=frond U r q j; have hf:=seed_Λ ι a b r U c d p q t hr i; have hv:=seed_Λ ι a b r U c d p q t hr j
 suffices w:∀ v∈toothW U r q i j,0≤ v.won ∧∀ i' j',v.val=some (i',j')→(ι i'∈v.seat ∨ i'=i)∧(ι j'∈v.seat∨j'=j) from ⟨fun i t=>(w _ t).1,fun i t=>(w _ t).2⟩
 intro e u; unfold toothW seedX sprigW at u; simp only [List.mem_append,List.mem_flatMap,List.mem_map] at u; cases u with
 | inl u =>
    obtain ⟨a,u,b,w,rfl⟩:=u; refine ⟨mul_nonneg (mul_nonneg hr (hf.1 _ u)) (hv.1 _ w),?_⟩; intro i' j' h; obtain ⟨rfl,rfl⟩:=Prod.mk.inj (Option.some.inj h); exact ⟨(hf.2 a u).elim (fun e=>Or.inr (e ▸ rfl)) (fun h=>Or.inl (Finset.mem_union_left _ h)), (hv.2 b w).elim (fun e=>Or.inr (e ▸ rfl)) (fun h=>Or.inl (Finset.mem_union_right _ h))⟩ -- rfl weird incl ht
 | inr v=> obtain ⟨a,u,b,w,rfl⟩:=v; exact ⟨mul_nonneg (mul_nonneg hr (hv.1 _ u)) (p.fee0 _ _ b w),fun c d h=>by change none=some (c,d) at h; contradiction⟩
local notation "V0"=> Lem I J (Option (G×G)) B
local notation "Zv"=> Lem I J G B
lemma grow_s (e:Lem I J (Option (G×G)) B)(a0:0 ≤ e.won)(u:puffQ ι e): Puffion ι (growL U r q e):=by
 unfold growL; cases v:e.val with
 | none=>exact ⟨fun j h=> List.mem_singleton.mp h ▸ a0,fun i h=>List.mem_singleton.mp h ▸ u⟩
 | some w=>
    rcases w with ⟨i,j⟩; have ht:= tooth_s ι a b r U c d p q t hr i j; have hy:=u i j v
    refine ⟨fun y v=>?_,fun y v=>?_⟩<;> obtain ⟨x,g,rfl⟩:= List.mem_map.mp v
    · exact mul_nonneg (mul_nonneg hr a0) (ht.1 x g)
    intro k l V; let H:=ht.2 x g k l V; exact ⟨H.1.elim (Finset.mem_union_right _) (fun h=>Finset.mem_union_left _ (h ▸ hy.1)),H.2.elim (Finset.mem_union_right _) (fun h=> Finset.mem_union_left _ (h ▸ hy.2))⟩
local notation "L" i:max=> frond U r q i
local notation "G0" =>RadBill r c D
include s ha hb ht hD hC
lemma tooth_G0(i:G):0≤ RadBill r c D:=(lea_n (L i) (fun v=>WG v) (fun j u=> WP_v _ _ _ hb ((seed_Λ ι a b r U c d p q t hr i).1 _ u))).trans (frond_cost ι a b h r U c d p q D t s hr ha hb ht i hD) -- i unneeded
abbrev ΘsF(r k c:ℝ):=r*k*k + r*k*c
lemma tooth_pay (i j:G): Lee (toothW U r q i j) (fun v=> weightV a b v) ≤ ΘsF r G0 c:=by
 let Tη(k:G):=seed_Λ ι a b r U c d p q t hr k; have hx:= tooth_G0 ι a b h r U c d p q D t s hr ha hb ht hD hC i -- order check
 let Rη(k):= frond_cost ι a b h r U c d p q D t s hr ha hb ht k hD
 unfold toothW seedX sprigW; rw [appA,joinA,joinA]; simp_rw [mapA]; apply add_le_add
 · refine le_trans (lea_p (L i) _ (fun v=> (r*G0)*WG v) (fun v V=>?_)) ?_
   · have hu:0≤ WG v:= WP_v _ b _ hb (Tη i|>.1 v V)
     have hw:0≤r*WG v:=mul_nonneg hr hu
     refine le_trans (lea_p _ _ (fun w=> r*WG v*WG w) (fun w x=> ?_)) ((lea_scale _ _ _).le.trans ((mul_le_mul_of_nonneg_left (Rη j) hw).trans_eq (mul_right_comm ..)))
     exact WP_pair a b r v w ha hb hr ((Tη _).1 _ V) ((Tη _).1 _ x) _
   rw [lea_scale]; exact mul_le_mul_of_nonneg_left (Rη _) (mul_nonneg hr hx)
 · refine le_trans (lea_p (L j) _ (fun v=> (r*c)*WG v) (fun v V=> ?_)) ?_
   · have hv:0≤r*WG v:=mul_nonneg hr (WP_v _ _ _ hb ((Tη _).1 _ V)); exact (lea_p _ _ (fun w=>r* WG v*WG w) (fun w u=>WP_pair a b r v w ha hb hr ((Tη _).1 _ V) (p.fee0 _ _ _ u) _)).trans ((lea_scale _ _ _).le.trans ((mul_le_mul_of_nonneg_left (raw_w a b ι U c d hb p i _) hv).trans_eq (mul_right_comm ..))) -- order!
   rw [lea_scale]; exact (mul_le_mul_of_nonneg_left (Rη _) (mul_nonneg hr hC)).trans_eq (mul_right_comm ..)

lemma WP_bill (i j:G)(x:J): let P(k:G):=Aqua_D a b r U q k x; Lee (toothW U r q i j) (fun v=> WX v x) ≤r*P i*G0+r*G0*P j + (r*P j*c+ r*G0*privH a b U i x):=by
 intro P; let Rη(k:G):= frond_cost ι a b h r U c d p q D t s hr ha hb ht k hD
 let Tη(k:G):=seed_Λ ι a b r U c d p q t hr k
 have he(k:G):0≤ P k:= Aqua_p ι a b r U c d p q t hr hb x k
 have hz:= tooth_G0 ι a b h r U c d p q D t s hr ha hb ht hD hC i
 unfold toothW seedX sprigW; rw [appA]; simp_rw [joinA,mapA]; apply add_le_add
 · refine le_trans (lea_p _ _ (fun v=> r*WX v x*G0+r* WG v*P j) fun v w=>?_) ?_
   · refine le_trans (lea_p (L j) _ _ (fun z t₀=> WP_union a b r v z ha hb hr ((Tη _).1 _ w) ((Tη j).1 z t₀) (some (v.val,z.val)) x)) ?_
     rw [lea_pair,lea_scale,lea_scale]; apply add_le_add _ le_rfl; exact mul_le_mul_of_nonneg_left (Rη j) (mul_nonneg hr (WP_p _ _ _ hb ((Tη _).1 _ w) x))
   simp_rw [mul_right_comm _ (bil a b _ x) G0, mul_right_comm _ (weightV a b _) (P j),lea_pair,lea_scale]; refine add_le_add (le_of_eq ?_) ((mul_le_mul_of_nonneg_left (Rη _) (mul_nonneg hr (he j))).trans_eq (mul_right_comm ..)); exact mul_right_comm ..
 · have hx(k:G): Lee (U i k) (fun z=>WX z x) ≤ privH a b U i x:= single_le_sum (f:=fun k=> Lee (U i k) (fun z=>WX z x)) (fun z _=> lea_n _ _ fun j t₀=>WP_p _ b _ hb (p.fee0 _ _ j t₀) x) (mem_univ _)
   refine le_trans (lea_p _ _ (fun v=> r* WX v x*c+r*WG v * privH a b U i x) (fun v w=>?_)) ?_
   · refine le_trans (lea_p (U i v.val) _ _ (fun z h=> WP_union a b r v z ha hb hr ((Tη j).1 v w) (p.fee0 _ _ _ h) (none:Option (G×G)) x)) ?_
     rw [lea_pair,lea_scale,lea_scale]; exact add_le_add (mul_le_mul_of_nonneg_left (raw_w _ _ ι _ _ d hb p _ _) (mul_nonneg hr (WP_p _ _ _ hb ((Tη j).1 v w) x))) (mul_le_mul_of_nonneg_left (hx _) (mul_nonneg hr (WP_v _ _ _ hb ((Tη j).1 _ w))))
   simp_rw [mul_right_comm _ (bil a b _ x) c,mul_right_comm _ (weightV a b _) (privH a b U i x),lea_pair,lea_scale]; exact add_le_add (le_of_eq (mul_right_comm ..)) ((mul_le_mul_of_nonneg_left (Rη j) (mul_nonneg hr (priv_w _ _ ι U c d hb p _ _))).trans_eq (mul_right_comm ..))
#print axioms WP_bill
end YM.CF.Fock.Wosk
end
