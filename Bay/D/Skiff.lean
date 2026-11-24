import Bay.D.Pier
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Bay
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet Scroll Finset Palot Cadre Vow
open RG MeasureTheory Rue
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Tap Levier Thera Oath Font Spire Dial Rill
open Kennel Swell

namespace D
open Buffered Lifted

/-- One-site cushion beyond the declaration in Vinyl.localV. -/
abbrev Band (o:Cover)(b:ℕ):Finset Cover:=pavilion o (13+b)
def AtEase(S:Finset Cover)(N:Side):Prop:=Set.InjOn (wrap (More N)) S

variable {S:Finset Cover}{N:Side}{b:ℕ}{o:Cover}
def refill (S:Finset Cover)(N:Side)(x:Seat N):Option Cover:=
 if h:∃y∈S,wrap (More N) y=x then some (Classical.choose h) else none
lemma refill_center (e:AtEase S N) {x}(h:x∈S): refill S N (wrap _ x)=some x:=by
 let p:∃y∈S,wrap (More N) y=wrap _ x:=⟨x,h,rfl⟩
 rw [refill,dif_pos p]; exact congrArg some (e (Classical.choose_spec p).1 h (Classical.choose_spec p).2)
def craft(S:Finset Cover)(N:Side)(v:LinksC):Pane N:=
  fun i=>match refill S N i.1 with
    |some x=>v (x,i.2)
    |none=>1
lemma craft_center(e:AtEase S N){x}(h:x∈S)(v:LinksC)(j:Axis):
  craft S N v (wrap _ x,j)=v (x,j):=by simp [craft,refill_center e h]
lemma craft_agrees(e:AtEase S N)(v:LinksC):Agrees S (onC N (craft S N v)) v:=
  fun i h _=> (onC_spec ..).trans (craft_center e h ..)

lemma craft_cont : Continuous (craft S N):=by
  apply continuous_pi; intro i
  unfold craft
  cases refill _ _ i.1
  · exact continuous_const
  exact continuous_apply _

local notation "SΩ"=>Band o b
local notation "c₀"=>wrap (More N) o
local notation "ridge"=>roost (12+b) c₀
def reedG(S:Finset Cover)(N:Side)(t:Cover→E):Seat N→E:=
  fun x=>match refill S N x with
    |some i=>t i
    |none=>1
lemma reedG_p(e:AtEase S N) {x}(h:x∈S)(t:Cover→E):reedG S N t (wrap _ x)=t x:=by simp[reedG,refill_center e h]

lemma atRidge {i}(hi:i∈ridge)(j:Axis) :
 ∃u∈SΩ,wrap (More N) u=i∧u+step j∈SΩ:=by
 rw [show ridge=(pavilion o (12+b)).image (wrap (More N)) from (wrap_pav ..).symm] at hi
 obtain ⟨u,w,rfl⟩:=mem_image.mp hi
 refine ⟨u,(pav_v ..).mpr fun a=>?_,rfl,(pav_v ..).mpr fun a=>?_⟩
 all_goals
   have ht :=(pav_v ..).mp w a
 · omega
 have g : u + step j ∈ visits u [posDir j]:=by simp [visits]
 have v:=(pav_v ..).mp (walk_pav _ _ _ g) a
 simp only[List.length_cons,List.length_nil] at v;omega

lemma craft_support(e:AtEase SΩ N) {u v}(p:Agrees SΩ u v):
 Agrees ridge (craft SΩ N u) (craft SΩ N v):=by
 rintro ⟨x,i⟩ h _
 obtain ⟨w,z,rfl,t⟩:= atRidge h i
 rw[craft_center e z,craft_center e z,p (w,i) z t]

lemma craft_back(e:AtEase SΩ N)(u:Pane N): Agrees ridge (craft SΩ N (onC N u)) u:=by
 rintro ⟨x,i⟩ h _
 obtain ⟨w,z,rfl,t⟩:= atRidge h i
 rw[craft_center e z,onC_spec]
lemma craft_hue(e:AtEase SΩ N)(t:Cover→E)(u:LinksC):
 Agrees ridge (craft SΩ N (Lattice.gauge t u)) (Lattice.gauge (reedG SΩ N t) (craft SΩ N u)):=by
 rintro ⟨x,i⟩ h _
 obtain ⟨w,z,rfl,v⟩:=atRidge h i
 rw [craft_center e z]
 change t w*u (w,i)*(t _)⁻¹=reedG SΩ N t (wrap (More N) w) *craft SΩ N u (wrap (More N) w,i)*(reedG SΩ N t (wrap (More N) w+step i))⁻¹
 have he:wrap (More N) w +step i=wrap (More N) (w+step i):=by rw[map_add,wrap_step]
 rw [he,craft_center e z,reedG_p e z,reedG_p e v]
lemma craft_tick(e:AtEase SΩ N)(t:ℝ)(u:LinksC):
 pingS t (roost b c₀) (craft SΩ N u) ↔ landingC b o t u:=by
 rw [←land_wrap] -- roost defeq?
 let T:= pavilion o (b+4+4)
 have q:T⊆ SΩ:=fun i h=>(pav_v ..).mpr fun a=>by have w:=(pav_v ..).mp h a;omega
 exact voyage_local o t _ _ (fun i h p=>craft_agrees e u i (q h) (q p))

def nubs(S:Finset Cover):=S ×ˢ (univ:Finset Axis)
def inlet(S:Finset Cover)(v:LinksC):↥(nubs S)→Bool→Twig:=
 fun i u=>if u then brand (v i.val) else star (brand (v i.val))

lemma inlet_bounds(S:Finset Cover): TotallyBounded (Set.range (inlet S)):= by
 have t : Continuous (inlet S):=by
    apply continuous_pi; intro i
    apply continuous_pi; intro u
    have h : Continuous brand:=matter_cont.prodMk SU.fund_cont
    have c:Continuous (fun x:LinksC=>brand (x i.val)):= h.comp (continuous_apply _)
    cases u
    · exact c.star
    exact h.comp (continuous_apply _)
 exact (isCompact_range t).totallyBounded

lemma fare_inlet {k:ℕ}(h:k≤12+b)(e:AtEase SΩ N)(x y:LinksC):
   fare (roost k c₀) (profile (craft SΩ N x)) (profile (craft SΩ N y))≤
     (nubs SΩ).card * dist (inlet SΩ x) (inlet SΩ y):=by
 let A := leaks (roost k c₀)
 let j:=fun i:Cover×Axis=>(wrap (More N) i.1,i.2)
 have l:A⊆ (nubs SΩ).image j:=by
   rintro ⟨i,t⟩ a
   obtain ⟨x,g,rfl,_⟩:=atRidge ((roost_expand h) (mem_filter.mp a).2.1) t
   exact mem_image.mpr ⟨(x,t),mem_product.mpr ⟨g,mem_univ _⟩,rfl⟩
 unfold fare
 apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg l (fun _ _ _=>norm_nonneg _))

 have v:Set.InjOn j ↑(nubs SΩ):=fun i a k b h=>
    Prod.ext (e (mem_product.mp a).1 (mem_product.mp b).1 (Prod.mk.inj h).1) (Prod.mk.inj h).2
 rw [sum_image v,dist_eq_norm]
 let W:=inlet SΩ x-inlet SΩ y
 apply le_trans (sum_le_sum (g:= fun i :Cover×Axis=> ‖W‖) fun i h=> ?_)
 · exact (by simp [nsmul_eq_mul,W] : (_:ℝ) = _).le
 let i' := (⟨i,h⟩:↥(nubs SΩ))
 have P(z:LinksC):profile (craft SΩ N z) (j i)=inlet SΩ z i':=by
    have q:craft SΩ N z (j i)=z i:= craft_center e (mem_product.mp h).1 ..
    unfold profile; rw[q]; rfl
 rw[P,P]; exact norm_le_pi_norm W i'
end YM.CF.Bay.D
