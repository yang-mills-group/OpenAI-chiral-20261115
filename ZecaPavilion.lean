import ZecaTrellis
import ZecaIvy
set_option autoImplicit false
set_option maxHeartbeats 270000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Zeca
open Function Filter Metric Set MeasureTheory OS OS.Semigroup Complex
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace ComplexOrder


open Poin Vp.Folio
variable {H:Hilbert}{ι:Type}(S:OS.Semigroup H timeAxis)(G:Canopy H ι)(Ω:H.space)
 (hΩ:∀x:E4,M S x Ω=Ω)
local notation "a"=>timeAxis
local notation "Λ"=>List (Item G.Chip)
local notation "φ"=>face S Ω G.dep G.grade
local notation "ψ"=>role S Ω G.dep G.grade
local notation "tm" t:max=> t • basis timeAxis
variable (d:E4→ₗ[ℝ]ℝ) (e:d (basis timeAxis)=0)

abbrev MarginD (x y:Item G.Chip):Prop:= d=0 ∨ d x.2 < d y.2
abbrev ArcJ : Set H.space := {x|∃ L:List (Item G.Chip), LaneE a 0 L ∧ L.Pairwise (MarginD G d) ∧ x=φ 0 L}
abbrev FarJ (b:ℝ) : Set H.space:= {x|∃ L:List (Item G.Chip), LaneE a 0 L ∧ L.Pairwise (MarginD G d) ∧ x=φ 0 L ∧ ∀i∈L,d=0∨ b < d i.2}

local notation "Y"=>ArcJ S G Ω d
lemma lifted (p:E4)(L:List (Item G.Chip)) (v:L.Pairwise (MarginD G d)): (shifted p L).Pairwise (MarginD G d):=
 List.pairwise_map.mpr (v.imp fun {i j} u=> u.imp id (fun h=> show d (p+i.2)< d (p+j.2) by simp [map_add,h]))

lemma laneLower {t s:ℝ}(h:s≤t){L:List (Item G.Chip)}(p:LaneE a t L):LaneE a s L:=
 ⟨p.1, fun x e=>h.trans_lt (p.2 x e)⟩
lemma clock_sep(t:ℝ):SEP a (tm t)=0:=Subtype.ext (by change tm t - ((tm t) a) • basis _ = 0;simp)
lemma clock_a(t:ℝ): (tm t) a=t:=by simp

include hΩ
lemma clock_face (t s:ℝ)(L:List (Item G.Chip))(p:LaneE a s L):LaneE a (s+t) (shifted (tm t) L) ∧ φ (s+t) (shifted (tm t) L)=φ s L:=by
 nth_rw 1 [←clock_a t]; constructor
 · exact headL' (tm t) s L p
 nth_rw 1 [←clock_a t]
 rw [vfront S Ω hΩ _ _ _ _ _ p, clock_sep]
 exact DFunLike.congr_fun (tini S) _
lemma side_face (u:Cross timeAxis)(t:ℝ)(L:List (Item G.Chip))(p:LaneE a t L):LaneE a t (shifted u.val L) ∧ φ t (shifted u.val L)=S.U u (φ t L):=by
 have h:u.val a=0:=u.property
 have y:=vfront S Ω hΩ G.dep G.grade u.val t L p
 have e:= headL' u.val t L p
 rw [h,add_zero] at y e
 have k:SEP a u.val = u:=Subtype.ext (by change u.val-(u.val a) • _=u.val; rw [h,zero_smul,sub_zero])
 exact ⟨e,by rw [y,k,laneslot]⟩

lemma warmWord (t:ℝ≥0)(x:H.space)(p:x∈ArcJ S G Ω d) : S.E t x∈ArcJ S G Ω d:=by
 obtain ⟨L,k,j,rfl⟩:=p
 by_cases r: t=0
 · subst t;rw [S.eZero]; exact ⟨L,k,j,rfl⟩
 have q:0<(t:ℝ):=show 0<t from pos_iff_ne_zero.mpr r
 let p:=tm (t:ℝ)
 obtain ⟨a₁,f⟩:=clock_face S G Ω hΩ (t:ℝ) 0 L k
 rw [zero_add] at a₁ f
 exact ⟨shifted p L,laneLower G q.le a₁,lifted G d p L j,by
    rw [frontHot S _ _ Ω hΩ _ _ _ q a₁,f,sub_zero,Real.toNNReal_coe]⟩

omit hΩ in
lemma coatOne (i:G.Chip)(p:E4)(m:p=basis a):stamps S G.dep (i,p)=G.dep i:=by
  have atp: SEP a p=0:=by rw [show p=(tm (1:ℝ)) by rw [m,one_smul], clock_sep]
  change optx S _ (SEP a p).val = _
  rw [atp]
  exact vroot ..
include e
lemma wrapped (i:G.Chip)(x:H.space)(m:x∈FarJ S G Ω d 0):
    (Par S (G.grade i) 1 * G.dep i * Par S (G.grade i) 1) x∈ ArcJ S G Ω d:=by
 obtain ⟨L,l,q,rfl,far⟩:=m
 let p:E4:=tm (2:ℝ)
 let M:=shifted p L
 let u:Item G.Chip:= (i,basis a)
 have y:=clock_face S G Ω hΩ 2 0 L l; rw [zero_add] at y
 have B:timesA a u=1:= by change basis a a=1;simp

 refine ⟨u::M,⟨List.pairwise_cons.mpr ⟨fun t p=>lt_trans (show timesA _ u<2 by rw [B];norm_num) (y.1.2 t p),y.1.1⟩,
       ?_⟩,List.pairwise_cons.mpr ⟨?_,lifted G d p _ q⟩,?_⟩
 · intro t a₁;rcases List.mem_cons.mp a₁ with v|v
   · rw [v,B];norm_num
   exact lt_trans zero_lt_two (y.1.2 _ v)
 · intro t w;obtain ⟨t,v,rfl⟩:=List.mem_map.mp w
   exact (far t v).imp id fun h=>show d (basis a)<d (p+t.2) by simp [e,map_add,p,h]
 rw [frontTicket S _ _ Ω hΩ _ 2 u _ (B.trans_lt (by norm_num)) y.1, y.2, B,
     coatOne S G i _ rfl,sub_zero, show (2:ℝ)-1=1 by norm_num]
 simp only [leanX,Real.toNNReal_one,u]

omit e
lemma eventFern (far:ArcJ S G Ω d⊆ Boxed (FarJ S G Ω d 0))(e:d (basis timeAxis)=0)
    : Fern (ArcJ S G Ω d) S G Ω:=by
  refine
   {omega:=⟨[],⟨List.Pairwise.nil,by simp⟩,List.Pairwise.nil,rfl⟩
    warm:=fun t=>manyKeeps _ fun y p=>grown Y _ (warmWord S G Ω hΩ d _ y p)
    space:=fun u=>manyKeeps _ fun x k=>grown Y _ ?_
    pay:=fun i=>?_}
  · obtain ⟨L,y,m,rfl⟩:= k;obtain ⟨a₁,e⟩:=side_face S G Ω hΩ u 0 L y
    exact ⟨_,a₁,lifted G d u.val _ m,e.symm⟩
  apply manyKeeps
  let R:= Par S (G.grade i) 1 * G.dep i * Par S (G.grade i) 1
  let V:=FarJ S G Ω d 0
  have u:(Submodule.span ℂ V) ≤ (Boxed Y).comap R.toLinearMap:=
     Submodule.span_le.mpr (show ∀⦃x⦄,x∈V→R x∈Boxed Y from fun {_} px=>grown Y _ (wrapped S G Ω hΩ d e i _ px))

  exact fun _ p=>(Submodule.span ℂ V).topologicalClosure_minimal u
    ((show IsClosed (Boxed Y:Set H.space) from isClosed_closure).preimage R.continuous) (far p)
#print axioms eventFern