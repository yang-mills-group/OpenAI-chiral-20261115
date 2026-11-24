import YM.SU5.FiniteGaugeData.Mirage.Gazelle
import YM.CF.Cubes.Inside
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 380000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Quest
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra
open Heat Brique Window.Brique Journey Py Py.Rate LocalLimit Preparation FullBill Steam Vale
namespace Chaperone
open Largo
set_option quotPrecheck false
variable {N:Side}{o a b x y:Cover}
section geometry
variable (N:Side)(p q:ℕ)
def zoneL (p q:ℕ)(i:Axis): ℤ:= if i=3 then p else q
abbrev estate (p q:ℕ) := Fintype.piFinset (fun i=> Finset.Icc (-zoneL p q i) (zoneL p q i))
abbrev zone_pay (i:Axis): zoneL p q i≥0:=by unfold zoneL; split <;> omega -- abbrev instead lemma
variable {p q}
lemma own (x:Cover) : x∈ estate p q↔ ∀ i:Axis,-zoneL p q i≤ x i∧ x i≤zoneL p q i:= by simp only [estate,Fintype.mem_piFinset, Finset.mem_Icc]
lemma owns (x:Cover): x∈ estate p q ↔ (∀ i:Tang,-(q:ℤ)≤ x i.castSucc∧ x i.castSucc≤ q) ∧ -(p:ℤ)≤ x 3 ∧ x 3 ≤ p := by
 rw [own]; constructor <;> intro t
 · exact ⟨fun i=>by obtain ⟨v,w⟩:=t i.castSucc; unfold zoneL at v w; rw [if_neg (show i.castSucc≠3 from Fin.castSucc_ne_last _)] at v w; exact ⟨v,w⟩, t 3⟩
 exact fun k=> Fin.lastCases (motive:=fun i=>-zoneL p q i≤ x i∧ x i≤ zoneL p q i) t.2 (fun i=>by rw [zoneL,if_neg (show i.castSucc≠3 from Fin.castSucc_ne_last _)]; exact t.1 i) k
lemma ownTown : (0:Cover)∈ estate p q:= by rw [owns]; simp
variable {r d v w J ℓ:ℕ}
lemma ownM (P:p≤r)(x:q≤v): estate p q ⊆ estate r v := by intro a u; obtain v:= own a|>.mp u; refine (own a).mpr (fun i=>?_); specialize v i; unfold zoneL at *; split_ifs at * <;> omega
lemma own_add (h:x∈ estate p q)(t:y∈ estate r v): x+y∈ estate (p+r) (q+v):=by obtain v:= own _|>.mp h; obtain t':= own _|>.mp t; refine (own _).mpr (fun i=>?_); specialize v i; specialize t' i; unfold zoneL at *; rw [Pi.add_apply]; split_ifs at * <;> omega -- x unbound
lemma own_halo (v:ℕ): Lattice.halo v (region (estate p q) N) ⊆ region (estate (p+v) (q+v)) N:=by
 intro i h; obtain ⟨x,y,h⟩:= halo_spec.mp h; obtain ⟨j,t,rfl⟩:= mem_image.mp y
 let a:= wrap (More N) j; let b:= Lattice.lift (i-a); have hp:b∈Lattice.box v:= Work.E08.lift_mem_box h; have hv:b∈ estate v v:=by
    apply (own _).mpr; intro j; unfold zoneL; rw [ite_self]; exact ⟨(box_test.mp hp).1 j,(box_test.mp hp).2 j⟩
 exact mem_image.mpr ⟨_,own_add t hv,(map_add _ j b).trans (by unfold b; rw [wrap_lift]; change a+(i-a)=i; abel)⟩
lemma own_walk (h:x∈ estate p q)(v:Walk)(t:o∈ visits x v): o∈estate (p+v.length) (q+v.length):=by
 induction v generalizing x p q o with
 | nil=> exact List.mem_singleton.mp t|>.symm ▸ h
 | cons a v ih=>
   rcases List.mem_cons.mp t with f|t; exact f ▸ ownM (Nat.le_add_right ..) (Nat.le_add_right ..) h; have he:x+a.vec∈estate (p+1) (q+1):= own_add h (by apply (own _).mpr; intro j; unfold zoneL; rw [ite_self, Nat.cast_one]; rw [Step.vec]; split <;> simp [Pi.neg_apply,step_apply] <;> split <;> omega); rw [List.length_cons,←add_assoc, add_right_comm, ←add_assoc q,add_right_comm q]; exact ih he t
lemma axis_travel (a b:Cover)(i): i ∈ visits a (route a b 1) → BetweenY a i b:= by
 intro t; have h:= way_visit a a b (allAxes (1:Lattice.Order)) ((List.nodup_finRange _).map (1:Lattice.Order).injective) i t; change BetweenY a i (stop a (route a b 1)) at h; rwa [route_end] at h
lemma convexTown(h:a∈ estate p q)(t:b∈estate p q)(x:BetweenY a o b): o∈estate p q:=by
 refine (own _).mpr fun i=>?_ ; have hu := (own _|>.mp h) i; have he := (own _|>.mp t) i; exact ⟨(le_min hu.1 he.1).trans (x.left i), (x.right i).trans (max_le hu.2 he.2)⟩
lemma payDeed : ∀ i:Axis,∃ t:ℤ,∀ x∈ estate (boardθ r d J) (boardU p d J), t≤x i∧ x i≤ t+ Deed p r d J i:=by
 intro i; refine ⟨-zoneL (boardθ r d J) (boardU p d J) i,fun x t=>?_⟩; have he:= (own _|>.mp t) i; unfold Deed zoneL at *; split_ifs at * <;> omega
-- positive & neg halves clipped. estate p q. floor choice l=reserve+1 for matter both; lane limit `ℓ=reserve+1` can reflect wrt 0. `0<l`. q width unaffected.
variable (b0:Bool)(l:ℕ)
def stagePr (p q l:ℕ)(b0:Bool) : Finset Cover:= (estate p q).filter fun i=> if b0 then (l:ℤ) ≤ i 3 else i 3 ≤ -(l:ℤ)
lemma aheadPop : Ahead 3 0 l (stagePr p q l true) := by intro x y; simpa [stagePr] using (show ((l:ℤ) ≤ x 3) from (by simpa using (mem_filter.mp y).2)) -- tune
lemma refS : Ahead 3 0 l (refract 3 0 (stagePr p q l false)):=by
 intro x y; obtain ⟨x,p',rfl⟩:=mem_image.mp y; have he:= (show x 3 ≤ -(l:ℤ) from by simpa using (mem_filter.mp p').2); rw [zero_add, fling_move,if_pos rfl]; omega
lemma stage_disj (v:0<l) : Disjoint (stagePr p q l false) (stagePr p q l true):=by
 refine Finset.disjoint_left.mpr fun i h p=>?_ ; have he:=(show i 3≤-(l:ℤ) from by simpa using (mem_filter.mp h).2); have hp:=(show (l:ℤ) ≤ i 3 from by simpa using (mem_filter.mp p).2); omega
lemma floor₃ (t:BetweenY a o b)(u:a∈stagePr p q l b0)(v:b∈stagePr p q l b0): o∈stagePr p q l b0:=by
 refine mem_filter.mpr ⟨convexTown ((mem_filter.mp u).1) ((mem_filter.mp v).1) t,?_⟩; have ht:=t.left (3:Axis); have hh:= t.right (3:Axis); obtain ⟨a,b⟩:= mem_filter.mp u; obtain ⟨p,q⟩:=mem_filter.mp v; cases b0 <;> simp only [Bool.false_eq_true, ↓reduceIte] at * <;> omega
-- chart using order. arbitrary roots.Price orientation exact. L->R. need H. BENT (branch) chart.
abbrev pegT (l:ℕ)(b0:Bool):Cover:= fun i=> if i=3 then if b0 then l else -(l:ℤ) else 0
lemma pegT_here (e:l≤p): pegT l b0∈ stagePr p q l b0:=by
 refine mem_filter.mpr ⟨?_,?_⟩
 · apply (own _).mpr; intro i; unfold pegT zoneL; by_cases t:i=3 <;> cases b0 <;> simp only [t, ↓reduceIte, Bool.false_eq_true] <;> omega
 unfold pegT; cases b0 <;> simp
def limbP (o:Cover): Chart o where
 τ i:= route o i 1
 endsT i:= route_end ..
lemma limbR (e:o∈stagePr p q l b0): Chart.Hires (stagePr p q l b0) (stagePr p q l b0) o (limbP o):= fun i t x v=> floor₃ b0 l (axis_travel o i x (List.mem_toFinset.mp v)) e t
local notation "Y"=> stagePr p q l false
local notation "Φ"=> stagePr p q l true
local notation "yL"=> pegT l false
local notation "yR"=> pegT l true
def Line (p q:ℕ)(l:ℕ): Chart (pegT l true) where
 τ i:= if i∈stagePr p q l false then route (pegT l true) (pegT l false) 1++(limbP (pegT l false)).τ i else route (pegT l true) i 1
 endsT x:=by split <;> simp [stop_append,route_end,limbP]
private lemma backer (P:a∈estate p q)(Q:b∈estate p q)(x:Cover)(h:x∈ visits a (route a b 1)): x∈estate p q:=convexTown P Q (axis_travel a b x h)
variable {u v:ℕ}
lemma Line_area (e:l≤ p)(u0:p≤u)(v0:q≤v): Chart.Hires (estate u v) (estate u v) (pegT l true) (Line p q l):=by
 intro i h x t; let g:= limbP; have hx:= List.mem_toFinset.mp t; change x∈visits yR (if i∈Y then _ else _) at hx; have hP(b):pegT l b∈estate u v:=ownM u0 v0 ((mem_filter.mp (pegT_here (q:=q) b l e)).1); split at hx; next v =>
    rcases append_visit hx with p|p; exact backer (hP true) (hP false) x p
    rw [route_end] at p; exact backer (hP false) h x p
 next v=> exact backer (hP true) h x hx
section
variable {T:Finset Cover} (p₀:Hosp T N)(q₀:estate p q⊆ T)
local notation "L"=> region (stagePr p q l false) N
local notation "R"=> region (stagePr p q l true) N
-- Frame proof. F₀.Own.
open Window.Mirage
variable (t:0<l)(e:l≤p)
abbrev cornerD(b:Bool):= Chart.passH (limbP (pegT l b)) p₀ (show stagePr p q l b⊆T from fun i z=> q₀ ((mem_filter.mp z).1)) (limbR b l (pegT_here b l e)) -- U ambiguous same
-- Line.Extend.Pith.
include t
lemma CurveF (Q:Chart.Hires (estate p q) T (pegT l true) (Line p q l)) : Mirage.Frame (cornerD N l p₀ q₀ e false) (cornerD N l p₀ q₀ e true) (Chart.passH (Line p q l) p₀ q₀ Q):=by
 constructor
 · intro a; let k:= travel (onC N a) yR (route yR yL 1); refine ⟨k,fun i h=>?_⟩; have h0: Chart.legH N T i∈ stagePr p q l false:=by obtain ⟨x,u,rfl⟩:=mem_image.mp (show i∈ L from h); rw [Chart.leg_on p₀ x (q₀ ((mem_filter.mp u).1))]; exact u
   unfold cornerD Chart.passH Chart.tenor Chart.rootF Line; dsimp only; rw [if_pos h0, travel_append,route_end]; rfl
 intro a x h; have hy:Chart.legH N T x∉stagePr p q l false:=by obtain ⟨x,u,rfl⟩:=mem_image.mp (show x∈ R from h); rw [Chart.leg_on p₀ x (q₀ ((mem_filter.mp u).1))]; exact fun e=> Finset.disjoint_left.mp (stage_disj l t) e u
 unfold cornerD Chart.passH Chart.tenor Chart.rootF Line; dsimp only; rw [if_neg hy]; rfl
end
end geometry
end Chaperone
end YM.CF.Buffered.Afterglow.Hierarchy.Quest
