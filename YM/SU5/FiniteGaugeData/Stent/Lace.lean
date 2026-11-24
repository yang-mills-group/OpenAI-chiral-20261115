import YM.SU5.FiniteGaugeData.Stent.Minna
import YM.CF.Cubes.Inside
set_option maxHeartbeats 380000
set_option synthInstance.maxSize 20000
noncomputable section
namespace YM.CF.Buffered.Stent
set_option linter.unusedSimpArgs false
open Function Filter Finset Lattice Laurent Fir Next.Free Bloch Lat Fock Rush Scroll MeasureTheory RG
open scoped Topology BigOperators Pointwise Matrix Matrix.Norms.L2Operator MatrixOrder InnerProductSpace Kronecker ENNReal
attribute [local instance] opCStarAlgebra
variable (R:Patch)
set_option quotPrecheck false
local notation "Λ"=> R.L
local notation "J"=> R.J
open Cube Stencil Tenant Tap Tulip Branch Spire Peaks Advance Skye Lifted CF.Stent
variable {x:Cover}
open SU -- More.E
set_option autoImplicit false
open scoped Classical
open Afterglow Afterglow.Hierarchy Satin Hierarchy.Quest Wilson Next.Rank Tree Precision Push.SectorMeasure Next.SectorChange
-- geometry.e=Δ
variable {L N P:Side}(G:Ratio N P) (e: Odd G.count.val)
abbrev fieldQ(L:Side):=scape (zeroL L) (L.val/2)
abbrev bedfield (L:Side)(L':ℕ) :=carpetB (zeroL L) (L.val/2) L'
local notation "Q"=> fieldQ G.count
local notation "F"=> region Q P
local notation "g"=> ratio G
local notation "W"=> node (0:Site N)
include e
lemma parentF(x:Seat P): x∈ region (fieldQ G.count) P ↔ (ratio G).parent x=node (0:Site N) :=by
 let Y:= zeroL G.count; constructor
 · intro h; obtain ⟨x,a,rfl⟩:=mem_image.mp h; obtain ⟨u,p,rfl⟩:=mem_image.mp (show x∈ fieldQ G.count from a); change (ratio G).parent (wrap (More P) (u+Y))=_; rw [map_add,← Launch G];
   rw [show wrap (More P) u+(ratio G).embed W=(ratio G).assemble (W, wrap (ratio G).count u) from ?_]; · exact (ratio G).assemble_parent _
   rw [Ratio.assemble]; dsimp only; rw [Ratio.half_lift (ratio G) e u p,add_comm]; -- ok
 intro h; let v:= lift ((ratio G).residue x); refine mem_image.mpr ⟨_,mem_image_of_mem (fun w=>w+Y) ((ratio G).half_box e ((ratio G).residue x)),?_⟩; rw [map_add,← Launch G,←h, add_comm, Ratio.unpack_at]; -- tuning block size (ratio G).def
abbrev Blok (L:Side)(P:Side): Finset (Seat P):= region (fieldQ L) P
local notation "Fₖ"=> Blok G.count P
lemma home(h:4≤G.count.val): nodeC (specialM G.count)∈ fieldQ G.count:= by rw [forward _ e]; rw [sap]; rw [add_comm (zeroL _),add_sub_cancel_right]; unfold rune; apply box_test.mpr; constructor <;> intro j <;> by_cases p:j=0 <;> by_cases t:j=1 <;> simp [p,t] <;> omega
lemma forge (h:4≤G.count.val)(o:Lattice.Order) : (visits (nodeC (specialM G.count)) (growAge o)).toFinset⊆ fieldQ G.count:=by
 intro x p; let L:= G.count; let v:= nodeC (specialM L); let y:= zeroL L; let X:=growAge o; have hp:v∈ fieldQ L:= home G e h; have he:= way_visit v 0 (-(2•rune)) (allAxes o) ((List.nodup_finRange _).map o.injective) x (List.mem_toFinset.mp p); change BetweenY v x (stop v X) at he; rw [show stop v X=y from tail L o e] at he; have hv:= sap_here y (L.val/2); refine sap_box.mpr (fun i=>?_); exact ⟨(le_min (sap_box.mp hp i).1 (sap_box.mp hv i).1).trans (he.left i), (he.right i).trans (max_le (sap_box.mp hp i).2 (sap_box.mp hv i).2)⟩
-- particular patch equality, including any forests. ν_E.C
section
local notation "c₁" x:max=> SU.group.chord x
variable (X:Forest (ratio G))(U:Pane P){r:ℝ}(p:0≤r)
abbrev bedfare (L:Side)(P:Side)(t:ℝ)(U:Pane P):Prop:=∀ i:Edge (Seat P),i.1∈ Blok L P→i.1+step i.2∈ Blok L P→ SU.group.chord (U i) ≤ t
include e
private lemma wake (x:Seat P)(u:x∈F)(y:Seat P)(v:y∈visits x (X.hike x)): y∈F:=by
 induction x using Forest.hike.induct X with
 | case1 i hi ih=>rw [Forest.hike,dif_pos hi] at v; rcases List.mem_cons.mp v with rfl|v; · exact u
                  exact ih ((parentF G e _).mpr ((X.stays i hi).trans ((parentF G e i).1 u))) v
 | case2 i hi=>rw [Forest.hike,dif_neg hi,visits] at v; exact List.mem_singleton.mp v ▸ u
omit e in
private lemma moneyP (R:Walk)(S:Support (More P))(x:Seat P)(h:(visits x R).toFinset ⊆ S)(e:∀ i:Edge (Seat P),i.1∈S→i.1+step i.2∈S→ c₁ (U i) ≤ r): c₁ (travel U x R) ≤ R.length*r:=by
 induction R generalizing x with
 | nil=>rw [travel,Gauge.chord_one]; simp
 | cons i l ih=>
    change (x::visits (x+i.vec) l).toFinset⊆ S at h; rw [List.toFinset_cons] at h; obtain ⟨he,h⟩:= insert_subset_iff.mp h
    rw [travel]; apply (Gauge.chord_triangle ..).trans; refine (add_le_add (show c₁ (i.read U x)≤ r from ?_) (ih _ h)).trans_eq (by rw [List.length_cons,Nat.cast_add,Nat.cast_one]; ring); have hv:x+i.vec∈S:= h (List.mem_toFinset.mpr (by cases l<;> simp [visits])); rcases i with ⟨i,u⟩; cases u; exact e (x,i) he hv; change SU.group.chord (U (x-step i,i))⁻¹≤r; rw [Gauge.chord_inv]; refine e _ (by simpa only [sub_eq_add_neg,Step.vec,ite_true] using hv) ?_; rw [show x-step i+step i=x from sub_add_cancel ..]; exact he
include p
private lemma ploy (h: bedfare G.count P r U)(i:Edge (Seat P))(he:i.1∈F)(hv:i.1+step i.2∈ F): SU.group.chord (gauge (X.foldAt U) U i) ≤ (8*G.count.val+1:ℝ)*r:=by
 let W':= gauge (X.foldAt U) U; have hh(x:Seat P)(t:x∈ F): SU.group.chord (X.foldAt U x) ≤ (4*G.count.val:ℕ)*r:=by
    unfold Forest.foldAt; rw [Gauge.chord_inv]; refine (moneyP U _ F x (fun y q=>wake G e X x t y (List.mem_toFinset.mp q)) h).trans (mul_le_mul_of_nonneg_right ?_ p); exact_mod_cast ((X.hike_lower x).trans (X.bound x))
 let B:= SU.group.chord; let i':=i.1+step i.2; let x:=X.foldAt U i.1*U i; let y:=X.foldAt U i'; refine (Gauge.chord_triangle SU.group x y⁻¹).trans (le_trans (add_le_add ((Gauge.chord_triangle ..).trans (add_le_add (hh _ he) (h i he hv))) ((Gauge.chord_inv SU.group y).le.trans (hh _ hv))) ?_); push_cast; nlinarith -- tune
omit p
variable (u:Chi)(d:ℝ)
variable (k:Spindle.Rules SU.group)(hz:0<d)(hm:d<firstRadius SU.group)
include p
include hz hm
private lemma sheep (h:bedfare G.count P r U)(V: Pane N)(a: (8*G.count.val+1:ℝ)*r≤ min k.c (d/2)): Agrees (region (fieldQ G.count) P) (seine G X u d U V) U:=by
 intro i v w; let x:= gauge (X.foldAt U) U i; have he:= (ploy G e X U p h i v w).trans a; have h0 : c₁ x≤k.c:= he.trans (min_le_left ..)
 have ha:portU G X u d U V i=x:=by
    change knit u d x _=x; rw [show Precision.replica g V i=1 from if_pos ((parentF G e _ |>.mp w).trans (parentF G e _|>.mp v).symm)]; refine knitHere u d _ _ hz hm ⟨SU.group.plog (SU.group.mat x),?_,?_⟩; · apply (k.sleeve x h0).trans; have ht:= he.trans (min_le_right ..); change c₁ x≤ _ at ht; linarith
    rw [mul_one, k.records x h0]
 unfold seine Lattice.gauge; rw [ha]; unfold x Lattice.gauge; simp only [Pi.inv_apply]; group -- tune group
omit p
lemma stove (t:ℝ)(p:0<t)(V: Pane N)(j:ℕ)(h':2*(G.count.val/2+1)< (More P).val)(a: (8*G.count.val+1:ℝ)*((4*(G.count.val/2:ℕ):ℝ)*(2*t))≤ min k.c (d/2))(h: bedH (bedfield G.count j) t (onC P U)≠0): Agrees Fₖ (seine G X u d U V) U:=by
 let y₀:= zeroL G.count; let o:= wrap (More P) y₀; let x:= Spindle.fingers (G:=SU.group) U o; let φ:=Spindle.spine (G:=SU.group) U o; let n₀:= G.count.val/2; let r:ℝ:= (4*(n₀:ℝ))*(2*t); have h'₁: bedfare G.count P r φ:=by
    intro i s v; unfold Blok fieldQ at s v; rw [spindle_PATCH] at s v; exact sap_fare t y₀ n₀ j P p h' U h ⟨i,mem_filter.mpr ⟨mem_univ _,s,v⟩⟩ -- signature s implicit?
 let Ω:= seine G X u d U V; intro i s v; let z:= sheep G e X φ (show 0≤r by unfold r; positivity) u d k hz hm h'₁ (gauge (scaleG G x) V) a; have he:gauge x Ω i=gauge x U i:=by unfold Ω; rw [←brake_g G u d X e U V x]; exact z i s v
 unfold Lattice.gauge at he; exact mul_left_cancel (mul_right_cancel he)
include hz hm
lemma Loire(t:ℝ)(p:0<t)(V:Pane N)(j:ℕ)(h':2*(G.count.val/2+1)<(More P).val)(a:(8*G.count.val+1:ℝ)*((4*(G.count.val/2:ℕ):ℝ)*(2*t))≤ min k.c (d/2))(w:bedH (bedfield G.count j) t (onC P U) ≠0)(q₀:G.count=R.L)(L:4≤G.count.val):Louvre R (onC P (seine G X u d U V))= Louvre R (onC P U):=by
 let H:= seine G X u d U V; let C:= onC P; have hv: Agrees F H U:= stove G e X U u d k hz hm t p V j h' a w; unfold Louvre Shadow; apply congrArg _; refine sum_congr rfl (fun x _=>?_); -- copy def
 rw [← q₀,show travel (C H) _ (growAge x)= _ from (travel_local (nodeC (specialM G.count)) (growAge x) (C H) (C U) (fun i h k=> on_agree P hv i (forge G e L x (List.mem_toFinset.mpr h)) (forge G e L x (List.mem_toFinset.mpr k))))] -- implicit
#print axioms Loire
end
end YM.CF.Buffered.Stent
