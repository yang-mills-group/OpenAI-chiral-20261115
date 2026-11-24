import YM.SU5.Selected.Lantern.Therm
import YM.SU5.FiniteGaugeData.Pannier.FoyerSeat
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 450000
set_option maxRecDepth 3000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Pannier.Chancel.Lantern
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye RG
open Crest.Airy
open Reed (Fine)
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
namespace Bulb
open Work.E08
-- Geometry integer frames. dedicated to rotation-invariant time positive. Gauge-scale box coordinates, not wrap widths. Give safe generic $enough() instances explicitly.
def plant (k:ℕ)(a:Cover):Finset Cover:= Finset.Icc (a+(fun _=>-(k:ℤ))) (a+fun _=> (k:ℤ))
variable {K n:ℕ}{x p:Cover}
lemma plant_test : x∈plant K p ↔ x-p∈ box K:= by
 rw [plant, Finset.mem_Icc,box_test]; constructor
 · rintro ⟨u,v⟩; exact ⟨fun i=>by specialize u i; simp only [Pi.sub_apply,Pi.add_apply] at *; omega,fun i=> by specialize v i; simp only [Pi.add_apply,Pi.sub_apply] at *; omega⟩ -- boxed implicit
 rintro ⟨u,v⟩; exact ⟨fun i=>by specialize u i; simp only [Pi.sub_apply, Pi.add_apply] at *; omega,fun i=>by specialize v i; simp only [Pi.sub_apply, Pi.add_apply] at *; omega⟩
lemma from_plant {K L:ℕ}(p:Cover) (h:K≤L): plant K p ⊆ plant L p:= by
 unfold plant; apply Finset.Icc_subset_Icc; · intro i; change _+_ ≤ p i+ _; push_cast; omega
 intro i; change _+_ ≤ p i+_; push_cast; omega
lemma plant_id (K:ℕ)(p:Cover):p∈plant K p:=plant_test.mpr (by simp)
variable {N:Side} {S T:Finset Cover}{s:ℤ} (a:Axis)
local notation "PN" => More N
-- all supported evaluated on exactly More count. Avoid conflict with `Tower.region/Satin.region`.
abbrev park (N:Side)(S:Finset Cover):Finset (Seat N):= S.image (wrap (More N))
def gleams (S:Finset Cover)(a:Axis):= S.image ((plane a 0).motion) = S
lemma motion_home (a:Axis) (x:Cover)(p:x a=0): (plane a 0).motion x=x:=funext fun i=> by by_cases z:i=a <;> simp_all [fling_move,eq_comm (a:=a) (b:=i)]
lemma motion_inv (a:Axis): Involutive (plane a 0).motion:= fun x=> funext fun i=>by by_cases t:a=i <;> simp [fling_move,t]
lemma GleamHome (S:Finset Cover) (a:Axis)(h:∀ x∈ S,(plane a 0).motion x∈ S): gleams S a:= by unfold gleams; ext x; rw [mem_image]; constructor; rintro ⟨w,q,rfl⟩; exact h _ q; exact fun u=> ⟨_,h _ u,motion_inv a x⟩
lemma gleam_plant (K:ℕ)(p:Cover)(a:Axis)(h:p a=0): gleams (plant K p) a:= by
 apply GleamHome; intro x u; obtain ⟨t,v⟩:= box_test.mp (plant_test.mp u); refine plant_test.mpr (box_test.mpr ⟨?_,?_⟩); all_goals intro i; specialize t i; specialize v i; simp only [Pi.sub_apply,fling_move] at *; split_ifs <;> (first| (subst a; omega)|omega)
lemma park_shimmer(v:{S:Finset Cover // gleams S a}): hyphen a (0:ℤ) (park N v.val)=park N v.val:= by
 let f:= (plane a 0).motion; let u:=(plane a 0).anon N; let g:=wrap (More N); let S:=v.val; have t:u ∘ g=g ∘ f:=funext fun _=>Shape.anno ..
 change Finset.image u (Finset.image g S)= _; rw [Finset.image_image,t, ←image_image, show S.image f= S from v.property]
lemma park_plant (B:ℕ)(p:Cover) (N:Side): park N (plant B p)=BlockP B (wrap (More N) p):=by
 ext x; let a:=wrap (More N) p; rw [park,mem_image,blocks_test]; constructor; rintro ⟨y,t,rfl⟩; have he:= separation_box_add a (plant_test.mp t); rw [map_sub, show _ - _+a= _ from (sub_add_cancel ..)] at he; exact he
 intro ht; let w:=Lattice.lift (x-a); have hx:w∈ box B:= lift_mem_box ht; refine ⟨w+p,plant_test.mpr (by rwa [add_sub_cancel_right]),?_⟩; unfold w; rw [map_add,wrap_lift]; exact sub_add_cancel ..

-- can use `centered injectivity` via exponent side bound
lemma lift_at {S:Side}(x:Cover)(h:∀ i, (x i).natAbs * 2 < S.val) : Lattice.lift (wrap S x) = x:=lift_eq_iff.mpr ⟨rfl,fun i=>by specialize h i; omega⟩
lemma lift_rad{S:Side}(p x:Cover) (h:x∈plant K p) (u:2*K<S.val) : Lattice.lift (wrap S x - wrap S p)= x-p:=by rw [←map_sub]; obtain ⟨t,v⟩:=box_test.mp (plant_test.mp h); refine lift_at _ (fun i=> ?_); specialize t i; specialize v i; omega
lemma sober_park (S:Side) (K:ℕ)(p:Cover)(h: 2*K<S.val): Set.InjOn (wrap S) ↑(plant K p):=by intro x u y v e; apply sub_left_injective (b:=p); change x-p=y-p; rw [←lift_rad p x u h,←lift_rad p y v h,e] -- adjust
lemma land_apart (K:ℕ)(p:Cover)(h:2*K<(More N).val)(u:S⊆ plant K p)(v:T⊆ plant K p)(d:Disjoint S T): Disjoint (park N S) (park N T):=by
 apply disjoint_left.mpr; intro i x y; obtain ⟨t,p,rfl⟩:= mem_image.mp x; obtain ⟨w,x,t'⟩:= mem_image.mp y; exact disjoint_left.mp d ((sober_park _ K _ h (v x) (u p) t').symm ▸ p) x -- orient
lemma lift_both {S:Side}(x y p:Cover)(u:x∈plant K p)(v:y∈plant K p)(t:4*K<S.val):Lattice.lift (wrap S x -wrap S y)= x-y:=by
 rw [←map_sub]; obtain ⟨a,b⟩:=box_test.mp (plant_test.mp u); obtain ⟨c,d⟩:=box_test.mp (plant_test.mp v); apply lift_at; intro i; specialize a i; specialize b i; specialize c i; specialize d i; simp only [Pi.sub_apply] at *; omega
variable (K L:ℕ)
lemma farther (p: K + n ≤ L)(x:Seat N) : Distant n ((BlockP L x)ᶜ) (BlockP K x):=by
 intro a u b v; have g: ¬ separation x a≤ L:= fun t=> mem_compl.mp u (blocks_test.mpr t); have h:=blocks_test.mp v; rw [separation_comm]; have t:=separation_triangle x b a; omega
lemma park_halo (p: K+n ≤ L) (x:Seat N) : Lattice.halo n (BlockP K x) ⊆ BlockP L x:=by
 intro b v; obtain ⟨a,u,t⟩:= halo_spec.mp v; apply blocks_test.mpr; exact (separation_triangle _ _ _).trans ((add_le_add (blocks_test.mp u) t).trans p)
-- dress key supports: Walk stays in rectangle for enough periods. interface Icc of restricted width K. use lifts. 
lemma walk_park (x y p a b:Cover)(P:Finset.Icc a b ⊆ plant K p)(u:x ∈ Finset.Icc a b)(v:y∈Finset.Icc a b)(h:4*K<(PN).val)
      (z:Seat N)(g:z∈visits (wrap PN x) (march (wrap PN x) (wrap PN y) 1)):z∈ park N (Finset.Icc a b):=by
 let t:= wrap PN x; let t':= wrap PN y; obtain ⟨c,hc,e⟩:= march_visit t t' 1 _ g; unfold t t' at *; rw [lift_both (K:=K) y x p (P v) (P u) h] at e; rw [hc, ← map_add]; obtain ⟨i,j⟩:= mem_Icc.mp u; obtain ⟨f,g⟩:= mem_Icc.mp v; apply mem_image_of_mem; refine mem_Icc.mpr ⟨fun s=>?_,fun s=>?_⟩
 · have he:=e.left s; change min 0 (y s-x s) ≤ c s at he; have ff: a s ≤ x s:= i s; have ii:a s ≤ y s:= f s; rw [Pi.add_apply]; change a s≤ x s+c s; omega
 have he:=e.right s; change c s ≤ max 0 (y s-x s) at he; have ff: x s≤ b s:= j s; have ii:y s ≤ b s:= g s; rw [Pi.add_apply]; change x s+c s ≤ b s; omega
lemma march_budget (x y p:Cover)(u:x∈plant K p)(v:y∈plant K p): (march (wrap PN x) (wrap PN y) 1).length ≤ 4*(K+K):=by
 apply march_len; apply (separation_triangle _ (wrap PN p) _).trans; refine add_le_add ?_ ?_; · rw [separation_comm]; apply blocks_test.mp; rw [←park_plant]; exact mem_image_of_mem _ v
 apply blocks_test.mp; rw [←park_plant]; exact mem_image_of_mem _ u
end Bulb
end YM.CF.Pannier.Chancel.Lantern
open YM.CF.Pannier.Chancel.Lantern.Bulb
#print axioms walk_park
