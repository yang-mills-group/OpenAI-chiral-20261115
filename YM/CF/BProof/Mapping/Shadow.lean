import YM.CF.BProof.Mapping.Look
import YM.CF.BProof.Mapping.Budget

/- short reach micro terms without extension depth. Tug patch in one gap. support
 radius and count in blocks at PL-choice. also when normal tag arrays attached. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Mapping.House
open Function RG Wilson Lattice Filter MeasureTheory SU Grid Angular Angular.Yard Finset Prox Gauss Release Release.hot Moment Push.AbsoluteSums Micro
open scoped Topology BigOperators Classical
variable {s c: Side}(Y:Yard s)(g:Ratio c s) (i:Y.Index)(X:Finset (Block Y c))(a b:Block Y c)(r:ℕ)

/- horizon patches within same gap. -/
def ray := (Bed Y c).ball a r |>.filter (fun x=> House.one Y x= House.one Y a)
lemma ray_cast : ray Y a r=(Grid.collar ({House.two Y a}:Finset (Space c)) r).image (place Y (one Y a)):=by
 let k:=one Y a; let t:=two Y a; ext x; simp only [ray,mem_filter, (Bed Y c).ball_m a x r]; refine ⟨fun ⟨v,h⟩=>?_,fun p=>?_⟩
 · exact mem_image.mpr ⟨two Y x,Grid.collar_mem.mpr ⟨_,mem_singleton_self _,Grid.dist_symm .. ▸ ((House.clock Y a x r).1 v).2⟩, h ▸ place_house Y x⟩
 obtain ⟨x,h,rfl⟩:= mem_image.mp p; replace h : Grid.dist x (two Y a) ≤ r:=by simpa using h
 refine ⟨?_,rfl⟩; change Grid.dist a _≤_; rw [clock]; simp only [one_place,two_place]; exact ⟨by unfold Circle.δ; simp [Cube.d_id],(Grid.dist_symm ..).trans_le h⟩
lemma ray_spec : b∈ ray Y a r↔ Grid.dist a b≤ r ∧ one Y b=one Y a:=by unfold ray; simp only [mem_filter, (Bed Y c).ball_m]; rfl
lemma ray_home : a∈ ray Y a r:= mem_filter.mpr ⟨Prox.Base.resides ..,rfl⟩
lemma ray_n : Conn (ray Y a r) 1:=by rw [ray_cast]; apply trail (place Y (one Y a)) _ _ (Prox.collar_solid r _); intro x y h; rw [dist_two]; exact h
lemma ray_pay : (ray Y a r).card ≤ fourBill r:=(card_le_card (Finset.filter_subset ..)).trans ((Bed Y c).size ..)
lemma ray_in {x:Block Y c}{t:ℕ}(v:t≤r) : ray Y x t⊆ ray Y x r:=fun y hy=> (ray_spec ..).2 (by obtain ⟨a,b⟩:=(ray_spec ..).1 hy; exact ⟨a.trans v,b⟩)
lemma ray_loan {a:Y.Col}{k:ℕ} (p:k≤r*g.count.val)(v:ray Y (hide Y g a) r⊆ X): Pawn.Shade g X a k:= Pawn.block_read g X a r p fun i hi g' => v ((ray_spec ..).2 ⟨g',hi⟩) -- order b vs a? check
lemma lens_cap (o:Block Y c): (univ.filter fun i=> o∈ ray Y (hide Y g i) r).card ≤ fourBill r*g.count.val^3:=by
 let T:=ray Y o r; let X(a:Block Y c):=univ.filter fun i=>hide Y g i=a
 apply le_trans (card_le_card (t:=T.biUnion X) (fun i (hi:i∈ _) =>?_)); apply le_trans card_biUnion_le; apply le_trans (sum_le_sum (fun i _=> height Y g _)); rw [sum_const,nsmul_eq_mul]; exact Nat.mul_le_mul_right _ (ray_pay ..)
 obtain ⟨a,b⟩:= (ray_spec ..).1 (mem_filter.mp hi).2; exact mem_biUnion.mpr ⟨_,(ray_spec ..).2 ⟨(Grid.dist_symm ..).trans_le a,b.symm⟩,mem_filter.mpr ⟨mem_univ _,rfl⟩⟩
abbrev ply (t r:ℕ)(α:ℝ):= ((fourBill r*t^3:ℕ):ℝ)*Real.exp (α*fourBill r)
lemma banner (A:Y.Col→ℝ)(d C:ℝ)(h:∀ i, 0≤A i∧ A i≤C)(t:0≤d): Toll (fun a=> ray Y (hide Y g a) r) A d (ply g.count.val r d*C):=by
 have hp: 0≤C:= (h (0,0)).1.trans (h (0,0)).2; let z:=Real.exp (d*fourBill r)*C; refine ⟨fun i=>(h i).1,fun i=> budget_finite (fun a=> ?_) ?_⟩
 · unfold hit; split; exact mul_nonneg (Real.exp_pos _).le (h _).1; exact le_rfl
 apply le_trans (b:=∑ b with i ∈ ray Y (hide Y g b) r,z) _; rw [sum_const,nsmul_eq_mul, show ply g.count.val r d*C=_ from mul_assoc _ _ C]; apply mul_le_mul_of_nonneg_right _ (by unfold z; positivity); exact_mod_cast lens_cap Y g r i -- order
 rw [sum_filter]; apply sum_le_sum; intro a ha; by_cases θ:i∈ray Y (hide Y g a) r; unfold hit; rw [if_pos θ,if_pos θ]; dsimp only; unfold z; refine mul_le_mul (Real.exp_monotone ?_) (h a).2 (h a).1 (Real.exp_pos _).le; gcongr; exact ray_pay ..; unfold hit; rw [if_neg θ,if_neg θ]
end YM.CF.BProof.Mapping.House

namespace YM.CF.BProof.Mapping.Pawn
open Function RG Wilson Lattice Filter MeasureTheory SU Grid Angular Angular.Yard Finset Prox House Gauss Release Release.hot Moment Push.AbsoluteSums Micro
open scoped Topology BigOperators Classical
local notation "G"=> SU.group
variable {s c: Side}{Y:Yard s}(g:Ratio c s)(S:Hall s)(x y: Pawn Y)(Z: Finset (Block Y c))(z:ℝ)(T:PathData G){R:ℝ}{c':Clip}{M:ℕ}(θ:ℝ)(U:Beam c' R Y.short M z)(h:Charge.Room Y M)(u:Agreed g x y Z)
variable (hx:Certified S x z T θ U)(hy:Certified S y z T θ U)
include h u hx hy
-- micro-near reading. r<2D. No other expenses.
lemma chops {t:ℕ}(a: Site s){i:Y.Index}(v:Y.Vic i t (time a))(p:t<2*Deep.D Y)(b:Bond s)(e:b.1=a)(g':Pawn.Shade g Z (i,space a) U.horizon') :
 put S x z T θ U b=put S y z T θ U b:= by
 have ht := Deep.D_le Y; have hh:2*t+1<Y.long:=by omega
 have hv: House.col Y b.1=(i,space a):=by unfold House.col; rw [e, Posts.vic Y i (time a) hh v]
 rw [←hv] at g'; by_cases l:b∈Y.rent; swap; · exact granted g S x y Z z T θ U h u b l g'
 obtain ⟨j,l⟩:= Y.rents.mp l; by_cases k:Y.D j; exact readsD g S x y Z z T θ U u b j k l (shade g Z _ _ g'); exact reads_safe g S x y Z z T θ U h u b l k (fun hp=> Deep.height Y (2*Deep.D Y) j t (e ▸ hp) p (by omega) v) g' hx hy

lemma detect {r k:ℕ}(a:Site s){i:Y.Index}(p:Y.Vic i r (time a))(v:k+r<2*Deep.D Y)(b:Bond s)(e:separation a b.1 ≤ k)(g':Pawn.Shade g Z (i,space a) (k+U.horizon')):
 put S x z T θ U b=put S y z T θ U b:=by
 apply chops g S x y Z z T θ U h u hx hy b.1 (Y.vic_trans i r _ _ k p ((time_jump _ _).trans e)) (by omega) b rfl; apply shade_rides g Z g'; exact ⟨rfl,Grid.dist_le.mpr (fun i=>Grid.dist_le.mp e i.succ)⟩
end YM.CF.BProof.Mapping.Pawn
