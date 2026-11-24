import YM.CF.DPress.Chess.Floor.Cross
import YM.CF.DPress.Chess.Planes.Rock
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.DPress.Wagon
open Function Filter Lattice RG Wilson MeasureTheory Skye Rush Spire Scree Tulip
open Fock Finset Scroll SU Lat Cube Phase Branch BPress Chess
open scoped Topology BigOperators Pointwise Classical ENNReal NNReal ComplexOrder Matrix.Norms.L2Operator Kronecker YM.CF.BPress
attribute [local instance] opCStarAlgebra
variable {n L:Side}
/-!
 doubling-the-gap geometry. We can use positive and negative periods parameters at any seam; address by grid tick, runtime in those units.
 `Word := List` descriptors later. -/
structure Race (n L:Side) where
 η:ℕ
 i:Axis -- time axis
 height: L.val*η=n.val
 grip: ℕ -- seam gap on this level in gauge coordinates, >0
 hp: 0<grip
namespace Race
variable (T:Race n L)
abbrev wall(a:ℤ):Wall:=⟨T.i,(L.val:ℤ)*a⟩
lemma aligned(a:ℤ):(T.wall a).aligned L:=⟨a,rfl⟩
local notation "δ_"=> Wall.len L
abbrev S_(a b:ℤ):Support (More n):= univ.filter fun i=> ∃ x:ℤ,i T.i=(x:Per _)∧ Wall.len L * a + T.grip ≤ x ∧ x + T.grip ≤ Wall.len L*b
lemma S_i(a b:ℤ)(i:Seat n) : i∈ T.S_ a b ↔∃ x:ℤ,i T.i=(x:Per _)∧ Wall.len L * a + T.grip ≤ x ∧ x + T.grip ≤ Wall.len L*b:=by rw [S_,mem_filter]; exact and_iff_right (mem_univ _)
include T
lemma rise : (δ_) * T.η = (More n).val:=by change 2*(L.val:ℤ) * _= (↑(n.val*2):ℤ); push_cast; rw [mul_assoc,show (L.val:ℤ)*(T.η:ℤ)=n.val from Nat.cast_mul ..|>.symm.trans (congrArg (Nat.cast (R:=ℤ)) T.height)]; ring -- tune
lemma height_p : 0 < T.η := by have h:= T.height; have p:n.val>0:= n.property; apply Nat.pos_iff_ne_zero.mpr; intro g; rw [g,mul_zero] at h; omega
lemma lane {a b i j:ℤ} (v:a ≤ i)(t:j ≤ b): T.S_ i j⊆ T.S_ a b:=by intro y p; obtain ⟨x,p,u,l⟩:= (T.S_i ..|>.1 p); have hv:=mul_le_mul_of_nonneg_left v (Wall.L_p L).le; have ht:=mul_le_mul_of_nonneg_left t (Wall.L_p L).le; exact (T.S_i ..).2 ⟨x,p,by omega,by omega⟩
lemma ratio(a b:ℤ) : T.S_ (a+(T.η:ℤ)) (b+(T.η:ℤ))=T.S_ a b:=by
 ext i; rw [T.S_i,T.S_i]; constructor <;> rintro ⟨x,h,v,e⟩ <;> rw [h]
 · refine ⟨x-(More n).val,?_,?_,?_⟩; · rw [Int.cast_sub,Int.cast_natCast,ZMod.natCast_self,sub_zero] -- tune
   all_goals rw [mul_add,T.rise] at v e; omega
 refine ⟨x+(More n).val,?_,?_,?_⟩; · rw [Int.cast_add,Int.cast_natCast,ZMod.natCast_self,add_zero]
 all_goals rw [mul_add,T.rise]; omega
lemma own {a b c d:ℤ}(p:b ≤ c)(h:d ≤ a+T.η): Disjoint (T.S_ a b) (T.S_ c d):=by
 apply disjoint_left.mpr; intro i x y; obtain ⟨v,k,s,r⟩:= T.S_i ..|>.1 x; obtain ⟨w,t,u,v'⟩:= T.S_i ..|>.1 y; let K:=Wall.L_p L; have ht:=ZMod.intCast_eq_intCast_iff_dvd_sub v w (More n).val |>.1 (k.symm.trans t); have hz:= mul_le_mul_of_nonneg_left p K.le; have he:= mul_le_mul_of_nonneg_left h K.le; rw [mul_add,T.rise] at he; have hp:=T.hp; have hx:=Int.le_of_dvd (show 0 < w-v from by omega) ht; omega
lemma crop_t {i:ℕ}(q:i+i=T.η)(a:ℤ): (T.wall a).crop n T.grip = T.S_ a (a+i):=by
 have hu:(δ_)* i=n.val:=by have he:=T.rise; rw [←q,Nat.cast_add,mul_add] at he; change _+_=( (↑(n.val*2)):ℤ) at he; omega
 ext x; rw [Wall.stay,T.S_i,mul_add,hu]; have hn: 2*(T.wall a).o = (δ_)*a:=by unfold wall Wall.len; ring
 rw [hn]; constructor
 · rintro ⟨z,g,p,v⟩; exact ⟨_,g,by omega,by omega⟩
 rintro ⟨z,t,x,q⟩; refine ⟨z-(δ_)*a,?_,by omega,by omega⟩; rw [show (T.wall a).i=T.i from rfl,t]; congr 1; omega
abbrev retro (a i:ℤ):= 2*a-i -- won't include T
lemma port_v (a i j:ℤ) : (T.wall a).negZ (T.S_ i j)= T.S_ (retro a j) (retro a i):=by
 ext x; rw [Wall.swipe,T.S_i,T.S_i]; have hp(c z:ℤ):(δ_)* (retro c z)= 2*((δ_)*c)-(δ_)*z:=by unfold retro; ring
 have hf:= (T.wall a).shape_p x
 rw [show (T.wall a).site n x T.i=4* ↑((T.wall a).o)-x T.i from hf,hp,hp]; let z:=(δ_)*a; have hv:4*(T.wall a).o=2*z:=by unfold z Wall.len wall; ring
 constructor
 · rintro ⟨v,p,u,t⟩; refine ⟨2*z-v,?_ ,?_ ,?_⟩; · rw [←hv,Int.cast_sub, Int.cast_mul,Int.cast_ofNat]; linear_combination -p
   all_goals unfold z; omega
 rintro ⟨v,p,u,t⟩; refine ⟨2*z-v,?_,?_,?_⟩; · rw [←hv,p,Int.cast_sub]; push_cast; ring
 all_goals unfold z; omega
end Race
end YM.CF.DPress.Wagon
