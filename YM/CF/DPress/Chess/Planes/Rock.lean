import YM.CF.DPress.Chess.Planes.Yard
-- all active gauge sites positive or negative for any plane. Used on lower levels of the Comparator stove.
set_option autoImplicit false
noncomputable section
namespace YM.CF.DPress.Chess
open Function Lattice Finset Laurent Spire Skye Scroll Lat Rush Wilson FD
open Cube (More assembly)
open scoped Topology BigOperators Classical
namespace Wall
variable (W:Wall){n:Side}{L:Side}{μ:ℕ}
abbrev aligned(L: Side):Prop:= (L.val:ℤ) ∣ W.o
lemma grid (n:Side)(p:W.aligned L):gridOK L (W.joy n):=by
 obtain ⟨k,v⟩:=p; refine ⟨2 • k • step W.i,(by dsimp [joy,shape,od]; rw [v]; apply congrArg; simp; ring)⟩
lemma boost_align (M:Side)(p:W.aligned L): (W.boost M).aligned L:=by unfold boost aligned; rw [nsmul_eq_mul]; exact dvd_mul_of_dvd_right p _
lemma spacing (p:W.aligned L): len L ∣ 2*W.o:=mul_dvd_mul_left _ p
lemma periodize(x: Seat n) :∃ z:ℤ,x W.i=((2*W.o+z:ℤ):Per _)∧-(n.val:ℤ)<z ∧ z≤ n.val:=by
 let b:= x W.i-(( (2*W.o:ℤ)):Per (More n)); let z:= b.valMinAbs; refine ⟨z,?_,?_⟩
 · rw [Int.cast_add,show (z:Per _)=_ from ZMod.coe_valMinAbs b]; unfold b; abel
 have h:= ZMod.valMinAbs_mem_Ioc b; change - ((↑(n.val*2):ℤ)) < z*2∧ z*2 ≤ ( (↑(n.val*2):ℤ)) at h; omega
lemma νlive (p:W.aligned L)(s: deed n L)(x:Seat n)(f: fort L μ x) : x∈ W.crop n μ ∨ x∈ W.negZ (W.crop n μ):=by
 obtain ⟨v,h,t,k⟩:= W.periodize x; have he: fieldS L μ v:= (incF L (2*W.o+v) v (by rw [add_sub_cancel_right]; exact W.spacing p)).1 (f W.i _ h.symm); by_cases b:0≤v; · left; apply (W.stay ..).2; obtain ⟨a,sa⟩:=s; let V_:=he 0; simp only [mul_zero,sub_zero,abs_of_nonneg b] at V_; have ht:= he a; rw [←sa,abs_of_nonpos (show v-(n.val:ℤ)≤0 by omega)] at ht; exact ⟨v,h,by omega,by omega⟩
 right; apply (W.minus ..).2; obtain ⟨a,sa⟩:=s; have v':= he 0; simp only [mul_zero,sub_zero,abs_of_nonpos (show v ≤ 0 by omega)] at v'; have ht:= he (-a); rw [mul_neg,←sa,abs_of_nonneg (show 0≤ v- -(n.val:ℤ) by omega)] at ht; exact ⟨-v,(by simpa only [sub_neg_eq_add] using h),by omega,by omega⟩
end Wall
end YM.CF.DPress.Chess
