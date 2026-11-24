import YM.CF.DPress.Chess.Planes.Wedge
import YM.Corona.Spend
import YM.Work.E01
/-! gauge coordinate interiors. No cut relocation. Does not assume any smallness relative to half-size. -/
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.DPress.Chess
open Function Lattice Finset Laurent Spire Skye Scroll Lat Rush Wilson FD Push.GridApprox
open Cube (More assembly)
open scoped Topology BigOperators Classical
namespace Wall
variable (W:Wall){n m:Side}{b a r:ℕ}
def crop(n:Side)(b:ℕ):Support (More n):= univ.filter fun i=>∃ z:ℤ,i W.i=((2*W.o+z:ℤ): Per _) ∧ (b:ℤ) ≤ z ∧ z+b ≤ n.val
lemma stay (x:Seat n)(b:ℕ) : x∈ W.crop n b ↔ ∃ z:ℤ,x W.i=((2*W.o+z:ℤ): Per _) ∧ b ≤ z ∧ z+b ≤ n.val:=by rw [crop,mem_filter]; exact and_iff_right (mem_univ _)
lemma grade (p:a ≤ b)(n:Side): W.crop n b ⊆ W.crop n a:= by intro i h; obtain ⟨z,h,p,h'⟩:= (W.stay ..|>.1 h); exact (W.stay ..).2 ⟨z,h,by omega,by omega⟩
lemma minus (x:Seat n)(b:ℕ): x∈ W.negZ (W.crop n b) ↔ ∃ z:ℤ,x W.i=((2*W.o-z:ℤ): Per _) ∧ b ≤ z ∧ z+b≤ n.val:=by
 rw [W.swipe,W.stay,W.shape_p]; constructor <;> rintro ⟨z,h,p,t⟩ <;> refine ⟨z,?_ ,p,t⟩ <;> push_cast at h ⊢ <;> linear_combination -h -- tune
lemma night (p:0<a+b)(n:Side):Disjoint (W.crop n a) (W.negZ (W.crop n b)):=by
 apply Finset.disjoint_left.mpr; intro i x y; obtain ⟨z,hz,zt,zp⟩:= (W.stay ..|>.1 x); obtain ⟨v,hv,vp,vt⟩:= (W.minus ..|>.1 y); have ht: ((v+z:ℤ):Per (More n))=0:=by rw [hz] at hv; push_cast at hv ⊢; linear_combination hv -- signs
 have he:= Int.le_of_dvd (show 0<v+z from by omega) ((ZMod.intCast_zmod_eq_zero_iff_dvd ..).1 ht); change (((n.val*2:ℕ):ℤ)) ≤ _ at he; omega
lemma surrounding (p:a+r≤b) (n:Side):halo r (W.crop n b)⊆ W.crop n a:=by
 intro i v; obtain ⟨j,h,t⟩:= halo_spec.mp v; obtain ⟨z,l,s,u⟩:= (W.stay ..|>.1 h); let k:= Lattice.lift (i-j) W.i; have hu:k.natAbs≤r:= (component_le (i-j) W.i).trans ((separation_comm ..).trans_le t : separation i j ≤ _)
 apply (W.stay ..).2; refine ⟨z+k,?_ ,by omega,by omega⟩; have hx: (k:Per _) = i W.i-j W.i:= ZMod.coe_valMinAbs _; rw [←add_assoc,Int.cast_add,←l,hx]; abel
lemma negativity (p:a+r ≤ b)(n: Side): halo r (W.negZ (W.crop n b))⊆ W.negZ (W.crop n a):=by rw [negZ,paysT]; exact W.spans (W.surrounding p n)
lemma aloof (hp:0<a+b)(p:a+r≤ b)(q:0<b) (n:Side): Far r (W.crop n b) (W.negZ (W.crop n b)):= fun i t j l=> lt_of_not_ge fun u=> Finset.disjoint_left.mp (W.night hp n) (W.surrounding p n (halo_spec.mpr ⟨i,t,u⟩)) l
-- scale embeddings
open Transit.Bough
lemma por_x (K:Ratio n m)(i:Site n)(d:Axis){t:ℤ}(p:i d=(t:Per n)):(K.embed i) d= ((K.count.val • t:ℤ): Per m):=by
 let q:= Function.update (Lattice.lift i) d t; rw [show i=wrap n q from ?_,K.embed_wrap]; · change (( (K.count.val • q d:ℤ)):Per m)=_; simp only [q,Function.update_self] -- note `2*den.pt`.
 ext j; by_cases h:j=d; rw [h,p]; change (t:Per n)=((q d:ℤ):Per n); simp only [q,Function.update_self]
 change i j=(q j:Per n); rw [show q j=Lattice.lift i j from Function.update_of_ne h _ _]; exact (ZMod.coe_valMinAbs _).symm
lemma spend (K:Ratio n m)(b:ℕ)(x:Seat n)(t:x∈ W.crop n b) : (ratio K).embed x∈ (W.boost K.count).crop m (K.count.val*b) :=by
 obtain ⟨z,h,p,u⟩:= (W.stay ..|>.1 t); apply (stay ..).2; have he:0< (K.count.val:ℤ):= by positivity
 refine ⟨K.count.val • z,?_ ,?_ ,?_⟩
 · rw [show (W.boost K.count).i=W.i from rfl, por_x (ratio K) _ _ h]; apply congrArg; change K.count.val • _=2*((K.count.val) • _ )+_; rw [smul_add,nsmul_eq_mul,nsmul_eq_mul]; ring
 · rw [nsmul_eq_mul]; push_cast; exact mul_le_mul_of_nonneg_left p he.le
 rw [K.exact_size,nsmul_eq_mul]; push_cast; rw [mul_comm (n.val:ℤ),← mul_add]; exact mul_le_mul_of_nonneg_left u he.le
lemma pay_c (K:Ratio n m)(hp:a+K.count.val ≤ K.count.val*b): twig (ratio K) (W.crop n b) ⊆ (W.boost K.count).crop m a:=by
 intro i t; have ht:= W.spend K b ((ratio K).parent i) ((twig_v ..).1 t); apply surrounding (W.boost K.count) hp m; apply halo_spec.mpr; refine ⟨_,ht,?_⟩; rw [separation_comm]; have hx:=Corona.near (ratio K) i; change 2*separation i _ ≤ K.count.val at hx; omega
end Wall
end YM.CF.DPress.Chess
