import YM.SU5.FiniteGaugeData.Chrono.Spill
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra
open Nacre Heat Charm Chrono
namespace SalonG
variable {K:Calibration}{S T:Finset Cover}(a:Axis){r n:ℕ}{x y z:ℤ}
section aperture
-- buffered portable cover interval (native units at each observing s)
abbrev Behind (a:Axis)(z:ℤ)(r:ℕ)(S:Finset Cover):Prop:= ∀ v∈S, v a+(r:ℤ) ≤ z
structure Studio (a:Axis)(x y:ℤ)(r:ℕ)(S:Finset Cover) : Prop where
 behind : Behind a y r S
 ahead : Ahead a x r S
variable {a}
lemma Studio.ante {u v:ℤ}(p:Studio a x y r S)(t:u≤x)(e:y≤ v):Studio a u v r S:= ⟨fun i h=> (p.behind _ h).trans e,fun i h=> (add_le_add_left t _).trans (p.ahead _ h)⟩
lemma Studio.union (p:Studio a x y r S)(t:Studio a x y r T):Studio a x y r (S∪T):= ⟨fun i h=> (mem_union.mp h).elim (p.behind i) (t.behind i), ahead_union S T a x p.ahead t.ahead⟩
lemma Studio.empty : Studio a x y r ∅:= by constructor<;> intro i hi <;> simp at hi
lemma Studio.reflected (p:Studio a x y r S)(z:ℤ) : Studio a (2*z-y) (2*z-x) r (refract a z S):=by
 constructor<;> intro i hi<;> obtain ⟨n,h,rfl⟩:=mem_image.mp hi<;> have ht:=p.ahead n h<;> have he:=p.behind n h<;> rw [fling_move,if_pos rfl]<;> omega
lemma Ahead.above (z:ℤ)(p:Ahead a x r S): Behind a (2*z-x) r (refract a z S):=by
 intro i h; obtain ⟨t,e,rfl⟩:=mem_image.mp h; specialize p t e; rw [fling_move,if_pos rfl]; omega
lemma Behind.above (z:ℤ)(p:Behind a x r S): Ahead a (2*z-x) r (refract a z S):=by
 intro i h; obtain ⟨t,e,rfl⟩:=mem_image.mp h; specialize p t e; rw [fling_move,if_pos rfl]; omega
abbrev gaugeW (K:Calibration)(z:ℤ):ℤ:= (tic K:ℤ)*z
abbrev yard (K:Calibration)(d:ℕ):ℕ:= tic K*d
lemma yard_le : (tic K:ℤ)*n=(yard K n:ℤ):= (Nat.cast_mul ..).symm
lemma yard_ice : (yard K n:ℤ)=2* Heat.gaugeShift K.B n:= by rw [← yard_le, tick_tock]
lemma arbour (p:Studio a 0 (yard K n) r S): Studio a 0 (yard K n) r (refract a (Heat.gaugeShift K.B n) S):= by
 have he:= p.reflected (Heat.gaugeShift K.B (n:ℤ)); rwa [sub_zero,← yard_ice,sub_self] at he
lemma Studio.hour (K:Calibration)(t:ℤ)(p:Studio a x y r S): Studio a (x+gaugeW K t) (y+gaugeW K t) r (Chrono.hour K S a t):=by
 constructor<;> intro i hi<;> obtain ⟨b,g,rfl⟩:= mem_image.mp hi<;> have he:=p.ahead _ g<;> have h':= p.behind _ g -- directional
 · change beat K a t b a+ ↑r ≤ _; rw [beat_same]; linarith [show gaugeW K t=(tic K:ℤ)*t from rfl]
 change _≤ beat K a t b a; rw [beat_same]; linarith [show gaugeW K t=(tic K:ℤ)*t from rfl]
lemma gaugeW_mul : gaugeW K (n*z) = (n:ℤ)*gaugeW K z:= by unfold gaugeW; ring
lemma yard_sum : yard K (r+n)= yard K r+yard K n:=by unfold yard; rw [mul_add]
lemma yard_mul : yard K (r*n)=r*yard K n:=by unfold yard; ring
-- from Cover in THAT phase to band, including wrapped intervals used later ± many MORE. important pay reserve
abbrev later (z:ℤ)(N:Side)(S:Finset Cover)(a:Axis)(r:ℕ) : Prop:=region S N ⊆ band N a z r
variable {N:Side}
lemma band_cast (x y:ℤ)(z:Per (More N))(h:(r:ℤ) ≤ y-x)(t:y-x+(r:ℤ)≤ N.val)(e:y=z): -- coercion eg
    r≤ZMod.val (z-(x:Per (More N))) ∧ ZMod.val (z-(x:Per (More N))) + r ≤ N.val:= by
 let I:=(y-x).toNat; have hn: 0 ≤ y-x:=by omega
 have hz:I<(More N).val:=by have he:0<N.val:=N.property; rw [show (More N).val=N.val*2 from rfl]; unfold I; omega
 rw [show z-(x:Per (More N))=(I:Per (More N)) from by rw [←e,←Int.cast_natCast, Int.toNat_of_nonneg hn,Int.cast_sub],ZMod.val_natCast_of_lt hz]; unfold I; omega
lemma band_seat (h:∀ p ∈ S,∃ v:ℤ, x+r ≤ v∧ v+(r:ℤ) ≤ x+↑N.val ∧ (v:Per (More N))=↑(p a)):
    later x N S a r:=by
 intro m i; obtain ⟨p,v,rfl⟩:= mem_image.mp i; obtain ⟨z,i,j,b⟩:=h p v; exact (band_spec ..).mpr (band_cast x z _ (by omega) (by omega) b) -- definitional
lemma Studio.later (p:Studio a x y r S)(t:y ≤ x+(N.val:ℤ)): later x N S a r:= band_seat fun i v=> ⟨_,p.ahead i v,(p.behind i v).trans t,rfl⟩
lemma Studio.earlier (p:Studio a x y r S)(t:y≤x+(N.val:ℤ)): SalonG.later y N (refract a y S) a r:=by
 have he:=(p.reflected y); rw [show 2*y-y=y from by omega] at he; exact he.later (by omega)
lemma refl_region : region (refract a x S) N=(region S N).image ((plane a x).anon N):=by
 unfold region refract; rw [image_image,image_image]; exact congrArg (fun f:Cover→ Seat N=> S.image f) (funext fun i=> ((plane a x).anno ..).symm)
lemma region_union : region (S∪T) N=region S N∪region T N:= image_union ..
end aperture
open Py Py.Rate LocalLimit Preparation Journey
variable {Λ:Preparation}{l:ℕ}
local notation "L₁"=> Λ.R.L
local notation "η"=> reserve Λ l
local notation "ξ"=> GridStep Λ l
variable {a} in
lemma Studio.grow (p: Studio a x y (reserve Λ l) S): Studio a ((Λ.R.L.val:ℤ)*x) ((Λ.R.L.val:ℤ)*y) (reserve Λ l) (GridStep Λ l S):=by
 have he:= Behind.above 0 p.behind
 rw [mul_zero,zero_sub] at he
 have hx:= ahead_grid (refract a 0 S) a _ (Λ:=Λ) he; have ht:=Ahead.above 0 hx; rw [grid_mirror,mul_zero, mul_zero,cold_twice,mul_neg,zero_sub,neg_neg] at ht
 exact ⟨ht,ahead_grid S a x p.ahead⟩
lemma cover_separate (t:Behind a y (reserve Λ l) S)(p:Ahead a y (reserve Λ l) T): Range (spaceBill Λ l) S T:=by
 rw [← cold_twice a y S]; apply ahead_split (t:=y) _ _ a _ p; convert Behind.above y t using 1<;> ring
lemma seat_separate (N:Side)(t: later y N (refract a y S) a (reserve Λ l))(p: later y N T a (reserve Λ l)) : SeatRange (spaceBill Λ l) N S T:=by
 intro x h z u; apply margin_separate a y (Journey.prepared Λ l) x z ?_ (p u); rw [←cold_twice a y S,refl_region] at h; exact image_subset_image t h
#print axioms Studio.grow
end SalonG
end YM.CF.Buffered.Afterglow.Hierarchy
