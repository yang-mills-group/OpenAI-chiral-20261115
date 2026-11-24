import YM.SU5.FiniteGaugeData.SalonG.Board
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra
namespace SalonG
open Nacre Heat Charm Chrono Journey
variable (K:Calibration)(m:Side)(a i:Axis)(z:ℤ)
-- thickness budgets Keep unit uniform at k. Sensible thereafter
variable {r d n j:ℕ}
local notation "D"=> yard K d
local notation "H"=> proceed K n d
local notation "η"=> K.ℓ
local notation "N"=> K.c m
local notation "φ"=> (K.c m).val
variable {S T:Finset Cover}
lemma shift_port (h:Studio a 0 (yard K d) K.ℓ S): Studio a D (proceed K (n+1) d) K.ℓ (hour K (proceed_set K a d S n) a d):=by have he:= (proceed_geo K a d n h).hour K (d:ℤ); rw [gauge_cast,zero_add] at he; rw [proceed_succ,Nat.cast_add]; exact he
lemma seal_twice {y:ℕ} (h:Studio a 0 y K.ℓ S): Studio a (-(y:ℤ)) y K.ℓ (refract a 0 S∪S):=by
 have he:= h.reflected 0; rw [mul_zero, zero_sub,sub_zero] at he; exact (he.ante le_rfl (Nat.cast_nonneg' _)).union (h.ante (by omega) le_rfl)
abbrev Cardboard (K:Calibration)(m:Side)(a:Axis)(z:ℤ)(r:ℕ)(S:Finset Cover):Prop:= ∀ (x:Cover),x∈ S→∃ y:ℤ,(y:Per (More (K.c m)))=(x a:ℤ)∧ z-(r:ℤ)≤ y ∧ y ≤ z+ ↑r
variable {K m a z} in
lemma ported {x:ℤ}(p:Cardboard K m a z r S)(e:x=z) -- PER coerce add?
    : Cardboard K m a x r S :=e.symm ▸ p
local notation "R₀"=> Cardboard K m a
namespace Cardboard
variable {K m a i z}
lemma raises {x:ℤ}(p:Cardboard K m a z r S)(e:(x:Per (More (K.c m)))=z) : Cardboard K m a x r S:=by
 intro y t; obtain ⟨u,t,v,g⟩:= p y t; exact ⟨u-z+x, (by rw [Int.cast_add,Int.cast_sub,e,sub_add_cancel,t]),by omega,by omega⟩
lemma monoLens {x:ℤ}(p:Cardboard K m a z r S)(u:x-r-((j:ℕ):ℤ)≤ z - (r:ℤ))(v:z+(r:ℤ) ≤ x + (r:ℤ)+j): Cardboard K m a x (r+j) S:=by -- use simpler inequality s
 intro y t; obtain ⟨p,e,u',v'⟩:= p y t; exact ⟨p,e,by omega,by omega⟩
lemma monoC {x:ℤ}(p:Cardboard K m a z r S)(u:x-(j:ℤ)≤ z-(r:ℤ))(v:z+(r:ℤ)≤x+(j:ℤ)):Cardboard K m a x j S:=by intro y t; obtain ⟨p,e,u',v'⟩:=p y t; exact ⟨p,e,u.trans u',v'.trans v⟩
lemma reflector0 (p:Cardboard K m a z r S)(x:ℤ): Cardboard K m a (2*x-z) r (refract a x S):=by
 intro y t; obtain ⟨y,tQ,rfl⟩:=mem_image.mp t; obtain ⟨b,t,v,h⟩:=p y tQ
 rw [fling_move,if_pos rfl]; exact ⟨2*x-b,by push_cast; rw [t]; ring,by omega,by omega⟩
lemma cross (p:Cardboard K m i z r S)(t:a≠ i)(x:ℤ) : Cardboard K m i z r (refract a x S):=by
 intro y v; obtain ⟨b,u,rfl⟩:=mem_image.mp v; rw [fling_move,if_neg t]; exact p b u
lemma deduct (p:Cardboard K m i z r S) (t:a≠ i)(x:ℤ): Cardboard K m i z r (hour K S a x):=by
 intro y h; obtain ⟨b,u,rfl⟩:=mem_image.mp h; change ∃ y:ℤ, (y:Per (More N))=(beat K a x b i:ℤ)∧_; rw [beat_slant K i a x b t]; exact p b u
lemma deduct_eq (p:Cardboard K m i z r S)(x:ℤ): Cardboard K m i (z+gaugeW K x) r (hour K S i x):=by
 intro y h; obtain ⟨b,u,rfl⟩:=mem_image.mp h; obtain ⟨p,d,e,f⟩:=p b u; change ∃ y:ℤ, (y:Per (More N))=(beat K i x b i:ℤ)∧_; rw [beat_same]; unfold gaugeW; exact ⟨p+(tic K:ℤ)*x, by rw [Int.cast_add,d,Int.cast_add],by omega,by omega⟩
lemma conjU (p:Cardboard K m a z r S)(t:Cardboard K m a z r T): Cardboard K m a z r (S∪T):= fun x e=> (mem_union.mp e).elim (p x) (t x)
lemma ledger (p:Cardboard K m a z r S): rest K m (region S (K.c m)) a (2*r):=by refine ⟨z-r,fun y v=>?_⟩; obtain ⟨x,t,rfl⟩:=mem_image.mp v; obtain ⟨k,h,u,v⟩:=p _ t; exact ⟨k,u,by omega,h⟩
lemma afterL {x:ℤ}(p:Cardboard K m a z r S)(t:x+(K.ℓ:ℤ) ≤ z-(r:ℤ))(u:z+(r:ℤ)+(K.ℓ:ℤ)≤ x+ ↑(K.c m).val): later x N S a K.ℓ:= band_seat fun i e=>by obtain ⟨b,h,g,f⟩:=p i e; exact ⟨b,by omega,by omega,h⟩
lemma beforeL {x:ℤ}(p:Cardboard K m a z r S)(t:z+(r:ℤ)+(K.ℓ:ℤ) ≤ x)(u:x+(K.ℓ:ℤ) ≤ z-(r:ℤ)+↑(K.c m).val): later x N (refract a x S) a K.ℓ:= (reflector0 p x).afterL (by omega) (by omega)
end Cardboard
lemma grace (S:Finset Cover): Cardboard K m a 0 (wall S) S:= fun x t=>⟨x a,rfl,by rw [zero_sub]; exact (wall_p S a t).1,by rw [zero_add]; exact (wall_p S a t).2⟩
-- geometry END splits around q.
structure PaidSpan (K:Calibration)(m:Side)(d n:ℕ):Prop where
 lower : 2*proceed K n d≤ (K.c m).val
 upper : (K.c m).val≤ 2*proceed K n d+ 2 *(yard K d)
local notation "Q₀"=> PaidSpan K m d n
local notation "W"=> wall T
abbrev Ran := 4*yard K d+wall T+ K.ℓ
local notation "C"=> Ran (T:=T) (d:=d) K -- binder tune
lemma rear_total (p:Ahead a 0 K.ℓ T): Studio a ↑(proceed K (n+2) d) ((proceed K (n+2) d:ℕ)+(wall T:ℕ)+K.ℓ:ℕ) K.ℓ (rear K a d n T):=by
 have he: Studio a 0 (wall T+ (K.ℓ:ℤ)) K.ℓ T:=⟨fun i v=> add_le_add (wall_p T a v).2 le_rfl,p⟩
 have hx:= he.hour K (d*(n+2):ℕ); rw [yard_step] at hx; unfold rear; rw [zero_add] at hx; convert hx using 1 <;> omega
-- last end square sits entirely on POS of q
local notation "V"=> rear K a d n T
local notation "A"=> refract a 0 V
-- helper
lemma grows_proceed (j n:ℕ)(p:j≤ n): proceed K j d ≤proceed K n d:= Nat.mul_le_mul_left _ p
lemma go_roll (u:PaidSpan K m d n)(p:Ahead a 0 K.ℓ T)(t:Studio a 0 (yard K d) K.ℓ S)(h: 2* Ran (T:=T) (d:=d) K ≤ (K.c m).val) {j:ℕ}(q:j≤ n): Studio a 0 (K.c m).val K.ℓ (proceed_set K a d S j ∪ rear K a d j T):=by
 have H':=u.lower; have e:= grows_proceed (d:=d) K j n q; refine ((proceed_geo K a d j t).ante le_rfl (by omega)).union ((rear_total K a (n:=j) (d:=d) p).ante (by omega) ?_); rw [proceed_succ K d (j+1), proceed_succ K d j] -- `(j+2)` literal definitional? rewrite
 unfold Ran at h; omega
variable (p:PaidSpan K m d n) (t:Ahead a 0 K.ℓ T) -- use notation η type?
include p t
lemma rear_ahead (h: 2* Ran (T:=T) (d:=d) K ≤ (K.c m).val): later (proceed K n d) N (refract a 0 (rear K a d n T) ∪ rear K a d n T) a K.ℓ := by
 have hx:= rear_total K a (d:=d) (n:=n) t; rw [proceed_succ K d (n+1),proceed_succ K d n] at hx; have ht:= p.lower; have hw:= p.upper; unfold later; rw [region_union]; apply union_subset; swap
 · apply (hx.ante _ (le_rfl)).later _ <;> unfold Ran at h <;> omega
 refine band_seat (S:=refract a 0 V) (fun i v=>?_); obtain ⟨x,b,rfl⟩:= mem_image.mp v; have he:=hx.ahead x b; have hf:=hx.behind x b; rw [fling_move,mul_zero, if_pos rfl,add_zero]; unfold Ran at h; refine ⟨-x a+((More N).val :ℤ), ?_, ?_, ?_⟩
 all_goals try rw [show (More N).val=φ*2 from rfl]; omega
 rw [Int.cast_add,Int.cast_natCast,ZMod.natCast_self,add_zero]

omit p t in
lemma east_r : Cardboard K m a (proceed K n d) (Ran (T:=T) (d:=d) K) (rear K a d n T):=by
 have h:= (grace K m a T).deduct_eq (d*(n+2):ℕ); rw [yard_step, proceed_succ K d (n+1),proceed_succ K d n, zero_add] at h; apply h.monoC <;> unfold Ran <;> omega
-- west near H+N. wrap
omit p t in
lemma more_zero : ((( (φ:ℤ)*2:ℤ)): Per (More N))=0:=by rw [← Nat.cast_ofNat (R:=ℤ),← Nat.cast_mul,← show (More N).val=(K.c m).val*2 from rfl, Int.cast_natCast]; exact ZMod.natCast_self _ -- accidental include p t
omit t in
lemma west_r : Cardboard K m a ((proceed K n d:ℤ)+ (φ:ℤ)) (Ran (T:=T) (d:=d) K) (refract a 0 V):=by
 have h:= ((grace K m a T).deduct_eq (d*(n+2):ℕ)).reflector0 0; rw [yard_step, proceed_succ K d (n+1),proceed_succ K d n, zero_add,mul_zero,zero_sub] at h; have hp:=p.lower; have ht:=p.upper
 apply Cardboard.raises (x:= (H:ℤ)+ (φ:ℤ)) (z:= (H:ℤ)-(φ:ℤ)) (h.monoC _ _) _; rotate_left 2
 · have he:(((φ:ℤ)*2:ℤ): Per (More N))=0:= ?_; rw [show (H:ℤ)+(φ:ℤ)=(H:ℤ)-(φ:ℤ)+(φ:ℤ)*2 from by ring,Int.cast_add,he,add_zero]; exact more_zero K m -- oops include p/t remove
 all_goals unfold Ran; omega
#print axioms rear_ahead
end SalonG
end YM.CF.Buffered.Afterglow.Hierarchy
