import YM.CF.Buffered.Mileage
/-!
# Tile rails in one physical period. Closed endpoint and face indices.
Tile positions start at 0 in coordinates; translate the tests to that coordinate
system separately. No powers of the scalar Haar probabilities paid to use
this coordinate representation (`slots` bijective).
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 420000
noncomputable section
namespace YM.CF.Buffered.Region
open Function Lattice Cube Finset Roost
variable {w l p m M n B:Side} {A D:Finset Axis}

lemma int_val (x:ℤ)(p:0≤x)(v:x<n.val) : ((x:Per n)).val = x.toNat:=by
 rw [←(show ((x.toNat:ℕ):ℤ)=x from Int.toNat_of_nonneg p),Int.toNat_natCast, Int.cast_natCast,ZMod.val_natCast_of_lt (by omega)]
lemma spill_same (x y:ℤ)(hx:0≤x)(hy:0≤y)(p:x<n.val)(q:y<n.val)(e:(x:Per n)=(y:Per n)): x=y:=by
 have ht:= congrArg ZMod.val e; rw [int_val x hx p,int_val y hy q] at ht; omega
lemma big_int (x:ℤ)(p:x=n.val) : (x:Per n) = 0:=by rw [p,Int.cast_natCast,ZMod.natCast_self]

structure Planck (n l p : Side): Prop where
 ratio : n.val=l.val*p.val
 -- don't require >=2 yet. apply for equivalences

variable (K:Planck n l p) (t:Rail (Uniform p)) (x:Cover)
include K
namespace Planck

def sail (_K:Planck n l p) (r:Rail (Uniform p)) : Cover:= fun i=> l.val*(r i).val
def zone (K:Planck n l p)(r:Rail (Uniform p)) (x:Cover): Site n := wrap n (K.sail r+x)
lemma zone_one (i:Axis) : zone K t x i=(((↑l.val:ℤ)*(t i).val+x i:ℤ):Per n):=rfl
lemma int_size : (↑n.val:ℤ)=l.val*(p.val:ℤ) := by exact_mod_cast K.ratio
lemma width (h:Landing (Uniform p)): l.val < n.val:=by have he:2≤p.val:=landing_ge h 0; rw [K.ratio]; have ht:0<l.val := floorL; nlinarith
lemma installed_next (i:Axis) : wrap n (sail K (Region.next i t))=wrap n (sail K t + l.val • step i):=by
 funext j; rw [wrap_here,wrap_here]; unfold sail; rw [Pi.add_apply,Pi.smul_apply,step_apply]; by_cases h:j=i; swap
 · rw [if_neg h, next_at t i h, smul_zero,add_zero]
 subst j; rw [if_pos rfl,next_val]; split
 next hk=> change ((↑l.val*(↑0:ℤ):ℤ):Per n)=_; rw [mul_zero,Int.cast_zero]; symm; apply big_int; rw [int_size K]; change _= (l.val:ℤ)*p.val; have ht: (p.val:ℤ)=↑(t i).val+1:=by change (t i).val+1=p.val at hk; omega
           rw [ht,nsmul_eq_mul]; ring
 next e=> rw [nsmul_eq_mul]; push_cast; ring -- tune
lemma next_zone (i:Axis): zone K (Region.next i t) x=zone K t (l.val • step i+x):=by unfold zone; rw [←add_assoc, map_add, map_add (wrap n) (K.sail t + _),installed_next]
lemma zone_slide (x:Roost l A) : zone K (Roost.slide t x).1 (Roost.slide t x).2.val=zone K t x.val:=by
 funext i; rw [zone_one,zone_one]; unfold Roost.slide; dsimp only; unfold wallet corner plusWall; rw [Pi.add_apply]; simp only [mem_filter,mem_univ,true_and]; split_ifs with h
 · rw [←next_rail, add_zero, next_val t i]; split_ifs with b; swap; · push_cast; rw [h]; push_cast; ring
   rw [Nat.cast_zero,mul_zero,Int.cast_zero]; symm; apply big_int; rw [int_size K]; change (t i).val+1=p.val at b; change (l.val:ℤ)*(t i).val+x.val i=(l.val:ℤ)*p.val; rw [h,←show (↑(t i).val:ℤ)+1=p.val by omega]; ring
 rw [add_zero]
lemma pilot (z:Post l)(i:Axis) : (zone K t z.val i).val=l.val*(t i).val+ (z.val i).toNat:=by
 have he:= z.nonneg i; have hx:= z.below i (mem_univ _); rw [zone_one, int_val]
 · rw [Int.toNat_add (by positivity) he,← Nat.cast_mul,Int.toNat_natCast]
 · exact add_nonneg (mul_nonneg (by positivity) (by positivity)) he
 have ht:(t i).val<p.val:= (t i).isLt; rw [int_size K]; nlinarith
lemma slots_bij : Bijective (fun z:Rail (Uniform p) × Post l=>zone K z.1 z.2.val):=by
 let Q:= Rail (Uniform p)
 let y(z:Q × Post l): Site n:=zone K z.1 z.2.val; let W(i:Site n)(j:Axis):= (i j).val
 let s (i:Site n): Q:= fun j=>⟨W i j / l.val,Nat.div_lt_of_lt_mul (by change W i j<l.val*p.val; rw [←K.ratio]; exact (i j).val_lt)⟩
 let a(i:Site n):Post l :=⟨fun j=> ↑(W i j%l.val),fun j=>by
    have he:= Nat.mod_lt (W i j) l.property; rw [wall_mem j (mem_univ _)]; change (0:ℤ)≤(↑(W i j%l.val):ℤ) ∧ ((W i j%l.val:ℕ):ℤ)≤(l.val:ℤ)-1; have ht: ((W i j%l.val:ℕ):ℤ)<l.val:=by exact_mod_cast he
    omega⟩
 let t (i:Site n):= (s i,a i)
 have lp : LeftInverse t y:=by
    rintro ⟨r,w⟩; refine Prod.ext (funext fun i=>Fin.ext ?_) (Subtype.ext (funext fun i=> ?_))
    · change (zone _ r w.val i).val / l.val=(r i).val; rw [pilot]; have he:=w.below i (mem_univ _) ; have hu:=w.nonneg i; rw [show (l.val*(r i).val + (w.val i).toNat)/l.val=(r i).val+(w.val i).toNat/l.val from Nat.mul_add_div l.property _ _, Nat.div_eq_of_lt (by omega), add_zero] -- tune
    change (_:ℤ)= _; change (↑((zone _ r w.val i).val%l.val):ℤ)=_; have hz: 0<l.val:= l.property; rw [pilot, Nat.mul_add_mod,Nat.mod_eq_of_lt (by have he:= w.below i (mem_univ _); omega), Int.toNat_of_nonneg (w.nonneg i)] -- tune
 have rp : RightInverse t y:=by
    intro x; funext i; apply ZMod.val_injective; rw [show y (t x)=zone K (s x) (a x).val from rfl,pilot]; simp only [s,a,Int.toNat_natCast]; exact Nat.div_add_mod ..
 exact ⟨lp.injective,rp.surjective⟩

def slots (K:Planck n l p) := Equiv.ofBijective _ (slots_bij K)
lemma slots_one (x:Post l) : slots K (t,x)=zone K t x.val:=rfl
lemma ports_sum (A: Finset Axis){F:Type*}[AddCommGroup F][Module ℝ F](g:Site n → F): ∑ r:Rail (Uniform p),∑ x:Roost l A, x.share • g (K.zone r x.val)= ∑ v,g v:=by
 let y(v:Rail (Uniform p) × Post l):=g (slots K v)
 rw [←Equiv.sum_comp (slots K),←Roost.share_all A y]; apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; unfold y slots; simp only [Equiv.ofBijective_apply]; rw [zone_slide]
-- room inject & no huge volumes
lemma anywhere_inj (h:Landing (Uniform p))(A: Finset Axis) : Injective (fun x:Roost l A=> K.zone t x.val):= by
 intro a b v; apply Subtype.ext; funext j; apply spill_same _ _ (a.nonneg j) (b.nonneg j) (by exact (a.maxval j).trans_lt (by exact_mod_cast K.width h)) (by exact (b.maxval j).trans_lt (by exact_mod_cast K.width h)); have hp:= congr_fun v j; dsimp only at hp; rw [zone_one,zone_one,Int.cast_add,Int.cast_add] at hp; exact add_left_cancel hp -- tune
end Planck

end YM.CF.Buffered.Region
#print axioms YM.CF.Buffered.Region.Planck.ports_sum
