
import YM.CF.Swell.Yard

/-! From anchor to incidence with 1/b slack. All payments for
finite actual labelled series on finite tori. Never multiply by volume. -/

set_option autoImplicit false
noncomputable section
namespace YM.CF.Zephyr
open Lattice Finset Push.AbsoluteSums.Trees
variable {n:Side} {I:Type*} [Fintype I]
variable (O:I→Site n) (X:I→Support n) (v:I→ℝ) (b:ℕ)

abbrev due (r:ℝ) (i:I):=currency b r (X i) * v i

/-- Total payments of these finite arrays at every anchor. -/
def Tab (r t:ℝ):Prop:=∀ x:Site n, ∑ i with x = O i, due X v b r i ≤ t
/-- ... at every hit! -/
def Touch (r t:ℝ):Prop:=∀ x:Site n, ∑ i with x ∈ X i, due X v b r i ≤ t

variable {O X v b} {r t:ℝ}

/-- Counting price polynomial (b+1)^8 times an absolute constant. -/
def taxB (b:ℕ) : ℝ := (16:ℝ)^4*Swell.κRepo*((b:ℝ)+1)^8

theorem Tab.mono {s:ℝ} (h:Tab O X v b r s)(g:s≤t): Tab O X v b r t:=fun i=>(h i).trans g

open Swell
variable (hv:∀i,0≤v i) (mem:∀i,O i∈ X i)

include hv mem
theorem Tab.touch (h:Tab O X v b (r+1/(b:ℝ)) t) (ht:0≤t)(hb:0<b):
    Touch X v b r (taxB b*t):= by
 classical
 have hB:0<(b:ℝ):=by exact_mod_cast hb
 intro y
 let s:=univ.filter (fun i=>y∈X i)
 let m(i):= coverNumber b (X i) / b
 let S:Finset ℕ := s.image m
 let f(j:ℕ):= s.filter (fun i=>m i=j)
 let M(j:ℕ):= (j+1)*b
 let H(j:ℕ):= halo (νfit b (M j)) {y}
 have perLink j i (u:i∈f j):
     due X v b r i ≤ Real.exp (-(j:ℝ))*due X v b (r+1/b) i:=by
   unfold due; rw [←mul_assoc,currency,currency,←Real.exp_add]
   refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (hv i)
   have w: j*b ≤ coverNumber b (X i):=by
       rw [←(mem_filter.mp u).2]
       exact Nat.div_mul_le_self ..
   have v': (j:ℝ) ≤ (coverNumber b (X i):ℝ)/b:=by
     rw [le_div_iff₀ hB]
     exact_mod_cast w
   rw [div_eq_mul_inv] at v' ⊢
   linarith only [v']

 have place j i (u:i∈f j): O i∈ H j:= by
    obtain ⟨g,t⟩:=(mem_filter.mp u)
    refine halo_spec.mpr ⟨_,mem_singleton_self _,(Corona.extent _ b ((mem_filter.mp g).2) (mem i)).trans ?_⟩

    have k:coverNumber b (X i) ≤ M j:=by
      let a:=coverNumber b (X i)
      rw [←t]; change a ≤ (a/b+1)*b
      rw [mul_comm,b.mul_add, mul_one]
      exact (Nat.div_add_mod a b).ge.trans (Nat.add_le_add_left (Nat.mod_lt a hb).le _) -- check sign
    exact Nat.add_le_add_right (Nat.mul_le_mul_right _ k) _

 let d(j:ℕ):=((j:ℝ)+1)^4*Real.exp (-(j:ℝ))
 let V:= (16:ℝ)^4*((b:ℝ)+1)^8
 have block j: ∑ i∈f j,due X v b r i ≤ V*t*d j:= by
   rw [←sum_fiberwise_of_maps_to (place j)]
   have sub(x:Site n): (f j).filter (fun i=>O i=x) ⊆ univ.filter (fun i=>x=O i):=
     fun i u=>mem_filter.mpr ⟨mem_univ _,(mem_filter.mp u).2.symm⟩
   have k(x:Site n): ∑ i∈f j with O i=x,due X v b r i ≤ Real.exp (-(j:ℝ))*t:=by
     apply (sum_le_sum fun i hi=>perLink j i (mem_filter.mp hi).1).trans
     rw [←mul_sum]
     refine mul_le_mul_of_nonneg_left (le_trans ?_ (h x)) (Real.exp_pos _).le
     exact sum_le_sum_of_subset_of_nonneg (sub x) fun i _ _=>mul_nonneg (Real.exp_pos _).le (hv _)

   apply (sum_le_sum fun x _=>k x).trans
   rw [sum_const,nsmul_eq_mul]
   have hcard: (H j).card ≤ 16^4*(b+1)^8*(j+1)^4:=by
     refine le_trans (le_trans ?_ (town_V b (M j))) ?_
     · simpa only [H,card_singleton,one_mul,two_mul] using Corona.halo_size {y} (νfit b (M j))
     refine le_trans (mul_le_mul_of_nonneg_left (show (M j+1)^4 ≤ ((j+1)*(b+1))^4 from ?_) (Nat.zero_le ((16*(b+1))^4))) ?_
     · gcongr; unfold M; rw [Nat.mul_add]; simp
     apply le_of_eq; ring
   have v':((H j).card:ℝ) ≤ V*((j:ℝ)+1)^4:=by unfold V;exact_mod_cast hcard
   exact (mul_le_mul_of_nonneg_right v' (mul_nonneg (Real.exp_pos _).le ht)).trans_eq (by unfold d;ring)
 change ∑ i∈s,_ ≤ _
 rw [←sum_fiberwise_of_maps_to (t:=S) (g:=m) (fun i u=> mem_image_of_mem _ u)]
 apply (sum_le_sum fun i _=>block i).trans
 rw [←mul_sum]
 have vd: ∑ i∈S,d i ≤ κRepo:= αfee.sum_le_tsum _ fun i _=>by positivity
 exact (mul_le_mul_of_nonneg_left vd (mul_nonneg (by unfold V; positivity) ht)).trans_eq (by unfold V taxB; ring)
#print axioms Tab.touch



omit mem
theorem Tab.bridge {u β:ℝ} (hl:Tab O X v b r t) (hu:Tab O X v b (r+1) u)
    (hp:0≤β) (hβ:β≤(b:ℝ)/2) (hb:0<b):
    Tab O X v b (r+β/b) (Real.exp β*t+Real.exp (-(b:ℝ)/2)*u):=by
 have hB:0<(b:ℝ):=by exact_mod_cast hb
 have hq: β/(b:ℝ) ≤ 1/2:=(div_le_iff₀ hB).mpr (by linarith only [hβ])
 have h0(i:I)(c:ℝ):0≤due X v b c i:= mul_nonneg (Real.exp_pos _).le (hv _)
 intro y
 refine le_trans (b:=Real.exp β*(∑ i with y=O i,due X v b r i)+
    Real.exp (-(b:ℝ)/2)*(∑ i with y=O i,due X v b (r+1) i)) ?_ (add_le_add (mul_le_mul_of_nonneg_left (hl _) (Real.exp_pos _).le) (mul_le_mul_of_nonneg_left (hu _) (Real.exp_pos _).le))
 rw [mul_sum,mul_sum,←sum_add_distrib]
 apply sum_le_sum; intro i _
 let d : ℝ:= coverNumber b (X i)
 have z:0 ≤ d:= Nat.cast_nonneg _
 have cmp(c q:ℝ)(h:(r+β/b)*d ≤ c+q*d): due X v b (r+β/b) i ≤ Real.exp c*due X v b q i:=by

   unfold due currency
   rw [←mul_assoc,←Real.exp_add]
   exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr h) (hv i)
 by_cases hi:d≤b
 · have e: β/(b:ℝ)*d ≤ β :=(mul_le_mul_of_nonneg_left hi (div_nonneg hp hB.le)).trans_eq (div_mul_cancel₀ β hB.ne')
   exact le_add_of_le_of_nonneg (cmp β r (by linarith only [e])) (mul_nonneg (Real.exp_pos _).le (h0 _ _))
 exact le_add_of_nonneg_of_le (mul_nonneg (Real.exp_pos _).le (h0 _ _))
   (cmp _ _ (by linarith only [hi,mul_le_mul_of_nonneg_right hq z]))
end YM.CF.Zephyr
