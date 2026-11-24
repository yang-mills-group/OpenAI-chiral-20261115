import Merino.Corolla.Stage


set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 360000
noncomputable section
namespace YM.CF.Merino.Corolla
open Finset Lattice RG Scree Skye Vow
open scoped Topology Classical Matrix Matrix.Norms.L2Operator
open Cadre Sour Push.AbsoluteSums.Trees Vow.TreasuryFog
open Cube Stax Mew Fock
open scoped YM.CF.Mew

variable {I:Type}[LinearOrder I][Fintype I]
variable {n:Side}{P:BudgetPoint}{q:ℕ}{h:ℝ}

open Rill Rue

open Lattice.Corona
open Leaf
variable (P:BudgetPoint)(o:Seat n)(L:ℕ)
private lemma away(u:Seat n)(a:ℕ)(v:2*a<(More n).val): ∃ x:Seat n, separation u x=a:= by
 let y:Seat n:= fun _=>a
 refine ⟨u-y,?_⟩; rw [separation,sub_sub_cancel]
 have e(i): (lift y i).natAbs=a:=by
    rw [lift]; change ((a:ZMod ((More n).val)).valMinAbs).natAbs=a
    rw [ZMod.valMinAbs_def_pos,ZMod.val_natCast_of_lt (show a<(More n).val by omega),if_pos (show a ≤ (More n).val /2 by omega), Int.natAbs_natCast]
 rw [pdist]; simp_rw [e]; exact le_antisymm (Finset.sup_le fun _ _=>le_rfl) (show (fun _:Axis=>a) 0 ≤ _ from le_sup (f:=fun _:Axis=>a) (mem_univ 0))

abbrev postL(L:ℕ):=8*L+20000
def guardX: Aura n:=
  ⟨Lattice.halo (postL L * P.B) {o}, o, halo_subset _ _ (mem_singleton_self o)⟩

lemma railgo (y:Aura n)(r:(guardX P o L).val ⊆ y.val)
    (p:2*(postL L*P.B)<(More n).val):
    L ≤ coverNumber P.B y.val:=by
 obtain ⟨x,v⟩:=away o _ p
 have h1:o∈ y.val:=r (halo_subset _ _ (mem_singleton_self _))
 have h2:x∈ y.val:=r (halo_spec.mpr ⟨o,mem_singleton_self _,v.le⟩)
 have w:= extent y.val P.B h1 h2
 rw [v] at w; unfold postL at w
 have :=P.B_pos
 by_contra! g
 nlinarith only [w,g,this,Nat.zero_le L]


def accent(L:ℕ):ℝ:=Real.exp (10*((2*postL L+1)^4:ℕ))

lemma tagcost :
    Sour.tact (eighth P.B) P.B (guardX P o L) ≤ accent L:=by
  unfold accent
  apply Real.exp_le_exp.mpr
  have e : widthK n P.B (guardX P o L) ≤ (((2*postL L+1)^4:ℕ):ℝ):= by
     change (coverNumber P.B (Lattice.halo _ {o}):ℝ)≤_
     rw [two_mul]
     exact_mod_cast tile o (postL L) P.B P.B_pos
  have hx:=P.B_pos
  have ey:eighth P.B≤10:= by
     have :1≤(P.B:ℝ):=by exact_mod_cast hx
     unfold eighth; rw [div_eq_mul_inv]; linarith only [inv_le_one_of_one_le₀ this]
  exact mul_le_mul ey e (Nat.cast_nonneg _) (by norm_num)


local notation "Y+:" X:max=> αK (guardX P o L) X
def pseudopod(y:Bag n): Bag n:=∑ X:Aura n,fun Z=> if Z=Y+:X then y X else 0
lemma total(y:Bag n): (∑ Z:Aura n,pseudopod P o L y Z)=∑X,y X:=by
 simp only [pseudopod,Finset.sum_apply]; rw [sum_comm]; simp

local notation "V+:" X:max=>Sour.tact (eighth P.B) P.B (Y+:X)
lemma down (k:Aura n→ℝ)(e:0≤k)(z:∀ i, o∉i.val→k i=0):
   (∑ X, k X * V+:X) ≤ accent L*voyageB k P.B (eighth P.B):=by
 rw [voyageB,mul_sum]
 apply sum_le_sum; intro i _
 by_cases v:o∈i.val; swap; · rw [z i v]; simp
 have r:i∈Cadre.blaze (guardX P o L):=mem_filter.mpr ⟨mem_univ _,
   fun y=>Finset.disjoint_left.mp y (halo_subset _ _ (mem_singleton_self o)) v⟩
 rw [mul_left_comm (accent L)]
 refine mul_le_mul_of_nonneg_left ?_ (e i)
 exact (tact_αK (by unfold eighth; positivity : 0 ≤ eighth P.B) r).trans
   (mul_le_mul_of_nonneg_right (tagcost P o L) (Real.exp_pos _).le)

theorem extend {e f:ℝ}{y:Bag n}(k:Barrage P q {o} h y (eighth P.B) e f):
  Barrage P q (guardX P o L).val h (pseudopod P o L y) (eighth P.B) (accent L*e) (accent L*f):=by
 obtain ⟨c,d,A,B,C,D⟩:=k.price
 have hm:0≤accent L:=(Real.exp_pos _).le
 let k1:=fun i=> c i * V+:i
 let k2:=fun i=> d i * V+:i
 have T:Barrage P q (guardX P o L).val h (pseudopod P o L y) (eighth P.B) (∑ X,k1 X) (∑ X,k2 X):=
   Barrage.whole _ _ _ _ (fun X _=>Barrage.single (Y+:X) _ ((A X).mantle subset_union_right) subset_union_left)
 exact T.bigR
    ((down P o L c (fun i=>(A i).tube.price) (fun i p=> (B i (by simpa only [singleton_subset_iff])).2.1)).trans (mul_le_mul_of_nonneg_left C hm))
    ((down P o L d (fun i=>let ⟨_,w,_⟩:=(A i).forms; w.price) (fun i p=>(B i (by rwa [singleton_subset_iff])).2.2)).trans (mul_le_mul_of_nonneg_left D hm))

abbrev arbour:=Lattice.halo (10000*P.B) {o}
lemma beyond(sz:2*(postL L*P.B)<(More n).val):
   ¬(guardX P o L).val⊆arbour P o :=by
 intro r
 obtain ⟨x,t⟩:=away o _ sz
 obtain ⟨u,b,h⟩:=halo_spec.mp (r (halo_spec.mpr ⟨o,mem_singleton_self _,t.le⟩))
 rw [mem_singleton] at b; rw [b,t] at h
 unfold postL at h
 have a:=P.B_pos
 nlinarith only [a,h,Nat.zero_le (L*P.B)]
end YM.CF.Merino.Corolla
