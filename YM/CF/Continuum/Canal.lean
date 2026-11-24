import YM.Branch.Covariant
import YM.Push.GRID_APPROXIMATION.KernelLocal
import YM.Next.RANK.Swath
import YM.CF.Continuum.Algebra

/-!
# Buffered positive-time Markov transport used to propagate real gauge part of the probe net under
`stove`. Includes reflected products. Uses the `GridApprox.back` base-project infrastructure.
Periods are actual `Carousel` periods and this addresses native stencil resolution (at fixed x),
not assuming agreement of coordinate choices on any thermal model.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Window
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision
open Lat Cube RP Push.GridApprox Next.Rank.Thirst
open scoped Topology BigOperators Classical
local notation "M"=> More
variable {c f B:Side}(P:Patch)(s:Axis)
def buffered (s:Axis)(p:Patch)(c:Side):Finset (Site (More c)):=univ.filter fun x=> reach p < (x s).val ∧ (x s).val+reach p<c.val
variable{G:Gauge}
lemma buff_disjoint : Disjoint ((buffered s P c:Set (Site (More c)))) ↑(swath (Signed.mirror s) 0 (buffered s P c)):=by
 refine Set.disjoint_left.mpr (fun i ht v=>?_); obtain ⟨j,p,rfl⟩:= Finset.mem_image.mp v
 have hm:(affine (Signed.mirror s) (0:Site (More c)) j) s= -(j s):=by simp [affine,Signed.act,Signed.mirror]
 obtain ⟨hl,hk⟩:=(Finset.mem_filter.mp p).2; obtain ⟨ht,hv⟩:= (Finset.mem_filter.mp ht).2; rw [hm] at *; haveI:NeZero (j s):= ⟨fun k=>by rw [k,ZMod.val_zero] at hl; omega⟩; rw [ZMod.val_neg_of_ne_zero] at ht hv; have he:(More c).val=c.val*2:=rfl; omega
lemma buff_up (m B:Side) : buffered s P (CSide m B) ⊆ upField m B s:= fun i p=> (north_mem ..).mpr (show _ from le_trans (Nat.le_add_right (i s).val _) ((Finset.mem_filter.mp p).2.2.le))
lemma embed_nat_ax (H:Ratio c f)(x: Site c) : (H.embed x s).val=H.count.val*(x s).val:=by
 let y:Cover:=fun i=> (x i).val
 have hy: wrap c y=x:=funext fun i=> (by dsimp [wrap_here,y]; rw [Int.cast_natCast,ZMod.natCast_zmod_val]) -- tune dsimp
 let L:=H.count.val; have z : H.embed x s=(L : Per f)*(x s).val:=by
    rw [show H.embed x= _ from (congrArg H.embed hy.symm).trans (H.embed_wrap y)]; simp only [wrap_here, nsmul_eq_mul]; simp [y,L] -- tune
 rw [z,←Nat.cast_mul, ZMod.val_natCast_of_lt]; rw [H.exact_size,mul_comm c.val]; exact Nat.mul_lt_mul_of_pos_left (ZMod.val_lt _) H.count.property
lemma buff_far (H:StepData (More c) (More f))(_hp:H.patch=P) (x:Site (More c))(u:x∈buffered s P c): window (H.ratio.embed x) (reach P) ⊆ ↑(buffered s P f):=by
 let R:=reach P; let L:=H.ratio.count.val; obtain ⟨ht,hx⟩:= (Finset.mem_filter.mp u).2
 have he: f.val=c.val*L:=by have he:= H.ratio.exact_size; change (More f).val = (More c).val*L at he; change f.val*2= c.val*2*L at he; rw [mul_right_comm c.val] at he; omega
 have hv:3 ≤ L:= H.patch.coarse; intro y p; obtain ⟨k,u',rfl⟩:=p; let Y:= k s +(H.ratio.embed x s).val
 obtain ⟨hk,vX⟩:= box_test.mp u'
 have hy:R<(k s)+(H.ratio.embed x s).val ∧ (k s)+(H.ratio.embed x s).val+ R < ↑f.val:=by
    rw [embed_nat_ax s, he]; change _<k s+↑(L*(x s).val) ∧ k s+↑(L*(x s).val)+ R<_
    have h:R < (x s).val:= ht; have hb:2*R ≤ L*R:= Nat.mul_le_mul_right R (by omega); have hh:= Nat.mul_lt_mul_of_pos_left ht (by omega: 0<L); have hz:= Nat.mul_lt_mul_of_pos_left hx (by omega: 0<L); have hi:=hk s; have hK:=vX s; change -(R:ℤ) ≤ _ at hi; change _ ≤ (R:ℤ) at hK; change L*R < _ at hh; change L*((x s).val+R) < L*c.val at hz; rw [mul_add] at hz; rw [Nat.mul_comm c.val]; omega
 have hp:Y.toNat < (More f).val:=by have ht:= f.property; unfold Y; change _ < f.val * 2; omega
 have hz:Y ≥ 0:=by unfold Y; omega
 have hk:(wrap f k)=(wrap f k):=rfl
 have hw : (wrap (More f) k + H.ratio.embed x) s=(Y.toNat: Per (More f)):=by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hz]; unfold Y; rw [Int.cast_add, Int.cast_natCast, ZMod.natCast_zmod_val]; rfl
 refine Finset.mem_filter.mpr ⟨mem_univ _,?_⟩; dsimp only; rw [hw,ZMod.val_natCast_of_lt hp]; change R <_ ∧ _+R < _; unfold Y at hz ⊢; omega
end YM.CF.Window
