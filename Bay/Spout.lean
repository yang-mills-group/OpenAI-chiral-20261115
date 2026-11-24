import Bay.Porch
import Zephyr.Chern.Amber
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Bay
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet Scroll Finset Palot Cadre Vow
open RG MeasureTheory Rue
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Tap Levier Thera Oath Font Spire Dial Rill
open Kennel Swell


open Zephyr.Chern
variable {N:Side}{o:Seat N}{S:Band N}{F:Oil N}{C:Toll (Single N)}{d a g B W:ℝ}{A:StemA N}

lemma soakBough (h:Soak o F a g d) :
 ∃ t:Bough d a g F,tallyC a t.c ≤ g ∧ ∀ D,t.c D≠0 → o∈D:= by
 obtain ⟨G,C,h,z,u,j⟩:=h
 let H:Band N→Oil N:= fun S x=> if hx:x∈Openc _ d then G S ⟨x,hx⟩ else 0
 have hh(T):G T=fun x=> H T x.val:=funext fun x=> by simp [H,x.property]
 refine ⟨⟨H,C,fun D=>?_,tally_F (fun D=>(h D).nonn) u,fun x t=>?_⟩, u,fun D p=> of_not_not (fun l=>p (z D l))⟩
 · have p:=h D; rw[hh D] at p;exact p
 calc
    _ = _ := j ⟨x,t⟩
    _ = _ := sum_congr rfl fun T _=>congrFun (hh T) ⟨x,t⟩

open Zephyr in
lemma rootBand {i j:Single N}
 (w:Oily a d B W)(t:Temper o A B)(p:C i j≠0 → o∈S)
 (v:Piece d S C F)(k:Fin 3) :
 ‖wad F A i j k‖≤ W*(rent a S * C i j):=by
 by_cases u:C i j=0
 · simp [wad,(kernel_free v u w.s.ready A).bud_eq,u]


 have l:= t.above
 have a1:1≤ B*(1+(S.card:ℝ)) :=one_le_mul_of_one_le_of_one_le l (by simp)
 have e':∀ x∈leaks S, |A x| ≤ B*(1+(S.card:ℝ)) := by
    intro x hx
    have h:= (((v.expo i j).triggered u).1).lim _ (mem_filter.mp hx).2.1 _ (p u)
    exact (t.grow x).trans (mul_le_mul_of_nonneg_left (add_le_add_right (by exact_mod_cast h.le) _) (zero_le_one.trans l))
 refine ((kernel_jet v w.s a1 e').2 k).trans ?_
 rw [← mul_assoc]
 refine mul_le_mul_of_nonneg_right ((w.q _).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) w.bound.le)) (v.nonn i j)
 exact mul_le_mul_of_nonneg_right (half_le_self w.hb.le) (by positivity)

open Zephyr
def spout (F:Oil N)(A:StemA N)(t:ℝ):ℂ:= Matrix.trace (F (profile (Chern.petals A t)))
lemma spoutBloom (x:Bough d a g F)(h:0<d)(A:StemA N) :
 Bloom (spout F A) (∑i,∑S, wad (x.f S) A i i):= Bloom.sum _ fun i _=> x.drip_sum A i i h
lemma rootSpout (w:Oily a d B W)(t:Temper o A B)(p:Soak o F a g d):
  Bud (spout F A) ∧ ∀ k,‖bud (spout F A) k‖≤W*g:=by
 obtain ⟨x,b,z⟩:=soakBough p
 have h:= spoutBloom x w.s.ready A
 refine ⟨h.1,?_⟩

 rw [h.bud_eq]
 intro k;simp_rw [Finset.sum_apply]
 apply le_trans (norm_sum_le ..)
 rw [tallyV] at b
 apply le_trans _ (mul_le_mul_of_nonneg_left b w.bound.le)
 simp_rw [mul_sum]
 exact sum_le_sum fun i _=>
   le_trans ((norm_sum_le ..).trans (sum_le_sum fun S _=>rootBand (C:=x.c S) (i:=i) (j:=i) w t 
    (fun u=>z S (fun e=>u (e ▸ rfl))) (x.pie S) k))
    ((mul_sum _ _ _).symm.trans_le (single_le_sum (fun j (_:j∈univ)=> mul_nonneg w.bound.le (sale_nn (fun S=>(x.pie S).nonn) a i j)) (mem_univ i))) -- sum rw issue

end YM.CF.Bay
#print axioms YM.CF.Bay.rootSpout
