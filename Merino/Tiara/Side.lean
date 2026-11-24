import Merino.Tiara.Fold
import Merino.Tiara.Pleats
import Merino.Mitre.Jetstream
import Merino.Hem.Agate
import Merino.Plume.Glue
set_option autoImplicit false
set_option synthInstance.maxSize 26000
set_option maxRecDepth 2500
set_option maxHeartbeats 600000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.Tiara
open Function Filter Metric SU Lat Lattice Cube Finset Spire Scroll Tulip Skye Window Vale Girt Buffered Fock
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
open Branch Sault Dial Vow BProof Reed Brooch Thera Kennel Hest

variable {N:Side}
open Plume Swell Sour Levier StressExchange

variable (z:Sweep N)
set_option maxHeartbeats 50000
lemma fareB (T:Sa N) (U V:Pane N):
  fare T (profile (flashA z U)) (profile (flashA z V)) =
    fare (mount z T) (profile U) (profile V):=by
 rw [show profile (flashA z U) = _ from veil_p z.charge (castX z) U,
    show profile (flashA z V) = _ from veil_p z.charge (castX z) V, roseC, tock]
 rfl

open RG Buffered.Lifted
variable {m:ℕ}{a b d τ:ℝ}{X:SOp N}{K:Scree.Loom N}{B:BudgetPoint}{o:Seat N}
lemma skirt {x y:LinksC}
 (r:Skylit B d K)(ha:0≤a)(h:Trunk o X (B.B/10) a b d)(g:B.threshold=τ)
 (v:quiz m τ x=quiz m τ y):
 entryBudget (masked K B o X (flashA z (dark N m x)) - masked K B o X (flashA z (dark N m y))) ≤
 cable m b d * dist (echoC m x) (echoC m y):=by
 have w:0≤b:=(norm_nonneg _).trans (norm_U h.pay ha (r.slot (1,fixedTags N)))
 have t:(flashA z (dark N m x) ∈ pass B o)↔(flashA z (dark N m y)∈ pass B o):=by
    rw [←pass_move,←pass_move]; exact ⟨lit_dark v _ g _,lit_dark v.symm _ g _⟩
 by_cases u:flashA z (dark N m x) ∈pass B o
 · apply (joins r ha h u (t.mp u)).trans

   rw [fareB]
   refine (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right (milk _ _) (abs_nonneg d)) w).trans_eq ?_
   unfold cable; ring
 rw [masked,Set.indicator_of_notMem u,Set.indicator_of_notMem (mt t.mpr u)]
 simp only [sub_self,entryBudget,Matrix.zero_apply,norm_zero,sum_const_zero]
 exact mul_nonneg (cable_pos m w _) dist_nonneg

lemma earringPair(A D:Op (Single N)):dist (preJ (tickA N) A) (preJ (tickA N) D)≤
     entryBudget (A-D) + entryBudget (A-D):=by
 rw [dist_eq_norm,show preJ (tickA N) A - preJ (tickA N) D = preJ (tickA N) (A-D) from ?_]
 · exact Mitre.earring ..
 have h(V W:Op (Single N)):dg (V-W)= dg V-dg W:=by rw [sub_eq_add_neg,dg_add,dg_neg,←sub_eq_add_neg]
 unfold preJ; rw [mul_sub _ A D,sub_mul,h,Matrix.trace_sub,sub_smul];abel
private lemma clear (w r:Bool)(U:UNI (Single N))(A:FC (Single N)):
    ‖tourP U w r A‖=‖A‖:=by
 have d: ‖windX w A‖=‖A‖:= by cases w; rfl; exact norm_cc _
 cases r
 · exact (twist_norm _ _).trans d
 exact ((twist_norm _ _).trans (norm_cc _)).trans d

open Hive
lemma clasp(z:Sweep N)(A:FC (Single N)):‖teen z A‖=‖A‖:=clear ..

lemma beaded {F:Evaluation N}(V:Pane N): ‖(Bide.move z⁻¹ F) V‖= ‖F (flashA z V)‖:=by
 change ‖teen _ (F (flashA z⁻¹⁻¹ V))‖=_
 rw [inv_inv,clasp]
lemma beaded_d {F:Evaluation N}(U V:Pane N):
 dist ((Bide.move z⁻¹ F) U) ((Bide.move z⁻¹ F) V)=dist (F (flashA z U)) (F (flashA z V)):=by
 simp only [dist_eq_norm]
 change ‖teen z⁻¹ (F (flashA z⁻¹⁻¹ U)) - teen z⁻¹ (F (flashA z⁻¹⁻¹ V))‖ = _
 rw [←map_sub,inv_inv,clasp]
lemma led (e:boxA z 0=0):mount z (centerB N m)=centerB N m:=by
 unfold centerB purse mount Bide.regionD
 rw [←show Salt.actY z⁻¹ _ = Finset.map .. from rfl,←Salt.walkA]
 simp [Salt.actY, sitU,e]

variable {y:Spool N}(t:y.Hem K B a b d)
abbrev topper (i:Axis)(z:Sweep N)(y:Spool N)(K:Scree.Loom N)(B:BudgetPoint):=
 Bide.move z⁻¹ (y.jPole K B i)
include t
lemma floss (eqm:B.B+16=m)(e:boxA z 0=0)(h:separation 0 y.post ≤4)
 (ht:B.threshold=τ)(i:Axis):
 Floss m τ (b+b) (2*cable m b d) (topper i z y K B):=by
 have r:= t.skylight; have u:=t.spurt i
 have l0:casing B y.post ⊆ centerB N m:=eqm ▸ Hem.space_at (b:=B.B) h le_rfl
 have j := inlay z ((t.jPole i).up l0)
 rw [led z e] at j
 refine ⟨j.loc,fun g v=> j.gauge_x _ _,fun x=>?_,fun x w g=>?_⟩
 · rw [topper,beaded]
   exact (Mitre.earring _).trans (add_le_add (mask_sum r t.sign u _) (mask_sum r t.sign u _))
 rw [topper,beaded_d,two_mul,add_mul]
 exact (earringPair _ _).trans (add_le_add (skirt z r t.sign u ht g) (skirt z r t.sign u ht g))

end YM.CF.Merino.Tiara
