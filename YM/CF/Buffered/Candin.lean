import YM.CF.Buffered.SugarCap
import YM.CF.Buffered.Weight
/-!
# Hot scalar mesh and seed in the cube
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 22000
set_option maxHeartbeats 420000
noncomputable section
namespace YM.CF.Buffered.Region
open Function Filter NormedSpace SU Lat Lattice Cube Finset Mir Mir.Trip Phase RP MeasureTheory Roost Rails Mil RG WilsonStartup Spark Nova Fock Gloss Scroll Spire Push.SectorMeasure Ordered
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
attribute [local instance] opCStarAlgebra
variable {m p v w l B n:Side}
local notation "D" => Domain m B
local notation "qM" => GridN m
local notation "I" => Xmind m B
local notation "X" => Pack m B
local notation "S" => Locale v B
local notation "N" => CSide v B
local notation "d" => Domain v B
local notation "g" => GridN v
variable {e x:ℝ}
namespace Ticket
variable (b: Ticket m v B p e x)(F:Pack m B)
variable (q:Clip) (β:ℝ)
lemma whole_coin : ∑ r, priceF q (reel r (b.K.fromCube F))=Vale.basicP q F.1:=by
 unfold priceF; rw [sum_comm, plain_s, Fintype.sum_prod_type_right]; refine sum_congr rfl fun i _=> ?_; simp_rw [Facade.intrinsic]; exact (b.K.sugar B).ports_sum (Facade.frame i) (fun j=> coinF q (faceValue F.1 (j,i))) -- tune
lemma whole_bill (h:F∈secure e x) : ∑ r, b.sumBill (reel r (b.K.fromCube F))=b.pin.cabin b.W F:=by unfold sumBill; simp_rw [tab_reads b F _ _ h]; rw [←tab_sum b.pin b.W]; exact b.K.pebbles.ports_sum ∅ (fun i=>tab b.pin b.W i F)
lemma whole_drizzle (h:F∈secure e x): ∏ r,b.drizzle (reel r (b.K.fromCube F))=net m B 0 F :=by
 have he (i):0 < water m B F.1 i F.2 := (water_pos ..).lt_of_ne (Ne.symm (((whole_s ..).1 h).1 i)); let W(i: Index m):= Real.log (water m B F.1 i F.2)
 unfold drizzle; simp_rw [water_reads, Real.rpow_def_of_pos (he _)]; rw [netv]; simp_rw [← Real.exp_sum]; rw [show (∑ r:Rail (Uniform p), ∑ i:Tor g,_) = ∑ i,W i from ?_, Real.exp_sum]
 · exact prod_congr rfl (fun i _=> Real.exp_log (he i))
 simp_rw [mul_comm (Real.log _)]; exact b.K.pebbles.ports_sum ∅ W
lemma whole_portion (h:F∈secure e x): Heat.scalarWeight b.pin b.W q β x e F= ∏ r,b.deck q β (reel r (b.K.fromCube F)):=by
 unfold deck Heat.scalarWeight primal; rw [Set.indicator_of_mem (show F ∈ TallyR m B e 0 from h.1),Set.indicator_of_mem (show F.1∈Calm group D x from h.2)]; simp_rw [Set.indicator_of_mem (((permit_iff ..).1 h) _), portion]
 rw [prod_mul_distrib, ← Complex.ofReal_prod, ← Complex.exp_sum, sum_sub_distrib,sum_neg_distrib, ←mul_sum, ← Complex.ofReal_sum, whole_coin b, whole_drizzle b F h, whole_bill b F h,sub_eq_add_neg,Complex.exp_add,Complex.ofReal_mul,Complex.ofReal_exp,Complex.ofReal_neg,Complex.ofReal_mul]; ring
lemma veil (a:F∉secure e x): (∏ r,b.deck q β (reel r (b.K.fromCube F)))=0:=by
 obtain ⟨v,h⟩ := not_forall.mp fun q=> a ((permit_iff ..).2 q); exact prod_eq_zero (mem_univ v) (Set.indicator_of_notMem h _)
lemma on_weights : ∏ r,b.deck q β (reel r (b.K.fromCube F))= Heat.scalarWeight b.pin b.W q β x e F:=by
 by_cases h:F∈secure e x; exact (b.whole_portion F q β h).symm
 rw [veil b F q β h]; unfold Heat.scalarWeight primal; by_cases p:F∈TallyR m B e 0; rw [Set.indicator_of_mem p,Set.indicator_of_notMem (show F.1∉Calm group D x from fun t=>h ⟨p,t⟩)]; simp; rw [Set.indicator_of_notMem p]

open Cin
local notation "T" => CSide m B
lemma cube_seed (_h:F∈secure e x) : Phase.pair m B F.1 F.2=jump (Equiv.refl _) (fun i=> localPair (grain m B F.1 (slot m F.2) (stick 0) i)):=rfl
lemma cube_R (h:F∈secure e x) : seedR (upperP T) (Phase.pair m B F.1 F.2)=∑ r, ∑ i: Post N, into (Mil.side ((b.K.spirit B).zone r i.val)) (b.seedM i (reel r (b.K.fromCube F))) :=by
 let A := fun i: Site T=> grain m B F.1 (slot m F.2) (stick 0) i
 rw [cube_seed F h]; rw [installed_seed (Mil.due T) (fun i=> localPair (A i)) _ (fun i j x y=> jump_apply ..) above (upperP T) ?_]; swap; · intro i x; change (i,x)∈ _↔_; simp [upperP,above]
 rw [←Equiv.sum_comp (b.K.spirit B).slots, Fintype.sum_prod_type]; refine sum_congr rfl fun i _=> sum_congr rfl fun j _=>?_ ; rw [seedI b _ (((permit_iff ..).1 h) _),paint_reads b]; rfl
end Ticket
end YM.CF.Buffered.Region
#print axioms YM.CF.Buffered.Region.Ticket.cube_R
