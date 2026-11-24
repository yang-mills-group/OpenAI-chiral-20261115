import Verses.Fusing
import CellQ.Keel
import YM.SU5.Relativistic.Raspa
import YM.CF.Continuum.Extensive
/-! # pinpoint charge. On clean ORBIT. (For unrepaired dirty count by t.) -/
set_option autoImplicit false
set_option maxHeartbeats 420000
noncomputable section
namespace YM.CF.Papyrus.Franc
open Function Filter NormedSpace Metric Fock Finset Lattice Lat Fir Ember Thera BPress.Spin.Blank Rush SU Scroll Tulip Dial Cube Skye Pannier Pannier.Chancel Buffered Pastry
open Crest.Sleet Pannier.Damask
open scoped Topology Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator BigOperators ComplexOrder Kronecker
attribute [local instance] opCStarAlgebra
open Graph Skye RG Laic Scree Peaks Branch
namespace Verses
variable {N:Side}{R:GramM N}{a b h v:ℝ} -- fix
lemma bases_f (X:Orbit N)(p:Dark (fun _=>False) R.K R.p h a)(hh:0≤h): ∑ i:Scree.Force N,tier h (clamp R.p i (R.K i) X).val ≤a*(More N).val^4:=by
 obtain ⟨f,g,H⟩:=p.weight
 have hs(i):0≤f i:= (Pastry.pitch hh _).trans (Graph.pad (g i) hh X)
 calc
 _ ≤ ∑ i:Scree.Force N,f i:=sum_le_sum fun i _=>Graph.pad (g i) hh X
 _ ≤ ∑ i:Scree.Force N,R.p.mass i.val.1.val.2 (f i):=sum_le_sum fun i _=> R.p.loMass _ _ (hs i)
 _ ≤ ∑ i:Scree.Force N,∑ j:Seat N, if j∈i.val.1.val.2 then R.p.mass i.val.1.val.2 (f i) else 0:=by
    apply sum_le_sum; intro i _; let v:=R.p.mass i.val.1.val.2 (f i); have ht:= single_le_sum (s:=(univ :Finset (Seat N))) (f:=fun j=> if j∈i.val.1.val.2 then v else 0) (fun y _=>by split; exact (hs i).trans (R.p.loMass _ _ (hs i)); exact le_rfl) (mem_univ i.val.1.val.1); rw [if_pos i.val.1.property] at ht; exact ht
 _ ≤_:=by rw [sum_comm]; exact (sum_le_sum (g:=fun _=>a) (fun i _=>H i)).trans_eq (by rw [sum_const,card_univ,site_card,nsmul_eq_mul]; push_cast; ring)
variable (h)
private lemma resolve_f (X:Orbit N)(K:ForceBudget N)(hh:0≤h)(k:BudgetPoint): tier h (fueled k K X).val ≤ Real.exp (∑ i:Scree.Force N,tier h (clamp k i (K i) X).val):=by
 let f(i:Force N):=tier h (clamp k i (K i) X).val; have ht (i):0≤f i:=pitch hh _
 classical
 have hp(s:Finset (Force N)): tier h ((∏ i∈s,clamp k i (K i) X).val)≤ ∏ i∈s,f i:=by
    induction s using Finset.induction_on with
    | empty=> rw [prod_empty,prod_empty]; exact (white1 (n:=LeanV (Single N)) h).le
    | insert i s v ih=> rw [prod_insert v,prod_insert v]; exact (tier_mul hh _ _).trans (mul_le_mul_of_nonneg_left ih (ht i))
 let W(s:Finset (Force N)):= if coverF k s X.1 ∧ Set.PairwiseDisjoint (s:Set (Force N)) (fun x=> x.val.1.val.2) then ∏ j∈s, clamp k j (K j) X else 0
 change tier _ (∑ i:Finset (Force N), W i).val ≤_ -- tune ite instance
 rw [show (∑ i:Finset (Force N), W i).val=∑ i,(W i).val from Graph.pipeP (LeanV (Single N)) _ _]; apply (tier_sum hh _ _).trans; apply (le_trans (b:=∑ i:Finset (Force N), ∏ j∈i,f j)); · refine sum_le_sum fun i _=>?_ ; unfold W; split; exact hp _; exact (show tier _ (0:Cipher N).val=0 from chaff _).trans_le (prod_nonneg fun i _=>ht i)
 have he:∏ i: Force N,(f i+1)=∑ s:Finset (Force N),∏ i∈s,f i:=by rw [prod_add]; simp
 rw [←he]; refine (prod_le_prod (fun i _=>by linarith [ht i]) (g:=fun i=>Real.exp (f i)) (fun i _=>Real.add_one_le_exp _)).trans_eq ?_; rw [← Real.exp_sum]
lemma rented (X:Orbit N)(R:GramM N)(E:RegBudget N)(F:ForceBudget N){a b c:ℝ}(hr:Graph.Ledger h a a b c R)(hh:0≤h): let Z:= Oise.color_b R R.beta (R.F+E) R.slip (R.K+F) R.v; let n(i:Scree.Hub N):=numbE R.p.threshold i.val.2 (E i) X.1
 let f(i:Scree.Force N):=clamp R.p i (F i) X
 tier h (Z.board X).val ≤ Real.exp ( (3*a)*(More N).val^4+(∑ i,tier h (n i).val)+(∑ i,tier h (f i).val)):=by -- valid actually mim_
 intro Z n f; let V:= (More N).val; let d:ℝ:=a*V^4
 let U:= ∑ i,tier h (n i).val; let D:= ∑ i,tier h (f i).val
 have he: tier h (Graph.actG Z X).val ≤ (d+d)+U:=by
    let A:= ∑ i,n i
    rw [show Graph.actG Z X=Graph.actG R X+A from ?_]; swap
    · change exponentL R.p (R.F+E) X.1 +_ = _+ exponentL R.p E X.1; rw [Larch.ripe_H R.p X]; change _+exponentL R.p R.slip X.1=_; unfold actG; abel
    apply (tier_plus hh ..).trans (add_le_add (Graph.marks R X hr.reg hr.slip hh |>.trans (le_of_eq (by unfold d V; ring))) ?_); unfold A U; change tier _ ((∑ i, n i).val)≤ _; rw [Graph.pipeP (LeanV (Single N)) (fun i=> n i) univ]; exact tier_sum hh _ _
 have hF:tier h (fueled Z.p Z.K X).val ≤ Real.exp (d+D):=by
    refine (resolve_f h X Z.K hh Z.p).trans (Real.exp_monotone ?_)
    apply le_trans _ (add_le_add (bases_f X hr.force hh) (le_refl D)); unfold D; rw [←sum_add_distrib]; apply sum_le_sum; intro i _; rw [show clamp Z.p i (Z.K i) X=clamp R.p i (R.K i) X+f i by change clamp R.p i ((R.K+F) i) X=_; unfold f clamp; split_ifs; rfl; simp]; exact tier_plus hh .. 
 change tier h ((exp (Graph.actG Z X): Dough _).val*(fueled Z.p Z.K X).val) ≤ _
 apply ((tier_mul hh (exp (Graph.actG Z X)) (fueled Z.p Z.K X)).trans (mul_le_mul ((dust_exp _ _ hh).trans (Real.exp_monotone he)) hF (pitch hh _) (Real.exp_pos _).le)).trans
 rw [←Real.exp_add]; exact le_of_eq (congrArg Real.exp (by unfold d D V U; ring))
end Verses
end YM.CF.Papyrus.Franc
