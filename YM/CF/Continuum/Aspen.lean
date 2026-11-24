import YM.CF.Graph.Coif
import YM.CF.Petal.Event
/-!
# A real-linear continuity estimate for thermal matching on *relative* financial columns
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
set_option maxHeartbeats 640000
set_option synthInstance.maxSize 16000
set_option linter.unusedSectionVars false
namespace YM.CF.Graph.Diff
open Function Filter Finset NormedSpace Lattice Cube SU Fock Lat Spire Scroll Peaks Drapes Rush Tulip Pastry Scree Girt Gall Branch Dial RG Skye Laic
open scoped Topology ContDiff Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Classical
attribute [local instance] opCStarAlgebra
variable {n:Side}{p:BudgetPoint}{Q Q':Sweep n→Prop}{h a C r v κ:ℝ}
abbrev rankV (n:Side)(u:ℝ):=u*(More n).val^4
local notation "κX" x:max => tier h (x:Cipher n).val
variable {U V:ForceBudget n}
variable (hp:1≤h)(x:Orbit n)
include hp in
lemma costs_U (e:Dark Q U p h v) : ∑ i:Force n,tier h (clamp p i (U i) x).val ≤ rankV n v:=by
 obtain ⟨f,B,H⟩:= e.weight; have hu:=zero_le_one.trans hp; have ht(i):0≤ f i:= (Pastry.pitch hu _).trans (pad (B i) hu x); let W(i:Force n):= p.mass i.val.1.val.2 (f i); apply (sum_le_sum (fun i _=>pad (B i) hu x)).trans
 calc
       _ ≤ ∑ i:Force n,∑ j:Seat n, if j∈i.val.1.val.2 then W i else 0:= sum_le_sum fun i _=> (p.loMass _ _ (ht i)).trans (by
         have hg : ∀ j:Seat n, 0 ≤ if j∈i.val.1.val.2 then W i else 0:=fun j=>by split; exact (ht _).trans (p.loMass _ _ (ht i)); exact le_rfl
         have he:= single_le_sum (s:= (univ:Finset (Seat n))) (fun j _=>hg j) (mem_univ i.val.1.val.1); rw [if_pos i.val.1.property] at he; exact he) -- adapted from toeF
       _ ≤ _ := by rw [sum_comm]; exact (sum_le_sum (g:=fun _=>v) (fun i _=> H i)).trans_eq (by rw [sum_const,card_univ,show Fintype.card (Seat n)= _ from site_card _]; simp [rankV,mul_comm])
section helper
variable {μ:Type*}[DecidableEq μ][Fintype μ]
variable (hpo:0≤h)(A B: μ→ Cipher n)
local notation "τ" a:max => tier h (a:Cipher n).val
include hpo in
private lemma prod_C (s:Finset μ)(Q:μ→ℝ)(e:∀ i∈s, τ (A i) ≤ Q i) : τ (∏ i∈s,A i) ≤∏ i∈s,Q i:=by
 induction s using Finset.induction_on with
 | empty=> simp only [prod_empty]; exact (white1 _).le
 | insert i s v ih=> rw [prod_insert v,prod_insert v]; have he:=e i (mem_insert_self ..); exact (tier_mul hpo (A i) _).trans (mul_le_mul he (ih fun j h=>e j (mem_insert_of_mem h)) (Pastry.pitch hpo _) ((Pastry.pitch hpo _).trans he))
local notation "Qz" => (fun i=>tier h (A i).val+tier h (B i).val)
local notation "℘" => (fun i=>tier h (A i-B i).val)
def bit_J (s:Finset μ)(i:μ)(p f:μ→ℝ) := if i∈s then p i*∏ j∈s.erase i,f j else 0
include hpo
private lemma summands (s:Finset μ) : tier h ( (∏ i∈s,A i) - ∏ i∈s,B i).val ≤ ∑ i, bit_J s i (fun i=> tier h (A i-B i).val) (fun i=>tier h (A i).val+tier h (B i).val) :=by
 let q := Qz; let f:=℘; have hA(i): τ (A i) ≤ q i:= le_add_of_nonneg_right (Pastry.pitch hpo _); have hB(i):τ (B i) ≤ q i:=le_add_of_nonneg_left (Pastry.pitch hpo _)
 have hf(i):0≤f i := Pastry.pitch hpo _; have hq(i):0≤q i:=(Pastry.pitch hpo _).trans (hA i)
 induction s using Finset.induction_on with
 | empty=> simp only [prod_empty,bit_J,notMem_empty,ite_false,Finset.sum_const_zero,sub_self]; exact (chaff _).le
 | insert i s v ih=>
    let a:=∏ i∈s,A i; let b:=∏ i∈s,B i
    have he: tier h (A i*a-B i*b).val ≤ f i*(∏ j∈s,q j)+q i* ∑ j,bit_J s j f q:=by
       rw [show A i*a-B i*b=(A i - B i)*a+B i*(a-b) from by ring]; refine (tier_plus hpo ((A i-B i)*a).val (B i*(a-b)).val).trans ?_; exact add_le_add ((tier_mul hpo (A i-B i) a).trans (mul_le_mul_of_nonneg_left (prod_C hpo A s q (fun j _=>hA j)) (hf _))) ((tier_mul hpo (B i) (a-b)).trans (mul_le_mul (hB i) ih (Pastry.pitch hpo _) (hq _)))
    rw [prod_insert v,prod_insert v]; refine he.trans_eq ?_
    have hx : f i*(∏ j∈s,q j)=∑ j,if j=i then f i*(∏ j∈s,q j) else 0:=by simp
    rw [hx,mul_sum, ←sum_add_distrib]; apply sum_congr rfl; intro j _; by_cases t:i=j
    · subst j; simp only [bit_J, if_pos, mem_insert_self, erase_insert v,if_neg v,mul_zero,add_zero]; rfl
    rw [if_neg (Ne.symm t),zero_add]; unfold bit_J; by_cases h:j∈s; swap; · simp [h, Ne.symm t];
    rw [if_pos h, if_pos (mem_insert_of_mem h), Finset.erase_insert_of_ne t, prod_insert (show i∉s.erase j from (fun x=> v (erase_subset _ _ x)))] -- tune order!
    change q i* (f j* _)= f j*(q i* _); ring
-- use identity sum via INSERT; supports cost tens.V.
omit hpo
private lemma census (f q:μ→ℝ)(i:μ): ∑ s:Finset μ,bit_J s i f q=f i * ∏ j∈ univ.erase i,(q j+1):=by
 let T:=univ.erase i; rw [prod_add,mul_sum]; simp only [prod_const_one,mul_one]; unfold bit_J; rw [←sum_filter]; let S:= univ.filter (fun s:Finset μ=> i∈s); have ht(j:Finset μ)(p:j∈T.powerset):i∉j:=fun s=>notMem_erase _ _ ((mem_powerset.mp p) s)
 have hz:S=T.powerset.image (fun j:Finset μ=> insert i j):=by
    ext j; refine ⟨?_,?_⟩; intro p; exact mem_image.mpr ⟨j.erase i, mem_powerset.mpr (fun k p=> mem_erase.mpr ⟨(mem_erase.mp p).1,mem_univ _⟩), insert_erase (mem_filter.mp p).2⟩; rintro p; obtain ⟨k,v,rfl⟩:=mem_image.mp p; exact mem_filter.mpr ⟨mem_univ _,mem_insert_self ..⟩
 change ∑ j∈S,_= _; rw [hz,sum_image]; apply sum_congr rfl; intro j p; rw [erase_insert (ht j p)]
 intro j v k p h; change insert i j= insert i k at h; exact Eq.trans ((erase_insert (ht j v)).symm) (Eq.trans (congrArg (·.erase i) h) (erase_insert (ht k p))) -- `.image` arguments
end helper
private lemma clamp_diff (p:BudgetPoint)(X:Force n) : clamp p X (U X) x-clamp p X (V X) x=clamp p X ((U-V) X) x:=by unfold clamp; split <;> simp_all
include hp in
lemma fuel_diff (hu:Dark Q U p h v) (hv:Dark Q V p h a)(u:Dark Q' (U-V) p h κ): tier h (fueled p U x-fueled p V x).val ≤ rankV n κ * Real.exp (rankV n v+rankV n a):=by
 let A(i:Force n):= clamp p i (U i) x; let B(i):=clamp p i (V i) x; let f(i):=tier h (A i-B i).val; let q(i):=tier h (A i).val+tier h (B i).val; let U'(s:Finset (Force n))(f: Force n→Cipher n):= if coverF p s x.1 ∧ Set.PairwiseDisjoint (s:Set (Force n)) (fun x=> x.val.1.val.2) then ∏ i∈s,f i else 0
 have hp0:=zero_le_one.trans hp; have hf(i:Force n):0 ≤ f i:= Pastry.pitch hp0 _; have hq(i:Force n):0 ≤ q i:= add_nonneg (Pastry.pitch hp0 _) (Pastry.pitch hp0 _)
 have he(s): tier h (U' s A-U' s B).val≤ ∑ i,bit_J s i f q:=by
    unfold U'; split; exact summands hp0 A B _
    rw [sub_self, show tier h (0:Cipher n).val = 0 from chaff _]; apply sum_nonneg; intro i _; unfold bit_J; split; exact mul_nonneg (hf i) (prod_nonneg fun i _=>hq i); exact le_rfl
 have hx:(∑ i,f i) ≤rankV n κ:=by
    unfold f A B; simp_rw [clamp_diff x p]; exact costs_U hp x u
 have hz:∑ i,q i ≤ rankV n v+rankV n a:=by unfold q; rw [sum_add_distrib]; exact add_le_add (costs_U hp x hu) (costs_U hp x hv)
 change tier h ((∑ i,U' i A)-(∑ i,U' i B)).val≤_; rw [←sum_sub_distrib,show ((∑ i,(U' i A-U' i B)):Cipher n).val= ∑ i,(U' i A-U' i B).val from pipeP _ _ _]; apply le_trans (le_trans (tier_sum hp0 _ _) (sum_le_sum (fun i _=>he i))); rw [sum_comm]; simp_rw [census f q];
 refine le_trans ?_ (mul_le_mul_of_nonneg_right hx (Real.exp_pos _).le); rw [sum_mul]; apply sum_le_sum; intro i _; apply mul_le_mul_of_nonneg_left _ (hf i);
 refine le_trans (prod_le_prod (fun i _=> add_nonneg (hq i) zero_le_one) (g:=fun i=>Real.exp (q i)) (fun i _=>Real.add_one_le_exp _)) ?_; rw [←Real.exp_sum]; exact Real.exp_monotone ((sum_le_sum_of_subset_of_nonneg (erase_subset ..) (fun i _ _=>hq i)).trans hz)
end YM.CF.Graph.Diff
#print axioms YM.CF.Graph.Diff.fuel_diff
