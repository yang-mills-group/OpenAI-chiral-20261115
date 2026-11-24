import YM.CF.BProof.Garden.Wheat
import YM.CF.BProof.Wick.Quest
/-! eq:B-cbra, eq:B-Madd. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Garden
open Function Filter Fock NormedSpace Finset Align Wick Fig Hearth Spin
open Lat Mir SU Lattice Dial Tenant Cube Tulip
open scoped Topology Matrix MatrixOrder InnerProductSpace Kronecker BigOperators Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {N:Side}
def cbra(A:Quilt N) (S:Support N):= (folk N).patch (broad A) S
def Madd(A:Quilt N):Plant N:= folk N * star (broad A)
def Plant.ket(P:Plant N):=acts (P.prod univ) (vacuum (Single N))
lemma broad_eq {A B:Quilt N}{S: Support N}(h:∀ i∈S,A (node i)=B (node i)): square (stake S) (pair A)=square (stake S) (pair B):=by
 ext i j; simp only [square_entry, mem_stake,pair_local]; split_ifs with e g; rw [show badgeOf i=node i.1.1 from rfl,h _ e.1]; rfl; rfl
lemma leaf_eq {A B:Quilt N}{i:Site N}(h:A (node i)=B (node i)): (broad A).leaf i=(broad B).leaf i:=by change plump (chef i) (pair A)=plump (chef i) (pair B); unfold plump; rw [broad_eq (A:=A) (B:=B) (S:={i}) (by intro j e; simp only [mem_singleton] at e; subst j; exact h)]
lemma cbra_spec(A:Quilt N)(h:∀ i,SealH (A i))(S:Support N): (cbra A S).ket=Double.pressB (bandSites S true) (bandSites S false) (pair A):=by
 change _= acts (visor S) _; rw [← plump_goal (pair A), ← stake_all (N:=N), ← broad_prod, ←goods_prod, ←act_mul,Plant.ket]; congr 2
 have hp:(goods N).prod S=((goods N).patch 1 S).prod univ:=by simp [Plant.prod_patch]
 rw [hp, ←Plant.prod_mul]; apply Plant.prod_eq; intro i _; change (if i∈S then (folk N).leaf i else (broad A).leaf i)=(if i∈S then (goods N).leaf i else 1)* (broad A).leaf i
 by_cases g:i∈S; · rw [if_pos g,if_pos g,← folk_pact h]; rfl
 rw [if_neg g,if_neg g,one_mul]
set_option maxHeartbeats 1000000 in
lemma desired(A:Quilt N)(S:Support N):acts (star ((Madd A).prod S)) (mateK N)=(cbra A Sᶜ).ket:=by
 have hp:(Madd A).prod S=((Madd A).patch 1 S).prod univ:=by simp [Plant.prod_patch];
 rw [hp, ← folk_pay,←Plant.prod_star, ←act_mul,←Plant.prod_mul,Plant.ket]; congr 2; apply Plant.prod_eq; intro i _; change star (if i∈S then (Madd A).leaf i else (1: FC (Single N))) * (folk N).leaf i=(if i∈ Sᶜ then (folk N).leaf i else (broad A).leaf i); by_cases g:i∈ S
 · simp only [g,if_true, mem_compl, not_true_eq_false, if_false]; change star ((folk N).leaf i * star ((broad A).leaf i))*_= _; rw [star_mul,star_star,mul_assoc,folk_hut]; exact plump_id ..
 simp only [g,if_false, mem_compl, not_false_eq_true, if_true,star_one,one_mul]
lemma broad_spin(A:Quilt N)(g:Geometry N)(i:Site N) : twist (quantU (tradew N g)) ((broad A).leaf i) =(broad (stitch g A)).leaf i:=by
 change twist _ (plump (chef i) (pair A))=plump _ (pair _); rw [pair_spin,plump_law]; exact totalComm (fun x=>(matter (g (node x.1))).val) {i} -- tune
lemma folk_spin (g:Geometry N) (i:Site N) : twist (quantU (tradew N g)) ((folk N).leaf i)=(folk N).leaf i:=by
 have he:(folk N).leaf i=(goods N).leaf i*(broad (stitch g (northW N))).leaf i:=congrArg (fun p:Plant N=>p.leaf i) (folk_pact (A:=stitch g (northW N)) (fun j=> seal_move _ (north_seal _))).symm
 conv_rhs=> rw [he]
 change twist _ (visor ({i}:Support N) * (broad (northW N)).leaf i)=visor _ * _; rw [map_mul,broad_spin]; rw [visor, cabin_spin (band_separate _) (blockG {i} g true).symm (blockG {i} g false).symm]
lemma Madd_spin(A:Quilt N)(g:Geometry N)(i:Site N): twist (quantU (tradew N g)) ((Madd A).leaf i)=(Madd (stitch g A)).leaf i:=by change twist _ ((folk N).leaf i * star ((broad A).leaf i))= (folk N).leaf i * star ((broad (stitch g A)).leaf i); rw [map_mul,map_star,broad_spin,folk_spin]
@[fun_prop] lemma Madd_cont(S:Support N) : Continuous (fun A:Quilt N=> (Madd A).prod S):= Plant.prod_cont _ (by intro x; change Continuous (fun q:Quilt N=>(folk N).leaf x*star (plump (chef x) (pair q))); fun_prop) S
lemma Madd_here {A B:Quilt N}{S:Support N}(h:∀ i∈S,A (node i)= B (node i)): (Madd A).prod S=(Madd B).prod S:=Plant.prod_eq _ _ fun i e=> by change _ * star ((broad _).leaf i)= _ * star ((broad _).leaf i); rw [leaf_eq (h i e)]
lemma Madd_march(A:Quilt N)(g:Geometry N)(S:Support N): twist (quantU (tradew N g)) ((Madd A).prod S)=(Madd (stitch g A)).prod S:=by induction S using Finset.induction_on with| empty=> simp only [Plant.prod_empty]; rw [twist_formula,mul_one]; exact (quantU (tradew N g)).property.2| insert x S k ih=>rw [Plant.prod_insert _ k,map_mul,ih,Madd_spin,Plant.prod_insert _ k]
def sitePrice:=Real.exp ((slotsu:ℝ)^2)
lemma sitePrice_p :1 ≤ sitePrice:= Real.one_le_exp (sq_nonneg _)
lemma broad_money{A:Quilt N}(h:∀ i,SealH (A i))(i:Site N): ‖(broad A).leaf i‖≤sitePrice:=by
 have he: ‖pair A‖=1:= CStarRing.norm_of_mem_unitary (pair_unit (fun i=>(h i).norm)); unfold sitePrice; rw [←stake_count i]; exact plump_cost _ he.le
lemma Madd_money{A:Quilt N}(h:∀ i,SealH (A i))(S:Support N):‖(Madd A).prod S‖≤ sitePrice ^ (S.card):=by
 refine Plant.prod_money _ S (zero_le_one.trans sitePrice_p) fun i=>?_ ; change ‖(folk N).leaf i*star ((broad A).leaf i)‖≤ _
 apply (norm_mul_le ..).trans; rw [norm_star]; apply (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (broad_money h i)
 have he:‖(folk N).leaf i‖*‖(folk N).leaf i‖=‖berth (chef i)‖:=(Eq.symm CStarRing.norm_star_mul_self).trans (congrArg norm (folk_hut i)); have hx:=stampCost (A:=berth (chef i)) (cabin_proj ..); nlinarith
end YM.CF.BProof.Garden
