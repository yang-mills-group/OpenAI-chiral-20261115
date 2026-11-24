import YM.CF.BProof.Garden.Crop
import YM.CF.BProof.Garden.Tube
/-! Optional vertex formulas and coefficient price; support only the node. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Garden
open Function Filter Fock NormedSpace Finset Align Wick Fig Hearth Spin
open Lat Mir SU Lattice Dial Tenant Cube Tulip
open scoped Topology Matrix MatrixOrder InnerProductSpace Kronecker BigOperators Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {N:Side}
lemma chefCom(x:Site N)(A:Quilt N):Commute (pair A) (cutM (chef x)):=by
 ext i j; rw [cutM, Matrix.diagonal_mul, Matrix.mul_diagonal]; simp only [chef,mem_stake,pair_local]; by_cases h:i.1.1=j.1.1; simp only [h,ite_true]; rw [mul_comm]; simp only [h,ite_false,mul_zero,zero_mul]
theorem corner (S:Support N){A B: Quilt N}(h:∀ i∈S,A (node i)=B (node i)){i:Single N}(g:i∈ stake S) : thorn (pair A) i=thorn (pair B) i:=by
 have ht:acts (pair A) (basisKet i)=acts (pair B) (basisKet i):=by
   apply PiLp.ext; intro j; rw [basis_act,basis_act,pair_local,pair_local]; split; · rename_i d; rw [show badgeOf j=node i.1.1 from congrArg node d,h _ ((mem_stake ..).mp g)]
   rfl
 unfold thorn spear; rw [ht]
lemma chef_eq(x:Site N){A B:Quilt N}(h:A (node x)=B (node x)){p:Finset (Single N)}(t:p∈alloy (chef x))(D:FC (Single N)): coeffJ (chef x) (pair A) p D=coeffJ (chef x) (pair B) p D:=by
 let U:Support N:={x}; have hp(i)(e:i∈U):A (node i)=B (node i):=by have ht:=mem_singleton.mp e; subst i; exact h
 have ht:crown (pair A) p=crown (pair B) p:=by unfold crown; apply congrArg; apply List.map_congr_left; intro i g; exact corner U hp ((mem_alloy ..).mp t|>.1 (mem_sort ..|>.mp g)) -- tune
 unfold coeffJ bodyJ tiara chef; rw [broad_eq hp,ht]
def siteJ(A:Quilt N)(B:Plant N):Plant N:=⟨fun i=>opJ (chef i) (pair A) (B.leaf i), fun i=>ownsJ (chefCom ..) _⟩
theorem payment {F:Quilt N}{B:Plant N}(p:∀ i,SealH (F i))(j:Site N){i:Finset (Single N)}(m:i∈alloy (chef j)){r:ℝ}(t:‖B.leaf j‖≤r): ‖coeffJ (chef j) (pair F) i (B.leaf j)‖≤r:=by -- remove args
 have v:= coeffJ_bound (A:=B.leaf j) (pair_unit (fun i=>(p i).norm)) (chefCom j F) (pair_skew _ (fun i=>(p i).symm)) i ((mem_alloy ..).mp m).1
 refine v.trans (le_trans ?_ t); apply (actuary ..).trans; rw [show ‖vacuum (Single N)‖=1 by simp [vacuum,basisKet],mul_one]
lemma folk_coin (x:Site N) : ‖(folk N).leaf x‖≤1:=by
 have he:‖(folk N).leaf x‖ * ‖(folk N).leaf x‖=‖berth (chef x)‖:=(Eq.symm CStarRing.norm_star_mul_self).trans (congrArg norm (folk_hut x)); have hx:=stampCost (A:=berth (chef x)) (cabin_proj ..); nlinarith
lemma cbra_coin{F:Quilt N}(p:∀ i,SealH (F i))(S:Support N)(i:Site N):‖(cbra F S).leaf i‖≤ sitePrice:=by change ‖if i∈S then (folk N).leaf i else (broad F).leaf i‖≤_; split; exact (folk_coin _).trans sitePrice_p; exact broad_money p i
lemma cbra_berth{F:Quilt N}(S:Support N)(i:Site N): (cbra F S).leaf i*berth (chef i)=(cbra F S).leaf i:=by unfold cbra Plant.patch; dsimp only; split; exact fuller_leaf ..; exact plump_id ..
/-- insertion points avoid `u`; comparison bra bits on `u`. desired bits on `s`. -/
theorem issueJ (p s u:Support N)(d: Disjoint u p)(A B: Quilt N)(h:∀ i,SealH (A i))(g:∀ i∉p,(cbra A u).leaf i=(cbra B s).leaf i): acts (star ((siteJ A (cbra B s)).prod p)) (cbra A u).ket=(cbra B s).ket:=by
 let R:=cbra A u; let D:=cbra B s; let J:=siteJ A D; change acts (star (J.prod _)) R.ket=D.ket; rw [←Plant.prod_star, Plant.ket,Plant.ket,←act_mul]; congr 2
 have hp:(star J).prod p=((star J).patch 1 p).prod univ:=by simp [Plant.prod_patch];
 rw [hp,←Plant.prod_mul]; apply Plant.prod_eq; intro i _; change (if i∈p then star (opJ (chef i) (pair A) (D.leaf i)) else 1) * R.leaf i= D.leaf i; by_cases b:i∈p; · rw [if_pos b, show R.leaf i=(broad A).leaf i from (if_neg (disjoint_left.mp d.symm b))]; exact convertJ (pair_unit (fun i=>(h i).norm)) (chefCom i A) (pair_skew _ (fun i=>(h i).symm)) (D.sector i) (cbra_berth ..)
 rw [if_neg b,one_mul]; exact g _ b
end YM.CF.BProof.Garden
