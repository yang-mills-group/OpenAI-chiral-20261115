import YM.CF.Leaf.Halo
import YM.CF.Graph.Pod
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Swell
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
-- anchored root physical PH column.Footprint
variable {N:Side}(o: Seat N)(F:Support (Cube.More N)→ ℝ){v a e d Q W a':ℝ}
abbrev SOp(N:Side):= Chin N → Op (Single N)
abbrev Sa(N:Side):= Support (Cube.More N)
def Soak (o: Seat N)(X:SOp N)(a v d:ℝ):Prop:=∃ (F:Sa N→ Raw (↥(Openc (Cube.More N) d)) (Single N)) (V:Sa N→ Toll (Single N)), (∀ S:Sa N, Suite (badge _) (bail N d) (bail N d) S (V S) (F S)) ∧ (∀ S, o∉ S→ V S=0) ∧ ((∑ S:Sa N,rent a S * Branch.ledgerV (V S)) ≤ v)∧ ∀ x:Openc (Cube.More N) d,X x.val=∑ S:Sa N,F S x
-- combine algebra with global Crown
local notation "D0"=> (Chin N)
variable {o:Seat N}{T X Y:SOp N}
lemma ring_u(o:Seat N) :Soak o (fun _=>0) a 0 d:=by
 refine ⟨_,_,fun S=> Suite.free _,fun _ _=>rfl,?_ ,fun x=>?_⟩
 · simp [Branch.ledgerV]
 simp
variable {L: Sa N→Toll (Single N)}
lemma plus_U (p:Soak o X a v d)(h:Soak o Y a W d):Soak o (fun x=>X x+Y x) a (v+W) d:=by
 obtain ⟨F,C,p,u,v,q⟩:=p; obtain ⟨G,D,h,x',k,t⟩:=h; refine ⟨_,_,fun S=>(p S).plus (h S),fun S w=>?_,?_ ,fun x=>?_⟩; · rw [u _ w,x' _ w,add_zero]
 · apply le_trans _ (add_le_add v k); refine le_of_eq ?_; unfold ledgerV; simp_rw [Pi.add_apply,sum_add_distrib,mul_add,sum_add_distrib]
 dsimp only; rw [q,t,sum_add_distrib]
lemma lift_U(p:Soak o X a v d)(h:v ≤ Q):Soak o X a Q d:=by obtain ⟨F,C,p,u,v,z⟩:=p; exact ⟨_,_,p,u,v.trans h,z⟩
lemma less_U(p:Soak o X a v d)(w:ℂ):Soak o (fun x=> w • X x) a (‖w‖*v) d:=by
 obtain ⟨F,C,p,u,v,z⟩:=p; refine ⟨_,_,fun S=>(p S).accel w,fun S t=>by rw [u _ t]; simp; rfl,?_,fun x=>by dsimp only; rw [z, smul_sum]⟩; apply le_trans _ (mul_le_mul_of_nonneg_left v (norm_nonneg _)); refine le_of_eq ?_; unfold ledgerV; simp_rw [←mul_sum,mul_left_comm _ ‖w‖,←mul_sum]
lemma minus_Q(p:Soak o X a v d)(h:Soak o Y a W d): Soak o (fun x=> X x-Y x) a (v+W) d:=by simpa only [norm_neg,norm_one,one_mul,neg_smul,one_smul,sub_eq_add_neg] using plus_U p (less_U h (-1))
lemma sun_K{ι:Type*}(S:Finset ι)(F:ι→SOp N)(V:ι→ℝ)(p:∀ i∈S,Soak o (F i) a (V i) d):Soak o (fun x=>∑ i∈S,F i x) a (∑ i∈S,V i) d:=by
 induction S using Finset.induction_on with |empty=> simpa using (ring_u (d:=d) (a:=a) o)|insert i S h ih=>simp_rw [sum_insert h]; exact plus_U (p _ (mem_insert_self ..)) (ih (fun j v=>p _ (mem_insert_of_mem v)))
abbrev tallyC (a:ℝ)(F: Sa N→ Toll (Single N)):= ∑ Y:Sa N, Branch.rent a Y* Branch.ledgerV (F Y)
lemma tallyV : tallyC a L=∑ i:Single N,∑ j:Single N,saleM a L i j:=by unfold tallyC ledgerV saleM; simp_rw [mul_sum]; rw [sum_comm]; simp_rw [sum_comm (s:=(univ:Finset (Sa N)))]
lemma tally_F (h:∀ S i j,0 ≤ L S i j) (q:tallyC a L≤ v) : Ledger a L v:=by
 rw [tallyV] at q; have hp:= sale_nn h a; refine ⟨(sum_nonneg fun i _=>sum_nonneg fun j _=>hp i j).trans q,fun i=>?_,fun i=>?_⟩; exact (single_le_sum (fun i _=>sum_nonneg fun j _=>hp i j) (mem_univ i)).trans q; rw [sum_comm] at q; exact (single_le_sum (fun j _=>sum_nonneg fun i _=>hp i j) (mem_univ i)).trans q
lemma norm_U (p:Soak o X a v d)(u:0≤ a)(x:Openc (Cube.More N) d): ‖X x.val‖≤v:=by
 obtain ⟨F,C,q,t,k,V⟩:=p; have hp:Solo a v X d:= ⟨_,_,q,tally_F (fun S=>(q S).nonn) k,V⟩; exact hp.lib.boundOp u x -- tune shadow
variable {s w: Sa N→ Toll (Single N)}
-- product anchored/unrooted. prove direct scalar sum. swap orientation.S.Cost
abbrev paceK(a:ℝ)(s w:Sa N→ Toll (Single N))(X:Sa N × Sa N) := Branch.rent a (X.1 ∪ X.2)*Branch.ledgerV (charge (s X.1) (w X.2))
lemma p_leaf (h:∀ X i j, 0≤ s X i j)(p:∀ X i j,0 ≤ w X i j)(x:0≤a)(i j:Single N): (∑ l:Sa N ×Sa N,rent a (l.1 ∪ l.2) * charge (s l.1) (w l.2) i j) ≤ ∑ k,2*(saleM a s i k * saleM a w k j):=by
 rw [Fintype.sum_prod_type]; simp_rw [charge,mul_sum,saleM,sum_mul,mul_sum]
 let F(k:Single N)(X Y:Sa N):ℝ:=rent a X * s X i k * (rent a Y*w Y k j); change _ ≤ ∑ k, ∑ X:Sa N, ∑ Y:Sa N,_ -- tune orientation
 rw [sum_comm (f:=fun k X=>∑ Y:Sa N,(2:ℝ)*F k X Y)]; -- tune orientation
 apply sum_le_sum; intro X _; rw [sum_comm]; refine sum_le_sum ?_; intro k _; apply sum_le_sum; intro Y _; apply le_trans (mul_le_mul_of_nonneg_right (rent_join X Y x) (show 0 ≤ 2*(s X i k*w Y k j) from mul_nonneg (by norm_num) (mul_nonneg (h ..) (p ..)))); exact le_of_eq (by ring)
lemma forge_L (h:∀ X i j, 0≤ s X i j)(p:∀ X i j,0 ≤ w X i j):∑ l:Sa N × Sa N, paceK a s w l=∑ i:Single N,∑ j:Single N,∑ l:Sa N × Sa N, rent a (l.1 ∪l.2) *charge (s l.1) (w l.2) i j:=by unfold paceK ledgerV; simp_rw [mul_sum]; rw [sum_comm]; simp_rw [sum_comm (s:=(univ:Finset (Sa N × Sa N)))]
lemma sumP (h:∀ X i j, 0≤ s X i j)(p:∀ X i j,0 ≤ w X i j)(x:0≤a): (∑ l:Sa N × Sa N,paceK a s w l) ≤ ∑ i:Single N,∑ j:Single N,∑ k:Single N,2*(saleM a s i k *saleM a w k j):=by rw [forge_L h p]; exact sum_le_sum fun i _=> sum_le_sum fun j _=>p_leaf h p x i j
lemma fleet_U(h:∀ X i j,0≤ s X i j)(p:∀ X i j,0≤ w X i j)(x:0≤a)(q:Ledger a w d)(v:tallyC a s ≤ Q): (∑ l:Sa N × Sa N,paceK a s w l) ≤ 2*(Q*d):=by
 refine le_trans (sumP h p x) ?_; rw [tallyV] at v; apply le_trans _ (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right v q.posP) (by norm_num)); simp_rw [sum_mul, mul_sum]; apply sum_le_sum; intro i _; rw [sum_comm]; refine sum_le_sum ?_; intro k _; rw [←mul_sum, ←mul_sum]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (q.rows _) (sale_nn h _ _ _)) (by norm_num)
lemma fleet_K(h:∀ X i j, 0≤ s X i j)(p:∀ X i j,0 ≤ w X i j)(x:0≤a)(q:Ledger a s d)(v:tallyC a w ≤ Q):(∑ l:Sa N × Sa N,paceK a s w l) ≤ 2*(d*Q):=by
 refine le_trans (sumP h p x) ?_; rw [tallyV] at v; apply le_trans _ (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left v q.posP) (by norm_num)); simp_rw [mul_sum]; rw [sum_comm,sum_comm (s:=(univ:Finset (Single N))) (f:=fun k j=>2*(d*saleM a w k j))]; refine sum_le_sum ?_; intro j _; rw [sum_comm]; apply sum_le_sum; intro k _; rw [←mul_sum,←sum_mul]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (q.cols _) (sale_nn p _ _ _)) (by norm_num)
-- raw documentation. one side local.
lemma arm_v {ι:Type*}[Fintype ι](F:ι→ Sa N)(K:ι→ Raw (↥(Openc (Cube.More N) d)) (Single N))(V:ι→ Toll (Single N))(h:∀ i,Suite (badge _) (bail N d) (bail N d) (F i) (V i) (K i))(p: (∑ i,rent a (F i)*ledgerV (V i)) ≤ v)(u:∀ i,o∉ F i→ V i=0)(g:∀ i:Openc (Cube.More N) d,X i.val= ∑ j:ι,K j i): Soak o X a v d:=by
 let Kc (S:Sa N): Toll (Single N):=fun i j=> ∑ y∈dest F S,V y i j; refine ⟨_,Kc,fun S=>⟨Ticket.sumT _ V K (fun i (v:i∈dest F S)=> (mem_filter.mp v).2 ▸ (h i).toTicket), License.suppose _ _ _ (fun i _=>(h i).fuel)⟩,fun S x=>?_,le_trans ?_ p,fun i=>Eq.trans (g i) (lump F _)⟩
 · unfold Kc; funext i j; exact sum_eq_zero fun k v=>by rw [u _ ((mem_filter.mp v).2 ▸ x)]; rfl
 refine le_of_eq ?_; rw [Branch.lump F]; refine sum_congr rfl fun i _=>?_ ; unfold ledgerV Kc; simp_rw [sum_comm (t:=dest F i) (s:=(univ:Finset (Single N)))]; rw [mul_sum]; exact sum_congr rfl (fun j u=>by rw [show F j=i from (mem_filter.mp u).2])
lemma aura_X (p:Soak o X a v d)(h:Solo a W Y d)(f:0≤a):Soak o (fun x=> X x*Y x) a (2*(v*W)) d:=by
 obtain ⟨F,S,t,u,z,g⟩:=p; obtain ⟨G,C,p,w,c⟩:=h; refine arm_v (o:=o) (fun l:Sa N×Sa N=>l.1∪l.2) _ (fun l=> charge (S l.1) (C l.2)) (fun i=> Suite.jointK (t i.1) (p i.2)) (fleet_U (fun X=>(t X).nonn) (fun X=>(p X).nonn) f w z) ?_ ?_
 · intro y g; rw [u _ (fun p=>g (mem_union_left _ p))]; funext i j; simp [charge]
 intro i; rw [g i,show Y i.val = _ from c i]; simp only [Fintype.sum_prod_type,sum_mul,mul_sum]; first|exact sum_comm|rfl -- tune
lemma aura_Y (p:Soak o X a v d)(h:Solo a W Y d)(f:0≤a): Soak o (fun x=>Y x* X x) a (2*(W*v)) d:=by
 obtain ⟨F,S,t,u,z,g⟩:=p; obtain ⟨G,C,p,w,c⟩:=h; refine arm_v (o:=o) (fun l:Sa N×Sa N=>l.1 ∪ l.2) _ (fun l=> charge (C l.1) (S l.2)) (fun i=> Suite.jointK (p i.1) (t i.2)) (fleet_K (fun X=>(p X).nonn) (fun X=>(t X).nonn) f w z) ?_ ?_
 · intro y g; rw [u _ (fun p=>g (mem_union_right _ p))]; funext i j; simp [charge]
 intro i; rw [g i,show Y i.val = _ from c i]; simp only [Fintype.sum_prod_type,sum_mul,mul_sum]; first|exact sum_comm|rfl
end YM.CF.Swell
