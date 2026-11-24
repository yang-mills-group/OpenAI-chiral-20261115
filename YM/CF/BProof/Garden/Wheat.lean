import YM.CF.BProof.Garden.Fall
import Mathlib.Data.Finset.NoncommProd
/-! Embedded graded tensor symbols (we only take even), including Bra site-pluses. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Garden
open Function Filter Fock NormedSpace Finset Align Wick Fig Hearth Spin
open Lat Mir SU Lattice Dial Tenant Cube Tulip
open scoped Topology Matrix MatrixOrder InnerProductSpace Kronecker BigOperators Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {N:Side}
@[ext] structure Plant(N:Side) where
 leaf : Site N → FC (Single N)
 sector (x:Site N): Sector (chef x) false (leaf x)
namespace Plant
variable (p q:Plant N) {S T:Support N}
def prod (S:Support N): FC (Single N):=noncommProd S p.leaf (fun _ _ _ _ e=> council (p.sector _) (p.sector _) (stake_umbrella (by simpa using e)))
lemma prod_at (S:Support N) : Sector (stake S) false (p.prod S):= noncommProd_induction _ _ _ _ (fun _ _ i j=>i.mul j) Sector.one (fun x h=> scope (p.sector x) (stake_up (singleton_subset_iff.mpr h))) -- tune
lemma splice(h:Disjoint S T): p.prod (S∪T)=p.prod S*p.prod T:=noncommProd_union_of_disjoint h .. -- tune
@[simp] lemma prod_empty :p.prod ∅=1:=by simp [prod]
@[simp] lemma prod_insert {x:Site N}{S:Support N}(h:x∉S): p.prod (insert x S)=p.leaf x*p.prod S:=by simp only [prod, noncommProd_insert_of_notMem _ _ _ _ h]
lemma prod_eq {S:Support N}(h:∀ i∈S,p.leaf i=q.leaf i): p.prod S=q.prod S:=by induction S using Finset.induction_on with | empty=> simp | insert x T k ih=> rw [prod_insert p k,prod_insert q k,h _ (mem_insert_self _ _), ih (fun i e=> h _ (mem_insert_of_mem e))]
instance : One (Plant N):=⟨⟨1,fun _=>Sector.one⟩⟩
instance : Mul (Plant N):=⟨fun x y=> ⟨x.leaf*y.leaf, fun i=> (x.sector i).mul (y.sector i)⟩⟩
instance : Star (Plant N):=⟨fun x=>⟨fun i=>star (x.leaf i), fun i=> (x.sector i).contr⟩⟩
instance : Add (Plant N):=⟨fun x y=>⟨x.leaf+y.leaf, fun i=> (x.sector i).add (y.sector i)⟩⟩
instance : SMul (Site N→ℂ) (Plant N):=⟨fun x y=>⟨fun i=>x i • y.leaf i,fun i=> (y.sector i).scale _⟩⟩
lemma prod_mul (S:Support N): (p*q).prod S=p.prod S*q.prod S:=noncommProd_mul_distrib p.leaf q.leaf _ _ (fun _ _ _ _ e=> council (q.sector _) (p.sector _) (stake_umbrella (by simpa using e))) -- tune
@[simp] lemma prod_star (S:Support N): (star p).prod S=star (p.prod S):=by
 induction S using Finset.induction_on with
 | empty=> simp only [prod_empty,star_one]
 | insert x T k ih=> rw [prod_insert _ k,prod_insert _ k,ih, (council (p.sector x) (p.prod_at T) (stake_umbrella (disjoint_singleton_left.mpr k))).eq,star_mul]; rfl
@[simp] lemma prod_one (S:Support N): (1:Plant N).prod S=1:=(noncommProd_eq_pow_card _ _ _ 1 (fun _ _=>rfl)).trans (one_pow _)
def patch (S:Support N) : Plant N:=⟨fun i=> if i∈S then p.leaf i else q.leaf i,fun i=>by split; exact p.sector i; exact q.sector i⟩
lemma prod_patch (S U:Support N) : (p.patch q U).prod S=p.prod (S∩U)*q.prod (S\U):=by
 conv_lhs=>arg 2; rw [← show S∩U∪S\U=S from (Finset.ext fun i=> by simp; tauto)]
 rw [splice _ (by rw [disjoint_left]; intro i h k; exact (mem_sdiff.mp k).2 ((mem_inter.mp h).2)), prod_eq _ p (fun _ k=>if_pos (mem_inter.mp k).2),prod_eq _ q (fun _ k=>if_neg (mem_sdiff.mp k).2)]
lemma prod_cont {D:Type*}[TopologicalSpace D](p:D→Plant N)(h:∀ x,Continuous (fun i=> (p i).leaf x))(S:Support N): Continuous (fun i=> (p i).prod S):=by induction S using Finset.induction_on with| empty=> simp; exact continuous_const | insert x T k ih=> simp_rw [prod_insert _ k]; exact (h _).mul ih
lemma prod_money(S:Support N){r:ℝ}(g:0≤r)(h:∀ i,‖p.leaf i‖≤r) :‖p.prod S‖≤r^S.card:=by induction S using Finset.induction_on with | empty=> simp | insert x T k ih=> rw [p.prod_insert k,card_insert_of_notMem k,pow_succ']; exact (norm_mul_le ..).trans (mul_le_mul (h _) ih (norm_nonneg _) g)
end Plant
def broad(A:Quilt N):Plant N:=⟨fun x=>plump (chef x) (pair A),fun _=>plump_here ..⟩
abbrev visor (S:Support N):= cabin (bandSites S true) (bandSites S false)
def goods (N:Side):Plant N:=⟨fun x=>visor ({x}:Support N),fun _=> tagged subset_union_left subset_union_right⟩
def fuller(A:Quilt N):Plant N:= goods N * broad A
lemma broad_prod (A:Quilt N)(S:Support N): (broad A).prod S=plump (stake S) (pair A):=by induction S using Finset.induction_on with| empty=> rw [Plant.prod_empty,stake_empty,plump_empty]| insert i T k ih=> have he:Disjoint ({i}:Support N) T:=disjoint_singleton_left.mpr k; rw [Plant.prod_insert _ k,ih,← singleton_union,stake_union,splitplump (stake_umbrella he) (stakesplit he A)]; rfl
lemma goods_prod(S:Support N): (goods N).prod S=visor S:=by
 induction S using Finset.induction_on with
 | empty=> rw [Plant.prod_empty]; simp [visor,bandSites,cabin_nil]
 | insert x T k ih=>
   have he(u:Bool): bandSites (insert x T) u=bandSites {x} u∪bandSites T u:=by ext i; simp; tauto
   rw [Plant.prod_insert _ k,ih]; unfold visor; rw [he,he,cabin_merge]; rfl
lemma fuller_leaf (A:Quilt N)(i:Site N): (fuller A).leaf i * berth (chef i)=(fuller A).leaf i:=by change ((goods N).leaf i*plump (chef i) (pair A))*_= (goods N).leaf i*_; rw [mul_assoc,plump_id]; rfl
lemma fuller_eff (A:Quilt N)(S:Support N): acts ((fuller A).prod S) (vacuum (Single N))=pf (pair A) (bandSites S true) • basisKet (bandSites S true):=by rw [fuller,Plant.prod_mul,goods_prod,broad_prod]; exact plump_slot (band_separate _) _
lemma fuller_once(A:Quilt N)(x:Site N): (fuller A).prod {x}=(fuller A).leaf x:=by rw [Plant.prod, noncommProd_singleton]
def northW(N:Side):Quilt N:= StampX N (vacuumW N)
def folk(N:Side):Plant N:= fuller (northW N)
lemma north_seal(i:Site (More N)): SealH (northW N i):= sealX _ (hookN ..)
lemma folk_hut(x:Site N):star ((folk N).leaf x)*(folk N).leaf x=berth (chef x):=by apply berth_iso ((folk N).sector x) (fuller_leaf ..); unfold folk; rw [← fuller_once,fuller_eff,norm_smul,siteNorm _ north_seal _]; simp [basisKet]
lemma folk_pact{A:Quilt N}(h:∀ x, SealH (A x)): fuller A= folk N:=by
 let P:=fuller A; let Q:=folk N; have ht:P.leaf=Q.leaf:= funext fun i=> by
   rw [← fuller_leaf A]; -- tune unfolds
   apply (berth_test (P.sector i) (Q.sector i) ?_).trans (fuller_leaf ..); unfold P Q folk; rw [←fuller_once,←fuller_once,fuller_eff,fuller_eff,sitePay _ h,sitePay _ north_seal]
 exact Plant.ext ht -- tune no @[ext]
lemma folk_pay :acts ((folk N).prod univ) (vacuum (Single N))= mateK N:=by
 unfold folk; rw [fuller_eff]; unfold northW; let T:=vacuumW N; rw [pair_post,←constB (hook T ∘ node) (fun i=> hookN ..),filled,←ticka,bandCut,cutLine,cut_oneAct]; rfl
end YM.CF.BProof.Garden
