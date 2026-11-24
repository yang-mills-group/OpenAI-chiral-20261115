import YM.CF.Gully.Depth
set_option autoImplicit false
set_option maxHeartbeats 550000
set_option synthInstance.maxSize 22000
noncomputable section
namespace YM.CF.Gully
open Function Fock Filter Metric NormedSpace Lat Lattice Branch Cube Tenant MeasureTheory Phase Finset Mir Scroll Spire RP Str Petal Manifest Palot Stilo Dial Paige Vault Brace RG Push.AbsoluteSums Trees
open scoped Topology Classical BigOperators InnerProductSpace Matrix Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {m B L N:Side}
local notation "Λ" => CSide m B
local notation "ξ" => Domain m B
open Maize Gloss Floe Ave Phase.Sample Jet Pastry Drapes Gas
variable {r e U K A H:ℝ}{n:ℕ}
variable {s c d Z C:ℝ} {p:1 ≤H}
def spallB (m B:Side)(a:Index m):Stamp m B:=Branch.bay (terr _) (Cube.address m B a) B.val
def spallA (m B:Side)(S:Acres m):Stamp m B:= S.biUnion (spallB m B)
lemma spore :Broc.Exceed (terr _) (terr _) (spallA m B) (feeG B.val) (feeG 2):=by
 refine ⟨fun {S} p=>?_,fun {S} p=>?_,fun i=>?_⟩
 · induction p with
   | single x=> simpa [spallA,spallB] using glen (Cube.address m B x) B.val
   | @join S x y g p' he ih=>
     let V:=Cube.address m B y; have hV := (distance_addr_iff (B:=B) x y 1).mp he; rw [mul_one] at hV
     rw [show spallA m B (insert x S)=spallB m B x∪ spallA m B S from Finset.biUnion_insert]; exact (show Grove _ (spallB m B x) from glen (Cube.address m B x) _).unite ih ((bay_mem _).mpr hV) (mem_biUnion.mpr ⟨y,p', (show V∈spallB m B y from by simp [V,spallB,terr])⟩)
 · calc
     _ ≤ ∑ i∈S,((spallB m B i).card:ℝ):=by unfold spallA; exact_mod_cast Finset.card_biUnion_le
     _ ≤ ∑ i∈S,feeG B.val:= sum_le_sum fun i _=>Tenant.reach ..
     _ = _:=by simp [mul_comm]
 obtain ⟨a,z,h⟩:= full_r m B i; refine ⟨Branch.bay (terr _) a 2,Tenant.reach ..,fun S g q=>?_⟩; obtain ⟨j,hj,t⟩:= mem_biUnion.mp q; refine ⟨j,(bay_mem _).mpr ((distance_addr_iff (B:=B) a j 2).mpr ?_),hj⟩; apply (separation_triangle _ i _).trans; have ht:separation _ _≤_ := (bay_mem _).mp t
 exact (Nat.add_le_add ((separation_comm ..).trans_le (room_span z)) ((separation_comm ..).trans_le ht)).trans_eq (mul_two _).symm
lemma leafB (S:Acres m): Ave.mount m B S⊆spallA m B S :=by intro i h; obtain ⟨a,g,v⟩:=mem_biUnion.mp h; exact mem_biUnion.mpr ⟨a,g,(bay_mem _).mpr ((separation_comm ..).trans_le (room_span v))⟩
def cairn (m B:Side)(S: Stamp m B): Finset (Hearth m B):= univ.filter fun i=> Tenant.carrier (CSide m B) i.2∈S -- tune
lemma Cairn_up : Monotone (cairn m B):=fun _ _ h _ v=>mem_filter.mpr ⟨mem_univ _, h ((mem_filter.mp v).2)⟩
def PinK (m B:Side)(e H:ℝ)(p:1≤H):Lodge (Site (Domain m B)) (Ewe m B) (Briar m B e) (Court m B) where
 toBell:= shelf H p (cairn m B) Cairn_up
 pick:= routeS (m:=m) (B:=B)
 zone S U V := Agrees S U.val V.val
 grows g h:= fun i p q=> h _ (g p) (g q)
 rule:= routeM m B
 ct g:= (routeM m B g).toLinearMap.continuous_of_finiteDimensional
structure Chalk(e H:ℝ)(p:1 ≤ H)(U:ℝ)(n:ℕ)(S:Stamp m B)(F:Briar m B e→ Ewe m B)(v:ℝ):Prop where
 home:Token (PinK m B e H p) S F v (Grove (terr _))
 actsJ:Fo B e U n F H v
def HatX(e H:ℝ)(p:1≤H)(U:ℝ)(n:ℕ)(F:Briar m B e→ Ewe m B)(s c:ℝ) := ∃ (T:Stamp m B→ Briar m B e→Ewe m B) (v:Stamp m B→ℝ),(∀ i, Chalk e H p U n i (T i) (v i))∧ (∀ i,hitE s v i ≤ c)∧∀ i,F i=∑ S:Stamp m B,T S i
lemma elevate {S:Acres m}{T:Briar m B e→ Ewe m B}{v:ℝ}(h:CoInk S e H p U n T v): Chalk e H p U n (spallA m B S) T v:=by
 have p':=h.home; refine ⟨{p' with shape:= fun q=> spore.plus (p'.shape q), gram := fun x=>?_, locality:= fun {x y} p=> p'.locality (fun i g l=> p i (leafB S g) (leafB S l))},h.growth⟩
 let Y:=brigade m B S; let Q:= cairn m B (spallA m B S); have he:Y⊆Q:=fun i p=> mem_filter.mpr ⟨mem_univ _,leafB S (mem_filter.mp p|>.2)⟩
 exact (show Flour Y _ from (p'.gram x)).lift he -- check
lemma chalk_sum{Y:Type}[Fintype Y](X:Y→Stamp m B){T:Y→ Briar m B e→ Ewe m B}{v:Y→ℝ}(h:∀ i,Chalk e H p U n (X i) (T i) (v i)) (g:∀ i,hitE s (fun S=>∑ i∈dest X S,v i) i≤ c){F:Briar m B e→ Ewe m B}(u:∀ i,F i=∑ S:Y,T S i):HatX e H p U n F s c:=by
 let Z(S:Stamp m B)(x:Briar m B e):= ∑ i∈dest X S,T i x; refine ⟨Z,_,fun S=>⟨Token.mass _ _ _ (fun i (u:i∈dest X S)=>((mem_filter.mp u).2: X i=S) ▸ (h i).home),?_⟩,g,fun i=>(u i).trans (lump ..)⟩
 intro E _ _ _ f W p l x hx; simp only [Z,map_sum]; exact allows_sum (s:=dest X S) (fun i _=>(h i).actsJ E f W p l x hx)
lemma way_p {S:Acres m}(s:ℝ)(h:0 ≤ s)(p:Grove (terr _) S): rent s (spallA m B S)≤ rent (s*feeG B.val) S:=by
 unfold rent; apply Real.exp_le_exp.mpr; rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (spore.band p) h
lemma elevate_C {F:Briar m B e→Ewe m B} (h:coBooks e U H p n F s c)(u:0≤ s)(v:0≤c): HatX e H p U n F (s/feeG B.val) (feeG 2*c):=by
 let f:=spallA m B; let r:= s/feeG B.val; have hy:0<feeG B.val:=by unfold feeG; positivity
 obtain ⟨T,w,q,l,e⟩:=h; apply chalk_sum f (fun i=>elevate (q i)) _ e; intro i; obtain ⟨y,g,Y⟩:= (spore (m:=m) (B:=B)).coverage i; apply le_trans _ (show ∑ j∈y,hitE s w j≤feeG 2*c from (sum_le_sum (fun i (_:i∈y)=>l i)).trans (by rw [sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right g v))
 rw [pay_conv]; unfold bill_X hitE hit0; simp_rw [sum_filter]; rw [sum_comm]; refine sum_le_sum fun T _=>?_
 have hp:= (q T).home.price; have ht(j:Index m):0 ≤ if j∈T then rent s T*w T else 0:=by split; exact mul_nonneg (rent_pos ..).le hp; rfl
 split_ifs with k
 · by_cases l:w T=0; · simp [l] -- tune rw
   have he:= (q T).home.shape l; obtain ⟨j,g,z⟩:=Y T he k; apply le_trans _ (single_le_sum (fun j _=>ht j) g); rw [if_pos z, mul_comm (w T)]; have hp':=way_p (m:=m) r (div_nonneg u hy.le) he (B:=B); rw [show r*feeG B.val=s from div_mul_cancel₀ _ hy.ne'] at hp'; exact mul_le_mul_of_nonneg_right hp' hp
 exact sum_nonneg (fun j _=>ht j)
end YM.CF.Gully
