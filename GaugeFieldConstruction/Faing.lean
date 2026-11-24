import GaugeFieldConstruction.Moulin
import YM.CF.Support.Sale
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedVariables false
set_option maxHeartbeats 200000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.XGarden
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Spire Branch
attribute [local instance] opCStarAlgebra
open Broc Jet Drapes
variable {K b c d r v e:ℝ}{N m B:Side}{n:ℕ}
local notation "Λ"=> CSide m B
abbrev aptK(i:Single N): Seat N:= Tenant.carrier N ((helix N) i)
abbrev MSheet(m B:Side):Type:= Pantry m B→Op (Single (CSide m B))
abbrev TicketM (K:ℝ)(n:ℕ)(e:ℝ) (S R:Stamp m B)(A:MSheet m B)(p:Toll (Single Λ)):Prop:= ∀ i j, Ka K n e S (fun x=> A x i j) (p i j) ∧ (p i j ≠0 → Grove (Tenant.terr _) S ∧ R⊆S ∧ aptK i∈S∧ aptK j∈S)
abbrev AllM (K:ℝ)(n:ℕ)(e:ℝ) (R:Stamp m B)(A:Stamp m B→ MSheet m B)(p:Stamp m B→ Toll (Single Λ)):Prop:= ∀ S,TicketM K n e S R (A S) (p S)
abbrev costM (a:ℝ)(w: Stamp m B→ Toll (Single Λ)):ℝ:= ∑ (i:Single Λ), ∑ j, saleM a w i j
abbrev PutM (K:ℝ)(n:ℕ)(e a d:ℝ) (P:MSheet m B):Prop:=∃ p A,AllM K n e ∅ A p ∧ Ledger a p d ∧ ∀ x∈ Lobby m B e, P x= ∑ i,A i x
abbrev HitM (K:ℝ)(n:ℕ)(e a d:ℝ)(R:Stamp m B)(P:MSheet m B):Prop:= ∃ p A,AllM K n e R A p ∧ costM a p ≤ d ∧ ∀ x∈ Lobby m B e, P x=∑ i,A i x
variable {a a':ℝ}
variable {q q' :Stamp m B→ Toll (Single (CSide m B))} {X Y: Stamp m B→ MSheet m B}{R:Stamp m B}{F G:MSheet m B}
lemma AllM.positive(h: AllM K n e R X q)(x i j):0≤ q x i j:= (h x i j).1.pos
lemma AllM.large(h:AllM K n e R X q)(b:ℝ):0 ≤ costM b q:=sum_nonneg fun _ _=> sum_nonneg fun _ _=> sale_nn h.positive b _ _
lemma AllM.low_K (h:AllM K n e R X q)(p:b ≤ K):AllM b n e R X q:=fun x i j=>⟨(h x i j).1.narrow p,(h x i j).2⟩
lemma AllM.low_n (h:AllM K n e R X q){k:ℕ}(p:k≤n):AllM K k e R X q:=fun x i j=>⟨(h x i j).1.lower p,(h x i j).2⟩
lemma lower_h(h:PutM K n e a c F)(p:b ≤ K){m:ℕ}(u:m≤n)(l:a'≤ a): PutM b m e a' c F:=by
 obtain ⟨q,X,t,w,h⟩:=h; exact ⟨q,X,t.low_K p|>.low_n u,w.lowers (fun x i j=> mul_le_mul_of_nonneg_right (rent_up l _) (t.positive ..)),h⟩
lemma lumpQ {I:Type}[Fintype I](ρ:I→Stamp m B)(X:I→ MSheet m B)(v:I→ Toll (Single Λ))(h:∀ x,TicketM K n e (ρ x) R (X x) (v x)):
 ∃ p A, AllM K n e R A p ∧ (∀ a i j, saleM a p i j=∑ k,rent a (ρ k)*v k i j)∧ (∀ x:Pantry m B, ∑ k,X k x= ∑ k,A k x):=by
 let Q(S:Stamp m B) i j:=∑ l∈ dest ρ S,v l i j; let Y(S:Stamp m B) (x:Pantry m B):=∑ l∈dest ρ S,X l x
 refine ⟨Q,Y,fun S i j=> ?_,fun a i j=> ?_,fun x=> lump ρ (fun i=>X i x)⟩
 · have hg(l)(p:l∈dest ρ S) : TicketM K n e S R (X l) (v l) := (mem_filter.mp p).2 ▸ h l
   refine ⟨?_,fun u=> ?_⟩
   · unfold Y; simp_rw [Matrix.sum_apply]; exact Ka.sumH _ _ _ (fun l g=> (hg l g i j).1)
   by_contra! e; exact u (sum_eq_zero fun l g=> not_ne_iff.mp (mt (hg l g i j).2 (by tauto)))
 unfold saleM; rw [lump ρ (fun l=> rent a (ρ l)* v l i j)]; refine sum_congr rfl fun k _=>?_ ; unfold Q; rw [mul_sum]; exact sum_congr rfl fun l u=> by rw [show ρ l=k from (mem_filter.mp u).2]
lemma add_Q (h:AllM K n e R X q)(p:AllM K n e R Y q'):AllM K n e R (X+Y) (q+q'):=by
 intro S i j; refine ⟨(h S i j).1.add_H (p S i j).1,fun l=>?_⟩; by_cases hx:q S i j=0; · exact (p S i j).2 (by simpa [hx] using l)
 exact (h S i j).2 hx
lemma neg_Q (h:AllM K n e R X q): AllM K n e R (-X) q:=fun x i j=>⟨(h x i j).1.neg_H, (h x i j).2⟩
private def barC':ℂ→L[ℝ]ℂ:= Complex.conjCLE.toContinuousLinearMap
private lemma signP (x:ℂ):barC' x=star x:=rfl
lemma cc_Q (h:AllM K n e R X q):AllM K n e R (fun S x=>cc (X S x)) q:=by
 intro x i j; refine ⟨?_,(h x i j).2⟩; have he:= (h x i j).1.maps_H barC' (show ‖barC'‖≤1 from by apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one; intro z; simp [signP]); rw [one_mul] at he; exact he
lemma tr_Q (h:AllM K n e R X q): AllM K n e R (fun S x=>(X S x)ᵀ) (fun S=>swap (q S)):=by
 intro x i j; have he:= h x j i; exact ⟨he.1, fun z=> (he.2 z).imp_right (fun f=> f.imp_right And.symm)⟩
lemma trtr {A:MSheet m B}: (fun x=>(A x)ᵀᵀ)=A:=funext fun _=>rfl
lemma PutM.turn (h:PutM K n e a c F): PutM K n e a c (fun x=> (F x)ᵀ):=by obtain ⟨q,X,g,e,p⟩:=h; exact ⟨_,_,tr_Q g,e.flip,fun x v=>by change (F x)ᵀ=_; rw [p x v,Matrix.transpose_sum]⟩
lemma costTr (p:Stamp m B→ Toll (Single Λ)): costM a (fun x=> swap (p x))=costM a p:=by unfold costM; rw [sum_comm]; rfl
lemma HitM.turn (h:HitM K n e a c R F): HitM K n e a c R (fun x=> (F x)ᵀ):=by obtain ⟨q,X,g,e,p⟩:=h; exact ⟨_,_,tr_Q g,(costTr _).trans_le e,fun x v=>by change (F x)ᵀ=_; rw [p x v,Matrix.transpose_sum]⟩
private lemma no(cc':Stamp m B→ Toll (Single Λ)) : costM a cc'=costM a cc':=rfl
lemma PutM.ccW (h:PutM K n e a c F):PutM K n e a c (fun x=> cc (F x)):=by obtain ⟨q,X,v,s,p⟩:=h; exact ⟨_,_,cc_Q v,s,fun x u=> by dsimp only; rw [p x u]; ext; simp [Matrix.sum_apply]⟩
lemma HitM.ccW (h:HitM K n e a c R F): HitM K n e a c R (fun x=> cc (F x)):=by obtain ⟨q,X,v,s,p⟩:=h; exact ⟨_,_,cc_Q v,s,fun x u=>by dsimp only; rw [p x u]; ext; simp [Matrix.sum_apply]⟩
lemma HitM.negW(h:HitM K n e a c R F): HitM K n e a c R (-F):=by obtain ⟨p,X,v,g,e⟩:=h; exact ⟨_,_,neg_Q v,g,fun x u=>by simp [e _ u]⟩
lemma priceA (p q:Stamp m B→ Toll (Single Λ)) (i j:Single Λ):saleM a (p+q) i j=saleM a p i j+saleM a q i j:=by simp only [saleM,Pi.add_apply, mul_add,sum_add_distrib]
lemma costA (p q:Stamp m B→ Toll (Single Λ)): costM a (p+q)=costM a p+costM a q:=by unfold costM; simp_rw [priceA p q,sum_add_distrib]
lemma HitM.plus (h:HitM K n e a c R F)(p:HitM K n e a d R G):HitM K n e a (c+d) R (F+G):=by obtain ⟨q,X,t,l,g⟩:=h; obtain ⟨r,Y,u,k,w⟩:=p; exact ⟨_,_,add_Q t u,by rw [costA]; exact add_le_add l k,fun x u=>by simp [g _ u,w _ u,sum_add_distrib]⟩
lemma TicketM.fuse {S T:Stamp m B}{X Y:MSheet m B}{u z:Toll (Single Λ)}(h:TicketM K n e S R X u)(p:TicketM K n e T ∅ Y z): TicketM K n e (S∪T) R (fun x=> X x*Y x) (fun i j=>∑ k,Ka.β_H n*u i k*z k j):=by
 intro i j; refine ⟨?_, fun w=>?_⟩
 · simp_rw [Matrix.mul_apply]; exact Ka.sumH _ _ _ (fun k _=> ((h i k).1.tin subset_union_left).mul_H ((p k j).1.tin subset_union_right))
 obtain ⟨k,g,g'⟩:= exists_ne_zero_of_sum_ne_zero w; obtain ⟨A,C,m,q⟩:= (h i k).2 (right_ne_zero_of_mul (left_ne_zero_of_mul g')); obtain ⟨B,H,r,z⟩:= (p k j).2 (right_ne_zero_of_mul g'); exact ⟨A.unite B q r,C.trans subset_union_left, subset_union_left m, subset_union_right z⟩
private lemma growthA {x y} (g: 0≤ a)(h: AllM K n e R X q)(p: AllM K n e ∅ Y q'):
 ∑ i:Stamp m B×Stamp m B,rent a (i.1∪i.2)*∑ k, Ka.β_H n*q i.1 x k*q' i.2 k y ≤ Ka.β_H n*∑ v,saleM a q x v*saleM a q' v y:=by
 let V(k:Single Λ)(i j: Stamp m B):=rent a i*q i x k * (rent a j*q' j k y)
 have he(k): ∑ i,∑ j,V k i j= saleM a q x k*saleM a q' k y:=by simp only [V,saleM,mul_sum,sum_mul]; rw [sum_comm]
 rw [Fintype.sum_prod_type]; simp_rw [←he,mul_sum]; rw [sum_comm (f:=fun (k:Single Λ) (i:Stamp m B)=> ∑ j,Ka.β_H n* V k i j)]; refine sum_le_sum fun i _=>?_; rw [sum_comm (f:=fun (k:Single Λ) (j:Stamp m B)=> Ka.β_H n*V k i j)];
 refine sum_le_sum fun j _=>sum_le_sum fun l _=> ?_; have a':0≤Ka.β_H n:=by unfold Ka.β_H; positivity
 refine (mul_le_mul_of_nonneg_right (rent_join i j g) (mul_nonneg (mul_nonneg a' (h.positive ..)) (p.positive ..))).trans_eq ?_; unfold V; ring
lemma HitM.fuseM (p:HitM K n e a c R F)(h:PutM K n e a d G)(hv:0≤a): HitM K n e a (Ka.β_H n*c*d) R (fun x=> F x*G x):=by
 obtain ⟨q,X,s,c',hx⟩:=p; obtain ⟨q',Y,t,d',hy⟩:=h
 obtain ⟨Q,V,L,l,w⟩:= lumpQ (fun z:Stamp m B×Stamp m B=>z.1∪ z.2) (fun z x=> X z.1 x*Y z.2 x) _ (fun i=> TicketM.fuse (s i.1) (t i.2)); refine ⟨Q,V,L,?_,fun x p=> ?_⟩
 · unfold costM; simp_rw [l a]; have hp:0≤ Ka.β_H n:=by unfold Ka.β_H; positivity
   refine (sum_le_sum fun i _=>sum_le_sum fun j _=>growthA hv s t).trans ?_
   simp_rw [←mul_sum]; rw [mul_assoc (Ka.β_H n) c d]; apply mul_le_mul_of_nonneg_left _ hp
   let X':=saleM a q; refine le_trans ?_ (mul_le_mul_of_nonneg_right c' d'.posP); unfold costM; rw [sum_mul]; apply sum_le_sum; intro i _; rw [sum_comm,sum_mul]; simp_rw [←mul_sum]; exact sum_le_sum fun j _=>mul_le_mul_of_nonneg_left (d'.rows j) (sale_nn s.positive ..)
 · dsimp only; rw [←w x,Fintype.sum_prod_type,hx x p,hy x p]; simp only [mul_sum,sum_mul]; rw [sum_comm (f:=fun i j=> X j x* Y i x)]
end YM.CF.XGarden
end
