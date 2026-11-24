import YM.CF.Haro.Weight
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxSize 18000
noncomputable section
namespace YM.CF.Exa
open Function Filter Metric Lattice Wilson Laurent Lat Stationary Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Fock Tulip Font Spire Nacre Ember Pec Branch NormedSpace Finset
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
section
variable {I D G W κ:Type}[Fintype I][DecidableEq I][TopologicalSpace κ][Fintype W][DecidableEq W][TopologicalSpace D]
variable {b:Stage W I D G}{s t u:Branch.Tag b}{L:License D}
abbrev pendB (L: License D)(s t: Branch.Tag b)(F:κ→Raw D I)(S:Seal W)(T:Toll I):Prop:=(∀ i, Suite L s t S T (F i)) ∧∀ x:D, Continuous (fun i:κ=>F i x)
def Vista (L: License D)(s t : Branch.Tag b)(F:κ→Raw D I)(d a:ℝ):Prop:=∃ (M:Seal W→ κ→ Raw D I)(C:Seal W→ Toll I),(∀ S,pendB L s t (M S) S (C S))∧Ledger a C d ∧ ∀ i x,F i x=∑ S,M S i x
variable {f g :κ→Raw D I}{d e a c:ℝ}
namespace Vista
lemma stem(p: Vista L s t f d a)(x:κ): Crown L s t a d (f x):=by obtain ⟨T,W,h,k,p⟩:=p; exact ⟨_,W,fun i=> (h i).1 x,k,p x⟩
lemma tall(p: Vista L s t f d a)(v:d≤c) : Vista L s t f c a:=by obtain ⟨T,W,h,k,p⟩:=p; exact ⟨T,W,h,k.book v,p⟩
lemma holds{X:Raw D I}(P:Crown L s t a d X):Vista L s t (fun _:κ=> X) d a:=by obtain ⟨M,K,H,l,p⟩:=P; exact ⟨_,K,fun i=> ⟨fun _=>H i,fun _=>continuous_const⟩,l,fun _=>p⟩
lemma plus(p:Vista L s t f d a)(q:Vista L s t g c a): Vista L s t (fun i x=>f i x+g i x) (d+c) a:=by
 obtain ⟨M,K,H,l,r⟩:=p; obtain ⟨N,B,q,l',v⟩:=q; refine ⟨fun V i x=> M V i x+ N V i x,_,fun i=> ⟨fun z=>(H i|>.1 z).plus ((q i).1 z),fun x=> (H i|>.2 x).add (q i|>.2 x)⟩,l.pairT l',fun i x=>?_⟩; dsimp only; rw [r,v,sum_add_distrib]
lemma scale(p:Vista L s t f d a)(U:κ→ ℂ)(V:ℝ)(v:∀ i, ‖U i‖≤ V)(e:0 ≤ V)(g:Continuous U): Vista L s t (fun i d=> U i • f i d) (V*d) a:=by
 obtain ⟨M,K,H,l,w⟩:=p
 refine ⟨fun S i x=>U i • M S i x,_,fun S=> ⟨fun i=> ⟨⟨?_,?_⟩,((H S|>.1 i).accel _).fuel⟩,fun _=> g.smul (H S|>.2 _)⟩,l.funds e,?_⟩ -- tune m
 · exact ((H S|>.1 i).accel _).frame
 · intro j k; let T:= ((H S|>.1 i).accel (U i)); have hk:=T.expo j k; have hf:‖U i‖ * K S j k≤ V*K S j k:=mul_le_mul_of_nonneg_right (v i) ((H S|>.1 i).nonn ..)
   exact ⟨hk.positive.trans hf,fun e=> ((H S|>.1 i).expo j k).triggered (right_ne_zero_of_mul e),fun x=> (hk.bounded _).trans hf,fun x y=>(hk.variation _ _).trans (mul_le_mul_of_nonneg_right hf (b.pos ..)),hk.connected⟩
 intro i x; dsimp only; rw [w, smul_sum]
lemma scaleC (p:Vista L s t f d a)(x:ℂ): Vista L s t (fun i m=> x • f i m) (‖x‖*d) a:= p.scale _ ‖x‖ (fun _=>le_rfl) (norm_nonneg _) continuous_const
lemma neg_m (p:Vista L s t f d a): Vista L s t (fun i m=> - f i m) d a:=by simpa using p.scaleC (-1)
lemma subtract(p:Vista L s t f d a)(q:Vista L s t g c a): Vista L s t (fun i x=> f i x-g i x) (d+c) a:=by simp_rw [sub_eq_add_neg]; exact p.plus q.neg_m
lemma dusk[Nonempty κ](p: Vista L s t f d a)(v:c≤a) : Vista L s t f d c:=by obtain ⟨T,W,h,k,p⟩:=p; exact ⟨T,W,h,k.lowers (fun S i x=>mul_le_mul_of_nonneg_right (rent_up v S) ((h S|>.1 (Classical.arbitrary κ)).nonn i x)),p⟩
lemma bundle {J:Type*}[Fintype J](v:ℝ)(hp:0≤v)(Z:J→Seal W)(M:J→κ→Raw D I)(X:J→Toll I)(q:∀ i,pendB L s t (M i) (Z i) (X i))(e:∀ i,∑ j,∑ k,Branch.rent a (Z k)*X k i j ≤ v)(w:∀ i,∑ j,∑ k,Branch.rent a (Z k)*X k j i ≤ v)(E:κ→ Raw D I)(h:∀ i x,E i x=∑ k,M k i x): Vista L s t E v a:=by
 let F(Y:Seal W)(i j:I):=∑ l∈ dest Z Y,X l i j
 have he i j:saleM a F i j=∑ l,Branch.rent a (Z l)*X l i j:=by rw [lump Z _]; unfold saleM F; apply Finset.sum_congr rfl; intro S _; rw [mul_sum]; exact sum_congr rfl fun i h=>by rw [(mem_filter.mp h).2]
 refine ⟨fun S i x=>∑ l∈dest Z S, M l i x,F,fun S=> ⟨fun i=> ⟨Ticket.sumT (dest Z S) X _ (fun j p=>by rw [←show Z j=S from (mem_filter.mp p).2]; exact (q j|>.1 i).toTicket), L.suppose _ _ (fun j _=>(q j|>.1 i).fuel)⟩,fun _=> continuous_finsetSum _ fun i _=> q i|>.2 _⟩,⟨hp,fun i=>by simp_rw [he]; exact e i,fun i=>by simp_rw [he]; exact w i⟩, fun i x=> by rw [h,lump Z _]⟩
lemma mint[Nonempty κ] (p:Vista L s t f d a)(q:Vista L t u g c a)(v:0 ≤ a): Vista L s u (fun i x=> f i x*g i x) (2*(d*c)) a:=by
 obtain ⟨M,K,H,l,p⟩:=p; obtain ⟨N,B,q,l',w⟩:=q
 let X(t:Seal W×Seal W)(i:κ)(x):=M t.1 i x*N t.2 i x
 have hx (i:κ)(x:D): f i x*g i x=∑ j,X j i x:=by rw [Fintype.sum_prod_type,p,w]; simp only [sum_mul,mul_sum]; rw [sum_comm];
 let Y(t:Seal W×Seal W):=Branch.charge (K t.1) (B t.2)
 have hy (j:Seal W×Seal W):pendB L s u (X j) (j.1∪j.2) (Y j):= ⟨fun i=>(H j.1|>.1 i).jointK (q j.2|>.1 i), fun x=>Continuous.mul (H j.1|>.2 x) (q j.2|>.2 x)⟩
 have hM(S:Seal W)(i j:I):0 ≤ K S i j:=(H S|>.1 (Classical.arbitrary κ)).nonn i j
 have hN(S:Seal W)(i j:I):0 ≤ B S i j:=(q S|>.1 (Classical.arbitrary κ)).nonn i j
 have ht:=slope_row hM hN l l' v; have hz:=slope_col hM hN l l' v
 refine bundle (2*(d*c)) (by have hX:=l.posP; have he:=l'.posP; positivity) _ X Y hy (fun i=> ht i) ?_ _ hx
 intro j; exact hz j
lemma slug[Nonempty κ] (p:Vista L s s f d a)(v:0≤ a)(n:ℕ):Vista L s s (fun i X=> (f i X)^n) (Real.exp a*(2*d)^n) a:=by induction n with| zero=> simpa using holds (κ:=κ) (Crown.ident L s a)| succ i ih=> simp_rw [pow_succ]; exact (ih.mint p v).tall (le_of_eq (by ring))
lemma markL {J:Type}[Nonempty κ](V:J→κ→Raw D I)(S:Finset J)(P:J→ℝ)(p:∀ i∈S,Vista L s t (V i) (P i) a):Vista L s t (fun i x=>∑ k∈ S,V k i x) (∑ i∈S,P i) a:=by
 classical
 induction S using Finset.induction_on with| empty=> simp_rw [sum_empty]; exact holds Crown.free| @insert v S q ih => simp_rw [sum_insert q]; exact (p v (mem_insert_self ..)).plus (ih (fun i z=> p i (mem_insert_of_mem z)))
end Vista
end
end YM.CF.Exa
