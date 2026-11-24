import GaugeFieldConstruction.Customers
/- Watermark sum on several excitation polynomials. Map here in list order starting left, Fock.rollC. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 30000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Fock.Flux
open Function NormedSpace Finset
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator Topology BigOperators InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {I:Type*} [LinearOrder I][Fintype I]{P: Op I}{w:Wave I}
variable {J:Type*} (a:J→Bool)(V:J→ Ket I){L R r:ℝ}
-- exact normal order on weighted price of annihilation. Useful also for W1–2/P3.
def tuckC (c:ℂ) (j:J) (A:J→FC I)(L:List J) (d:J→ℂ): FC I:= (c*d j) • rollC A L
lemma groom (v:J→FC I)(x:FC I)(d:J→ℂ)(h:∀ i,x*v i+v i*x=d i •1)
 (L:List J):
   x * rollC v L= ((-1:ℂ)^L.length) • (rollC v L * x) + ((picks L).map fun i=>tuckC (cval i.neg) i.front v i.back d).sum:=by
 let f(i:Bout J):= tuckC (cval i.neg) i.front v i.back d
 induction L with
 | nil=> simp [rollC,picks]
 | cons i l ih=>
    let y:= rollC v l; let c:ℂ:= (-1)^l.length; let S:= (picks l).map f; let A:= v i
    change x*(A*y)= _; have ht: x*(A*y)= d i • y - A*(x*y):=by rw [←mul_assoc, show x*A=d i • 1-A*x from eq_sub_of_add_eq (h i),sub_mul, Matrix.smul_mul,one_mul,mul_assoc]
    rw [ht,show x*y= c • (y*x)+ S.sum from ih]
    change _= ((-1:ℂ)^_ ) • ((A*y)*x) + ((picks (i::l)).map f).sum
    rw [picks,List.map_cons,List.sum_cons,List.map_map, List.length_cons,pow_succ']
    have he (x:Bout J): f (beside i x) = -(A * f x):=by
       unfold f tuckC; dsimp only [beside]; rw [cneg,Fock.rollC,List.map_cons,List.prod_cons]; change _ • (A*rollC v x.back)=_
       rw [Matrix.mul_smul, neg_mul,neg_smul]
    have hh(B:List (Bout J)): (B.map (f ∘ beside i)).sum= -(A*(B.map f).sum):=by
       induction B with | nil=>simp| cons i l ih=> simp only [List.map_cons,List.sum_cons,comp_apply,he,ih,mul_add, neg_add]
    rw [hh,show f ⟨false,i,l⟩= d i • y from (by unfold f tuckC cval; simp [y])]; change d i • y-A*(c • (y*x)+S.sum)=((-1:ℂ)*c) • ((A*y)*x)+(d i • y + -(A*S.sum)) -- tune remove minus
    rw [mul_add,Matrix.mul_smul,neg_one_mul,neg_smul,mul_assoc]; abel
lemma picks_size (l:List J): (picks l).length=l.length:=by induction l with| nil=>rfl | cons i l ih=>simp only [picks,List.length_cons,List.length_map,ih]
lemma picks_rank {l:List J}(j:Bout J)(h:j∈ picks l): j.front ∈ l ∧ j.back.length < l.length∧ j.back⊆l:=by
 induction l generalizing j with
 | nil=> simp [picks] at h
 | cons i l ih=>
    obtain h|⟨x,p,rfl⟩:= show j=⟨false,i,l⟩∨_ from ((List.mem_cons.mp h).imp Iff.rfl.mp List.mem_map.mp)
    · subst j; simp [List.subset_def]; tauto
    obtain ⟨f,b,d⟩:=ih _ p; unfold beside; refine ⟨List.mem_cons_of_mem _ f,?_ ,?_⟩
    · exact Nat.succ_lt_succ b
    exact List.cons_subset_cons i d
abbrev quotation (x:Wave I)(M:FC I):ℂ:= inner ℂ x (acts M x)
lemma quot_scale (x:Wave I)(M:FC I)(c:ℂ): quotation x (c • M)= c*quotation x M:=by unfold quotation; rw [act_smul,inner_smul_right]
lemma quot_sum (x:Wave I)(M N:FC I): quotation x (M+N)=quotation x M+quotation x N:=by unfold quotation; rw [act_add,inner_add_right]
lemma quot_sub (x:Wave I)(M N:FC I): quotation x (M-N)=quotation x M- quotation x N:=by unfold quotation; rw [act_sub,inner_sub_right]
lemma quot_nil (x:Wave I)(p:‖x‖=1): quotation x (1:FC I)=1:=by unfold quotation; rw [act_one,inner_self_eq_norm_sq_to_K,p]; simp
lemma quot_cost (x:Wave I)(p:‖x‖=1)(S:FC I): ‖quotation x S‖≤‖S‖:=by
 apply (norm_inner_le_norm ..).trans; rw [p,one_mul]; exact (Graph.spentS _ _ _).trans (by rw [p,mul_one])
abbrev pieceV (i:J) := creed (a i) (V i)
lemma lick {l:List J}(z:0≤r)(p:∀ i∈l, ‖V i‖ ≤ r):‖rollC (pieceV a V) l‖ ≤ r^l.length:=by
 induction l with| nil=> simp [rollC] | cons i l ih=> exact (norm_mul_le (pieceV a V i) (rollC (pieceV a V) l)).trans ((mul_le_mul ((Flare.cost_pe ..).trans (p i (List.mem_cons_self))) (ih fun j h=>p j (List.mem_cons_of_mem _ h)) (norm_nonneg _) z).trans_eq (pow_succ' ..).symm)
def predrawn (r:ℝ) : ℕ → ℝ
 | 0=>0
 | k+1 => 2*r^k + (k:ℝ)*r*r*(predrawn r k) + predrawn r k
lemma pred_nonneg (r:ℝ)(p:0≤r)(n:ℕ):0≤predrawn r n:=by induction n with|zero=>rw [predrawn] | succ n ih=> unfold predrawn; positivity
lemma pred_raise (r:ℝ)(p:0≤r): Monotone (predrawn r):=by apply monotone_nat_of_le_succ; intro n; rw [predrawn]; refine le_add_of_nonneg_left ?_; have he:=pred_nonneg r p n; positivity
lemma list_charge {A:List (FC I)}(x z:Wave I)(h:∀ i∈A, ‖quotation x i-quotation z i‖≤ R): ‖quotation x A.sum-quotation z A.sum‖ ≤ A.length*R:=by
 induction A with
 | nil=> simp [quotation]
 | cons i l ih=> rw [List.sum_cons,quot_sum,quot_sum,show quotation x i+quotation x l.sum-(quotation z i+quotation z l.sum)=(quotation x i-quotation z i)+(quotation x l.sum-quotation z l.sum) by abel]; apply (norm_add_le ..).trans; apply (add_le_add (h _ List.mem_cons_self) (ih fun i p=>h i (List.mem_cons_of_mem _ p))).trans_eq; simp only [List.length_cons,Nat.cast_add,Nat.cast_one]; ring
-- x and v both unit; contracted scalar is paid separately in (56). high momenta x and w Price
lemma wick_Rate (g:IsStarProjection P)(h:Sea P w)(z:Wave I)(n:‖z‖=1)(f:1≤r)(p:0≤ L): ∀ m:ℕ,∀ l:List J, l.length≤ m → (∀ i∈l,‖V i‖≤ r) →(∀ i∈l,∀ v:Bool,‖acts (dustAnn v P (V i)) z‖≤ L) →
  ‖quotation z (rollC (pieceV a V) l)-quotation w (rollC (pieceV a V) l)‖ ≤ predrawn r m * L:=by
 let F:= pieceV a V; let Q:= quotation z; let Ω:= quotation w; have hp:0 ≤ r:= zero_le_one.trans f
 intro m; induction m with
 | zero=> intro l H _ _; have ht:l=[]:= List.length_eq_zero_iff.mp (le_antisymm H (Nat.zero_le _)); rw [ht]; simp [rollC,quot_nil z n, quot_nil w h.2,predrawn]
 | succ m ih=>
    rintro (_|⟨i,l⟩) e pV u
    · simp only [rollC,List.map_nil,List.prod_nil,quot_nil z n,quot_nil w h.2,sub_self,norm_zero]; exact mul_nonneg (pred_nonneg r hp _) p
    have he:l.length ≤ m:= Nat.le_of_succ_le_succ e; let Y:=rollC F l; have hv:= V i; let A:=dustAnn (a i) P (V i); let B:=dustAnn (!(a i)) P (V i); let R:=r^m
    have hm:‖Y‖≤ R:= (lick a V hp (l:=l) (fun i p=>pV i (List.mem_cons_of_mem _ p))).trans (pow_le_pow_right₀ f he)
    have hc : ‖Q (star B*Y)‖ ≤ L*R:=by
       change ‖inner ℂ _ (acts _ _)‖ ≤ _; rw [act_mul,←act_inner,star_star]; apply (norm_inner_le_norm ..).trans; apply mul_le_mul (u i List.mem_cons_self _) ((Graph.spentS _ _ _).trans (by rw [n,mul_one]; exact hm)) (norm_nonneg _) p
    have hx : Ω (star B*Y)=0:=by change inner ℂ _ (acts _ _)=_; rw [act_mul,←act_inner,star_star,dust_kills _ _ g h,inner_zero_left]
    have ha: ‖Q (Y*A)‖ ≤ R*L:=by
       change ‖inner ℂ _ (acts _ _)‖≤ _; rw [act_mul]; apply (norm_inner_le_norm ..).trans; rw [n,one_mul]; apply (Graph.spentS _ _ _).trans (mul_le_mul hm (u i List.mem_cons_self _) (norm_nonneg _) ((norm_nonneg _).trans hm))
    have hQ: Ω (Y*A)=0:=by change inner ℂ _ (acts _ _)=_; rw [act_mul, dust_kills _ _ g h,map_zero,inner_zero_right]
    let d(j:J):=laceSC (a i) (a j) (acts (penny (a i) P) (V i)) (V j);
    have ht(j:J):antiB A (F j)=d j • 1:= centSC ..
    let S:= (picks l).map fun j=> tuckC (cval j.neg) j.front F j.back d
    let c:=((-1:ℂ)^l.length); have hs: ‖Q S.sum-Ω S.sum‖ ≤ (m:ℝ)*(r*r*predrawn r m*L):=by
       apply le_trans (list_charge z w (A:=S) (R:=r*r*predrawn r m*L) ?_) ?_
       · intro j xq; obtain ⟨V',pV',rfl⟩:= List.mem_map.mp xq; obtain ⟨P',l₀,t⟩:= picks_rank _ pV'
         have hv': ‖d V'.front‖≤r*r:= (lace_le ..).trans (mul_le_mul ((dust_char g ..).trans (pV _ List.mem_cons_self)) (pV _ (List.mem_cons_of_mem _ P')) (norm_nonneg _) hp)
         let R':= rollC F V'.back; let c:= cval V'.neg * d V'.front; have hN: ‖c‖≤ r*r:=by unfold c; rw [norm_mul,show ‖cval V'.neg‖=1 from (by cases hx:V'.neg <;> simp [cval,hx]),one_mul]; exact hv'
         change ‖Q (c • R')-Ω (c • R')‖≤ _; rw [show Q _= c* Q R' from quot_scale ..,show Ω _= c* Ω R' from quot_scale ..,←mul_sub,norm_mul]; have hb(k:J)(h:k∈ V'.back):k∈ i::l:=List.mem_cons_of_mem _ (t h)
         exact (mul_le_mul hN (ih V'.back (l₀.le.trans he) (fun j p=>pV j (hb j p)) (fun j p=>u j (hb j p))) (norm_nonneg _) (mul_nonneg hp hp)).trans_eq (by ring)
       unfold S; rw [List.length_map,picks_size]; apply mul_le_mul_of_nonneg_right (Nat.cast_le.mpr he); have he:=pred_nonneg r hp m; positivity
    change ‖quotation z (F i*Y)-quotation w (F i*Y)‖ ≤ _; rw [show F i=star B+A from dust_star .., add_mul, show A*Y= _ from (show A*Y= c • (Y*A)+ S.sum from groom F A d ht l),quot_sum,quot_sum,quot_sum,quot_sum,quot_scale,quot_scale]; change ‖Q (star B*Y)+(c* Q _+Q S.sum) - (Ω (star B*Y)+(c*Ω _+Ω S.sum))‖ ≤ _; rw [hx,hQ,mul_zero,zero_add,zero_add]; let W:= c* Q (Y*A); rw [show Q (star B*Y)+ (W+Q S.sum)-Ω S.sum=(Q (star B*Y)+W)+(Q S.sum-Ω S.sum) by abel]; have hW: ‖W‖≤ R*L:=by unfold W c; rw [norm_mul]; simpa using ha -- tune simp
    apply (norm_add_le ..).trans ((add_le_add ((norm_add_le ..).trans (add_le_add hc hW)) hs).trans ?_); rw [predrawn]; have hm:0≤predrawn r m:= pred_nonneg r hp m; unfold R; linarith only [mul_nonneg hm p]
end YM.CF.Fock.Flux
end
