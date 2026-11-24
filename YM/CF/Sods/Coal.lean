import YM.CF.Sods.Deck
set_option autoImplicit false
noncomputable section
namespace YM.CF.Sods
open Function Filter Metric Finset
open scoped Topology BigOperators ContDiff Matrix MatrixOrder Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {E F:Type*}[Fintype E][DecidableEq E][Nonempty E][DecidableEq F]{f:E→F}{A B C D:Op E}{R t k a z b:ℝ}
lemma switch_mir (p:Switch A B t)(U:UNI E):Switch (twist U A) (twist U B) t:=by unfold Switch; rw [←map_mul,← map_mul, ←map_sub,twist_norm]; exact p
lemma head_off (h:‖C-A‖≤z)(t:‖C‖≤R)(p:‖B‖≤R)(q:‖D-B‖≤b):‖C*D-A*B‖ ≤ z*R + R*b:=by
 rw [show C*D-A*B=(C-A)*B+C*(D-B) by rw [sub_mul,mul_sub]; abel]; apply (norm_add_le ..).trans; exact add_le_add ((norm_mul_le ..).trans (mul_le_mul h p (norm_nonneg _) ((norm_nonneg _).trans h))) ((norm_mul_le ..).trans (mul_le_mul t q (norm_nonneg _) ((norm_nonneg _).trans t)))
lemma switch_b (p:Switch A B k)(hA:‖A‖≤R)(hB:‖B‖≤R)(hC:‖C‖≤R)(hD:‖D‖≤R)(h:‖C-A‖≤z)(l:‖D-B‖≤z):Switch C D (k+4*z*R):=by
 unfold Switch
 rw [show C*D-D*C=(A*B-B*A)+((C*D-A*B)-(D*C-B*A)) by abel]; exact (norm_add_le ..).trans (add_le_add p ((norm_sub_le ..).trans ((add_le_add (head_off h hC hB l) (head_off l hD hA h)).trans_eq (by ring))))
lemma invite (p: F→ℝ)(U:UNI E)(h:Bl f U.val): twist U (Matrix.diagonal fun i=>(p (f i):ℂ))= (Matrix.diagonal fun i=>(p (f i):ℂ)):=by
 let W:=Matrix.diagonal fun i=>(p (f i):ℂ)
 rw [twist_formula,show U.val*W=W*U.val from ?_,mul_assoc,(U.property).2,mul_one]
 ext i j; unfold W; rw [Matrix.mul_diagonal,Matrix.diagonal_mul]; by_cases H:f i=f j; rw [H,mul_comm]; rw [h _ _ H,mul_zero,zero_mul]
lemma gather (d:E→ℝ)(ha:0≤a):∃ F:E→ℝ,(∀ i,|F i-d i|≤Fintype.card E*a) ∧ ∀ i j,F i≠ F j→ a ≤|d i-d j|:=by
 obtain ⟨v,V,X⟩:= turn (univ.image d) a ha; have he(i):d i∈univ.image d:=mem_image_of_mem _ (mem_univ _) -- syntax
 refine ⟨v ∘ d,fun i=>?_,fun i j=> X _ (he i) _ (he j)⟩; rw [abs_sub_comm]; exact (V _ (he i)).trans (mul_le_mul_of_nonneg_right (by exact_mod_cast card_image_le.trans_eq (card_univ (α:=E))) ha)
-- approximate hermitian theorem
abbrev Glaze(E:Type*):= E→List ℝ
lemma recruit(X:E→ℝ)(f:Glaze E)(U:UNI E)(h:Bl (fun i=>X i::f i) U.val):twist U (Matrix.diagonal fun i=>(X i:ℂ))=Matrix.diagonal fun i=>(X i:ℂ):=by
 let Y(i:E):=X i::f i; let P(v:List ℝ):=v.headD 0; have ht:X=P ∘ Y:=funext fun i=>rfl; rw [ht]; exact invite P U (f:=Y) h
lemma recruit_b(X:E→ℝ)(f:Glaze E)(U:UNI E)(h:Bl (fun i=>X i::f i) U.val):Bl f U.val:=fun i j e=>h _ _ (fun E=> e (List.cons.inj E).2)
set_option maxHeartbeats 600000 in
theorem pact (E:Type*)[Fintype E][DecidableEq E][Nonempty E]{I:Type*}(S:Finset I)(v:ℝ)(hp:1≤v):∃ (r:ℕ)(C c:ℝ),1 ≤ r∧0<C∧ 0<c∧∀ (k:ℝ),0<k→ k≤1→∀ (f:Glaze E)(A:I→Op E),(∀ i∈S,IsSelfAdjoint (A i)∧ ‖A i‖≤v∧Bl f (A i))→ (∀ i∈S,∀ j∈S,Switch (A i) (A j) (c*k^r))→ ∃ U:UNI E, Bl f U.val ∧∀ i∈S,∃ F:E→ℝ,‖A i-spectral U F‖≤ C*k:=by
 classical
 induction S using Finset.induction_on generalizing v with
 | empty=> exact ⟨1,1,1,le_rfl,one_pos,one_pos,fun _ _ _ f _ _ _=>⟨1,Bl.one,by simp⟩⟩
 | @insert i S t ih=>
   obtain ⟨r,C,c,l,H,p,Q⟩:= ih (v+1) (by linarith); let m:ℝ:=Fintype.card E; have hm:0<m:=by unfold m; positivity
   let b:= min (1/m) (c/(1+4*m*(v+1))); have hb: 0<b:=lt_min (by positivity) (by apply div_pos p; nlinarith)
   have he:m*b≤1:=by have hx:= (le_div_iff₀ hm).mp (show b≤1/m from min_le_left ..); linarith
   have hh:b+4*(m*b)*(v+1) ≤ c:= by have ht:=(_root_.le_div_iff₀ (show 0< 1+4*m*(v+1) by nlinarith)).mp (show b ≤ c/(1+4*m*(v+1)) from min_le_right ..); nlinarith
   refine ⟨r+1, m*m+m*b+C,b,by omega,by positivity,hb,fun k θ κ f A α hf=>?_⟩
   have hA:=α i (mem_insert_self ..); obtain ⟨U,d,hU,P⟩:= dozen hA.2.2 hA.1
   obtain ⟨F,V,Z⟩:= gather d θ.le
   let X(u:E):=F u :: f u
   let W(j:I):=twist (star U:UNI E) (A j); let T(j:I):=crew X (W j); let D(a:E→ℝ):= Matrix.diagonal fun i=>(a i:ℂ)
   let z:=m*b*k^r; let t₀:= b*k^(r+1); have hz:k^r≤k:= (pow_le_pow_of_le_one θ.le κ l).trans_eq (pow_one _); have hq:W i=D d:=by unfold W; rw [P, spectral, twist_inv]
   have ha(j)(p:j∈S): IsSelfAdjoint (W j)∧Bl f (W j) ∧‖W j‖≤v:=by
     have h:=α j (mem_insert_of_mem p); unfold W; exact ⟨show star _= _ from (map_star _ _).symm.trans (congrArg _ h.1.star_eq),h.2.2.pull hU.star,(twist_norm ..).le.trans h.2.1⟩
   have hP(j)(p:j∈S): Switch (W j) (W i) t₀:= switch_mir (hf j (mem_insert_of_mem p) i (mem_insert_self ..)) _
   have hK(j)(p:j∈S):‖W j-T j‖≤z:=by
     have ht:= crown (f:=f) (ha j p).2.1 (hq ▸ hP j p) θ Z X (fun i j=> by simp [X,and_comm])
     refine ht.trans_eq ?_; unfold z t₀ m; field_simp; ring
   have hV(j)(p:j∈S):‖T j‖≤v+1:=by
      apply (norm_le_norm_sub_add _ (W j)).trans; rw [norm_sub_rev]; have he:= he; have h:= (ha j p).2.2; have ha:=hK j p; have hl:z≤1:=le_trans (mul_le_mul_of_nonneg_left (hz.trans κ) (mul_nonneg hm.le hb.le)) (by simpa using he); linarith
   obtain ⟨Y,u,G⟩:=Q k θ κ X T (fun j h=>⟨(crew_s X (W j)).symm.trans (congrArg (crew X) (ha j h).1.star_eq),hV j h,crew_f X (W j)⟩) (fun j t m' o=> by
      have ht:= switch_b (C:=T j) (D:=T m') (switch_mir (hf j (mem_insert_of_mem t) m' (mem_insert_of_mem o)) (star U)) (le_trans (ha j t).2.2 (show v ≤ v+1 by linarith)) (le_trans (ha m' o).2.2 (by linarith)) (hV j t) (hV m' o) ((norm_sub_rev ..).trans_le (hK j t)) ((norm_sub_rev ..).trans_le (hK m' o)); refine le_trans ht ?_; unfold z; rw [pow_succ]; have he: b*(k^r*k) ≤ b*k^r:=mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (by positivity) κ) hb.le; nlinarith [mul_le_mul_of_nonneg_right hh (pow_nonneg θ.le r)])
   refine ⟨U*Y,hU.mul (recruit_b F f Y u),fun a p=>?_⟩; rcases mem_insert.mp p with p|p
   · subst a; refine ⟨F,?_⟩; rw [P,← twist_spectral,spectral,spectral, recruit F f Y u,←map_sub,twist_norm]; -- tune
     refine (Branch.schur (fun _ _=>m*k) _ (m*m*k) (by positivity) ?_ (fun _=>by rw [sum_const,card_univ,nsmul_eq_mul]; change m*_≤_; rw [←mul_assoc]) (fun _=>by rw [sum_const,card_univ,nsmul_eq_mul]; change m*_≤_; rw [←mul_assoc])).trans (by gcongr; nlinarith); intro j w; by_cases h:j=w; subst w; rw [Matrix.sub_apply,Matrix.diagonal_apply_eq,Matrix.diagonal_apply_eq,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_sub_comm]; exact V _ ; rw [Matrix.sub_apply,Matrix.diagonal_apply_ne _ h,Matrix.diagonal_apply_ne _ h]; simp; positivity
   obtain ⟨D',hd⟩:= G a p; refine ⟨D',?_⟩; rw [← twist_spectral, ← twist_norm (star U:UNI E),map_sub,twist_inv]
   refine (norm_sub_le_norm_sub_add_norm_sub (W a) (T a) _).trans ((add_le_add (hK a p) hd).trans ?_); unfold z; nlinarith [mul_le_mul_of_nonneg_left hz (mul_nonneg hm.le hb.le)]
end YM.CF.Sods
