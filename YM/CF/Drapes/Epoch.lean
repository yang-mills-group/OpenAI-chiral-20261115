import YM.CF.Drapes.Camp
set_option autoImplicit false
noncomputable section
namespace YM.CF.Drapes.Crown
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Topology
open Branch Finset Function Fock Filter
attribute [local instance] opCStarAlgebra
variable {I Y D G : Type*} [Fintype I] [DecidableEq I] [Fintype Y] [DecidableEq Y] [TopologicalSpace D]
variable {b : Stage Y I D G} {s t : Tag b} {Q0 : License D} {a d K C : ℝ}
variable {f₁ : ℕ→Raw D I}
lemma tsK (d : ℕ → ℝ) (h : ∀ n, Crown Q0 s t a (d n) (f₁ n)) (p : 0 ≤ a) (e : Summable d) : Crown Q0 s t a (∑' n,d n) (fun x=>∑' n,f₁ n x) := by
  choose F C L Q R using h
  let H (S:Seal Y) (x:D) := ∑' n,F n S x
  let K (S:Seal Y) (i j : I) := ∑' n,C n S i j
  have nn (n S i j) : 0≤C n S i j := (L n S).nonn _ _
  have ho S i j : Summable (fun n=>C n S i j) := e.of_nonneg_of_le (fun n=>nn n S i j) (fun n=>(Q n).price p (nn n) S i j)
  have hl S i j x : Summable (fun n=> ‖F n S x i j‖) := (ho S i j).of_nonneg_of_le (fun _=>norm_nonneg _) (fun n=>((L n S).expo i j).bounded x)
  have hm S x : Summable (fun n=>F n S x) := kernel_sum _ fun i j=>(hl S i j x).of_norm
  have hx S x i j : H S x i j=∑' n,F n S x i j := kernel_entry (hm S x) i j
  have hs i j : Summable (fun n=>saleM a (C n) i j) := summable_sum fun S _=> (ho S i j).mul_left _ -- tune
  have hk i j : saleM a K i j=∑' n,saleM a (C n) i j := by
    simp_rw [saleM]; rw [Summable.tsum_finsetSum (f:=fun S n=>rent a S*C n S i j)]; unfold K; simp_rw [tsum_mul_left]
    intro S _; exact (ho S i j).mul_left _
  have hw (S) : Ticket s t S (K S) (H S) := by
    refine ⟨fun i x=>?_,fun i j=>?_⟩
    · unfold H; rw [← Summable.tsum_mul_right _ (hm S _), ← Summable.tsum_mul_left _ (hm S _)]; apply tsum_congr; intro n; exact (L n S).frame i x
    have he := ho S i j
    have hp x := hl S i j x
    simp_rw [hx]; refine ⟨tsum_nonneg (fun _=>nn _ S i j),fun p=>?_,fun x=>(norm_tsum_le_tsum_norm (hp x)).trans ((hp x).tsum_le_tsum (fun n=>((L n S).expo i j).bounded x) he),?_,continuous_tsum (fun n=>((L n S).expo i j).connected) he (fun n=>((L n S).expo i j).bounded)⟩
    · by_contra g; apply p
      have hz (n:ℕ) : C n S i j=0 := by by_contra v; exact g (((L n S).expo i j).triggered v)
      simp [K,hz]
    intro x y
    let r := b.eval S x y
    have hi n : ‖F n S x i j-F n S y i j‖≤C n S i j*r := ((L n S).expo i j).variation ..
    have H := (he.mul_right r); have ht := H.of_nonneg_of_le (fun n=>norm_nonneg _) hi
    rw [← (hp x).of_norm.tsum_sub (hp y).of_norm]
    exact (norm_tsum_le_tsum_norm ht).trans ((ht.tsum_le_tsum hi H).trans (le_of_eq (he.tsum_mul_right _)))
  refine ⟨H,K,fun S=> ⟨hw S,fun i j=> by simp_rw [hx]; exact Q0.sumK _ _ (ho S i j) (fun l=> (L l S).fuel i j) (fun l d=>((L l S).expo i j).bounded d)⟩,⟨tsum_nonneg fun n=>(Q n).posP,?_,?_⟩,?_⟩
  · intro i; simp_rw [hk]; rw [←Summable.tsum_finsetSum (f:=fun j n=>saleM a (C n) i j) (hf:=fun j _=> hs i j)]; exact (summable_sum (fun j (_:j∈(univ:Finset I))=>hs i j)).tsum_le_tsum (fun n=>(Q n).rows i) e
  · intro j; simp_rw [hk]; rw [←Summable.tsum_finsetSum (f:=fun i n=>saleM a (C n) i j) (hf:=fun i _=>hs i j)]; exact (summable_sum (fun i (_:i∈(univ:Finset I))=>hs i j)).tsum_le_tsum (fun n=>(Q n).cols j) e
  intro x; dsimp only; simp_rw [R]; exact Summable.tsum_finsetSum (f:=fun S n=>F n S x) (fun S _=>hm S x) -- tune

variable {F A B: Raw D I} {v : ℕ}
lemma sheet {a C : ℝ} (h : Capacity b C) (c : 0≤C) (p : 0 ≤ a) (f : Inter s t F) (e : Continuous F) (g : 0≤K) (m : ℕ)
    (H : Q0.all F) (L : ∀ x, FiniteOp b m (F x)) (A : ∀ i j x, ‖F x i j‖ ≤ K) (B : ∀ i j x y, ‖F x i j-F y i j‖≤ K * b.eval (bay b.F (b.home i) m) x y) :
    Crown Q0 s t a (C*((m:ℝ)+1)^4 * Real.exp (a*(C*((m:ℝ)+1)^4))*K) F := by
  let S := fun i=>bay b.F i m; let D' := fun i (x:D)=> strip b ({i}:Seal Y)*F x
  let X (y:Y) (i j:I) := if y=b.home i ∧ b.home j∈S (b.home i) then K else 0
  have ht y : Ticket s t (S y) (X y) (D' y) := by
    refine ⟨fun i x=>?_,fun i j=>?_⟩
    · dsimp only [D']; rw [mul_assoc,f i,←mul_assoc,strip_tag,mul_assoc]
    have he d : D' y d i j=if y=b.home i then F d i j else 0 := by unfold D'; rw [stripL]; simp [eq_comm]
    simp_rw [he]; unfold X; by_cases l:y=b.home i
    · subst y; simp only [ite_true,true_and]; by_cases k:b.home j ∈ S (b.home i)
      · rw [if_pos k]; exact ⟨g,fun _=>⟨h.grove _ _,bay_mem m|>.mpr (by rw [b.F.reflex]; omega),k⟩,A i j,B i j,e.matrix_elem i j⟩
      rw [if_neg k]; simp_rw [show ∀ x, F x i j=0 from fun x=> L x i j (lt_of_not_ge fun ℓ=>k ((bay_mem _).mpr ℓ))]; exact nothing ..
    simp only [l,false_and,ite_false]; exact nothing ..
  let V := C*((m:ℝ)+1)^4; let R := Real.exp (a*V); let W := V*R*K; have hv : 0≤V := by unfold V; positivity
  have hr : 0<R := Real.exp_pos _
  have hE x : rent a (S x) ≤ R := Real.exp_monotone (mul_le_mul_of_nonneg_left (h.ball x m) p)
  have hx : ∀ x:D,F x=∑ i:Y,D' i x := by
    intro x; ext i j; rw [Matrix.sum_apply]; simp_rw [D',stripL, mem_singleton]; simp
  have hk i j : ∑ l,rent a (S l)*X l i j = rent a (S (b.home i))* (if b.home j∈S (b.home i) then K else 0) := by
    unfold X; simp only [ite_and,mul_ite,mul_zero]; simp -- tune
  refine Crown.absorb S D' X a (show 0≤W by unfold W; positivity) F (fun i=>⟨ht i,Q0.times (Q0.base _) H⟩) hx ?_ ?_
  · intro i; simp_rw [hk]; -- requires unfold ticket in lemma
    simp_rw [mul_ite,mul_zero, ←sum_filter];
    unfold W; rw [sum_const,nsmul_eq_mul,mul_assoc]
    exact mul_le_mul (show ((board b (S (b.home i))).card:ℝ) ≤ V from h.place _ _) (mul_le_mul_of_nonneg_right (hE _) g) (mul_nonneg (rent_pos ..).le g) hv
  intro j; simp_rw [hk]; simp_rw [mul_ite, mul_zero,←sum_filter]
  unfold W; rw [mul_assoc]; apply le_trans (sum_le_sum (g:=fun _=>R*K) (fun i _=>mul_le_mul_of_nonneg_right (hE _) g))
  rw [sum_const,nsmul_eq_mul]
  have hp : univ.filter (fun i=>b.home j∈S (b.home i))=board b (S (b.home j)) := by ext i; simp [board,S,b.F.sym (b.home i)]
  rw [hp]; exact mul_le_mul_of_nonneg_right (h.place _ _) (mul_nonneg hr.le g)

variable (N : Seal Y → Raw D I) (U : Seal Y→Toll I)
-- truncated displays
abbrev ch (Y : Type*) [Fintype Y] (v : ℕ) := (univ : Finset (Seal Y)).filter fun i=>i.card < v
def lop (v : ℕ) (x : D) : Op I := ∑ S ∈ ch Y v,N S x

theorem short (h : ∀ S, Suite Q0 s t S (U S) (N S)) (g : Ledger a U K) : Crown Q0 s t a K (lop N v) := by
  let X S := if S∈ch Y v then U S else 0
  let A S := if S∈ch Y v then N S else 0
  refine ⟨A,X,fun S=>?_,g.lowers ?_,?_⟩
  · by_cases e:S∈ch Y v <;> unfold A X <;> simp only [e,ite_true,ite_false]; exact h S; exact Suite.free S
  · intro S i j; by_cases e:S∈ch Y v
    · rw [show X S=U S from if_pos e]
    rw [show X S=0 from if_neg e]; exact mul_le_mul_of_nonneg_left ((h S).nonn i j) (rent_pos _ _).le
  intro x; rw [lop]; symm; rw [←sum_subset (ch Y v).subset_univ]; apply sum_congr rfl; intro i hi; rw [show A i=N i from if_pos hi]
  intro i _ g; rw [show A i=0 from if_neg g]; rfl -- indent
lemma tail (h : ∀ S, Suite Q0 s t S (U S) (N S)) (p : Ledger a U K) (w : ∀ x,F x=∑ S,N S x) (he : 0 ≤ a) :
    Crown Q0 s t (a/2) (Real.exp (-a/2*v)*K) (fun x=> F x-lop N v x) := by
  let t' := Real.exp (-a/2*v); have Q := p.funds (Real.exp_pos (-a/2*v)).le
  let X S := if S∈(ch Y v)ᶜ then U S else 0
  let A S := if S∈(ch Y v)ᶜ then N S else 0
  refine ⟨A,X,fun S=>?_,Q.lowers ?_,?_⟩
  · unfold A X; by_cases e:S∈(ch Y v)ᶜ <;> simp only [e,ite_true,ite_false]; exact h S; exact Suite.free S
  · intro S i j; change _≤rent a S * (t'*U S i j); by_cases e:S∈(ch Y v)ᶜ
    · rw [show X S=U S from if_pos e,←mul_assoc]; apply mul_le_mul_of_nonneg_right _ ((h S).nonn i j)
      have hp : v ≤ S.card := by simpa [ch] using e
      unfold rent t'; rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; have hu : (v:ℝ)≤S.card := by exact_mod_cast hp
      nlinarith [mul_le_mul_of_nonneg_left hu he]
    rw [show X S=0 from if_neg e]; simp only [Pi.zero_apply, mul_zero]; exact mul_nonneg (rent_pos ..).le (mul_nonneg (Real.exp_pos _).le ((h S).nonn _ _))
  intro x; dsimp only; rw [w x,←sum_add_sum_compl (ch Y v),lop,add_sub_cancel_left]; symm; rw [←sum_subset ((ch Y v)ᶜ).subset_univ]; apply sum_congr rfl; intro i hi; rw [show A i=N i from if_pos hi]
  intro i _ g; rw [show A i=0 from if_neg g]; rfl
lemma delta {a r m : ℝ} (h : Crown Q0 s s a r B) (e : Crown Q0 s s a r A) (p : Crown Q0 s s a m (fun x=>A x-B x)) (g : 0≤a) (n : ℕ) :
    Crown Q0 s s a (2*((n:ℝ)*Real.exp a*m*(2*r)^(n-1))) (fun x=> A x^n-B x^n) := by
  induction n with
  | zero => simp only [pow_zero,sub_self,Nat.cast_zero, zero_mul,mul_zero]; exact Crown.free
  | succ n ih =>
    let f := fun x:D=> A x^n*(A x-B x)+(A x^n-B x^n)*B x
    have he x : A x^(n+1)-B x^(n+1)=f x := by unfold f; rw [pow_succ,pow_succ,mul_sub,sub_mul]; abel
    simp_rw [he]
    have ht := ((e.powers g n).product p g).plus (ih.product h g)
    apply ht.books; cases n with
    | zero => simp [mul_assoc,mul_comm]
    | succ n => simp only [pow_succ, Nat.add_sub_cancel]; push_cast; exact le_of_eq (by ring)


lemma choir [Nonempty I] (h : ∀ S, Suite Q0 s s S (U S) (N S)) (p : Ledger a U K) (q : Capacity b C) (e : 0≤C) (u : ℝ) (he : 0≤u) (hk : 0≤a) (v n : ℕ) (d : ℝ) (hd : 0≤d) (B : ∀ x, ‖lop N v x‖ ≤ u) : let m := n*v+v; let V := C*((m:ℝ)+1)^4;
    Crown Q0 s s d (V*Real.exp (d*V)*blockCost u K n) (fun x => lop N v x^n) := by
  intro m V; let R := blockCost u K n
  have hl x : FiniteOp b v (lop N v x) := lop_rad N U (fun S=>(h S).toTicket) x
  have hn := (short (v:=v) N U h p).powers hk n
  let A := fun x=> lop N v x^n; have ht : Continuous A := by
    apply Continuous.pow
    exact continuous_finsetSum _ fun i _=> (h i).toTicket.cont
  have hg := p.posP; refine sheet q e hd hn.lib.tiesK ht (show 0 ≤ R by unfold R blockCost; positivity) _ hn.air (fun x=> ((hl x).powr _).weak (by unfold m; omega)) ?_ ?_
  · intro i j x; change ‖(lop N v x ^ n) i j‖≤_; unfold R blockCost; exact (norm_entry ..).trans ((norm_pow_le ..).trans ((pow_le_pow_left₀ (norm_nonneg _) (B x) _).trans (le_add_of_nonneg_right (by positivity))))
  intro i j x y; let X z := cage b (b.home i) (n*v) (lop N v z)
  change ‖(A x) i j-(A y) i j‖≤_
  have hQ z : ‖X z‖ ≤ u := (locker (X:=A) ..).trans (B z) -- remove extra arg
  have hw z : A z i j=(X z ^ n) i j := (lock_tight (hl z) (b.home i) n i j (by simp [b.F.reflex])).symm
  have H : ‖X x-X y‖≤K*b.eval (bay b.F (b.home i) m) x y := cage_lip N U (fun S=>(h S).toTicket) p hk _ _ _ (n*v) v
  rw [hw x,hw y]; apply (norm_entry (X x^n-X y^n) i j).trans; apply (pow_near he (hQ _) (hQ _) n).trans
  unfold R blockCost; apply (mul_le_mul_of_nonneg_left H (by positivity)).trans; rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by positivity)) (b.pos ..)
lemma natural [Nonempty I] (C a K u m P : ℝ) (n v : ℕ) (d : ℝ) (pC : 0≤C) (pa : 0≤a) (pu : 0≤u) (q : 0 ≤ d) (p : d ≤ a/2) (g : Real.exp (-a/2*v)*K+P≤u) (w : let V := C*(((n*v+v:ℕ):ℝ)+1)^4; 2*((n:ℝ)*Real.exp (a/2)*(Real.exp (-a/2*v)*K)*(2*K)^(n-1)) + V*Real.exp (d*V)*blockCost u K n ≤ m) : Capacity b C→ Crown Q0 s s a K A → (∀ x, ‖A x‖≤P)→ Crown Q0 s s d m (fun x=> A x^n) := by
  rintro h B H
  obtain ⟨F,N,hF,hN,heq⟩ := B
  let V := C*(((n*v+v:ℕ):ℝ)+1)^4; let Y := V*Real.exp (d*V)*blockCost u K n; let L := 2*((n:ℝ)*Real.exp (a/2)*(Real.exp (-a/2*v)*K)*(2*K)^(n-1)); let T := lop F v
  have hA : Crown Q0 s s (a/2) K A := (show Crown Q0 s s a K A from ⟨F,N,hF,hN,heq⟩).drop (half_le_self pa)
  have hp : Crown Q0 s s (a/2) K T := (short F N hF hN).drop (half_le_self pa)
  have he : Crown Q0 s s (a/2) (Real.exp (-a/2*v)*K) (fun x=>A x-T x) := tail F N hF hN heq pa
  have hi : Crown Q0 s s (a/2) L (fun x=>A x^n-T x^n) := delta hp hA he (q.trans p) _
  have hb : ∀ x, ‖lop F v x‖≤u := fun x=> (norm_le_norm_sub_add _ (A x)).trans ((add_le_add (by rw [norm_sub_rev]; exact he.lib.boundOp (q.trans p) x) (H x)).trans g)
  have hY : Crown Q0 s s d Y (fun x=>T x^n) := choir F N hF hN h pC u pu pa v n d q hb
  simpa only [sub_add_cancel] using (((hi.drop p).plus hY).books w)
end YM.CF.Drapes.Crown
