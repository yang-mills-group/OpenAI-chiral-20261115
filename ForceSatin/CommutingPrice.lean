import ForceSatin.Excitation
import YM.SU5.Relativistic.Nero

/-! Normal-order estimation in WA.11. Existence on Bosonic Point fields
    doesn't mean the finite estimates can suppress orientation in the CAR
    movement. Bound vac-and-active difference by expanding CAR in the finite
    *word*. Keep constants independent of the scale at fixed length/B.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Papyrus.Franc.SatinForce
open Function Filter NormedSpace Fock Finset Cascade Thera Flare
open scoped Topology Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator BigOperators ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
variable {I : Type} [LinearOrder I] [Fintype I]

def reading (q x : Wave I) : FC I →ₗ[ℂ] ℂ where
 toFun A := inner ℂ q (acts A x)
 map_add' a b:=by rw [act_add,inner_add_right]
 map_smul' c a:=by rw [act_smul,inner_smul_right]; rfl

def resid (q x: Wave I) : FC I→ₗ[ℂ] ℂ := reading x x - (inner ℂ x x) • reading q q
lemma resid_unit (q x: Wave I)(p:‖q‖=1): resid q x 1=0 := by simp [resid,reading,inner_self_eq_norm_sq_to_K,p]
lemma read_price (q x: Wave I)(A:FC I): ‖reading q x A‖ ≤ ‖A‖*(‖q‖*‖x‖):=by
  change ‖inner ℂ q (acts A x)‖ ≤ _
  apply (norm_inner_le_norm ..).trans; apply le_trans (mul_le_mul_of_nonneg_left (Graph.spentS _ A x) (norm_nonneg q)); rw [mul_left_comm]
lemma resid_price (q x: Wave I)(u:‖q‖=1)(A:FC I) : ‖resid q x A‖ ≤ 2*‖A‖*‖x‖^2:=by
  change ‖reading x x A-inner ℂ x x * reading q q A‖ ≤_
  apply (norm_sub_le ..).trans; rw [norm_mul,inner_self_eq_norm_sq_to_K,norm_pow,RCLike.norm_ofReal,abs_of_nonneg (norm_nonneg _)]
  have hv:= read_price q q A; rw [u,mul_one,mul_one] at hv
  exact le_trans (add_le_add (read_price ..) (mul_le_mul_of_nonneg_left hv (sq_nonneg _))) (le_of_eq (by ring))

-- one annihilator on the occupied space (when acts on right)
structure Annihilation (q x:Wave I)(ε:ℝ)(A:FC I) : Prop where
 kill : acts A q=0
 cheap : ‖acts A x‖≤ ε

variable {q x:Wave I}{ε C : ℝ}

lemma resid_right (L D:FC I)(u:Annihilation q x ε D) :
    ‖resid q x (L*D)‖ ≤ ‖L‖*ε*‖x‖:=by
  change ‖inner ℂ x _-inner ℂ x x * inner ℂ q (acts (L*D) q)‖≤_
  rw [act_mul,act_mul,u.kill,map_zero,inner_zero_right,mul_zero,sub_zero]
  exact (read_price x (acts D x) L).trans (le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left u.cheap (norm_nonneg x)) (norm_nonneg L)) (le_of_eq (by ring)))

lemma resid_left (A L:FC I)(u:Annihilation q x ε (star A)) :
    ‖resid q x (A*L)‖ ≤ ‖L‖*ε*‖x‖:=by
  change ‖inner ℂ x _-inner ℂ x x * inner ℂ q (acts (A*L) q)‖≤_
  rw [act_mul,act_mul,←act_inner A x,←act_inner A q,u.kill,inner_zero_left,mul_zero,sub_zero]
  exact (read_price (acts (star A) x) x L).trans (le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right u.cheap (norm_nonneg x)) (norm_nonneg L)) (le_of_eq (by ring)))

-- bound resid everywhere shorter before commuting; ε bound simultaneous across letter occurrences in a copy, not a volume charge for each
private theorem commute_price [Nonempty I] {J:Type*}(A:J→FC I) (ok : J → Prop)(B U:ℝ)(h:1≤B)
    (m:ℕ)(p:0≤ε)(u:0≤U)(v:∀ i, ok i → ‖A i‖ ≤ B)(D:FC I)(x0:Annihilation q x ε D)
    (y:∀ i, ok i → ∃ c:ℂ, D*A i+A i*D=c • 1 ∧ ‖c‖≤U)
    (b:ℝ) (_bh:0≤b) (IH:∀ L:List J, L.length ≤ m→ (∀ j∈L,ok j)→ ‖resid q x (rollC A L)‖≤ b*ε*‖x‖) : ∀ L R:List J, L.length+R.length ≤ m → (∀ j∈L++R,ok j)→
     ‖resid q x (rollC A L * D * rollC A R)‖≤ (B^m+R.length * U*b)*ε*‖x‖:=by
  intro L R; induction R generalizing L with
  | nil=>
    intro l p'; have hL:L.length ≤ m:=by simpa using l
    rw [show rollC A []=1 from rfl,mul_one]; simp only [List.length_nil,Nat.cast_zero,zero_mul,add_zero]
    apply (resid_right _ _ x0).trans; gcongr; exact (Loaves.normC A _ (zero_lt_one.trans_le h) _ (fun i hi=> v i (p' _ (List.mem_append_left _ hi)))).trans (pow_le_pow_right₀ h hL)
  | cons i R hr=>
    intro l p'
    have hi: ok i:=p' _ (List.mem_append_right _ List.mem_cons_self)
    obtain ⟨c,f,g⟩:= y i hi
    have hv:(rollC A L)*D*rollC A (i::R)= c • rollC A (L++R) - rollC A (L++[i])*D*rollC A R:=by
      simp only [rollC,List.map_append,List.map_cons,List.map_nil,List.prod_append,List.prod_cons,List.prod_nil,mul_one]; rw [← mul_assoc _ (A i), mul_assoc _ D, eq_sub_of_add_eq f,mul_sub,sub_mul,Algebra.mul_smul_comm,mul_one,Algebra.smul_mul_assoc,mul_assoc _ (A i)];
    have ok0(j): j∈ L++R→ ok j:=fun t=>p' j (by simp at t ⊢; tauto)
    have hz:=IH (L++R) (by simp only [List.length_append]; simp only [List.length_cons] at l; omega) ok0
    have hg:= hr (L++[i]) (by simp only [List.length_cons,List.length_append,List.length_nil] at *; omega) (fun j hj=>by
      simp only [List.mem_append,List.mem_singleton] at hj; grind)
    rw [hv, map_sub,map_smul]; apply (norm_sub_le ..).trans; rw [norm_smul]
    apply (add_le_add (mul_le_mul g hz (norm_nonneg _) u) hg).trans_eq; rw [List.length_cons]; push_cast; ring

/-- Cost recursion before any prices with t or volumes. -/
def normalCost (B:ℝ) : ℕ → ℝ
| 0 => 0
| n+1 => 2*B^n + (1+n* (B*B)) * normalCost B n

lemma normal_non {B:ℝ}(p:1≤ B)(n:ℕ) : 0≤normalCost B n:=by
  have h:=zero_lt_one.trans_le p; induction n with | zero=>rfl| succ n ih=>rw [normalCost]; positivity

lemma pair_bond {d c:Ket I}{b a:Bool}{B:ℝ}(h:‖d‖ ≤ B)(p:‖c‖≤B) : ∃ x:ℂ,
    creed a d * creed b c + creed b c * creed a d=x • 1∧ ‖x‖≤ B*B:=by
  have ht:0≤B:=(norm_nonneg _).trans h
  cases a <;> cases b
  · exact ⟨0,by rw [zero_smul]; exact car_create .., by rw [norm_zero]; positivity⟩
  · exact ⟨inner ℂ c d,(add_comm ..).trans (car c d),(norm_inner_le_norm ..).trans (mul_le_mul p h (norm_nonneg _) ht)⟩
  · exact ⟨inner ℂ d c,car d c,(norm_inner_le_norm ..).trans (mul_le_mul h p (norm_nonneg _) ht)⟩
  exact ⟨0,by rw [zero_smul]; exact car_rem ..,by rw [norm_zero]; positivity⟩

lemma flipCreed {q:Ket I} (a:Bool) : star (creed a q) = creed (!a) q := by
  cases a; rfl; exact star_star _

def shield (P:Op I)(x:Wave I)(v:Ket I)(ε:ℝ):Prop:=
    ‖acts (create (acts P v)) x‖ ≤ ε ∧ ‖acts (Fock.remove (acts (1-P) v)) x‖ ≤ ε

variable [Nonempty I]
lemma length_price {J:Type*}(A:J→Ket I) (X:J→Bool)(P:Op I)(t:IsStarProjection P)(v:Sea P q)
    {ε B:ℝ}(h:1≤B)(p:0≤ε) (m:ℕ)(L:List J) (g:L.length ≤ m)
    (u:∀ i∈L, ‖A i‖≤B ∧ shield P x (A i) ε) :
    ‖resid q x (rollC (fun j=>creed (X j) (A j)) L)‖ ≤ normalCost B m *ε* ‖x‖:=by
  let W(i:J):=creed (X i) (A i)
  change ‖resid q x (rollC W L)‖ ≤ _
  have hf(n:ℕ): ‖resid q x (rollC W [])‖ ≤ normalCost B n *ε*‖x‖:=by
    rw [rollC,List.map_nil,List.prod_nil,resid_unit q x v.2,norm_zero]; exact mul_nonneg (mul_nonneg (normal_non h n) p) (norm_nonneg _)
  induction m generalizing L with
  | zero => rw [List.length_eq_zero_iff.mp (Nat.le_zero.mp g)]; exact hf 0
  | succ m IH=>
    cases L with
    | nil=> exact hf _
    | cons i L =>
      let D:= A i; let a:=X i; let Y:= if a then 1-P else P; let b:=normalCost B m
      have hb:= u i List.mem_cons_self
      have hv:IsStarProjection Y:=by unfold Y; split; exact t.one_sub; exact t
      let x' := acts Y D; let w:= creed a x'; let l:= rollC W L; let y':=acts (1-Y) D; let z:= creed a y'
      have hl (i:J)(p:i∈L): ‖A i‖≤B ∧ shield P x (A i) ε:=u i (List.mem_cons_of_mem _ p)
      have g':L.length ≤ m:=Nat.le_of_succ_le_succ g
      change ‖resid q x (W i*l)‖ ≤ _
      have ann(t':Ket I): acts (create (acts P t')) q=0:= tarp t v.1 (by rw [←act_mul,t.isIdempotentElem.eq])
      have ant(t':Ket I): acts (Fock.remove (acts (1-P) t')) q=0:= tars t v.1 (by rw [←act_mul,Porth t,act_zero])
      have ha : Annihilation q x ε w ∧ Annihilation q x ε (star z):= by
        rw [show star z=_ from flipCreed (q:=y') a]; unfold w x' y' Y; cases e:a
        · change Annihilation q x ε (create _) ∧ Annihilation q x ε (Fock.remove (acts (1-P) D)); exact ⟨⟨ann D,hb.2.1⟩,⟨ant D,hb.2.2⟩⟩
        simp only [ite_true,sub_sub_cancel]
        exact ⟨⟨ant D,hb.2.2⟩,⟨ann D,hb.2.1⟩⟩
      have sy(j:J)(t:j∈L): ‖W j‖ ≤ B:= (cost_pe ..).trans (hl j t).1
      have kh:0<B:=zero_lt_one.trans_le h
      have hz : ‖l‖ ≤ B^m := (Loaves.normC _ _ kh _ sy).trans (pow_le_pow_right₀ h g')
      have hx:‖x'‖≤B:= (opy ..).trans ((mul_le_of_le_one_left (norm_nonneg _) (hv.norm_le _)).trans hb.1)
      have hh : ‖resid q x (w*l)‖ ≤ (B^m+(m:ℝ)*(B*B)*b)*ε*‖x‖:=by
        have hh:= commute_price W (fun j=> j∈L) B (B*B) h m p (by positivity) sy w ha.1 (fun j hj=> pair_bond hx (hl j hj).1) b (normal_non h m) (fun l f x=>IH l f (fun i p=> hl _ (x i p))) [] L (by simpa using g') (fun i j=>by simpa using j)
        rw [show rollC W []=1 from rfl, one_mul] at hh; apply hh.trans; gcongr; exact normal_non h m
      rw [show W i=z+w from ?_,add_mul,map_add]; swap
      · change creed a D=creed a (acts (1-Y) D)+creed a (acts Y D); rw [←creed_a,←act_add,sub_add_cancel,act_one]
      apply (norm_add_le ..).trans; apply le_trans (add_le_add ((resid_left z l ha.2).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hz p) (norm_nonneg _))) hh)
      rw [normalCost]; change _≤(2*B^m+ _*b)*_*_
      nlinarith only [mul_nonneg (mul_nonneg (show 0≤b from normal_non h m) p) (norm_nonneg x)]

end YM.CF.Papyrus.Franc.SatinForce
