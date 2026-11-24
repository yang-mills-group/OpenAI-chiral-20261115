import Gingham.Ruff.Tassel

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

noncomputable section
namespace YM.CF.Gingham.Ruff
open Function NormedSpace Finset Fock Scree Pastry
open scoped Topology BigOperators InnerProductSpace ComplexConjugate Matrix MatrixOrder Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {n : Type*} [LinearOrder n] [Fintype n]


/-! dΓ is a derivation on the even symbol algebra. (No projection required here.) -/
def shock (Z : FC n) : FC n→ₗ[ℂ]FC n where
 toFun b := Z*b - b*Z
 map_add' x y := by rw [mul_add,add_mul]; abel
 map_smul' z x := by rw [Algebra.mul_smul_comm,Algebra.smul_mul_assoc,RingHom.id_apply,smul_sub]

lemma shock_times (Z x y : FC n) :
    shock Z (x*y) = shock Z x * y + x * shock Z y := by
  simp only [shock,LinearMap.coe_mk,AddHom.coe_mk,sub_mul,mul_sub,mul_assoc]
  abel
lemma shock_one (Z : FC n) : shock Z 1 = 0 := by
  change Z*1-1*Z=0
  simp
lemma shock_scal (x : ℂ) (Z Q : FC n) :
    shock (x • (1:FC n) - Z) Q = - shock Z Q := by
  change (x • (1:FC n) - Z)*Q-Q*(x • (1:FC n) - Z)=-(Z*Q-Q*Z)
  rw [sub_mul,mul_sub,Algebra.smul_mul_assoc,one_mul,Algebra.mul_smul_comm,mul_one]
  abel

lemma pulse_let (E:Op n) (i:n) :
    shock (dg E) (put i) = ∑ j, E j i • put j := by
  change dg E * put i - put i * dg E = _
  rw [shelve,create_def]
  simp only [basis_act]


variable {s : Finset n}
theorem flour_every (P : FC n → Prop) (pair : ∀ i∈s,∀ j∈s, P (put i*put j))
    (scale : ∀ {x}, P x → ∀ t:ℂ, P (t • x)) (plus : ∀ {x y}, P x → P y → P (x+y))
    (times : ∀ {x y}, P x → P y → P (x*y)) (single : P 1)
    {A : FC n} (h : Flour s A) : P A := by
  have z : ∀ k, k∈ Wheat s → P (poke k) := by
    intro k
    induction k using Finset.strongInductionOn with
    | _ k ih =>
      intro w
      obtain ⟨u,p⟩ := mem_filter.mp w
      have hsub : k ⊆ s := mem_powerset.mp u
      by_cases v:k.Nonempty
      · obtain ⟨j,g⟩:=v
        have he : (k.erase j).Nonempty := by
          rw [←card_pos,card_erase_of_mem g]
          have hx:= (show k.Nonempty from ⟨j,g⟩).card_pos
          obtain ⟨i,f⟩:=p; omega
        obtain ⟨l,u⟩:=he
        let t := (k.erase j).erase l
        have hx : t ⊂ k := lt_trans (erase_ssubset u) (erase_ssubset g)
        have hv : Even t.card := by
          unfold t; rw [card_erase_of_mem u,card_erase_of_mem g]
          have hj:= (show (k.erase j).Nonempty from ⟨l,u⟩).card_pos
          obtain ⟨i,f⟩:=p; rw [card_erase_of_mem g] at hj; exact ⟨i-1,by omega⟩
        unfold poke
        rw [← insert_erase g,Poly.tag_any _ _ _ (notMem_erase j k)]
        rw [show (cane n).tag _=parity l t • ((cane n).term l*poke t) from by
                nth_rw 1 [← insert_erase u]; exact Poly.tag_any _ _ _ (notMem_erase l (k.erase j)),
            Algebra.mul_smul_comm,←mul_assoc]
        apply scale; apply scale
        apply times (pair _ (hsub g) _ (hsub (mem_of_mem_erase u)))
        exact ih _ hx (mem_filter.mpr ⟨mem_powerset.mpr ((le_of_lt hx).trans hsub),hv⟩)
      rw [not_nonempty_iff_eq_empty.mp v,show poke ∅=(1:FC n) from Poly.tag_void _]
      exact single
  obtain ⟨f,rfl⟩ := h
  have p : ∀ t : Finset (Finset n), t ⊆ Wheat s → P (∑ a∈t, f a • poke a) := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
        intro _
        rw [sum_empty]
        simpa only [zero_smul] using scale single 0
    | insert j t k ih=>
        intro h
        rw [sum_insert k]
        exact plus (scale (z _ (h (mem_insert_self ..))) _) (ih ((subset_insert ..).trans h))
  exact p _ le_rfl


lemma shock_pair (E:Op n) (i j:n) :
    shock (dg E) (put i*put j) =
    (∑ k,E k i • (put k*put j)) + (∑ k,E k j • (put i*put k)) := by
  rw [shock_times,pulse_let,pulse_let,sum_mul,mul_sum]
  simp only [Algebra.smul_mul_assoc,Algebra.mul_smul_comm]

lemma shock_flour {t : Finset n} (hst : s⊆t) (E:Op n)
    (he : ∀ j∈s,∀ i, i∉t → E i j=0) {A:FC n} (h:Flour s A) :
    Flour t (shock (dg E) A) := by
  let P := fun B:FC n => Flour t B ∧ Flour t (shock (dg E) B)
  have e : P A := by
    refine flour_every P (s:=s) ?_ ?_ ?_ ?_ ?_ h
    · intro i u j v
      refine ⟨Flour.putPut t (hst u) (hst v),?_⟩
      rw [shock_pair]
      apply Flour.add
      · apply Flour.sum
        intro k _
        by_cases hk:k∈t
        · exact (Flour.putPut t hk (hst v)).smul _
        rw [he i u k hk,zero_smul]
        exact Flour.trivial
      apply Flour.sum
      intro k _
      by_cases hk:k∈t
      · exact (Flour.putPut t (hst u) hk).smul _
      rw [he j v k hk,zero_smul]
      exact Flour.trivial
    · intro x v y
      exact ⟨v.1.smul _, by rw [map_smul]; exact v.2.smul _⟩
    · intro x y v r
      exact ⟨v.1.add r.1, by rw [map_add]; exact v.2.add r.2⟩
    · intro x y v r
      exact ⟨v.1.mul r.1, by rw [shock_times]; exact (v.2.mul r.1).add (v.1.mul r.2)⟩
    exact ⟨Flour.grainE, by rw [shock_one]; exact Flour.trivial⟩
  exact e.2

def jolt (E:Op n) : Dough n →ₗ[ℝ] Dough n where
  toFun x := ⟨shock (dg E) x.val,
    shock_flour (s:=univ) (t:=univ) le_rfl E
      (fun _ _ i p => absurd (mem_univ i) p) (fineShape x)⟩
  map_add' x y := Subtype.ext (map_add _ _ _)
  map_smul' c x := Subtype.ext
    (show shock (dg E) (c • x.val) = c • _ from by
       simp only [show ∀ y:FC n, c • y = (c:ℂ) • y by
                    intro y; ext; simp [Complex.real_smul],map_smul])

lemma jolt_mul (E:Op n) (x y : Dough n) :
    jolt E (x*y)= jolt E x * y + x * jolt E y :=
  Subtype.ext (shock_times (dg E) ..)
lemma jolt_one (E:Op n) : jolt E 1 = 0 :=
  Subtype.ext (shock_one _)


lemma jolt_hollow (E:Op n) (x:ℂ) : jolt E (hollow x)=0 :=
  Subtype.ext
    (show shock (dg E) (x • (1:FC n)) = 0 from by rw [map_smul,shock_one,smul_zero])

lemma jolt_exp (E:Op n) (q:Dough n) : jolt E (exp q) = jolt E q * exp q := by
  let b := dg E
  let x := q.val
  let y := (jolt E q).val
  have e : (exp q).val = exp x := by
    letI : NormedAlgebra ℚ (Dough n):= NormedAlgebra.restrictScalars ℚ ℝ (Dough n)
    letI : NormedAlgebra ℚ (FC n):= NormedAlgebra.restrictScalars ℚ ℝ (FC n)
    exact map_exp (Dough n).val continuous_subtype_val q
  apply Subtype.ext
  change b*(exp q).val - (exp q).val*b = y * (exp q).val
  have z : x*b - b*x = -y := by
    change _ = -(b*x-x*b)
    rw [neg_sub]
  have r : x*(-y) = (-y)*x := by
    rw [mul_neg,neg_mul,show x*y=y*x from
      Flour.comm (fineShape q) (fineShape (jolt E q))]
  rw [e,calms x b _ z r,add_mul,neg_mul]
  abel

variable {m : Type*} [LinearOrder m] [Fintype m]
lemma readTimes (v : Poly n m) {x y : FC n} (w : Flour univ x) (u : Flour univ y) :
    v.eval (x*y) = v.eval x * v.eval y := v.eval_mul ⟨x,w⟩ ⟨y,u⟩


/-- Price with arbitrary read hom for which E lifts single substitutions. -/
lemma shock_lift (E:Op n) (Z:FC m) (v: Poly n m)
    (hv : ∀ i, shock Z (v.term i) = ∑ j,E j i • v.term j)
    (x : Dough n) : shock Z (v.cook x)=v.cook (jolt E x) := by
  let P := fun B:FC n => Flour univ B ∧ shock Z (v.eval B)=v.eval (shock (dg E) B)
  have e : P x.val := by
    refine flour_every P ?_ ?_ ?_ ?_ ?_ x.property
    · intro i u j w
      refine ⟨Flour.putPut _ u w,?_⟩
      rw [shock_pair,v.eval_double,shock_times,hv,hv]
      simp only [map_add,map_sum,map_smul,v.eval_double,sum_mul,mul_sum,
          Algebra.smul_mul_assoc,Algebra.mul_smul_comm]
    · intro X h b
      refine ⟨h.1.smul _,?_⟩
      simp only [map_smul,h.2]
    · intro X Y h w
      refine ⟨h.1.add w.1,?_⟩
      simp only [map_add,h.2,w.2]
    · intro X Y h w
      refine ⟨h.1.mul w.1,?_⟩
      have h1 : Flour univ (shock (dg E) X) :=
        fineShape (jolt E ⟨X,h.1⟩)
      have w1 : Flour univ (shock (dg E) Y) :=
        fineShape (jolt E ⟨Y,w.1⟩)
      rw [readTimes _ h.1 w.1, shock_times _ X, map_add,
          readTimes _ h1 w.1,readTimes _ h.1 w1,
          shock_times,h.2,w.2]

    refine ⟨Flour.grainE,?_⟩
    rw [v.eval_one,shock_one,shock_one,map_zero]
  exact e.2

