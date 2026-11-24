import YM.SU5.WakeInvestment.Bessel

/-!
After WA.11 high-mode tilt. Estimate local expectation, subtracting flat. The cost will still
exploit Bessel bounds on successively higher Saber orders. No recon Vergence assumption.
Peel off the first row instead of explicitly rewriting the whole polynomial to Wick normal order.
-/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.WakeInvestment
open Function Set Filter Fock Lattice Finset NormedSpace
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators ComplexOrder InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {I:Type*} [LinearOrder I] [Fintype I]
variable {A B Q:Op I} (x y:Wave I) {u v:ℝ}

-- Helpers for assembly of many-root estimates
noncomputable def grain : FC I →ₗ[ℂ] ℂ where
  toFun F:=inner ℂ x (acts F x)
  map_add' F Q:=by rw [act_add,inner_add_right]
  map_smul' c F:=by rw [act_smul,inner_smul_right]; rfl

lemma paid_normW (V:FC I)(x:Wave I): ‖acts V x‖≤ ‖V‖*‖x‖:=by
  nth_rw 1 [← Matrix.l2_opNorm_toEuclideanCLM V]; exact (acts V).le_opNorm _

lemma grain_cap (A : FC I) : ‖grain x A‖ ≤ ‖x‖^2*‖A‖ := by
  change ‖inner ℂ x _‖ ≤ _; apply (norm_inner_le_norm ..).trans; have R := paid_normW A x
  exact (mul_le_mul_of_nonneg_left R (norm_nonneg _)).trans_eq (by ring)

def discrepancy : FC I →ₗ[ℂ] ℂ := grain x - ((‖x‖^2:ℝ):ℂ) • (grain y)

lemma discrepancy_type (F:FC I) : discrepancy x y F= grain x F - ((‖x‖^2:ℝ):ℂ)*grain y F:=rfl

lemma discrepancy_nil (p : ‖y‖=1) : discrepancy x y 1=0 := by simp [discrepancy_type,grain,inner_self_eq_norm_sq_to_K,p]

lemma discrepancy_cap (p:‖y‖=1) (F:FC I) : ‖discrepancy x y F‖ ≤ 2*‖x‖^2*‖F‖ := by
  rw [discrepancy_type]; apply (norm_sub_le ..).trans; rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (sq_nonneg ‖x‖)]
  have h : ‖grain y F‖ ≤ ‖F‖:= by simpa [p] using grain_cap y F
  nlinarith only [grain_cap x F,mul_le_mul_of_nonneg_left h (sq_nonneg ‖x‖)]

abbrev Leg (I:Type*) [Fintype I] := Bool × Ket I

-- $\mathcal N$ book estimated by a *single* tolerance on this Root
private def safe (Q:Op I) (x:Wave I) (v u:ℝ) (y : Leg I) : Prop :=
  ‖y.2‖ ≤ v ∧ ‖acts (create (acts Q y.2)) x‖ ≤ u ∧ ‖acts (Fock.remove (acts (1-Q) y.2)) x‖ ≤ u

private lemma car_slot (i j:Leg I) : ∃ c:ℂ, antiB (Flare.ton i) (Flare.ton j) = c • 1 ∧ ‖c‖ ≤ ‖i.2‖ * ‖j.2‖:=by
  obtain ⟨b,p⟩:= i; obtain ⟨d,q⟩:=j; cases b <;> cases d
  · exact ⟨0,(car_create p q).trans (zero_smul ..).symm, (norm_zero (E:=ℂ)).trans_le (mul_nonneg (norm_nonneg p) (norm_nonneg q))⟩
  · exact ⟨_,(antiB_comm _ _).trans (car q p), (norm_inner_le_norm ..).trans_eq (mul_comm ..)⟩
  · exact ⟨_,car p q,norm_inner_le_norm ..⟩
  exact ⟨0,(car_rem p q).trans (zero_smul ..).symm, (norm_zero (E:=ℂ)).trans_le (mul_nonneg (norm_nonneg p) (norm_nonneg q))⟩

variable [Nonempty I]
lemma proj_cap (p:IsStarProjection Q) (x: Ket I): ‖acts Q x‖ ≤ ‖x‖:=
  (Flare.opy _ x).trans (mul_le_of_le_one_left (norm_nonneg _) (p.norm_le _))

private lemma part (p:IsStarProjection Q) (h:Sea Q y) (t:Leg I)(hz:safe Q x v u t) :
    ∃ L : Leg I, ∃ A : FC I, ‖L.2‖ ≤ v ∧ ‖acts (Flare.ton L) x‖ ≤ u ∧
      acts (Flare.ton L) y=0 ∧ ‖acts A x‖ ≤ u ∧ acts A y=0 ∧
      Flare.ton t=Flare.ton L+star A := by
  obtain ⟨b,t⟩:=t; let f:=acts Q t; let g:=acts (1-Q) t; let C:=create f; let A:=Fock.remove g
  have hf:acts C y=0:= tarp p h.1 (by unfold f; rw [←act_mul,p.isIdempotentElem.eq])
  have hg:acts A y=0:= tars p h.1 (by unfold g; rw [←act_mul,Porth p,act_zero])
  have hx:f+g=t:=by unfold g f; rw [act_sub,act_one]; abel
  cases b
  · refine ⟨(false,f),A, (proj_cap p _).trans hz.1,hz.2.1,hf,hz.2.2,hg,?_⟩; change create t=C+star A
    nth_rw 1 [←hx]; rw [map_add, star_star]
  refine ⟨(true,g),C,(proj_cap p.one_sub _).trans hz.1,hz.2.2,hg,hz.2.1,hf,?_⟩; change Fock.remove t=A+star C
  unfold Fock.remove; nth_rw 1 [←hx]; rw [map_add,star_add,add_comm]


abbrev loads (l:List (Leg I)) := (l.map Flare.ton).prod
omit [Nonempty I] in
lemma load_price (l:List (Leg I)) (v:ℝ) (u:1≤v) (p:∀ a∈l, ‖a.2‖≤v) (n:ℕ) (z:l.length≤n) : ‖loads l‖ ≤ v^n := by
  suffices h : ‖loads l‖≤ v^l.length from h.trans (pow_le_pow_right₀ u z)
  clear z; induction l with
  | nil => simp [loads]
  | cons i l ih =>
    let hv:0≤v:=zero_le_one.trans u
    rw [loads, List.map_cons,List.prod_cons,List.length_cons,pow_succ']; apply (norm_mul_le ..).trans
    exact mul_le_mul ((Flare.cost_pe ..).trans (p _ List.mem_cons_self)) (ih (fun a b=> p a (List.mem_cons_of_mem _ b))) (norm_nonneg _) hv

variable {w:ℝ}
omit [Nonempty I] in
lemma right_ann (A B:FC I) (h:acts B y=0) (v:‖acts B x‖≤u) (p:‖A‖≤w) :
    ‖discrepancy x y (A*B)‖ ≤ ‖x‖ * (w*u) := by
  simp only [discrepancy_type,grain,LinearMap.coe_mk,AddHom.coe_mk,act_mul,h,map_zero,inner_zero_right,mul_zero,sub_zero]
  apply (norm_inner_le_norm ..).trans; exact mul_le_mul_of_nonneg_left
    ((paid_normW ..).trans (mul_le_mul p v (norm_nonneg _) ((norm_nonneg _).trans p))) (norm_nonneg _)

omit [Nonempty I] in
lemma left_cred (A B:FC I) (h:acts A y=0) (v:‖acts A x‖≤u) (p:‖B‖≤w) :
    ‖discrepancy x y (star A*B)‖ ≤ ‖x‖ * (w*u) := by
  simp only [discrepancy_type,grain,LinearMap.coe_mk,AddHom.coe_mk,act_mul]
  rw [←act_inner,←act_inner (star A) y,star_star,h]; simp only [inner_zero_left,mul_zero,sub_zero]
  apply (norm_inner_le_norm ..).trans; exact (mul_le_mul v ((paid_normW ..).trans (mul_le_mul_of_nonneg_right p (norm_nonneg _)))
    (norm_nonneg _) ((norm_nonneg _).trans v)).trans_eq (by ring)

variable (Q : Op I)
local notation "Φ" => discrepancy x y
set_option quotPrecheck false
local notation "aX" x:max a:max b:max => ∀ (i:Leg I), i∈b → safe Q x v a i

def wordToll (v:ℝ) : ℕ → ℝ
| 0 => 0
| n+1 => 2*v^n + n*v^2*wordToll v n

lemma prance (h:0≤v) (n:ℕ) : 0≤ wordToll v n := by
  induction n with
  | zero=> exact le_rfl
  | succ n ih=>rw [wordToll]; positivity

omit [Nonempty I] in
private lemma throughOne {k:ℕ}(b:Leg I) (p:‖b.2‖≤v)(u₀:1≤ v)(_:0≤u)
    (e:acts (Flare.ton b) y=0) (hy:‖acts (Flare.ton b) x‖ ≤ u)
    (t:∀ (l:List (Leg I)), l.length ≤ k → (aX x u l) → ‖Φ (loads l)‖≤ ‖x‖ * u * wordToll v k)
    (J L:List (Leg I)) (sJ:aX x u J) (sL:aX x u L) (z:J.length+L.length ≤ k) :
    ‖Φ (loads J * Flare.ton b * loads L)‖ ≤ ‖x‖* u * (v^k + L.length * v^2 *wordToll v k) := by
  have nv:0 ≤ v:= zero_le_one.trans u₀
  induction L generalizing J with
  | nil =>
    simpa [loads, mul_assoc, mul_comm u] using right_ann x y (loads J) (Flare.ton b) e hy (load_price J v u₀ (fun i h=>(sJ i h).1) k (by simpa using z)) -- assoc tune
  | cons m L ih=>
    obtain ⟨c,hf,he⟩:= car_slot b m; have h:J.length+L.length<k:=by rw [List.length_cons] at z; omega
    have hx := t (J ++ L) (by simpa using h.le) (fun i g=> (List.mem_append.mp g).elim (sJ i) (fun h=> sL i (List.mem_cons_of_mem _ h)))
    have hp := ih (J++[m]) (fun i g=> (List.mem_append.mp g).elim (sJ i) (fun h=> sL i (by simp_all))) (fun i g=> sL i (List.mem_cons_of_mem _ g)) (by simp; omega) -- simp
    change ‖Φ (loads J * Flare.ton b * (Flare.ton m*loads L))‖≤ _
    rw [show loads J * Flare.ton b * (Flare.ton m*loads L)= c • loads (J++L) - loads (J++[m])*Flare.ton b*loads L from ?_]; swap
    · rw [mul_assoc,←mul_assoc (Flare.ton b)]; rw [show Flare.ton b * Flare.ton m=c • 1 - Flare.ton m * Flare.ton b from eq_sub_of_add_eq hf]; unfold loads; simp only [List.map_append,List.prod_append,List.map_cons,List.prod_cons,List.map_nil,List.prod_nil,mul_one]; rw [sub_mul,mul_sub,Algebra.smul_mul_assoc,Algebra.mul_smul_comm,one_mul]; simp only [mul_assoc]
    rw [map_sub,map_smul]; apply (norm_sub_le ..).trans; rw [norm_smul]
    have hc := he.trans (mul_le_mul p ((sL m List.mem_cons_self).1) (norm_nonneg _) nv); apply le_trans (add_le_add (mul_le_mul hc hx (norm_nonneg _) (mul_nonneg nv nv)) hp)
    rw [List.length_cons]; push_cast; exact le_of_eq (by ring)

private lemma seedOne {k:ℕ} (q:IsStarProjection Q)(p:Sea Q y)(u₀:1≤ v)(v₀:0≤u) (L:List (Leg I)) (w:L.length≤k) (t:aX x u L) :
    ‖Φ (loads L)‖≤ ‖x‖ * u * wordToll v k := by
  induction k generalizing L with
  | zero=> cases L; · rw [show loads ([]:List (Leg I))=1 from rfl,discrepancy_nil x y p.2,norm_zero]; apply mul_nonneg (mul_nonneg (norm_nonneg x) v₀) (prance (zero_le_one.trans u₀) _)
           simp at w
  | succ n ih=>
    have hx:0≤‖x‖*u:=mul_nonneg (norm_nonneg x) v₀
    cases L with
    | nil=>rw [show loads ([]:List (Leg I))=1 from rfl,discrepancy_nil x y p.2,norm_zero]; exact mul_nonneg hx (prance (zero_le_one.trans u₀) _)
    | cons i L =>
      rw [List.length_cons] at w; have hw:= Nat.le_of_succ_le_succ w; have hl:aX x u L:=fun i h=>t i (List.mem_cons_of_mem _ h)
      obtain ⟨b,C,h₁,h₂,h₃,h₄,h₅,h⟩:=part x y q p i (t i List.mem_cons_self)
      have he:=left_cred x y C (loads L) h₅ h₄ (load_price L v u₀ (fun i h=> (hl _ h).1) _ hw)
      have ht: ‖Φ (Flare.ton b * loads L)‖ ≤ ‖x‖* u * (v^n + L.length * v^2 *wordToll v n):=by
        simpa only [loads,List.map_nil,List.prod_nil,List.length_nil,one_mul] using throughOne x y Q b h₁ u₀ v₀ h₃ h₂ ih [] L (by simp) hl (by simpa)
      change ‖Φ (Flare.ton i * loads L)‖≤_
      rw [h,add_mul,map_add]; refine (norm_add_le ..).trans ((add_le_add ht he).trans ?_)
      rw [wordToll]
      have hh: (L.length:ℝ) ≤ n:= by exact_mod_cast hw
      nlinarith only [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh (sq_nonneg v)) (prance (zero_le_one.trans u₀) n)) hx]

theorem probe_diff (q:IsStarProjection Q)(p:Sea Q y) (t:ℕ) (v u:ℝ) (u₀:1≤ v) (v₀:0≤u) (l:List (Leg I))(hl:l.length≤t)
    (price:∀ i∈l, ‖i.2‖ ≤ v)(food:∀ i ∈ l,‖acts (create (acts Q i.2)) x‖≤u ∧ ‖acts (Fock.remove (acts (1-Q) i.2)) x‖ ≤ u) :
    ‖discrepancy x y (loads l)‖ ≤ ‖x‖ * u * wordToll v t := seedOne x y Q q p u₀ v₀ l hl (fun i p=>⟨price i p, food i p⟩)
#print axioms probe_diff
end YM.CF.WakeInvestment
