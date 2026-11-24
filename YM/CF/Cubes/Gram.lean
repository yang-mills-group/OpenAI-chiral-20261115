import YM.CF.Cubes.Candidate
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-! Quantitative incremental independence of short flags. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Cube
open Lattice Lat SU
open scoped InnerProductSpace BigOperators
-- floor at margin for continuity globally on label space
def baluster (e n:ℝ):ℝ:= n^2 + expNegInvGlue (e^2-n^2)
lemma baluster_pos {e:ℝ}(h:0<e) (n:ℝ): 0<baluster e n:= by
  unfold baluster; by_cases hg:n^2=0; rw [hg,sub_zero,zero_add]; exact expNegInvGlue.pos_of_pos (sq_pos_of_pos h)
  exact add_pos_of_pos_of_nonneg (lt_of_le_of_ne (sq_nonneg _) (Ne.symm hg)) (expNegInvGlue.nonneg _)
lemma baluster_at {e n:ℝ}(h:0<e)(g:e≤n):baluster e n=n^2:=by rw [baluster,expNegInvGlue.zero_of_nonpos (show e^2-n^2≤0 from by nlinarith),add_zero]
def shave (e : ℝ) (y z : Vect) := z - (inner ℝ y z / baluster e ‖y‖) • y
def restrain (e : ℝ) : List Vect → Vect → Vect
  | [], z => z
  | y::l,z => shave e (restrain e l y) (restrain e l z)
lemma shave_cont (e : ℝ) (h : 0 < e) : Continuous (fun t : Vect×Vect => shave e t.1 t.2) := by
  have hu : Continuous (baluster e) :=by unfold baluster; exact (continuous_id.pow 2).add ((expNegInvGlue.contDiff (n:=0)).continuous.comp (continuous_const.sub (continuous_id.pow 2)))
  let F (t: Vect×Vect):=inner ℝ t.1 t.2
  let G (t:Vect×Vect):=baluster e ‖t.1‖
  have hf: Continuous F:=Continuous.inner continuous_fst continuous_snd
  have hg: Continuous G:=Continuous.comp hu continuous_fst.norm
  have hQ:= hf.div hg (show ∀ t:Vect×Vect, G t≠0 from fun t=>(baluster_pos h _).ne')
  exact continuous_snd.sub (hQ.smul (continuous_fst (X:=Vect)))
lemma strain_cont {I X : Type*} [TopologicalSpace X] (e : ℝ) (h : 0 < e) (l : List I)
    (f : I→X→Vect) (g : ∀ i∈l, Continuous (f i)) (p : X→Vect) (c : Continuous p) : Continuous (fun x => restrain e (l.map (fun i=>f i x)) (p x)) := by
  induction l generalizing p with
  | nil => exact c
  | cons y l ih =>
    have he i (h:i∈l) := g i (List.mem_cons_of_mem _ h)
    exact (shave_cont e h).comp ((ih he (f y) (g y (by simp))).prodMk (ih he p c))
lemma strain_inner (e) (l : List Vect) (w v : Vect) (h : ∀ x∈l, inner ℝ w x=0) : inner ℝ w (restrain e l v)=inner ℝ w v := by
  induction l generalizing v with
  | nil => rfl
  | cons y l ih =>
    have he x (k:x∈l) := h x (List.mem_cons_of_mem y k)
    rw [restrain,shave,inner_sub_right,real_inner_smul_right,ih _ he,ih _ he,h y (by simp),mul_zero,sub_zero]
lemma strain_margin (e) (l : List Vect) (w : Ballot) (v : Vect) (h : ∀ x∈l, inner ℝ w.val x=0) : |inner ℝ v w.val|≤ ‖restrain e l v‖ := by
  rw [real_inner_comm,←strain_inner e l w.val v h]
  exact (abs_real_inner_le_norm ..).trans (by rw [vote_unit,one_mul])
lemma shave_self (e) (h : 0<e) (y : Vect) (he : e ≤ ‖y‖) : shave e y y=0 := by rw [shave,baluster_at h he,real_inner_self_eq_norm_sq,div_self (pow_ne_zero _ (h.trans_le he).ne'),one_smul,sub_self]
lemma shave_norm (e) (h : 0<e) (y z : Vect) (he : e ≤ ‖y‖) : ‖shave e y z‖≤ ‖z‖ := by
  have ho := h.trans_le he
  let c := inner ℝ y z / ‖y‖^2
  have hy : c*‖y‖^2=inner ℝ y z := div_mul_cancel₀ _ (pow_ne_zero _ ho.ne')
  rw [shave,baluster_at h he]; change ‖z-c • y‖≤ ‖z‖
  rw [←sq_le_sq₀ (norm_nonneg _) (norm_nonneg _),norm_sub_sq_real,real_inner_smul_right,norm_smul,
    real_inner_comm y,mul_pow,Real.norm_eq_abs,sq_abs,←hy]
  nlinarith [sq_nonneg (c*‖y‖)]
lemma strain_add (e) (l : List Vect) (u v : Vect) : restrain e l (u+v)=restrain e l u+restrain e l v := by
  induction l with
  | nil => rfl
  | cons y l ih => simp only [restrain,ih,shave, inner_add_right,add_div,add_smul]; abel
lemma strain_mul (e) (l : List Vect) (v : Vect) (c : ℝ) : restrain e l (c • v)=c • restrain e l v := by
  induction l with
  | nil => rfl
  | cons y l ih => simp only [restrain,ih,shave, real_inner_smul_right, smul_sub,smul_smul, mul_div_assoc]
lemma strain_turn (e) (l : List Vect) (g : E) (v : Vect) : restrain e (l.map (turn g)) (turn g v)=turn g (restrain e l v) := by
  induction l generalizing v with
  | nil => rfl
  | cons y l ih => simp only [restrain,List.map_cons, ih,shave,turn_norm,spinV_i,turn_sub,turn_mul]
/-- Robust independence. -/
def Thick (e : ℝ) : List Vect → Prop
  | [] => True
  | w::l => e < ‖restrain e l w‖ ∧ Thick e l
lemma Thick.step {y : Vect} {l : List Vect} {e : ℝ} (h : Thick e (y::l)) : Thick e l := h.2
lemma thick_turn_iff (e : ℝ) (l : List Vect) (g : E) : Thick e (l.map (turn g))↔ Thick e l := by
  induction l with
  | nil => simp
  | cons i l ih => rw [List.map_cons,Thick,Thick,ih,strain_turn,turn_norm]
lemma Thick.norm {l : List Vect} {e : ℝ} (h : Thick e l) (g : 0<e) (x : Vect) : ‖restrain e l x‖≤ ‖x‖ := by
  induction l with
  | nil => exact le_rfl
  | cons y l ih => exact (shave_norm _ g _ _ (le_of_lt h.1)).trans (ih h.2)
lemma Thick.null {l : List Vect} {e : ℝ} (h : Thick e l) (g : 0<e) (x : Vect) (ht : x∈l) : restrain e l x=0 := by
  induction l with
  | nil => simp at ht
  | cons y l ih => rcases List.mem_cons.mp ht with rfl|ht; exact shave_self _ g _ (le_of_lt h.1); rw [restrain, ih h.2 ht]; simp [shave]

section
variable {I : Type*}
def combo (l : List I) (f : I → Vect) (t : I → ℝ) := (l.map (fun i=> t i • f i)).sum
lemma thick_null (l : List I) (f : I → Vect) (t : I → ℝ) (K : List Vect) (e : ℝ) (h : Thick e K) (g : 0<e) (he : ∀ i∈l, f i∈K) :
    restrain e K (combo l f t)=0 := by
  induction l with
  | nil => exact ((norm_le_zero_iff).mp (by simpa [combo] using h.norm g (0:Vect))) -- tune
  | cons i l ih => rw [show combo (i::l) f t=t i • f i+combo l f t from by simp [combo],strain_add,strain_mul,h.null g _ (he i (by simp)),ih (fun i' hi=>he _ (List.mem_cons_of_mem _ hi)),smul_zero,zero_add]
/-- ℓ1 estimate for nonnegative coefficients. -/
def magC (e : ℝ) : ℕ → ℝ
  | 0 => 1
  | n+1 => e⁻¹+magC e n*(1+e⁻¹)
lemma magC_pos (e : ℝ) (g : 0<e) (n : ℕ) : 0 < magC e n := by induction n with | zero => exact one_pos | succ n ih => rw [magC]; positivity
lemma magC_inc (e : ℝ) (g : 0<e) : Monotone (magC e) := by
  apply monotone_nat_of_le_succ; intro n; have h := magC_pos e g n; have ht := inv_pos_of_pos g; rw [magC]; nlinarith
lemma combo_guard (l : List I) (f : I → Vect) (t : I → ℝ) (e : ℝ) (g : 0 < e) (h : Thick e (l.map f))
    (ht : ∀ i ∈ l, 0 ≤ t i) (hv : ∀ i ∈ l, ‖f i‖=1) : (l.map t).sum ≤ magC e l.length * ‖combo l f t‖ := by
  induction l with
  | nil => simp [combo]
  | cons i l ih =>
    let P := combo (i::l) f t; let Q := combo l f t
    have hc : P=t i • f i+Q := by simp [P,Q,combo]
    change Thick e (f i :: l.map f) at h
    have h₁ := ht i (by simp); have h₂ := hv i (by simp)
    have he := h.step.norm g P
    rw [hc,strain_add,strain_mul,show restrain e (l.map f) Q=0 from thick_null l f t _ e h.2 g (fun _ H=>List.mem_map_of_mem H),add_zero,norm_smul, ← hc, Real.norm_of_nonneg h₁] at he
    have hk : t i ≤ e⁻¹*‖P‖ := by rw [mul_comm,←div_eq_mul_inv,le_div_iff₀ g]; exact (mul_le_mul_of_nonneg_left (le_of_lt h.1) h₁).trans he
    have hg : ‖Q‖≤(1+e⁻¹)*‖P‖ := by
      calc ‖Q‖ = ‖P-t i • f i‖ := by rw [hc,add_sub_cancel_left]
           _ ≤ ‖P‖+‖t i • f i‖ := norm_sub_le ..
           _ ≤ _ := by rw [norm_smul,h₂,mul_one,Real.norm_of_nonneg h₁]; linarith
    have h' := ih h.step (fun j hj=> ht j (List.mem_cons_of_mem _ hj)) (fun j hj=> hv j (List.mem_cons_of_mem _ hj))
    have hp := (add_le_add hk (h'.trans (mul_le_mul_of_nonneg_left hg (magC_pos e g _).le)))
    calc (List.map t (i::l)).sum = t i+(List.map t l).sum := by simp
         _ ≤ _ := hp
         _ = _ := by simp [P,magC]; ring
end
end YM.CF.Cube
