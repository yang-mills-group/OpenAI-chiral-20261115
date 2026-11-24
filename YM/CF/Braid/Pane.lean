/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.CF.Braid.Vac
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Braid
open Function Lattice RG Exterior Bloch Laurent Filter Finset Asymptotics Stationary
open Matrix (transpose mulVec of)
open scoped Matrix Topology ContDiff BigOperators
open Work.F06
variable {α ξ:Type}[Fintype α][DecidableEq α][Fintype ξ] {σ τ A C : ℝ}{M N r t:ℕ}
def mate(n M:ℕ):ℝ:= (4*(M:ℝ))^n
lemma mate_pos(n M:ℕ):0 ≤ mate n M:= by unfold mate; positivity
variable{n:ℕ}
def decaym (m : Keys (n+1) ↪ α) : Keys n ↪ α where
    toFun p := m (p.1.succ,p.2)
    inj' p q h := by have hh := m.injective h; simpa only [Prod.mk.injEq, Fin.succ_inj,Prod.ext_iff] using hh

omit [Fintype α] [DecidableEq α] in
private lemma decayms (m : Keys (t+1) ↪ α) : Uniforms _ _ ((stick t).trans m)
    (fun p : Corn α => locus (decaym m) (axes p)) := by
  intro p q H
  have he (i : Fin t) : strands (decaym m) (axes p) i=strands (decaym m) (axes q) i := by
    funext a
    change (p (m (i.succ,a)):ℂ) = ((q (m (i.succ,a)):ℝ):ℂ); congr 1
    apply H
    rintro ⟨b,hb⟩; have hi : (0,b)=(i.succ,a) := m.injective hb; exact (Fin.succ_ne_zero i) (congr_arg Prod.fst hi).symm
  ext w
  change (∀ i (b : Run t), ∑ j : TypeFace 1, symbol 0 (strands _ (axes p) i) j vac * w (update b i j)=0) ↔
    ∀ i (b : Run t), ∑ j : TypeFace 1, symbol 0 (strands _ (axes q) i) j vac * w (update b i j)=0
  simp_rw [he]

lemma solo (t M:ℕ) (m : Keys t ↪ α) :
    ∀ (A : ℝ) (s : ℕ) (f : Run t → Phase α → ℂ), 0 ≤ A →
        (∀ i, Pond M A (f i)) → (∀ i, Rays s (f i ∘ axes)) →
        (∀ p : Corn α,(fun i => f i (axes p))∈locus m (axes p)) →
        ∃ g : CurRun t → Phase α → ℂ, (∀ i, Pond M (A*mate t M) (g i)) ∧ (∀ i, Rays (s-t) (g i ∘ axes)) ∧
          ∀ p : Corn α,(fromCurl (strands m (axes p)) (fun i => g i (axes p)))=fun i => f i (axes p) := by
  induction t with
  | zero =>
    intro A s f ha hf hw he
    refine ⟨fun _ => f default,fun _ => by unfold mate; rw [pow_zero,mul_one]; exact hf _,fun _ => hw _,fun p => funext fun i => ?_⟩
    simp [fromCurl,show i=default from Subsingleton.elim ..]
  | succ t ih =>
    have H := ih (decaym m)
    intro A s f ha hf hj h
    let F (p : Phase α) (a : TypeFace 1) (x : Run t) := f (Fin.cons a x) p
    let i := (stick t).trans m
    have hx : Cycles (projected i) 1 F := by
      intro p
      funext b x; rw [vac_only b]
      have he : ∑ y : TypeFace 1, symbol 0 (strands _ (axes p) 0) y vac * f (update (Fin.cons (coord 0) x) 0 y) (axes p)=0 := h p 0 _
      simp only [Fin.update_cons_zero] at he; exact he
    have hw : wall (fun p => locus (decaym m) (axes p)) F := by
      intro p a j b
      have he : ∑ y : TypeFace 1, symbol 0 (strands m (axes p) j.succ) y vac * f (update (Fin.cons a b) j.succ y) (axes p)=0 := h p _ _
      simp_rw [← Fin.cons_update] at he
      exact he
    obtain ⟨G,hG,Gh,hV,Gp⟩ := wall_pull i ha F (fun i j => hf _) hx (Or.inl (by norm_num))
      (fun i j => hj _) (decayms m) hw
    choose U hU HJ he using fun a => H (A*(4*(M:ℝ))) (s-1) (fun b p => G p a b) (mul_nonneg ha (by positivity))
      (hG a) (Gh a) (fun p => hV p a)
    let g (b : CurRun (t+1)) : Phase α → ℂ := U (b 0) (Fin.tail b)
    refine ⟨g,fun i => ?_,fun i => ?_,fun p => funext fun b => ?_⟩
    · rw [mate,pow_succ',← mul_assoc]; exact hU _ _
    · rw [show s-(t+1)=s-1-t by omega]; exact HJ _ _
    rw [fromCurl_cons]; simp only [g,Fin.tail_cons,Fin.cons_zero]
    rw [show Fin.tail (strands m (axes p))=strands (decaym m) (axes p) from rfl]; simp_rw [he]
    change cob 1 (projected i) G (axes p) (b 0) (Fin.tail b)=_
    rw [← Gp]; simp [F, Fin.cons_self_tail]
abbrev cardR(v:Axis→ℝ)(p:Space t): Fin (t+1)→ Momentum:=Fin.cons (twist (axes v) p) (fun i=>projected (strand i) p)
abbrev ShiftsP(v:Axis→ℝ)(f:Run (t+1)→ Space t→ℂ):Prop:= ∀ p:Corn (Keys t),∀ i b,∑ j:TypeFace 1,symbol 0 (cardR v (axes p) i) j vac*f (update b i j) (axes p)=0
def liftL(t M:ℕ):=paneR t 0 M
lemma triangleL(v:Axis→ℝ)(t M:ℕ)(C:ℝ)(hC:0 ≤ C)(p:1+2*t>4∨∃ i:Axis, q (axes v) i≠0 ∧ ‖(q (axes v) i)⁻¹‖ ≤ C)(A:ℝ)(f: Run (t+1)→Space t→ℂ)(ha:0≤ A)(hf:∀ i,Pond M A (f i))(h:ShiftsP v f):∃ F:CurRun (t+1)→Space t→ℂ,(∀ i,Pond (liftL t M) (A*(palmJ C t 0 M*mate t (liftL t M))) (F i)) ∧ ∀ (p:Corn (Keys t)) b,fromCurl (cardR v (axes p)) (fun i=> F i (axes p)) b=f b (axes p):=by
 let P:=palmJ C t 0 M
 have hp: Cycles (twist (axes v)) 1 (clauses f) ∧ wall locus0 (clauses f):=by
    constructor
    · intro p; funext i b; have he := h p 0 (Fin.cons (coord 0) b); simp only [Fin.update_cons_zero] at he; rw [vac_only i]; exact he
    intro p a i b; have he:=h p i.succ (Fin.cons a b); simp_rw [← Fin.cons_update] at he; simp only [cardR,Fin.cons_succ] at he; exact he
 obtain ⟨V,hV,hW,H⟩:=vacL v t 0 M hC p (clauses f) ha (fun i b=>hf _) hp.1 hp.2
 choose W hw hh hw' using fun i=>solo t (liftL t M) (Embedding.refl (Keys t)) (A*P) 0 (fun b p=>V p i b) (mul_nonneg ha (palm_pos C hC ..)) (hV i) (fun b=>rays_zero ((hV i b).analytic.analytic_real _)) (fun p=>hW p i)
 refine ⟨fun b=> W (b 0) (Fin.tail b), fun i=>?_,fun p b=> ?_⟩
 · rw [← mul_assoc]; exact hw _ _
 rw [fromCurl_cons]; simp only [Fin.cons_zero, Fin.tail_cons,cardR]
 rw [show (fun i=>projected (strand i) (axes p))=strands (Embedding.refl (Keys t)) (axes p) from rfl]; simp_rw [hw']; change cob 1 (twist (axes v)) V (axes p) _ _ = _; rw [←H]; simp [clauses]
end YM.CF.Braid
