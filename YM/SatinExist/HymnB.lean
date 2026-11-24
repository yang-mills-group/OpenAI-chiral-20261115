import YM.SatinExist.Iambic
import YM.SU5.Aria.Screens
/-!
 # In the chosen gaps. Hearing the EU & polynomials in the actual order.
-/
set_option autoImplicit false
set_option maxRecDepth 2400
set_option maxHeartbeats 350000
noncomputable section
namespace YM.SatinJets
open Function Filter Metric InnerProductSpace Set Complex MeasureTheory Measure
open Analysis Boundary Spectral OS OS.Semigroup
open CF.Buffered.Afterglow.Hierarchy.Seld Poin LineDeriv
open scoped NNReal ENNReal Topology BigOperators InnerProductSpace ComplexOrder Classical
open CF.Buffered.Afterglow.Tower.Aria
variable {H : Hilbert}{j:Axis} (S : OS.Semigroup H j)
local notation "Λ" => 𝓝[>] (0:ℝ)
local notation "E" => elast S
local notation "D" => Bench S
local notation "K" => Cache S
local notation "R" => saucer S
local notation "T" => M S
local notation "τ" m:max t:max=> Par S m (Real.toNNReal t)
variable (Ω:H)(w:∀ x, M S x Ω=Ω) {n:ℕ}(p:E4)
variable (F:Fin n→H.Op)(r:Fin n→ℕ)(y:Fin n→E4)(z u v:Fin n→ℝ)
-- can sym directly in fields' holog orientation. Fine intervals may use $d> z_{n-1}$ ANY. Starts after prev.
def rebate (z u v:Fin n→ℝ)(p:Fin n):H.Op:= let t:=u p; let s:=v p; T (y p)*τ (r p) (z p-t)*F p*τ (r p) (s-z p)*T (-y p)
def GateK : ∀ {n:ℕ}, (Fin n→ℝ) → (Fin n→ℝ) → (Fin n→ℝ) → ℝ → Prop
 | 0,_,_,_,_=>True
 | n+1,z,u,v,b => u 0=b ∧ b < z 0 ∧ z 0 < v 0 ∧ GateK (Fin.tail z) (Fin.tail u) (Fin.tail v) (v 0)
def StepsW : ∀ {n:ℕ}, (Fin n→ℝ) → ℝ → Prop
 | 0,_,_=>True
 | n+1,z,s=>s<z 0 ∧ StepsW (Fin.tail z) (z 0)
def momentsE : ∀ {n:ℕ}, (Fin n→ℝ) → ℝ → Fin n→ ℝ≥0
 | 0,_,_=> Fin.elim0
 | n+1,z,p=> Fin.cons ((z 0-p).toNNReal) (momentsE (Fin.tail z) (z 0))
lemma points_offer (p:ℝ)(q:StepsW z p): ∃ p'> p,StepsW z p':=by cases n with
 | zero=> exact ⟨p+1, by linarith,trivial⟩
 | succ n=> obtain ⟨t,e⟩:=q; obtain ⟨b,u,v⟩:= exists_between t; exact ⟨b,u,v,e⟩ -- Gate requires v0>s\n
lemma heirs (p:ℝ)(q:StepsW z p): ∃ u v:Fin n→ℝ, GateK z u v p:=by
 induction n generalizing p with
 | zero=> exact ⟨0,0,trivial⟩
 | succ n ih=>
    obtain ⟨t,e⟩:= q; obtain ⟨d,v,h⟩:=points_offer _ _ e; obtain ⟨l,a,b⟩:= ih (Fin.tail z) d h; let X:Fin (n+1)→ℝ:=Fin.cons p l; let Y:Fin (n+1)→ℝ:=Fin.cons d a
    exact ⟨X,Y,rfl,t,v,b⟩
lemma Stair_gate (b:ℝ) : StepsW z b ↔ ∀ i,0 < momentsE z b i:=by
 induction n generalizing b with
 | zero=> exact ⟨fun _ i=>Fin.elim0 i,fun _=>trivial⟩
 | succ n ih=> constructor
               · rintro ⟨p,h⟩ i; exact Fin.cases (Real.toNNReal_pos.mpr (sub_pos.mpr p)) (ih _ _|>.mp h) i -- type motive
               intro p; exact ⟨sub_pos.mp (Real.toNNReal_pos.mp (p 0)),(ih _ _).mpr fun i=> p i.succ⟩ -- indentation
include w
lemma parΩ (m:ℕ)(t:ℝ)(h:0<t): (τ m t) Ω = Ω:=by
 let u:= t.toNNReal; have hp:0<u:=Real.toNNReal_pos.mpr h; apply cache_I S m; rw [keepO S Ω (rlock S Ω w) m]; exact (DFunLike.congr_fun (P_Heq S u m hp) Ω).trans (earthO S Ω _ (rlock S Ω w)) -- binder order
variable (a b:ℝ)
lemma galaK (a b:ℝ) (d:GateK z u v b)(t:a < b)(m:ℕ):
  regiaN S Ω n (slew S (pedestal m r) (momentsE z a)) F p y=T (-p) ((τ m (b-a)) ((List.ofFn (rebate S F r y z u v)).prod Ω)):=by
 induction n generalizing p a b m with
 | zero=> rw [List.ofFn_zero,List.prod_nil,regiaN]; exact (show Ω= _ from ((congrArg (T (-p)) (parΩ S Ω w m (b-a) (sub_pos.mpr t))).trans (w (-p))).symm)
 | succ n ih=>
    obtain ⟨c',p',q,d⟩:=d; let H':= Fin.tail F; let Y':= Fin.tail y; let u':= Fin.tail u; let v':= Fin.tail v; let r':= Fin.tail r; let Z:= Fin.tail z; let k:=z 0; let K':= r 0; let τ':= v 0; let x:= y 0
    let Q:= T x; let E':= (List.ofFn (rebate S H' r' Y' Z u' v')).prod Ω
    let ht:= ih x H' r' Y' Z u' v' k τ' d q K'; rw [List.ofFn_succ, List.prod_cons,regiaN]; change T (x-p) ((τ (m+K') (k-a)) (F 0 (regiaN S Ω n (slew S (pedestal K' r') (momentsE Z k)) H' x Y')))= T (-p) ( (τ m (b-a)) (rebate S F r y z u v 0 E'))
    rw [ht]; unfold rebate; simp only [c']; refine DFunLike.congr_fun (?_ : T (x-p) * τ (m+K') (k-a)*F 0*(T (-x)*τ K' (τ'-k)) = T (-p)* (τ m (b-a) * (T x*τ K' (k-b)* F 0 *τ K' (τ'-k)*T (-x)))) E'
    rw [show x-p= -p+x from by abel, ← tgo, ← show τ m (b-a)*τ K' (k-b)=τ (m+K') (k-a) from (Eq.trans (part_par S m K' _ _ (sub_pos.mpr t) (sub_pos.mpr p')) (by rw [show b-a+(k-b)= k-a from by abel]))]; -- commute
    have he: Commute (T x) (τ m (b-a)):= (mslot S x (OS.Semigroup.duration ((b-a).toNNReal)) (dur.mpr (Real.toNNReal_pos.mpr (sub_pos.mpr t))) m).symm
    have hx: Commute (T (-x)) (τ K' (τ'-k)):= (mslot S _ _ (dur.mpr (Real.toNNReal_pos.mpr (sub_pos.mpr q))) K').symm
    simp only [mul_assoc]; rw [← mul_assoc (T x),he.eq,hx.eq,mul_assoc]
lemma msumK (a b:ℝ)(d:GateK z u v b)(t:a < b) (i: Fin n): u i < z i ∧ z i < v i:=by
 induction n generalizing b with
 | zero=> exact Fin.elim0 i
 | succ n ih=> obtain ⟨p,w,z',d⟩:=d; refine Fin.cases ?_ (ih _ _ _ _ d ((t.trans w).trans z')) i; rw [p]; exact ⟨w,z'⟩
omit w in
lemma adjacency (a b:ℝ)(d:GateK z u v b): ∀ i j: Fin n,∀ L W:List (Fin n), Each n=L++i::j::W → v i=u j:=by
 induction n generalizing b with
 | zero=>intro i _ _ _ _; exact Fin.elim0 i
 | succ n ih=>
   obtain ⟨e,w,vp,d⟩:=d; intro i j' L' W h; unfold Each at h; rw [List.finRange_succ] at h
   cases L' with
   | nil=> simp only [List.nil_append, List.cons.injEq] at h; rcases h with ⟨rfl,H⟩; cases n with
       | zero=> simp at H
       | succ n=> rw [List.finRange_succ,List.map_cons] at H; exact (List.cons.inj H).1 ▸ (show _= _ from d.1.symm)
   | cons g L' =>
       have he:= (List.cons.inj h).2
       obtain ⟨l,L,hT,h₁,h₂⟩:=List.map_eq_append_iff.mp he -- tune equation
       obtain ⟨i',t,r₁,rfl,z'⟩:=List.map_eq_cons_iff.mp h₂
       obtain ⟨k,L₁,qK,rfl,zF⟩:=List.map_eq_cons_iff.mp z'
       apply ih _ _ _ _ d i' k l L₁; rw [r₁,qK] at hT; exact hT
end YM.SatinJets
