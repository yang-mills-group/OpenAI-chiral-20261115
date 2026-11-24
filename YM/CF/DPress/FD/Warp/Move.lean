import YM.CF.DPress.FD.Geo.Promise
import YM.CF.DPress.FD.Tile.CSP
import YM.CF.Skye.Zap
/-! Local construction and symmetry.

 Sweep of a seed has precisely the componentwise law used in mend. This will also let
 us rotate prior simplex/frame values (and still reason locally about their support
 queries in both systems) without imposing symmetry on any of the Borel extension methods.
 -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.DPress.FD
open Function Filter Lattice Cash Bifold Deck Hue Geo Warm Frame Ramp Spire Skye SU Cube Lat
open scoped Topology BigOperators ENNReal NNReal Classical ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {I J:Type*}{n:Side}{X Y K:Type*}{r m:ℕ}
structure Tw(N:Side)(I:Type*) where
 mv : Sweep N→ I→ I
 one : mv 1=id
 pair(a b) x : mv a (mv b x)=mv (b*a) x
namespace Tw
variable (P: Tw n X)(Q: Tw n Y)
lemma idP(x:X):P.mv 1 x=x:=congrFun P.one _
lemma vert (i:Sweep n)(x:X):P.mv i⁻¹ (P.mv i x)=x:=by rw [P.pair,mul_inv_cancel,idP]
def e (i:Sweep n) : Equiv.Perm X:=⟨P.mv i,P.mv i⁻¹,P.vert i,fun x=> by rw [P.pair,inv_mul_cancel,idP]⟩
abbrev pane (N:Side): Tw N (Pane N):=⟨flashA,funext rev1,fun a b x=> lights b a x⟩
lemma boxV : boxA (1:Sweep n)=Equiv.refl _:=by apply Equiv.ext; intro x; rw [sitA]; change affine 1 ((assembly n).root 0) x=x; rw [map_zero]; simp [affine]
abbrev pos(N:Side): Tw N (Seat N):=⟨fun i=>(boxA i).symm, funext (by simp [boxV]),fun a b x=> by rw [←sitU a,←sitU b,←sitU _,sitV,mul_inv_rev]⟩
lemma pos_y (s:Sweep n)(x:Seat n): (pos n).mv s⁻¹ x=boxA s x:=by change (boxA s⁻¹).symm _=_; rw [sitU,Equiv.symm_symm]
def arr :Tw n (X→Y):=⟨fun i p=> Q.mv i ∘ p ∘ P.mv i⁻¹, funext (fun x=> funext (by simp [P.one,Q.one])), fun a b x=> funext (fun i=> by simp only [comp_apply,Q.pair,P.pair,mul_inv_rev])⟩ -- pair p order? f.input pre pull P^-; order:mv pre (x^-¹) etc.
abbrev ζ (i:Sweep n)(S:Support (More n)):=S.map (boxA i).toEmbedding
lemma mem_s(s:Sweep n)(x:Seat n)(S:Support (More n)):boxA s x∈ζ s S ↔ x ∈ S:= by simp [ζ]
lemma mem_T(s:Sweep n)(x:Seat n)(S:Support (More n)):x∈ζ s⁻¹ S ↔ boxA s x∈ S:= by simp [ζ,sitU]
lemma ζv(s t:Sweep n)(S:Support (More n)):ζ s (ζ t S)=ζ (s*t) S:=by
 ext x; obtain ⟨x,rfl⟩:= (boxA (s*t)).surjective x; rw [mem_s,←sitV,mem_s,mem_s]
lemma ζ1(S:Support (More n)):ζ 1 S=S:=by simp [ζ,boxV]
abbrev scale (N:Side): Tw N (Support (More N)):=⟨fun i s=> ζ i⁻¹ s, funext (fun x=>by rw [inv_one,ζ1]; rfl), fun a b x=> by rw [ζv,mul_inv_rev]⟩
lemma ζ_inv (s:Sweep n)(A:Support (More n)):ζ s⁻¹ (ζ s A)=A:=by rw [ζv,inv_mul_cancel,ζ1]
lemma ζ_rev (s:Sweep n)(A:Support (More n)):ζ s (ζ s⁻¹ A)=A:=by rw [ζv,mul_inv_cancel,ζ1]
-- orientation array indexed by sets
abbrev Cotton(n:Side):= Support (More n)→Sweep n
abbrev Salar(n:Side)(r:ℕ):= Sat.pool r (@Sat.key (More n)) (Sweep n)
variable (s:Sweep n)(η:Cotton n) (S:Support (More n))
def act :Equiv.Perm (Cotton n):= Sat.bonus (Sat.hull (boxA s)) (fun i=> Equiv.mulLeft s⁻¹)
lemma act_P : (act s η) S=s⁻¹*η (ζ s S):=rfl
lemma w_t: Chooses (Salar n r).c (act s):=Sat.chooseB r (@Sat.key (More n)) (act s)
lemma earnings (S:Support (More n)) (p:S.Nonempty): (Salar n r).idT (fun η=>η S) S:= fun i j t=> Sat.single_p _ i j S (Sat.tithe S p) t
-- generic local symmetrization. Ψ_{η_E} first on input
abbrev tune(f: I→X→Y)(R:Tw n I)(s:Sweep n)(i:I)(x:X):Y:= Q.mv s⁻¹ (f (R.mv s i) (P.mv s x))
lemma tune_p (R:Tw n I)(i:I)(k:Sweep n)(x:X)(f:I→X→Y):Q.mv s (tune P Q f R k i x) = tune P Q f R (s⁻¹*k) (R.mv s i) (P.mv s x):=by
 simp [tune,R.pair,Q.pair,P.pair,mul_inv_rev]
lemma tune_v (R:Tw n I)(i:I)(w:I→ Support (More n))(v:∀ i,w (R.mv s i)=ζ s⁻¹ (w i))(x:X)(f:I→X→Y):tune P Q f R ((act s η) (w (R.mv s i))) (R.mv s i) (P.mv s x)= Q.mv s (tune P Q f R (η (w i)) i x):=by
 rw [act_P,v,ζ_rev]; exact (tune_p ..).symm
lemma ζL : Finset.Nonempty S ↔ (ζ s S).Nonempty:= Finset.map_nonempty.symm
lemma ζmono {S T:Support (More n)}(p:S⊆T):ζ s S⊆ζ s T:= Finset.map_subset_map.mpr p
lemma cellV (r:ℕ)(x): ζ s (Hue.cell (More n) x r)= Hue.cell (More n) (boxA s x) r:=by simp only [Hue.cell,ζ,←paysT,Finset.map_singleton,Equiv.toEmbedding_apply]
end Tw
end YM.CF.DPress.FD
