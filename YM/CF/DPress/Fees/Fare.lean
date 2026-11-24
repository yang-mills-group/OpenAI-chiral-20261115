import YM.CF.DPress.Fees.Well
import YM.CF.Hype.Ace
import YM.CF.Hype.Migrate
/-!
 Algebra of Rays price (usable on any ℂ module including Real correction extension in VolumeD-Lips1). always use Min price qualifiers; export equivalences.
 -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000
noncomputable section
namespace YM.CF.DPress.Fees
open Function Lattice MeasureTheory Filter Metric Analytic Finset
open Tulip Lat Cube RG Fock Pastry Skye Scree Vow Mew Jet Hake JetRead Rails Wray
open scoped Topology Classical BigOperators ContDiff Matrix Matrix.Norms.L2Operator YM.CF.Mew
attribute [local instance] opCStarAlgebra
variable {X Y:Type}[AddCommGroup X][Module ℂ X][AddCommGroup Y][Module ℂ Y]
structure Finance (p: Credit X)(V:Dial X):Prop extends Receipt p V where
 add {x y:X}{a b:ℝ}: p x a→p y b→p (x+y) (a+b) -- remove unused
 scale {x:X}{a:ℝ}:∀ c:ℂ,p x a→ p (c • x) (‖c‖*a)
 zero_p: p 0 0
namespace Finance
variable {V:Dial X}{U:Dial Y}{p:Credit X}{F:Credit Y}(Q:Finance p V){a b R:ℝ}{x y:X}
include Q
lemma neg (t:p x a): p (-x) a:=by simpa using Q.scale (-1) t
lemma sub (f:p x a)(t:p y b): p (x-y) (a+b):=by rw [sub_eq_add_neg]; exact Q.add f (Q.neg t)
abbrev Qual (X:Type*)(p:Credit X)(x:X):Prop:= ∃ a,p x a
lemma qual(x:X): Qual X p x ↔ p x (meter V x):= ⟨Q.toReceipt.paid,fun t=>⟨_,t⟩⟩
omit Q in
lemma thru {u:X→Y}(H:Finance F U)(h:∀ (x y:X), u (x+y)=u x+u y)(f:∀ (c:ℂ) (x:X),u (c • x)=c • u x): Finance (F∘u) (hood u U):=  by
 have he:u 0=0:=by have h₁:= f 0 0; simpa using h₁
 refine ⟨Receipt.move H.toReceipt, fun {x y a b} p q=> ?_, fun {x a} c v=> ?_,?_⟩ ; unfold Function.comp; rw [h]; exact H.add p q; unfold Function.comp; rw [f]; exact H.scale c v; unfold Function.comp; rw [he]; exact H.zero_p
lemma earn (Z:ℂ→ X)(c:1<R)(u:∀ z∈ank R,p (Z z) a)(H:Brings R Z (Z 1-Z 0) V): p (Z 1-Z 0) (a/(R-1)):= Q.toReceipt.approved H u ⟨_,Q.sub (u 1 (planeOne c)) (u 0 (planeZero c))⟩ c
lemma priceQ (x:X){a:ℝ}(b:p x a) :0≤ a:=(Q.perspective x a b).p
section roller
variable {I J:Type}(A:I→ Dial X)(φ:I→Credit X) (S:Finset I)(H:J→I→ℝ)(Yz:∀ i∈S, Finance (φ i) (A i))(hp:∀ j,∀ i∈ S,0≤H j i)
omit Q
open Receipt
include hp Yz
lemma system : Finance (Measures φ S H) (Relay A S H):=by
 constructor; exact Receipt.collects A φ S H (fun i p=>(Yz i p).toReceipt) hp
 · rintro x y a b ⟨p,k,v,t⟩ ⟨u,w,x,q⟩; exact ⟨add_nonneg p u,k+w,fun i p=>(Yz i p).add (v i p) (x i p),fun j=>by simp_rw [Pi.add_apply,mul_add,sum_add_distrib]; exact add_le_add (t j) (q j)⟩ -- tune order
 · rintro x a c ⟨p,k,v,t⟩; exact ⟨mul_nonneg (norm_nonneg _) p,‖c‖ • k,fun i p=>(Yz i p).scale _ (v i p),fun j=> by simp_rw [Pi.smul_apply,smul_eq_mul,mul_left_comm _ ‖c‖,←mul_sum]; exact mul_le_mul_of_nonneg_left (t j) (norm_nonneg _)⟩
 exact ⟨le_rfl,0,fun i h=>(Yz i h).zero_p,fun i=>by simp⟩
-- useful bound extraction any visible incidence choose j. 
lemma qualifyZ(t:Measures φ S H x a)(u:I)(p:u∈S)(j:J)(k:1 ≤ H j u):φ u x a:=by
 rcases t with ⟨w,v,t,q⟩; have he(i:I)(p:i∈S): 0≤v i:= (Yz i p).priceQ _ (t _ p); exact (Yz _ p).toReceipt.relax (t u p) (((le_mul_of_one_le_left (he u p) k).trans (single_le_sum (f:=fun i=> H j i * v i) (fun i g=>mul_nonneg (hp j i g) (he i g)) p)).trans (q j))
end roller
omit Q
lemma anti (V W:Credit X)(f0:Dial X)(p:Finance V f0)(w:∀ i x,V i x↔ W i x): Finance W f0:= funext₂ (fun i x=>propext (w i x)) ▸ p
end Finance
-- instances
variable {n:Side}(P:BudgetPoint)(h:ℝ)(R:Scree.Hub n)(Q:Force n)(S t:Support (More n))
variable (p:1≤h)
include p
lemma capE : Finance (fun f v=> PressB P R f h v) (beaming P h R):=⟨ritual P h R p,Larch.prop_add P R,fun c h=>Roots.súe R _ h c, Vale.rinse ..⟩ -- tune 
lemma capD : Finance (fun f v=> ForceB P Q f h v) (streak P h Q):=⟨chiC P h Q p,fun v t=>Roots.dom_h Q _ _ v t,fun c p=> Roots.dúe Q _ p c, Vale.rinsed ..⟩
omit p
-- adapted from CF/Neon/Plast general size
lemma num_h (p0:BudgetPoint) (S t:Support (More n)){x:ℝ}{Pn:Copy n}(q:Medal p0 S t Pn h x)(v:ℂ): Medal p0 S t (v • Pn) h (‖v‖ *x):=by
 obtain ⟨Z,b,u,w,v'⟩:=q; refine ⟨⟨fun i j f g=> congrArg (v • ·) (Z.same i j f g),fun i=>(Z.lit i).smul v,Z.keeps.const_smul v,fun i j=>?_⟩,‖v‖ • b,fun i=>mul_nonneg (norm_nonneg _) (u i),fun i s _ z=>?_ ,?_ ⟩
 · let X:= hueV (tradew _ j); change v • _= X (v • _); rw [Z.gaugeX,map_smul]; rfl
 · let h:=w i s z; refine ⟨Eventually.of_forall (fun y=> (fineShape _).allP),fun j=>?_⟩; exact (h.haveP j).σ v
 unfold joinV; simp_rw [Pi.smul_apply,smul_eq_mul,mul_left_comm _ ‖v‖,← mul_sum]; exact mul_le_mul_of_nonneg_left v' (norm_nonneg _)
include p
lemma capM : Finance (fun f v=> Medal P S t f h v) (shield P h S t):=⟨armourC P h S t p,Medal.plus,fun c v=> num_h h P S t v c,Medal.zeroT⟩ -- tune
end YM.CF.DPress.Fees
