import YM.CF.Hive.Good
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Hive
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Urn Hake Levier Spire Scree Stilo
attribute [local instance] opCStarAlgebra
variable {n:Type*}[LinearOrder n][Fintype n](b r t c:Bool)(U V:UNI n)
open Kennel Proa Acorn
variable {m L B N:Side}{a t b' d c' v e:ℝ}{H: Odd L.val}{j k:ℕ}{Y:Pricing j L H (Thread j)}{P:Grasp Y B e}
section
variable {ι:Type}(G:Ratio N (CSide m B))(X:Skin m B)(h:Guard X e)(p:P.roundZ≤(CSide m B).val)
include p h
lemma nest_r (K:Aim (CSide m B))(M:Male)(F:WG ι)(Q:ι→Male)(x:ι)(t: Q x=M)(g:F x (CSide m B) (profile X)=K.den X)(V:Bkg (More N)): -- bad V different!
 cartsL (switchG G).symm (nest P K M X)=acts (exp (dg (prime j F Q x G (unionP (X,V))))) (cartsL (switchG G).symm (changeM P X M)):=by
 let Z:= (K.den X); let S:= spar j M X; let C:=capT S Z; have he:C*C=0:= TagG.nil (P:=S) (tag_g Z ((P.broadness _ p M).projection _ h))
 have hx:prime j F Q x G (unionP (X,V))=portW (switchG G).symm C:=by unfold prime; rw [t]; change capT (foot G S) (foot G (F _ _ (profile _)))=_; rw [g]; unfold capT; rw [←foot_one,←foot_sub,←foot_mul,←foot_mul]; rfl
 rw [hx]; exact relabelExp (switchG G) C he _
end
open Cour
abbrev home_n (N:Side)(i:Single N):Site (More N):= node i.1.1
lemma grams(K:ℝ)(hK:1≤K)(g:Stamped j L H Y)(hp:0 ≤ a)(hz:0 ≤ b')(hk:0<d)(hv:0<v)(p:Even j)(w:1≤j)(R:Repair j) (s:ℕ):∃ e:ℝ,0<e ∧∃ k:ℕ,∀ {c B}(P:Grasp Y B c),0<c→Pearl P → c≤e → P.baseline ≤ R.d → ∃ α C:ℝ,0<α ∧0<C∧∀ {m:Side}(W:Aim (CSide m B))(M:Male), k ≤ (CSide m B).val → P.roundZ≤ (CSide m B).val→ W.toll d v a b' → ∀ (S:Broc.Table m B),Grove (terr _) S→∀ z:ℝ,1≤z→∃ F:Castle m B c S→ FC (Single (CSide m B)), CookC (landX s K S c) (home_n _) S α z F (Real.exp (C*S.card*z^2))∧∀ x,acts (F x) (nest P W M (x.val false))= nest P W M (x.val true):=by
 obtain ⟨u,f⟩:= alum hp hz hk hv; let B':= arcB d v a b'; obtain ⟨e,hE,k,H⟩:=shop L _ Y g p w B' u f Prod.snd s K hK R; refine ⟨e,hE,k,fun {c B} P y p v' q=>?_⟩
 obtain ⟨α,C,t,k',D⟩:= H P y p v' q; refine ⟨α,C,t,k',fun {m} W M ht hx hk S V z hp'=>?_⟩
 let N:=CSide m B; let G:= idrat N; obtain ⟨i,Y,Hx⟩:=demand N hp hz W hk M; obtain ⟨F,H,w⟩:= D (m:=m) (max_le ht hx) S V i z hp'; obtain ⟨A,g,T⟩:= oakLift (O:=home_n N) (switchG G) F H
 refine ⟨A,g,fun x=> carts_inj (switchG G).symm ?_⟩; rw [T]; let v:=nest P W M
 have hy(U:Skin m B): B' i N (profile U)=W.den U:=by unfold B' arcB; rw [Y,Moire.bloom_P]
 simp_rw [←Hx]; rw [nest_r G _ (x.property.1 false) hx W _ B' Prod.snd i rfl (hy _) (x.val false),nest_r G _ (x.property.1 true) hx W _ B' Prod.snd i rfl (hy _) (x.val true)]; exact w x
end YM.CF.Hive
