import YM.CF.BProof.Chess.Stack
/-! Distinguish blank from paid P slots even for unit (label-only distinction). -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BProof.Chess
open Function Filter Metric NormedSpace Finset Lattice Cube Bide Spire Bide.Half RG Fock Lat Skye Scree
open scoped Matrix.Norms.L2Operator Matrix ComplexOrder Topology BigOperators InnerProductSpace Kronecker Classical
attribute [local instance] opCStarAlgebra
variable {N L:Side}{i:Axis}{s t h z w:ℕ}
local notation "Trup"=> Scute N L i w
namespace Drum
variable {H:Obs N→ℝ}(D:Drum N L i w H)
open Scute Tack
variable {p n m k r a:ℕ}{A B c:ℝ}{x y:Scute N L i w}
abbrev eligible(p:ℕ)(c:ℝ)(x:Scute N L i w):Prop:= x.length=p ∧ Paid x.mark c
lemma eligBar(t:eligible p c x): eligible p c x.bar:=⟨t.1,x.barCost t.2⟩
/-- Blank contribution has weight B and fill has A. Bound any mark Chess of this *cost*.
Positivity hypotheses required only on proposed per-finest-slot upper prices, not on reads. -/
structure Costed (D:Drum N L i w H)(p:ℕ)(c A B:ℝ): Prop where
 pos :0<A
 born:0<B
 prim(n:ℕ): halfC L N (p*n) → H 1 ≤ B^(2*n)
 high(n:ℕ): halfC L N (p*n) → ∀ x:Scute N L i w, eligible p c x → price H ((x*x.bar)^n) ≤ A^(2*n)
abbrev pair (p k:ℕ)(c:ℝ)(x:Scute N L i w): Prop:= ∃ L':List (Scute N L i w), x=L'.prod ∧ L'.length=k ∧ ∀ i∈L',eligible p c i
namespace pair
variable (Y:pair p k c x)
include Y
lemma number:x.length=p*k:=by obtain ⟨L,rfl,g,v⟩:=Y; rw [amount (fun i t=>(v i t).1),g]
lemma flip (e:field L (p*k) ≤ (More N).val)(u:0<w): pair p k c x.bar:=by
 have hz:=Y.number; obtain ⟨L,rfl,h,g⟩:=Y; refine ⟨flop bar L,bar_stack _ (by rw [hz]; exact e) u,(flop_len ..).trans h,fun i y=>?_⟩; obtain ⟨b,p,t⟩:= List.mem_map.mp (List.mem_reverse.mp y); exact t ▸ eligBar (g b p)
lemma paste (z:pair p m c y): pair p (k+m) c (x*y):=by obtain ⟨L,rfl,h,H⟩:=Y; obtain ⟨K,rfl,g,G⟩:=z; exact ⟨L++K,(List.prod_append ..).symm,(by simp [h,g]),fun i y=> (List.mem_append.mp y).elim (H i) (G i)⟩
omit Y
lemma coin (u:eligible p c x):pair p 1 c x:=⟨[x],(by simp), rfl,fun i h=>List.mem_singleton.mp h ▸ u⟩ -- subst issue
end pair
-- finite alphabet interface for a list of representatives
section
variable {α:Type*}
abbrev jump : α×Bool→ α×Bool:=fun p=> (p.1,!p.2)
abbrev code (F:α→ Scute N L i w)(e:α× Bool) :Scute N L i w:= if e.2 then (F e.1).bar else F e.1
lemma equip(F:α→ Scute N L i w)(t:∀ i,(F i).length=p): Tack jump p (code F):=by
 refine ⟨?_,?_,?_⟩
 · rintro ⟨i,b⟩; cases b<;> rfl
 · rintro ⟨i,b⟩; cases b<;> exact t _
 rintro ⟨i,b⟩; cases b; exact rfl; exact (bar_b _).symm
variable {F:α→ Scute N L i w}{π:α→α}(T:Tack π p F)
local notation "Vc"=> vacant N L i w p
abbrev addBlank(p:ℕ)(F:α→ Scute N L i w)(o:Option α) := Option.elim o (vacant N L i w p) F
include T
lemma fare : Tack (Option.map π) p (addBlank p F):=by
 refine ⟨fun i=>?_,fun i=>?_,fun i=>?_⟩
 · cases i; rfl; rename_i a; exact congrArg some (T.inv a)
 · cases i; rfl; exact T.size _
 cases i; exact (bar_v p).symm; exact T.spin _
omit T
end
lemma power_v (x y:ℕ): (vacant N L i w x)^y=vacant N L i w (x*y):=by induction y with|zero=> rw [pow_zero,mul_zero]; rfl|succ y ih=> rw [pow_succ,ih,←vacant_plus,Nat.mul_succ]
namespace Costed
variable (K:Costed D p c A B)
section
variable {α:Type*}[Finite α]{F:α→Scute N L i w}{π:α→α}(T: Tack π p F)(tU:∀ i,Paid (F i).mark c)(u:0<n)(p':halfC L N (p*n))
abbrev κ (A B:ℝ)(x:Option α) := Option.elim x B fun _=> A
local notation "Yb"=> addBlank p F
include K T u p' tU
lemma cover (x:List (Option α))(v:x.length=2*n):price H (stack (addBlank p F) x) ≤ Price.rate (κ A B) x:=by
 refine (D.prices p' u (fare T)).victory (κ A B) (fun x=> ?_) (fun x=>?_) (fun x=> ?_) x v
 · cases x; exact K.born; exact K.pos
 · cases x <;>rfl
 rw [(fare T).stature]; cases x with
 | none=>
   change price H ((vacant N L i w p*(vacant N L i w p).bar)^n) ≤ B ^ (2*n); rw [bar_v, ←vacant_plus,power_v]; exact K.prim n p'
 | some x=> exact K.high n p' (F x) ⟨T.size _, tU x⟩
omit K T tU p' u
lemma countSome (A B:ℝ)(d:List α) : Price.rate (κ A B) (d.map some)=A^d.length:=by induction d with| nil=>simp [Price.rate]| cons i d g=> rw [List.map_cons,List.length_cons, pow_succ', Price.rate,List.map_cons,List.prod_cons]; exact congrArg (A*·) g
lemma stack_s (d:List α): stack Yb (d.map some)=stack F d:=by rw [stack,List.map_map, show Yb ∘ some=F from funext fun _=>rfl]
include K T u p' tU
lemma role (d:List α)(j r:ℕ)(v:(d.length+r)*j=2*n) : price H ((stack F d*(vacant N L i w p)^r)^j) ≤ A^(d.length*j)*B^(r*j):=by
 let f:List (Option α) := d.map some++List.replicate r none; let x:=(List.replicate j f).flatten; have hk:stack Yb f=stack F d*(vacant N L i w p)^r:=by rw [Tack.chat, stack_s]; simp [stack]
 have hp : Price.rate (κ A B) f=A^d.length *B^r:=by rw [Price.append, countSome]; simp [Price.rate,κ] -- tune κ abbrev
 have ht(j:ℕ):(List.replicate j f).flatten.length=f.length*j:=by induction j with|zero=> simp|succ j ih=> rw [List.replicate_succ,List.flatten_cons,List.length_append, ih, Nat.mul_succ,add_comm]
 have hh: x.length=2*n:=by unfold x; rw [ht]; simpa [f] using v; -- no semicolon
 have hz:stack Yb x=(stack Yb f)^j:=by simp [x,stack,List.map_flatten,List.prod_flatten]; -- diag
 have hy : Price.rate (κ A B) x=(Price.rate (κ A B) f)^j:=by simp [x,Price.rate,List.map_flatten,List.prod_flatten]
 rw [pow_mul A, pow_mul B] -- intended `pow_mul A`? lemma `pow_mul : a^(x*y)=(a^x)^y`
 rw [←hk,←hz, ←mul_pow,←hp,←hy]; exact K.cover D T tU u p' x hh
omit T u p' tU
end
include K
lemma rent(v:pair p k c x)(s t n:ℕ)(u:0<n)(g:halfC L N (p*n))(p':(k+s)*t=2*n) : price H ((x*(vacant N L i w p)^s)^t) ≤ A^(k*t)* B^(s*t):=by
 obtain ⟨D',rfl,h,H'⟩:=v; let L' := D'.toFinset; let Z (x:L'):= x.val; let f:= code Z; have hh(i:(L': Type _)): eligible p c (Z i) := H' _ (List.mem_toFinset.mp i.property) -- Lean type cast syntax tune
 let d:= D'.attach.map (fun i=>((⟨i.val,List.mem_toFinset.mpr i.property⟩:L'),false)); have hL : d.map f=D':=by
    unfold d; rw [List.map_map,show f∘_=Subtype.val from rfl,List.attach_map_subtype_val] -- tune
 have hl:d.length=k:=by simp [d,h]
 have e: stack f d=D'.prod:=by rw [stack,hL];
 rw [←e,←hl]; refine K.role D (F:=f) (equip Z (fun j=>(hh j).1)) ?_ u g d t s ?_
 · rintro ⟨x,b⟩; cases b; exact (hh x).2; exact (eligBar (hh x)).2
 rw [hl]; exact p'
end Costed
end Drum
end YM.CF.BProof.Chess
