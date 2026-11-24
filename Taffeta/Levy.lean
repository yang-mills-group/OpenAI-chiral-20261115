import Weft.Bridge
import Taffeta.Fissure
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Mew
open Drift Function Finset
open scoped Classical
variable {I:Type}[Fintype I][LinearOrder I]
attribute [-instance] instDecidableEqLex
local notation "P"=>PairKey I
variable {E:Type*}[AddCommGroup E][Module ℂ E]
/-- α i charge for lA v heights, β i for B lower promoted. Order in lists preserved. No commutation with other external Marks is being claimed. -/
def levy (α β:P→ℂ)(S:List I→List I→E)(L:List P):E:=match L with
 | []=>S [] []
 | i::l=> α i • levy α β (fun lA lB=>S (i.1::lA) lB) l + β i • levy α β (fun lA lB=>S lA (i.1::lB)) l
lemma levy_add (α β:P→ℂ)(S S':List I→ List I→ E)(l:List P):levy α β (fun a b=> S a b+S' a b) l=levy α β S l + levy α β S' l:=by
 induction l generalizing S S'
 case nil=>rfl
 case cons i l ih=> unfold levy; simp_rw [ih (fun a b=> S (i.1::a) b) _,ih (fun a b=>S a (i.1::b)) _,smul_add]; abel
lemma levy_smul(α β:P→ℂ)(S:List I→List I→E)(l:List P)(c:ℂ):levy α β (fun a b=>c • S a b) l=c • levy α β S l:=by
 induction l generalizing S
 case nil=>rfl
 case cons i l ih=> unfold levy; rw [ih (fun a b=> S (i.1::a) b), ih (fun a b=>S a (i.1::b)), smul_add, smul_comm (α i),smul_comm (β i)]
lemma levy_c (α β:P→ℂ)(S S':List I→List I→E)(l:List P)(p:∀ a b,a.Sublist (l.map yard)→b.Sublist (l.map yard)→S a b=S' a b): levy α β S l=levy α β S' l:=by
 induction l generalizing S S'
 case nil=> exact p [] [] (.refl _) (.refl _)
 case cons i l ih=>
    unfold levy; apply congrArg₂ (·+·)
    · exact congrArg (α i • ·) (ih _ _ fun a b x y=> p (i.1::a) _ (.cons_cons _ x) (.cons i.1 y))
    exact congrArg (β i • ·) (ih _ _ fun a b x y=> p _ (i.1::b) (.cons i.1 x) (.cons_cons _ y))
-- divide coeff convert with high constant.Portion.As Direct.Personal
lemma divisor (c:P→ℂ)(L:List P)(f:List P→ℂ)(S:List I→ℂ)(p:∀ l,l.Sublist L→ f l=S (l.map yard)):divide c L f=levy 1 c (fun a _=>S a) L:=by
 induction L generalizing f S
 case nil=>exact p _ (.refl _)
 case cons i L ih=>
   unfold divide levy; rw [add_comm,Pi.one_apply,one_smul]; apply congrArg₂ (·+·)
   · exact ih _ _ fun l h=> p _ (.cons_cons _ h)
   exact congrArg (c i • ·) (ih _ _ fun l h=> p _ (.cons i h))
lemma levyPull (L:List P)(α β:P→ℂ)(a b:I→ℂ)(S:List I→ List I→ E):
 levy (fun i=>a i.1*α i) (fun i=>b i.1*β i) S L = levy α β (fun l t=> ((l.map a).prod*(t.map b).prod) • S l t) L:=by
 induction L generalizing S
 case nil=> simp [levy]
 case cons i L ih=>
   unfold levy; rw [ih,ih,mul_comm (a _),mul_comm (b _),mul_smul,mul_smul]; apply congrArg₂ (·+·)
   · apply congrArg (α i • ·); rw [←levy_smul]; simp only [smul_smul,List.map_cons,List.prod_cons,mul_assoc]
   apply congrArg (β i • ·); rw [←levy_smul]; simp only [smul_smul,List.map_cons,List.prod_cons,mul_left_comm]
lemma levyMulR (L:List P)(α β:P→ℂ)(b:I→ℂ)(S:List I→ List I→ E):levy α (fun i=>b i.1*β i) S L=levy α β (fun l t=>(t.map b).prod • S l t) L:=by
 have h(d:List I):(d.map (fun _=> (1:ℂ))).prod=1:=by induction d with|nil=>rfl|cons i l ih=> simp only [List.map_cons,List.prod_cons,one_mul,ih]
 simpa only [one_mul,h] using levyPull L α β (fun _=>1) b S
lemma levyMulL (L:List P)(α β:P→ℂ)(a:I→ℂ)(S:List I→ List I→ E):levy (fun i=>a i.1*α i) β S L=levy α β (fun l t=>(l.map a).prod • S l t) L:=by
 have h(d:List I):(d.map (fun _=>(1:ℂ))).prod=1:=by induction d with|nil=>rfl|cons i l ih=> simp only [List.map_cons,List.prod_cons,one_mul,ih]
 simpa only [one_mul,h,mul_one] using levyPull L α β a (fun _=>1) S
-- Compose location-fiber matrices. For snow term across product expansion root at fixed same anchor, transform l. Define cast i k b universal Root σ comparisons relation.H head.NoChange.
open Lattice
lemma cashPipe {J:Type*}[DecidableEq J](o:I→J)(h:Injective o)(i:P)(F:P→ℂ):∑ j∈Roots.pipe_ζ (o∘yard) i,F j=F (pick i.1 false) + F (pick i.1 true):=by
 -- already have `melt_pipe` uses Site. adapt
 let D:= Roots.pipe_ζ (o ∘ yard) i; let t (k:Bool):PairKey I:=pick i.1 k
 have h (j k:P): (o ∘ yard) j=(o ∘ yard) k ↔ yard j=yard k:= ⟨fun p=>h p,fun p=>congrArg o p⟩
 have u: D={t false,t true}:=by ext j; unfold D Roots.pipe_ζ; simp only [mem_filter,mem_univ,true_and,mem_insert,mem_singleton]; rw [h]; exact ⟨fun p=> (show j=t false ∨ j=t true from by cases h:j.2; exact Or.inl (Prod.ext p h); exact Or.inr (Prod.ext p h)),fun z=> z.elim (fun k=> (show yard j=yard (t false) from congrArg yard k)) (fun k=> (show yard j=yard (t true) from congrArg yard k)) ⟩
 have g:t false ∉ ({t true}:Finset P):= fun g=>Bool.noConfusion (congrArg (altQ (I:=I)) (mem_singleton.mp g))
 change ∑ j∈D,_=_; rw [u,sum_insert g,sum_singleton]
def pallets(M:Bool→Bool→ℂ)(G:P→ℂ):P→ℂ:=fun i=>M false i.2*G (pick i.1 false)+ M true i.2*G (pick i.1 true)
lemma spinLevy {J:Type*}[DecidableEq J](o:I→J)(h:Injective o)(α β:P→ℂ)(S:List I→ List I→ ℂ)(L:List P)(M:Bool→Bool→ℂ):Roots.snow (o∘yard) (fun i j:PairKey I=> M i.2 j.2) (levy α β S) L=levy (pallets M α) (pallets M β) S L:=by
 induction L generalizing S with
 | nil=>rfl
 | cons i l ih=>
   let C:= fun i j:PairKey I=> M i.2 j.2
   rw [Roots.snow,cashPipe o h]
   have q(b:Bool):Roots.snow (o ∘yard) C (fun s=> levy α β S ((pick i.1 b)::s)) l = α (pick i.1 b) • levy (pallets M α) (pallets M β) (fun a b'=>S (i.1::a) b') l+ β (pick i.1 b) • levy (pallets M α) (pallets M β) (fun a b'=>S a (i.1::b')) l:=by
      let t:=pick i.1 b
      let V:= levy α β (fun a b=>S (i.1::a) b); let W:=levy α β (fun a b=>S a (i.1::b))
      change Roots.snow (o ∘yard) C (α t • V+β t • W) l =_
      rw [Roots.tally_ADD,Roots.tally_scale,Roots.tally_scale]; exact congrArg₂ (·+·) (congrArg (α t • ·) (ih ..)) (congrArg (β t • ·) (ih ..))
   change M false i.2 • (Roots.snow (o∘yard) C _ l)+ M true i.2 • _= _
   rw [q false,q true,levy,pallets,pallets]; simp only [smul_eq_mul,←mul_assoc]; ring
-- Principal l list.Two stroke V uses.
lemma shrinkSnow {J:Type*}[DecidableEq J](o:I→J)(h:Injective o)(L:List I)(k v b:ℝ)(F: List P→ℂ):Roots.snow (o∘yard) (fun i j:PairKey I=> Py.stone k v b i.2 j.2) F (L.map (fun i=>pick i false))=(k:ℂ)^L.length* F (L.map (fun i=>pick i false)):=by
 induction L generalizing F with
 | nil=> simp [Roots.snow]
 | cons i l ih=>
    simp only [List.map_cons,Roots.snow]; rw [cashPipe o h, ih]; change (k:ℂ) • _+(0:ℂ) • _=_; rw [zero_smul,add_zero,List.length_cons,pow_succ',smul_eq_mul,mul_assoc]
#check levy
#print axioms spinLevy
end YM.CF.Mew
end
