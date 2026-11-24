import YM.CF.BProof.Radar.Match
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxRecDepth 4000
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.BProof.Mesh
open Lattice Function Finset Equiv Regard Rows
open scoped BigOperators Classical
variable {n:Side}{l k r d s:ℕ}{C A:Type*}
open Sleet Crop.Native
namespace Policy
namespace Busy
variable {z a:ℕ}
abbrev palette(a:ℕ):= Fin (a+1)
variable (S:Field n A Prop)(Y:Field n A (Fin z))(l:ℕ)
private def voidA (a:ℕ)(F:Finset (palette a)):palette a:= if h:∃ j:palette a,j∉ F then Classical.choose h else 0
private lemma noA(p:Finset (palette a))(h:p.card ≤ a):voidA a p∉ p:=by
 unfold voidA; split; next h=> exact Classical.choose_spec h
 next h'=> push Not at h'; rw [show p= univ from Finset.eq_univ_of_forall h',card_univ,Fintype.card_fin] at h; omega
variable (a:ℕ)
private def offP (F:Field n A (palette a))(Z:A)(x:Site n):= ((cell (crowd S Z) l x).image (F Z))
def fork (u:ℕ)(F:Field n A (palette a)) :Field n A (palette a) := fun Z i=> if S Z i ∧ (Y Z i).val=u then voidA a (offP S l a F Z i) else F Z i
local notation "Fκ"=> (Joint S Y)
private lemma fork_h(i:ℕ)(F:Field n A (palette a)): Uses (Joint (Joint S Y) F) (fork S Y l a i F) l:=by
 let X:=Joint Fκ F; intro x w v h; have he(y:Site n)(p:separation x y≤ l): X w y=X v y:= h ((reg_in ..).mpr p); have p:=he x (by simp); have hs{i}(u:separation x i≤ l) : S w i=S v i:=congrArg (Prod.fst ∘ Prod.fst) (he i u); unfold fork; let M(w):=cell (crowd S w) l x; suffices t: (M w).image (F w)=(M v).image (F v) by rw [hs (by simp),show Y w x= _ from (show _= Y v x from congrArg (Prod.snd ∘Prod.fst) p), show offP S l a F w x= _ from t,show F w x= _ from (show _= F v x from congrArg Prod.snd p)]; rfl
 rw [show M v=M w from ?_]; swap; · ext i; simp only [M,cell,reg_in,crowd_in,mem_inter]; apply and_congr_left; intro p; rw [hs p] -- tune p is nearby
 exact Finset.image_congr fun x p=> congrArg Prod.snd (he x (reg_in ..|>.1 (mem_inter.mp p).2))
private lemma forkL (i:ℕ)(F:Field n A (palette a)): Loyal (Joint (Joint S Y) F) (fork S Y l a i F):=by
 intro s x E p w y; let e:=facet s x; have he(z):S (E w) z=S w (e z):=congrArg (Prod.fst ∘Prod.fst) (p w z); have hu(z):F (E w) z=F w (e z):=congrArg Prod.snd (p w z); let M(w i):=cell (crowd S w) l i; have hM(u):u∈M (E w) y↔e u∈M w (e y):=by simp only [M,cell,mem_inter,crowd_in,reg_in,he,e,facet_keeps]
 unfold fork; suffices h: (M (E w) y).image (F (E w))=(M w (e y)).image (F w) by rw [he,show Y (E w) y= _ from (show _=Y w (e y) from congrArg (Prod.snd ∘Prod.fst) (p w y)),show offP S l a F (E w) y = _ from h,hu]; rfl -- maybe rw handles
 ext k; rw [mem_image,mem_image]; constructor <;> rintro ⟨i,v,rfl⟩; · exact ⟨e i,(hM _).mp v,(hu i).symm⟩
 obtain ⟨i,rfl⟩:=e.surjective i; exact ⟨i,(hM _).mpr v,hu i⟩
abbrev grant(j:ℕ):=stage (0:palette a) (fork S Y l a) j
lemma grantD(j:ℕ): Uses (Joint S Y) (grant S Y l a j) (j*l):=stage_uses l _ _ _ (fork_h S Y l a) _ -- tune .. munch
lemma home(j:ℕ): Loyal (Joint S Y) (grant S Y l a j):= stageL _ _ _ (forkL S Y l a) _
variable {S Y l a} -- reorder
abbrev goodHue(S:Field n A Prop)(F: Field n A C)(l:ℕ):= ∀ t x y,S t x→S t y→ x≠y→ separation x y≤ l → F t x≠F t y
lemma leased (t:OrderC Y l)(v:∀ x y,(cell (crowd S x) l y).card ≤ a): goodHue S (grant S Y l a z) l:=by
 intro w x y p q h u
 let f(j:ℕ):=grant S Y l a j w
 have hf(j):∀ x,S w x→ f (j+1) x= if (Y w x).val=j then voidA a (offP S l a (grant S Y l a j) w x) else f j x:=by intro x p; simp only [grant,f,stage,fork,p,true_and]
 have ht(j):∀ x y:Site n,S w x→ S w y→x≠y→ separation x y ≤ l→ (Y w x).val< j→(Y w y).val<j→f j x≠f j y:=by
    intro x y p q h u; induction j generalizing x y with
    | zero=> omega
    | succ j ih=>
       intro hx hy; let g(i):=Y w i; have hz:(g x).val≠(g y).val:=fun Q=>t x y h u w (Fin.ext Q); have ha(x y:Site n)(h:S w x)(p:S w y)(t:separation x y≤ l)(m:(g x).val=j)(n:(g y).val< j) :f (j+1) x≠f (j+1) y:=by
          rw [hf j x h,hf j y p,if_pos m,if_neg (ne_of_lt n)]; intro e; let Q:=offP S l a (grant S Y l a j) w x; have he: (f j y)∈Q:= mem_image_of_mem _ (mem_inter.mpr ⟨(crowd_in ..).2 p,(reg_in ..).2 t⟩); exact noA Q (card_image_le.trans (v ..)) (e ▸ he)
       rcases eq_or_ne (Y w x).val j with a|a; · exact ha x y p q u a (by change (g y).val<_ at hy; change (g x).val=j at a; omega)
       by_cases hY:(Y w y).val=j; · exact Ne.symm (ha y x q p (separation_comm .. ▸ u) hY (by unfold g; omega))
       rw [hf j x p,hf j y q,if_neg a,if_neg hY]; exact ih _ _ p q h u (by omega) (by omega)
 exact ht _ x y p q h u (Y w x).2 (Y w y).2
end Busy
end Policy
end YM.CF.BProof.Mesh
