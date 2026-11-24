import YM.CF.Hake.Boom
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Hake
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube Relation
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Scree Pastry Stilo
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{ι n A:Type*}[LinearOrder n][Fintype n][SemilatticeSup A][OrderBot A][Fintype A][DecidableEq A]{k:ℕ}{x:E}
variable {r m:Type*}[LinearOrder r][Fintype r][LinearOrder m][Fintype m][LinearOrder ι][Fintype ι]{S:A}
-- germ relations can hold only in requested incidence. payments also only in subset.
lemma struck(P:ι→FC n)(W:List ι):rollC P W=(W.map P).prod:=rfl
lemma climb(u:ι→ Track A ℝ)(h:∀ i,ownH ℝ A≤u i)(L T:List ι)(p:L.Sublist T):payH u L ≤payH u T:=by
 have he(i):0≤u i:= coinH.trans (h i); induction p with
 | slnil=> exact le_rfl
 | cons i p ih=> apply ih.trans; exact le_trans (le_of_eq (crank_L ..).symm) (crank_r _ _ _ (pay_S he) (h i))
 | cons_cons i p ih=> exact crank_mono _ _ _ (he _) ih
lemma stave(E X: Type*)[SemilatticeSup X][OrderBot X][DecidableEq X][Fintype X]{R:Type*}[Ring R] (L:ι→Track X (E→R))(G:ι→ι→Track X (E→R))(l:List ι)(y:X)(x:E):view y (fun t=> spanned L G l t x)=taskC (fun i=> view y (L i) x) (fun i j=> view y (G i j) x) l:=by
 let P:=(spanned L G l); rw [show view y (fun t=> P t x)=view y P x from ?_,show view y P= _ from Stilo.spans .. ]; swap; · simp [view,Finset.sum_apply]
 suffices ht:∀ a w,ticketB (fun i=>view y (L i)) (fun i j=> view y (G i j)) a w x=ticketB (fun i=>view y (L i) x) (fun i j=>view y (G i j) x) a w from ht l.length l -- tune
 intro a; induction a with
 | zero=> exact fun w=>rfl
 | succ a ih=> intro w; cases w with
            | nil=> rfl
            | cons i w=>
                rw [ticketB,ticketB,Pi.add_apply,Pi.mul_apply, ih]; apply congrArg
                let Y(j:Bout ι):= (if j.neg then -view y (G i j.front) else view y (G i j.front))* ticketB (fun i=>view y (L i)) (fun i j=>view y (G i j)) a j.back
                have he(l:List (Bout ι)): (l.map Y).sum x=(l.map (fun j=> Y j x)).sum:=by induction l with| nil=> rfl| cons i l H=> simp only [List.map_cons,List.sum_cons,Pi.add_apply,H]
                rw [show _ = _ from he (picks w)]; simp_rw [Y,Pi.mul_apply, ih]; congr 1; apply List.map_congr_left; intro j p; split <;> rfl
section
variable (pr:r→ι)(pb:Oboe m→ι)(G:ι→ι→ Track A (E→FC n))(F:ι→ Track A (E→FC n))
abbrev crew(P:List r)(X: List (Oboe m)):= P.map pr ++ X.map pb
abbrev inn(s:A)(y:E):Prop:= ∃ (K:ι→ι→ℂ)(L:ι→n→ℂ), (∀ i j, K (pr i) (pr j)+K (pr j) (pr i)=0) ∧(∀ i j,K (pb i) (pb j)+K (pb j) (pb i)= if i=revertP j then 1 else 0) ∧(∀ i,view s (F i) y=lank L i) ∧ ∀ i j,view s (G i j) y=price K n i j
lemma hark (s:A)(y:E)(h: inn pr pb G F s y):∃ L:FC r→ₗ[ℂ] FC m→ₗ[ℂ] FC n, ∀ P:List r,∀ X:List (Oboe m),view s (fun t=>spanned F G (crew pr pb P X) t y)=L (rollC put P) (rollC bell X):=by obtain ⟨K,J,c,h,e,u⟩:=h; refine ⟨petL K J pr pb c h, fun P X=>?_⟩; rw [stave E A]; simp_rw [e,u]; exact pet_r K J pr pb c h _ _
end
variable (B:Raid n) (u:r→ι)(v:Oboe m→ι)(e: Injective u)(d: Injective v)(g:∀ i j,u i ≠ v j)
include e d g
lemma lunar (Q:ι→Track A ℝ)(p: Turner B)(h:∀ i,ownH ℝ A ≤ Q i)(c:ι→ Track A (Raid n))(w:ι→ι→ Track A (Raid n))(hc:∀ i,0≤ c i)(hw:∀ i j,0≤ w i j)(hcw:∀ i,rateT B (c i)+∑ j:ι,rateT B (w i j) ≤ Q i)(P:List r)(X:List (Oboe m)):∃ f:Track A (Raid n),0≤f ∧ rateT B f ≤ payH Q (crew u v P X) ∧ ∀(E:Type)[NormedAddCommGroup E][NormedSpace ℝ E](z:E) k (S:A)(G:ι→ι→Track A (E→FC n))(F:ι→Track A (E→FC n)),(∀ s,s ≤ S → ∀ᶠ y in 𝓝 z, inn u v G F s y) → (∀ i∈ crew u v P X,∀ s,s ≤ S → Woody k (F i s) z (c i s)) → (∀ i∈ crew u v P X,∀ j∈crew u v P X,∀ s,s ≤ S → Woody k (G i j s) z (w i j s)) → Woody k (spanned F G (crew u v P X) S) z (f S):=by
 let U:= rollC put P; let V:=rollC bell X; let L:=crew u v P X
 by_cases hl : U=0 ∨ V=0
 · refine ⟨0,le_rfl,?_,?_ ⟩
   · rw [show rateT B (0:Track A (Raid n))=0 from funext fun i=> show joinV B 0=0 by simp [joinV]]; exact pay_S fun i=> coinH.trans (h i)
   intro E _ _ z k S G F K _ _; apply Woody.germ (Woody.empty _)
   classical
   have ht:∀ᶠ y in 𝓝 z,∀ s:A,s≤S→ inn u v G F s y:= eventually_all.mpr fun s=> eventually_all.mpr fun i=>K s i
   filter_upwards [ht] with y i; change 0=_; symm
   apply proves (f:=fun t=>spanned F G (crew u v P X) t y) (g:=0); intro s t; obtain ⟨a,l⟩:= hark u v G F s y (i _ t); rw [l,view_zero]; rcases hl with u|v; rw [show rollC put P=0 from u,map_zero,LinearMap.zero_apply]; rw [show rollC bell X=0 from v,map_zero] -- tune
 obtain ⟨P',hp,up,x,hx,E'⟩:= (no_clash put P retreat).resolve_left (not_or.mp hl).1
 obtain ⟨X',hq,uq,s,hs,R⟩:= (no_clash bell X revive).resolve_left (not_or.mp hl).2
 let T:= crew u v P' X'; have ht: T.Sublist L:= (hp.map u).append (hq.map v)
 have hf:T.Nodup:=List.pairwise_append.mpr ⟨List.Nodup.map e up,List.Nodup.map d uq,fun b i j t=>by obtain ⟨a,-,rfl⟩:= List.mem_map.mp i; obtain ⟨r,-,rfl⟩:=List.mem_map.mp t; exact g _ _ ⟩
 refine ⟨shadeB c w T.length T,sPos c w hc hw _ _,(sWear c w hc hw Q p h hcw _ _ le_rfl hf).trans (climb Q h T L ht),?_ ⟩
 intro E _ _ z k S G F K f b
 classical
 let cut(W:Track A (E→FC n)) : Track A (E→FC n):=fun i=>if i≤S then W i else 0
 have hZ (W:Track A (E→FC n))(c:Track A (Raid n))(l:0≤c)(p:∀ i,i ≤ S → Woody k (W i) z (c i)): Course k (cut W) z c:=by
    intro i; unfold cut; split_ifs with t; · exact p i t
    let H:= Woody.empty (n:=n) (k:=k) z; exact ⟨H.own,fun j=>⟨(H.haveP j).smooth,(H.haveP j).earned.trans (l i j)⟩⟩
 let N i:=cut (F i); let M i j:=cut (G i j)
 have hy:= sPays (x:=z) c w T.length T N M (fun i p=> hZ _ _ (hc i) (f _ (ht.subset p))) (fun i p j q=>hZ _ _ (hw _ _) (b _ (ht.subset p) _ (ht.subset q))) S
 apply Woody.germ ((hy.ride x hx).ride s hs);
 have hv:∀ᶠ y in 𝓝 z,∀ s:A,s≤S→ inn u v G F s y:= eventually_all.mpr fun s=> eventually_all.mpr fun i=>K s i
 filter_upwards [hv] with y i
 change s • x • spanned N M T S y=spanned F G (crew u v P X) S y
 apply proves (f:=fun a=> s • x • spanned N M T a y) (g:=fun a=> spanned F G (crew u v P X) a y); intro a t
 have hl(W:Track A (E→FC n)):view a (cut W)=view a W:=sum_congr rfl fun b p=> if_pos (((deckH ..).mp p).trans t)
 rw [show view a _ = s • x • view a (fun b=> spanned N M T b y) from ?_]; swap; · simp [view,smul_sum]
 obtain ⟨V,l⟩:= hark u v G F a y (i _ t); rw [stave E A]; simp_rw [N,M,hl,←stave E A F G T a y]
 unfold T; rw [l,l,E',R,map_smul,map_smul,LinearMap.smul_apply]
end YM.CF.Hake
