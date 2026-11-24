import YM.SU5.FiniteGaugeData.Seld.Limb
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Leal
open Function Filter Metric Complex Set MeasureTheory Lattice Mist Celeritas Land OS OS.Semigroup
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace ComplexOrder ContDiff
variable {K:Axis→Hilbert}(W:∀ a:Axis, OS.Semigroup (K a) a)(Ω:(i:Axis)→(K i).space) {H:Hilbert} {a:Axis}
variable (S:OS.Semigroup H a)(n m:ℕ) (Y:Shrine K)
variable (a b: Axis){σ:Type}(L:List σ)(ν:σ→ℕ)(F:σ→ Shrine K)(x:σ→ E4)
local notation "L*"=>Shrine K -- reserve
local notation "Q"=> chalk W Ω a ν
variable (U:Set (Shrine K)) [DecidableEq σ] (P P':(σ→ Shrine K)→Prop)
abbrev Magic(n:ℕ):= Sprout ((armor W n) '' U)
omit [DecidableEq σ] in
lemma magic0 (m: Shrine K)(p:m∈U): m∈ Magic W U 0:= by
 apply sprout_sub; refine ⟨m,p,?_⟩; cases m with | mk t f=> simp only [armor,Cache,pow_zero,one_mul,mul_one]
-- parameter P.Basic says open acceptance of moving Weave. keep F all finite ε.Of.All parameters. also Calendar L matching.L.Other P
structure Invitation (P:(σ→ Shrine K)→Prop) : Prop where
 wish (i:σ)(f:ℕ→(σ→ Shrine K))(F:σ→ Shrine K)(p: ∀ j, Weaves (fun n=>f n j) (F j))(κ:∀ j,j≠i→∀ n,f n j=F j) : P F→∀ᶠ n in atTop,P (f n)
lemma openingC (Y:Set ℂ)(p:IsOpen Y)(h:L.Nodup): Invitation (fun F=> L.Pairwise (Seers F x a) ∧ chalk W Ω a ν F x L∈Y) := by
 constructor; rintro i f F t k ⟨v,g⟩; exact (Seers.along F f x L a v t).and ((Chalk_lim W Ω a L ν F x v f t i k h).eventually (p.mem_nhds g))
omit [DecidableEq σ] in
lemma openingT (i:σ)(Y:Set ℝ≥0)(p:IsOpen Y): Invitation (K:=K) (fun F=> (F i).t a∈Y):=⟨fun _ _ _ h _ t=> ((h i).grows a).eventually (p.mem_nhds t)⟩
omit [DecidableEq σ] in
lemma openingM (i:σ)(x y:(K a).space)(Y:Set ℂ)(p:IsOpen Y): Invitation (K:=K) (fun F=> inner ℂ x ((F i).f a y)∈Y):=⟨fun _ _ _ h _ t=>(((h i).looks a).funds _ _).eventually (p.mem_nhds t)⟩
omit [DecidableEq σ] in
lemma invitation_both (p:Invitation P)(h:Invitation P'): Invitation (fun f=>P f∧P' f):=⟨fun i _ _ g z h' => (p.wish i _ _ g z h'.1).and (h.wish i _ _ g z h'.2)⟩
omit [DecidableEq σ] in
lemma invitation_finite {β:Type*}(p:Finset β)(T:β→ (σ→ Shrine K)→Prop)(H:∀ i∈p,Invitation (T i)): Invitation (fun F=>∀ i∈p,T i F):=⟨fun i f F h z t' => (eventually_all_finset p).mpr fun j y=> (H j y).wish i f F h z (t' j y)⟩
variable [Fintype σ]
lemma gala (R:Invitation P)(p:P F)(h: ∀ i,F i∈ Magic W U (ν i)) : ∃ Y:σ→Shrine K,(∀ i,Y i∈ U) ∧ P (dressed W ν Y):=by
 suffices hv: ∃ f:σ→Shrine K,(∀ i,f i∈armor W (ν i) '' U)∧ P f by
    obtain ⟨f,v,p⟩:=hv; choose Y m h using v; exact ⟨Y,m, (funext (show ∀ i, dressed W ν Y i=f i from h)) ▸ p⟩
 let X(i:σ):=armor W (ν i) '' U
 suffices he:∀ Z:Finset σ,(∀ i, if i∈Z then F i∈ Sprout (X i) else F i∈X i) → ∃ Y:σ→Shrine K,(∀ i,Y i∈X i)∧ P Y from he Finset.univ (fun i=>by simpa only [Finset.mem_univ,↓reduceIte] using (show _ from h i)) -- tune shows_goal show _ 
 clear h; intro Z; induction Z using Finset.induction generalizing F with
  | empty=> exact fun t=>⟨F,(by simpa using t),p⟩
  | insert i T e ih=>
     intro h; obtain ⟨Y,u,v⟩:= (show F i∈ Sprout (X i) from (by simpa using h i)); let B(n:ℕ):=Function.update F i (Y n)
     have hh(j:σ)(p:j≠i):∀ n,B n j=F j:= fun n=> Function.update_of_ne p _ _
     have hp(n:ℕ): B n i=Y n:= Function.update_self ..
     have ht(j:σ): Weaves (fun n=>B n j) (F j) := by
       by_cases q:j=i; · subst j; simp_rw [hp]; exact v
       simp_rw [hh j q]; exact weaves_r _
     obtain ⟨n,a⟩:= (R.wish i _ F ht hh p).exists; apply ih _ a; intro j; by_cases q:j=i; · subst j; rw [hp,if_neg e]; exact u n
     simpa [Finset.mem_insert,q,hh j q] using h j
#print axioms gala
-- arity cleaning general (U property.Philos public). 
abbrev Philos {σ:Type} (U:Set (Shrine K)):= ∀ (F:σ→ Shrine K), (∀ i,F i∈ U)→ ∀ (x:σ→E4)(L M: List σ),L.Perm M→L.Nodup→ L.Pairwise (Seers F x a)→ M.Pairwise (Seers F x b)→ chorus W Ω F x L a= chorus W Ω F x M b
variable (R:Philos (σ:=σ) W Ω a b U)(P₁:saucer (W a) (Ω a)=Ω a)(P₂:saucer (W b) (Ω b)=Ω b)
include R P₁ P₂
lemma Cords (p: ∀ i,F i∈ Magic W U (ν i))(M:List σ)(h:L.Perm M)(d:L.Nodup)(u:L.Pairwise (Seers F x a))(v:M.Pairwise (Seers F x b)): chalk W Ω a ν F x L= chalk W Ω b ν F x M:=by
 by_contra y; obtain ⟨U',V',p₀,p₁,u₀,u₁,h'⟩:= t2_separation y; obtain ⟨Y,p,⟨t',s⟩, t1, s'⟩:= gala W ν F U (fun z=>(L.Pairwise (Seers z x a)∧chalk W Ω a ν z x L∈U') ∧ (M.Pairwise (Seers z x b)∧chalk W Ω b ν z x M∈V')) (invitation_both _ _ (openingC W Ω a L ν x U' p₀ d) (openingC W Ω b M ν x V' p₁ (h.nodup_iff.mp d))) ⟨⟨u,u₀⟩,v,u₁⟩ p
 have he: chalk W Ω a ν (dressed W ν Y) x L=chalk W Ω b ν (dressed W ν Y) x M:= (index_k W Ω a L ν Y x t' P₁).trans ((R Y p x L M h d t' t1).trans (index_k W Ω b M ν Y x t1 P₂).symm)
 exact Set.disjoint_left.mp h' s (he ▸ s')
#print axioms Cords
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Leal
