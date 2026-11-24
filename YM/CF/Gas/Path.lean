import YM.CF.Gas.Basin
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Gas
open Function Filter Metric Finset NormedSpace Lattice Branch Tenant Petal Manifest Palot Stilo Corona RG Push.AbsoluteSums Trees Ursell Relation Graph MeasureTheory Phase.Sample Jet
open scoped Topology Classical BigOperators
variable {I A D E G T:Type} [Fintype I][DecidableEq I][Fintype A][DecidableEq A]
variable[TopologicalSpace D][FirstCountableTopology D][LocallyCompactSpace D][TopologicalSpace T][CompactSpace T][T2Space T][SecondCountableTopology T][MeasurableSpace T][BorelSpace T][Nonempty T]{μ:Measure T}[IsProbabilityMeasure μ][NormedCommRing E][NormedAlgebra ℝ E][CompleteSpace E][NormOneClass E]{M:ℕ}{r C v K α γ δ k k':ℝ}
variable {n:Side}
variable{L:Lodge (Site n) E D G}{V:Cabin μ L}{X:I→ Y n}{Q:I→ Support n}{w:I→ℝ}{F:I→ Mood (Site n) D T→E}{ρ:ℕ→ℝ}
abbrev parcelF (V:Cabin μ L)(X:I→ Y n)(F:I→ Mood (Site n) D T→E):Y n→ D→ E := Fiscal (Xi X (airport V F))
-- discrete supports exact; occurrence row invoices after
variable (h:Team L (terr _) V (fun i=> (X i).val) Q w F univ r)
abbrev moreK (w:I→ℝ)(i:I):= 4*w i -- includes factor two
include h
lemma yardB (x:D):Yard X fun i=> airport V F i x:=⟨(club h).startE x,fun P Q p g=>(club h).stitch P Q (subset_univ _) (subset_univ _) g p x⟩
lemma doff(T:Finset I): Token L (T.biUnion fun i=> (X i).val) (airport V F T) (heavy (moreK w) T) (fun _=>True):=by
 have he:=(club h).placed T (subset_univ _); have hp:heavy (fun i=>2*w i) T ≤ heavy (moreK w) T:=by
    apply prod_le_prod (fun i _=> mul_nonneg (by norm_num) (h.allowed i (mem_univ _)).price); intro i _; unfold moreK; exact mul_le_mul_of_nonneg_right (by norm_num) (h.allowed _ (mem_univ _)).price
 exact { he with price:=he.price.trans hp,shape:=fun _=> trivial,owns x:=(he.owns x).trans hp }
lemma dimeF(Y:Y n) :creditS Y (Xi X (airport V F) Y) (CoinX X (moreK w) Y) L:= credit_u Y (fun i p=>h.placed _ (mem_univ _) (right_ne_zero_of_mul p)) (doff h)
variable(t:Ready (stern ∘ X) 0 (moreK w) (α+1) γ δ k)(p:0≤α)(hq:0<v)(hg:γ*(1-k)⁻¹ ≤ v)(hu:k'<1)(hn:degreePrice 0 v 1 ≤ k')
include t p hq hg hu hn
lemma desks : Ready stern 0 (CoinX X (moreK w)) α v 1 k':=⟨hq,zero_lt_one,hn,hu,fun i=>(dimeF h i).price,ticket (fun i=> (dimeF h i).shape) (fun i=>(dimeF h i).price) fun i=> (starts (X:=X) (fun i q=>h.placed i (mem_univ _) (right_ne_zero_of_mul q)) (show Ready _ _ _ _ _ _ _ from t) (by linarith) i).trans hg⟩
lemma mortar (x:D): motor V (fun x=> exp (∑ i,F i x)) x= exp (∑ j:Y n,parcelF V X F j x):=by
 rw [Floor_eq h x,Floor,powerset_univ]; exact armed _ (yardB h x) (fun i=>(L.normF _).trans ((dimeF h i).owns _)) p (desks h t p hq hg hu hn)
lemma armX(q:Y n): creditS q (parcelF V X F q) (sumTax (CoinX X (moreK w)) q) L:= fiscal_g (desks h t p hq hg hu hn) p (dimeF h) q
lemma payA (i:Site n): bill_X stern (sumTax (CoinX X (moreK w))) α i ≤ v*(1-k')⁻¹:= taxesC (desks h t p hq hg hu hn) p i
section s
variable {J:Type}[NormedAddCommGroup J][NormedSpace ℝ J][FiniteDimensional ℝ J]{W:Set J}{Y':J→D} (P:FireK W (V.seat ∘ Y') K M)
variable (Z:E→ₐ[ℝ] E)(ph:Continuous Z)(uc:∀ x,‖Z x‖≤ L.fare x)
variable (g:Apert ρ)(he:∀ t:(Site n→ T),∀ x∈ W, fall (V.seat (Y' x)) t≠ 0 →∀ i, Assets M (fun y=> Z (F i (Y' y,t))) x (ρ (X i).val.card) (w i))
include Z ph uc g P he
omit t p hq hg hu hn
lemma pact(T':Finset I)(x:J)(hx:x∈W): Assets M (fun x=> Z (airport V F T' (Y' x))) x (torchR K ρ M (roof (stern ∘ X) T').card) (heavy (moreK w) T'):=by
 let l:= (roof (stern ∘ X) T').card
 cases em T'.Nonempty with
 | inr e=>
    have hh(v:D):Z (airport V F T' v)=1:=by rw [not_nonempty_iff_eq_empty.mp e, show airport V F ∅ v=1 from (club h).startE v,map_one];
    simp_rw [hh,heavy,not_nonempty_iff_eq_empty.mp e,prod_empty]; exact Assets.fixed _ norm_one.le
 | inl e=>
    have hz:(2:ℝ) ≤2^T'.card:=by nth_rw 1 [← pow_one (2:ℝ)]; apply pow_le_pow_right₀ (by norm_num); exact card_pos.mpr e
    let a(t):(Site n→ T)→ E:= fun y=> ∏ i∈T',secA (F i (Y' t,y))
    have ht:=crewW h (subset_univ T'); let L(t:Site n→ T):= {x:J| x∈W ∧ fall (V.seat (Y' x)) t ≠0}
    refine Assets.monoL (c:=2*heavy (fun i=>2*w i) T') (meritB g P Z ph uc ht ?_ x hx) ?_ -- args
    · intro t x v w'; have hi:IsOpen (L t):=by
         apply isOpen_iff_mem_nhds.mpr; intro x g; obtain ⟨u,s⟩:=g; exact inter_mem (P.support.mem_nhds u) ((show ContinuousAt (fun x=>fall (V.seat (Y' x)) t) x from (fire_num P u _ _).continuousAt).eventually_ne s)
      simp_rw [map_prod]; refine Assets.prodF (g.pos _).le _ (fun i p=>?_) -- tune P.A.Memory
      have he'(q:J): Z (secA (F i (Y' q,t)))=secA (Z (F i (Y' q,t))) := by
         letI : NormedAlgebra ℚ E:= NormedAlgebra.restrictScalars ℚ ℝ E; unfold secA; rw [map_sub,map_one,map_exp _ ph]
      refine (show Assets M (fun v=> Z (secA (F i (Y' v,t)))) x (ρ l) _ from ?_ ); simp_rw [he']; refine assets_front (g.pos _) (g.cap _) (L t) hi ⟨v,w'⟩ (fun y l=>Assets.cheaperA (he t y l.1 l.2 i) (g.pos _).le (g.ant ?_)) (per_one h _ (mem_univ _))
      exact card_le_card (roof_atom (X:=stern ∘ X) p)
    unfold heavy; simp_rw [moreK, show ∀ x:ℝ,4*x= 2*(2*x) from fun x=>by ring, prod_mul_distrib]; rw [prod_const]; apply le_trans (mul_le_mul_of_nonneg_right hz (show 0 ≤ 2^T'.card*∏ i∈T', w i from mul_nonneg (by positivity) (prod_nonneg (fun i _=> (h.allowed i (mem_univ _)).price)))) (le_of_eq ?_); ring
include h t p hq hg hu hn
lemma indoors(q:Y n)(x:J)(hx:x∈ W): Assets M (fun x=> Z (parcelF V X F q (Y' x))) x (torchR K ρ M q.val.card) (sumTax (CoinX X (moreK w)) q):=by
 let w':=Apert.tor M K g; apply ascent_s Z ph (desks h t p hq hg hu hn) p (dimeF h) w'.pos w'.cap w'.ant q P.support _ x hx
 exact fun j x y=> credit_jet x Z j (w'.pos _).le (fun i=>pact h P Z ph uc g he i x y)
end s
end YM.CF.Gas
