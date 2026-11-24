import YM.CF.Gas.Path
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Gas
open Function Filter Metric Finset NormedSpace Lattice Branch Tenant Petal Manifest Palot Stilo Corona RG Push.AbsoluteSums Trees Ursell Relation Graph MeasureTheory Phase.Sample Jet
open scoped Topology Classical BigOperators
variable {I A D E G T:Type} [Fintype I][DecidableEq I][Fintype A][DecidableEq A]
variable[TopologicalSpace D][FirstCountableTopology D][LocallyCompactSpace D][TopologicalSpace T][CompactSpace T][T2Space T][SecondCountableTopology T][MeasurableSpace T][BorelSpace T][Nonempty T]{μ:Measure T}[IsProbabilityMeasure μ][NormedCommRing E][NormedAlgebra ℝ E][CompleteSpace E][NormOneClass E]{M:ℕ}{r C v K α γ δ k k':ℝ}
variable {n:Side}
variable{L:Lodge (Site n) E D G}{V:Cabin μ L}{X:I→ Y n}{Q:I→Support n}{w:I→ℝ}{F:I→ Mood (Site n) D T→E}
abbrev Pearl := unitInterval
variable (h:Team L (terr _) V (fun i=>(X i).val) Q w F univ r)
abbrev grate (F:I→ Mood (Site n) D T→E)(t:Pearl)(i:I) (x:Mood (Site n) D T):= (t.val) • F i x
include h
lemma cared(t:Pearl): Team L (terr _) V (fun i=>(X i).val) Q w (grate F t) univ r:=by
 refine ⟨h.positive,h.placed,fun i u=>?_,h.mass⟩; obtain ⟨g,v,l,s,w,H,f,G,m⟩:=h.allowed i u; refine ⟨g,v,fun i p=>?_ ,fun i p=> Subalgebra.smul_mem _ (s i p) _, continuousOn_const.smul w,H,fun a b c d=> congrArg (fun x:E=>t.val • x) (f a b c d),fun t=> G t, fun y x p=> (map_smul ..).trans (congrArg _ (m y x p))⟩
 rw [grate,L.scale]; exact (mul_le_of_le_one_left (Bell.starL _) (by rw [Real.norm_of_nonneg t.property.1]; exact t.property.2)).trans (l i p)
omit h in
private lemma product_p {X Y:Type*}[TopologicalSpace X][TopologicalSpace Y][CommMonoid Y][ContinuousMul Y]{S: Finset I}{f:I→X→Y}{x:X}(p:∀ i∈S,ContinuousAt (f i) x):ContinuousAt (fun x=>∏ i∈S,f i x) x:=by
 induction S using Finset.induction_on with| empty=> simp_rw [prod_empty]; exact continuousAt_const| insert i S v ih=> simp_rw [prod_insert v]; exact (p i (mem_insert_self ..)).mul (ih fun j t=>p j (mem_insert_of_mem t))
lemma the_p (x:D)(p:Finset I):Continuous fun t:Pearl=> airport V (grate F t) p x:=by
 letI : NormedAlgebra ℚ E := NormedAlgebra.restrictScalars ℚ ℝ E
 let U(t:Pearl)(i):=∏ j∈p, secA (grate F t j i)
 have he(t:Pearl):Manifest V (U t) _ _ _:=crewW (cared h t) (subset_univ p)
 let T'(i:Pearl × (Site n→T)):= barF V (x,i.2); let W(i:Pearl× (Site n→T)):= (U i.1 (x,i.2))
 refine Phase.net_cont (fun i:Pearl× (Site n→ T)=>T' i • W i) _ ?_
 apply (soft (v:=T') (f:=W) (fun _=> sails_nonneg ..) (fun i p=> (L.normF _).trans ((he i.1).avail (x,i.2) p)) (V.ct.comp (continuous_const.prodMk continuous_snd)) ?_).weighted
 rintro ⟨i,t⟩ g; unfold W U; exact product_p (S:=p) (f:=fun j q=>secA (grate F (q:Pearl ×(Site n→T)).1 j (x,q.2))) fun j _=> (exp_continuous.continuousAt.comp (((continuous_subtype_val.comp continuous_fst).continuousAt).smul (((h.allowed j (mem_univ _)).giftT.family V.ct g).comp (f:=fun q:Pearl× (Site n→T)=>(x,q.2)) (continuous_const.prodMk continuous_snd).continuousAt))).sub continuousAt_const
lemma origin_v(p:Y n)(x:D): parcelF V X (grate F 0) p x=0:=by
 let U:=airport V (grate F 0); let S:=Xi X U; letI : NormedAlgebra ℚ E:= NormedAlgebra.restrictScalars ℚ ℝ E
 have hh(i:Y n): S i x=0:=by
    unfold S Xi; rw [bank_p]; apply sum_eq_zero; intro T p; obtain ⟨a,hA⟩:=(slate_s p).1; unfold U airport motor; have hv(i:Mood (Site n) D _):(∏ j∈T,secA (grate F 0 j i))=0:=prod_eq_zero hA (by simp [secA,grate]); simp only [hv,bet,smul_zero,integral_zero]
 change jingle (fun i=>S i x) p=_; unfold jingle; simp only [hh]; simp [guava]
variable(t:Ready (stern ∘ X) 0 (moreK w) (α+1) γ δ k)(p:0≤α)(hq:0<v)(hg:γ*(1-k)⁻¹ ≤ v)(hu:k'<1)(hn:degreePrice 0 v 1 ≤ k')
include t p hq hg hu hn
lemma tough(X':Y n)(x:D): Continuous fun k:Pearl=>parcelF V X (grate F k) X' x:=by
 let P:=CoinX X (moreK w); let C (k:Pearl):=Xi X (airport V (grate F k)); have he:=desks h t p hq hg hu hn; let Xb(i:Clusters (Y n))(k:Pearl):=strictX i X' (C k) x; change Continuous fun k=> ∑' i,Xb i k; apply continuous_tsum (u:=fun i=>wageA i X' P) _ (τ_w X' he p)
 · intro i k; exact (L.normF _).trans ((dues X' i (dimeF (cared h k))).owns x)
 intro i; by_cases g: X'=tideU i; swap; · simp only [Xb,strictX,if_neg g]; exact continuous_const
 unfold Xb strictX; simp only [if_pos g, guava,C,Xi,bank_p]; exact continuous_const.smul (continuous_finsetProd _ fun a _=> continuous_finsetSum _ (fun j _=>the_p h x j))
omit t p hq hg hu hn h
lemma simpleL (F V:Pearl→ E)(g: Continuous F)(p:Continuous V)(h:F 0= V 0)(v:∀ x,exp (F x)=exp (V x))(x:Pearl): F x=V x:=by
 let D(x:Pearl):=F x-V x; let P:= {x| D x=0}; have he:Continuous D:=g.sub p
 letI : NormedAlgebra ℚ E:= NormedAlgebra.restrictScalars ℚ ℝ E
 let U:= ContinuousLinearEquiv.refl ℝ E; have hv:HasStrictFDerivAt exp U.toContinuousLinearMap (0:E):=hasStrictFDerivAt_exp_zero; let Y:=hv.toOpenPartialHomeomorph _
 have hh : IsOpen P:=by
    refine isOpen_iff_mem_nhds.mpr fun q (l:D q=0)=>?_ ; filter_upwards [(Y.open_source.preimage he).mem_nhds (x:=q) (show D q∈Y.source from l.symm ▸ hv.mem_toOpenPartialHomeomorph_source)] with k g; apply Y.injOn g hv.mem_toOpenPartialHomeomorph_source; change exp (F k-V k)=exp _; rw [sub_eq_add_neg,exp_add,v,←exp_add,add_neg_cancel]
 have hy:= isClopen_iff.mp (show IsClopen P from ⟨isClosed_eq he continuous_const,hh⟩); rcases hy with l|l; exact absurd (show (0:Pearl)∈P from sub_eq_zero_of_eq h) (by simp [l]); exact sub_eq_zero.mp (show x∈P from l.symm ▸ Set.mem_univ x)
include t p hq hg hu hn h
-- wind camp using relative hom along amplitude extension
abbrev pathMar(V:Cabin μ L)(x:D)(F:I→ Mood (Site n) D T→ E) (t:Pearl):=motor V (fun x=>exp ((t.val) • (∑ i,F i x))) x
set_option maxHeartbeats 600000 in
lemma lyricX(Z:E→ₐ[ℝ] E)(g:Continuous Z) (x y:D)(u:∀ t,Z (pathMar V x F t)=pathMar V y F t): Z (∑ i:Y n,parcelF V X F i x)=∑ i:Y n,parcelF V X F i y:=by
 let Y'(x:D)(s:Pearl):=∑ i:Y n,parcelF V X (grate F s) i x; have hm(j): Z (pathMar V x F j)=pathMar V y F j:=u j
 have hk(z): Continuous (Y' z):=continuous_finsetSum _ (fun i _=> tough h t p hq hg hu hn i z)
 have hh(s z): pathMar V z F s=exp (Y' z s):=by unfold pathMar; simp_rw [smul_sum]; exact mortar (cared h s) t p hq hg hu hn z
 letI : NormedAlgebra ℚ E:= NormedAlgebra.restrictScalars ℚ ℝ E
 have hp:= simpleL (Z∘Y' x) (Y' y) (g.comp (hk x)) (hk y) (by unfold Y'; simp only [origin_v h,Function.comp_apply,sum_const_zero,map_zero]) (fun s=>by rw [Function.comp_apply,←map_exp Z g,←hh,←hh,hm] ) 1 -- tune
 have hv:F=grate F 1:=funext fun i=>funext fun x=>(one_smul ..).symm; change Z (Y' x 1)=Y' y 1 at hp; unfold Y' at hp; rw [←hv] at hp; exact hp
end YM.CF.Gas
