import YM.SU5.FiniteGaugeData.Celeritas.Eclipse
set_option autoImplicit false
set_option maxHeartbeats 480000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Celeritas
open OS OS.Semigroup Spectral Lattice Function Filter Metric Mist.Utah Complex Set MeasureTheory MeasureTheory.Measure Boundary Probe NormedSpace InnerProductSpace
open scoped Topology NNReal ENNReal InnerProductSpace ComplexOrder BigOperators
set_option quotPrecheck false
namespace Land
variable {K:Axis→Hilbert}(W:∀ a:Axis,OS.Semigroup (K a) a)(Ω:(i:Axis)→(K i).space) (U:Set (Shrine K)) (a b:Axis)
variable (A:Shrine K)(p:Bool)
local notation "J"=> W a
local notation "P"=> K a
variable (Oa:∀ z:E4,(W a).unit.translation z (Ω a)=Ω a)
-- little reflection Boo. pick * separately.
abbrev coup (b:Bool)(F:(K a).Op) := if b then star F else F
abbrev soup (A:Shrine K)(p:Bool)(y:E4): (K a).space:=coup a p (orbit_on W a y A) (Ω a)
variable (v:(K a).space)
abbrev Seance (p:Bool):Prop:= ∀ v:(K a).space,(∀ L:Shrine K,L∈ U→∀ y:E4,inner ℂ v (soup W Ω a L p y)=0)→ v=0
lemma tales (e:Seance W Ω U a p) {G:Set (Shrine K)}(q:U⊆G): Seance W Ω G a p := fun x v=> e x fun L u=> v L (q u)
local notation "η" => soup W Ω a
local notation "G" x:max=> leg (W a) x
include Oa
lemma soup_Plant (y:E4):soup W Ω a A p y= leg (W a) y (coup a p (K:=K) (A.f a) (Ω a)):=by
 unfold soup orbit_on coup; split; rw [opt_star]; unfold opt; simp_rw [mul_apply_eq_comp, leg_G J (-y) (Ω a) Oa]; unfold opt; simp_rw [mul_apply_eq_comp,leg_G J (-y) (Ω a) Oa]
lemma sit (t:ℝ)(y:E4): soup W Ω a A p (jeer a y t)=soup W Ω a A p y:=by rw [soup_Plant W Ω a A p Oa, soup_Plant W Ω a A p Oa,jeer,leg_add,leg_veil,mul_one] -- arg order
variable (pB:b≠a) (L:Cinema (W a))
include L pB
local notation "F"=>fieldQ b a pB.symm
local notation "C"=> (W a).E 1
/-- any v annihilating on some **open set** of displacements (including distant) annihilates on whole. -/
lemma starting (y:E4)(u:ℝ)(h:∀ᶠ t:ℝ in 𝓝 u, inner ℂ v (C ((η) A p (jeer b y t)))=0) : inner ℂ v (C ((η) A p y))=0:=by
 let z:= (η) A p y; let O:= cup J 1 L F (le_of_eq (field_v ..)); let f(t:ℂ):= inner ℂ v (O t z); have he(t:ℝ): f t=inner ℂ v (C ((η) A p (jeer b y t))):=by
    have ht: (η) A p (jeer b y t)= (W a).U (t • F) z:=by unfold z; rw [soup_Plant W Ω a A p Oa,soup_Plant W Ω a A p Oa,jeer,add_comm y,leg_add,leg_rook W b a pB.symm]; rfl
    unfold f O; rw [ht, credit_h J F 1 t L _ zero_lt_one, show (W a).U _* (C) = _ from (show _ from ((W a).independent 1 (t • F)).symm)]; rfl
 have hv:AnalyticOnNhd ℂ f (lanes (↑(1:ℝ≥0):ℝ)):=fun i p=> (innerSL ℂ v).analyticAt _ |>.comp ((ContinuousLinearMap.apply ℂ (P).space z).analyticAt _ |>.comp (cup_A J F 1 L _ i p))
 have hf:Set.EqOn f (fun _=>0) (lanes (↑(1:ℝ≥0):ℝ)):=hv.eqOn_of_preconnected_of_frequently_eq analyticOnNhd_const ( (lane_v _).isPreconnected) (show (u:ℂ)∈ lanes (↑(1:ℝ≥0):ℝ) from (by simp [lanes])) ?_
 swap; · intro k; have hp:Tendsto ((↑):ℝ→ℂ) (𝓝[>] u) (𝓝[≠] (↑u:ℂ)):=by apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ continuous_ofReal.continuousAt.continuousWithinAt; filter_upwards [self_mem_nhdsWithin] with r q; exact fun t=>(Set.mem_Ioi.mp q).ne' (ofReal_injective (show (r:ℂ)=(u:ℂ) from t))
         obtain ⟨r,q,w⟩:= ( (hp.eventually k).and (nhdsWithin_le_nhds h)).exists; exact q ((he r).trans w)
 rw [← show jeer b y 0=y from (by simp [jeer]),← he]; exact hf (show _∈ _ from (by simp [lanes])) -- rewrite replacing y even jeer errors
-- advance to chosen a cost
local notation "Y"=> E4
abbrev Shift (p:Bool)(x:ℝ):ℝ:= if p then -x else x
local notation "ℍ"=> Shift p
abbrev Want (p:Bool)(d o:ℝ)(y:E4):= y a=o ∧ Shift p (y b)> d
-- height o=A-dependent; ref.L
variable (t:Shrine K→ℝ)(D:Shrine K→ℝ)(q:Seance W Ω U a p)
include q
lemma spatial_s (v:(K a).space)(h:∀ L:Shrine K,L∈ U→∀ y:E4,Want a b p (D L) (t L) y→ inner ℂ v ((W a).E 1 ((η) L p y))=0) : v=0 :=by
 apply ((W a).heat_faithful 1 _); apply q; intro L' z y; rw [←ContinuousLinearMap.adjoint_inner_right,(W a).sym]; let m:=t L'-y a; rw [← sit W Ω a L' p Oa m y]; let y':=jeer a y m; have hp:y' a=t L':=by unfold y'; rw [top_a]; ring
 let k:= D L'; -- choose sign.T
 by_cases e:p; swap -- p Bool syntax Bool as prop coerc Lean.L
 · apply starting W Ω a b L' p Oa v pB L y' (D L'+1-y' b); filter_upwards [lt_mem_nhds (show D L'-y' b<D L'+1-y' b by linarith)] with i hi; refine h L' z _ ⟨(jeer_other b a y' i pB).trans hp,?_⟩; have ht:D L'-y' b< i :=hi; rw [Shift,if_neg e,top_a]; linarith
 apply starting W Ω a b L' p Oa v pB L y' (-D L'-1-y' b); filter_upwards [gt_mem_nhds (show -D L'-1-y' b < - D L'-y' b by linarith)] with i hi; refine h L' z _ ⟨(jeer_other b a y' i pB).trans hp,?_⟩; rw [Shift,if_pos e,top_a]; linarith only [show i< - D L'-y' b from hi]
#print axioms spatial_s
omit q
variable (v':Seance W Ω U a true)(v_: Seance W Ω U a false)(hV: Cleaning W Ω a b U)(l:Cinema (W b))
include v' v_ hV l
-- cone marker localized along coordinate wedge. no boost germs. 
omit Oa pB L v' v_ hV l in
private lemma push_inner {H:Hilbert}(f g:H.Op)(x y:H)(h:inner ℂ y (f x)=inner ℂ y (g x)): inner ℂ (f x-g x) y=0:= by rw [inner_sub_left,← inner_conj_symm,←inner_conj_symm (g x) y]; rw [h,sub_self] -- tune
set_option maxHeartbeats 280000 in
lemma vehicle (A B:Shrine K)(p:A.t a=0)(h:B.t a=0)(k:A∈U)(v:B∈U)(o y:E4)(e:o a=y a)(t:ℝ)(yP:|t|<y b-B.t b-(o b+A.t b)) : Commute (orbit_on W a o A) (orbit_E W a y B t):= by
 obtain ⟨r,hp,hq⟩:= exists_between yP; let V:= orbit_on W a o A*orbit_E W a y B t; let V':= orbit_E W a y B t*orbit_on W a o A; have hr:0<r:=(abs_nonneg _).trans_lt hp; let X(F0: Shrine K):=o a-1- F0.t a; let Y'(F0: Shrine K):=o a+1+ F0.t a; let z(F0:Shrine K):= -(o b-A.t b)+F0.t b; let Z(F0:Shrine K):= r + y b+B.t b+ F0.t b
 ext1 i; change V i=V' i; apply ext_inner_left ℂ; intro j; have he(L' R:Shrine K)(x y':E4)(t':Want a b true (z L') (X L') x)(p':Want a b false (Z R) (Y' R) y')(u:L'∈U)(k':R∈U): let u:=(W a).E 1 (soup W Ω a L' true x); let z:=(W a).E 1 (soup W Ω a R false y'); inner ℂ u (V z)=inner ℂ u (V' z):=by
    intro u' z'; refine boulder W Ω U a b L' A B R o y x y' t ⟨p,h,e,?_,?_⟩ r hr ⟨?_,hq.le,?_⟩ pB hp hV l ?_
    · rw [t'.1]; unfold X; ring
    · rw [p'.1]; unfold Y'; ring
    · linarith only [show -(o b-A.t b)+ ↑(L'.t b)< -(x b) from t'.2]
    · linarith only [show r+y b+↑(B.t b)+↑(R.t b)< y' b from p'.2]
    intro i; fin_cases i <;> simp [choice4, *] -- tune
 -- extend right output maps via adjoint. Orientation choose fixed right. Test `he L ...` implies for all j then extend right.
 have hv(R:Shrine K)(w:R∈U)(y':E4)(e:Want a b false (Z R) (Y' R) y'):let x:=(W a).E 1 (soup W Ω a R false y'); V x=V' x :=by
    intro v; apply sub_eq_zero.mp; apply spatial_s W Ω U a b true Oa pB L X z v' (V v-V' v); intro L p x t; exact push_inner V V' v _ (he L R x y' t e p w)
 rw [← ContinuousLinearMap.adjoint_inner_left,← ContinuousLinearMap.adjoint_inner_left V' i]; -- rewrites pattern likely adjoint? lemma check
 suffices (V.adjoint-V'.adjoint) j=0 from (congrArg (inner ℂ · i) (sub_eq_zero.mp this))
 apply spatial_s W Ω U a b false Oa pB L Y' Z v_; intro R q x z; rw [_root_.sub_apply,inner_sub_left, ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left,hv R q x z,sub_self] -- hv let ▸
#print axioms vehicle
end Land
end YM.CF.Buffered.Afterglow.Hierarchy.Celeritas
