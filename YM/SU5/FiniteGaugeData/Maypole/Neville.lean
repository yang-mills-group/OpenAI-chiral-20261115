import YM.SU5.FiniteGaugeData.Maypole.Piquant
/-! # Long gaps. Eu point operations, joins and priced measures -/
set_option autoImplicit false
set_option maxHeartbeats 340000
set_option synthInstance.maxSize 16000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Vp
open Function Filter Metric Set MeasureTheory OS OS.Semigroup Mink General Lorentz Complex
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace ComplexOrder
open Poin Celeritas Land Leal Breve Poin.Gem
open Boundary Probe
namespace Folio
variable {H:Hilbert}{a:Axis}(S:OS.Semigroup H a)(Ω:H)(hp:∀ x:E4,M S x Ω=Ω)
-- chronology.Braces
variable {α:Type}(A:α→H.Op)(ν:α→ℕ)
local notation "Ι"=> Item α
local notation "Ω°"=> wordValue S Ω A ν
local notation "Φ"=> legis S A ν
local notation "δ"=> gapK S ν
local notation "η"=> timesA a
local notation "Γ"=> leanX S
namespace Haven
variable (p:E4)(t:ℝ) (L:List (Item α))
-- buy clearance all Ray spin drags
lemma SEP_t(b:Axis)(q:ℝ): SEP b (q • basis b)=0:=Subtype.ext (by change q • basis b-(q • basis b:E4) b • basis b=0; simp)
def ZoomTime (a:Axis)(t:ℝ)(x:E4): E4:= x+(t-1) • ((x a) • basis a)
def Zoom(a:Axis)(t:ℝ)(x:Ι):Ι:=(x.1,ZoomTime a t x.2)
def deep(a:Axis)(v:List (Item α)):= v.Pairwise (fun x y=> 2*‖SEP a (y.2-x.2)‖<timesA a y-timesA a x)
abbrev goodF(a:Axis)(v:List (Item α)):= deep a v∧ (∀ i∈v, 2*‖SEP a i.2‖< timesA a i)
abbrev goodB(a:Axis)(v:List (Item α)):= deep a v∧ (∀ i∈v, 2*‖SEP a i.2‖< -(timesA a i))
lemma AheadL(h:deep a L): ahead a L:=h.imp (fun {i j}(p:2*‖SEP a (j.2-i.2)‖<timesA a j-timesA a i)=>by apply sub_pos.mp; exact (show 0≤ 2*‖SEP a (j.2-i.2)‖ from by positivity).trans_lt p)
lemma inF(h:goodF a L): LaneE a 0 L:=⟨AheadL L h.1,fun i p=>(show 0≤2*‖SEP a i.2‖ from by positivity).trans_lt (h.2 i p)⟩
lemma inB(h:goodB a L): BackE a 0 L:=⟨AheadL L h.1,fun i p=> neg_pos.mp ((show 0≤2*‖SEP a i.2‖ from by positivity).trans_lt (h.2 i p))⟩
lemma hours_x(i:Item α): timesA a (Zoom a t i)= t*timesA a i:=by unfold Zoom timesA ZoomTime; simp; ring
lemma zoom_p(x:Item α): SEP a (Zoom a t x).2=SEP a x.2:=by unfold Zoom ZoomTime; rw [map_add,map_smul,SEP_t]; simp
lemma gratis (i:Item α) : stamps S A (Zoom a t i)=stamps S A i:=by unfold stamps coreSp; rw [zoom_p]; rfl
lemma onOrbit (x y:Item α): gapK S ν (Zoom a t x) (Zoom a t y)= Γ (t*(η y-η x)) (ν x.1+ν y.1):=by unfold gapK; change Γ (η (Zoom a t y)-η (Zoom a t x)) (ν x.1+ν y.1)=_; rw [hours_x,hours_x,mul_sub]
private lemma verge (B x:ℝ)(p:0<x): ∀ᶠ t:ℝ in atTop, B<t*x :=(tendsto_id.atTop_mul_const p).eventually (eventually_gt_atTop _)
lemma deeply (u:ahead a L): ∀ᶠ t:ℝ in atTop, deep a (L.map (Zoom a t)):=by
 induction L with
 | nil=> exact Eventually.of_forall fun _=> List.Pairwise.nil
 | cons x L ih=>
    obtain ⟨hu,hh⟩:=List.pairwise_cons.mp u; classical
    have hf:∀ᶠ t:ℝ in atTop,∀ i∈L.toFinset,2*‖SEP a i.2-SEP a x.2‖ < t*(η i-η x):= (Finset.eventually_all _).mpr (fun i h=>verge _ _ (sub_pos.mpr (hu i (List.mem_toFinset.mp h))))
    filter_upwards [hf, ih hh] with t h k; refine List.pairwise_cons.mpr ⟨?_,k⟩; intro i e; obtain ⟨i,f,rfl⟩:= List.mem_map.mp e; rw [map_sub,zoom_p,zoom_p,hours_x,hours_x,←mul_sub]; exact h _ (List.mem_toFinset.mpr f)
lemma amen (u:LaneE a 0 L): ∀ᶠ t:ℝ in atTop, goodF a (L.map (Zoom a t)):=by
 classical
 have he:∀ᶠ t in atTop,∀ i∈L.toFinset,2*‖SEP a i.2‖ < t*η i:= (Finset.eventually_all _).mpr (fun i h=> verge _ _ (u.2 i (List.mem_toFinset.mp h))); refine (he.and (deeply L u.1)).mono ?_; intro t v; refine ⟨v.2,fun i p=>?_⟩; obtain ⟨x,q,rfl⟩:= List.mem_map.mp p; rw [zoom_p,hours_x]; exact v.1 x (List.mem_toFinset.mpr q)
lemma τOdd (K:α→α)(p:goodF a L): goodB a (oddSpin L a K):=by
 refine ⟨List.pairwise_reverse.mpr (List.pairwise_map.mpr (p.1.imp (fun {x y} h=>?_))), fun i v=>?_ ⟩; swap; · obtain ⟨x,h,rfl⟩:= List.mem_map.mp (List.mem_reverse.mp v); rw [movetime,neg_neg, mirrorsK,Θv]; exact p.2 x h
 rw [movetime,movetime,neg_sub_neg,map_sub,mirrorsK,mirrorsK,Θv,Θv,norm_sub_rev]; rw [map_sub] at h; exact h
lemma gapAnalytic(s:ℝ)(q:0<s)(n:ℕ) (p:0<t): AnalyticAt ℝ (fun x:ℝ=> leanX S (x*s) n) t:=by
 let u:= t*s; have hx:0<u:=mul_pos p q; let L(x:ℝ):ℂ:= ↑(x*s); let B:= parabola S n; have hl:AnalyticAt ℝ L t:= (Complex.ofRealCLM.analyticAt _).comp ((analyticAt_id (𝕜:=ℝ)).mul analyticAt_const); have hb:AnalyticAt ℂ B (L t):= (Bokeh S n _ (show L t∈OS.Semigroup.inside from hx)); refine ((show AnalyticAt ℝ B (L t) from hb.restrictScalars).comp hl).congr ?_; filter_upwards [Ioi_mem_nhds p] with x h; unfold leanX Par Function.comp B L OS.Semigroup.duration; rw [Real.coe_toNNReal (x*s) (mul_nonneg (Set.mem_Ioi.mp h).le q.le)]
lemma votary(u: LaneE a 0 L) (p:0<t) : AnalyticAt ℝ (fun x:ℝ=>face S Ω A ν 0 (L.map (Zoom a x))) t :=by
 let Z(x:ℝ)(L:List (Item α)):= L.map (Zoom a x); have he(y:List (Item α))(p₁:ahead a y): AnalyticAt ℝ (fun x:ℝ=> Φ (Z x y)) t:=by
    cases y with | nil=> exact analyticAt_const| cons i y=> induction y generalizing i with
    | nil=> unfold legis; simp_rw [Z,List.map_cons,List.map_nil,solitary,gratis]; exact analyticAt_const
    | cons j L ih=>
       unfold legis; simp_rw [Z,List.map_cons,twoF]; obtain ⟨k,v⟩:= List.pairwise_cons.mp p₁; simp_rw [gratis, onOrbit]; exact AnalyticAt.mul (analyticAt_const.mul (gapAnalytic S t _ (sub_pos.mpr (k _ List.mem_cons_self)) _ p)) (ih j v)
 cases L with| nil=> exact analyticAt_const| cons i L=>
 let N:= he (i::L) u.1; let F:= ContinuousLinearMap.apply ℂ H.space Ω; apply (F.restrictScalars ℝ |>.analyticAt _).comp (AnalyticAt.mul (show AnalyticAt ℝ (fun x:ℝ=>billBefore S ν 0 0 (Z x (i::L))) t from ?_) N); simp_rw [Z,List.map_cons,budgetFoot,hours_x,sub_zero]; exact gapAnalytic S t _ (u.2 i List.mem_cons_self) (0+ν i.1) p
abbrev BudgeSet(A:α→H.Op)(ν:α→ℕ):Set H:={x|∃ v:List (Item α),goodF a v∧ face S Ω A ν 0 v=x}
lemma sweep (q:Dense (Submodule.span ℂ (John S Ω A ν):Set H)) : Dense (Submodule.span ℂ (BudgeSet S Ω A ν): Set H) :=by
 refine secTo _ (fun z p=>?_); suffices he:∀ x∈John S Ω A ν,inner ℂ z x=0 by
    let F:=innerSL ℂ z; let C:= (Submodule.span ℂ (John S Ω A ν)); have hv:C≤ F.ker:=Submodule.span_le.mpr he; exact inner_self_eq_zero.mp (show z∈ F.ker from closure_minimal hv F.isClosed_ker (q z))
 intro i v; obtain ⟨L,u,rfl⟩:=v; let A_:=face S Ω A ν 0; let f(t:ℝ):= inner ℂ z (A_ (L.map (Zoom a t))); let S₀:= Set.Ioi (0:ℝ); have hf:AnalyticOnNhd ℝ f S₀:=fun x q=> ((innerSL ℂ z).restrictScalars ℝ).analyticAt _|>.comp (votary S Ω A ν x L u q); obtain ⟨N,h⟩:=eventually_atTop.mp (amen L u); have hh:f 1=0:=by
   have hw:N< |N|+1:= lt_of_le_of_lt (le_abs_self _) (lt_add_one _); have he:0< |N|+1:=by positivity;
   refine hf.eqOn_of_preconnected_of_eventuallyEq (g:=(fun _=>0)) analyticOnNhd_const (convex_Ioi _).isPreconnected (Set.mem_Ioi.mpr he) ?_ (Set.mem_Ioi.mpr zero_lt_one) -- tune
   filter_upwards [Ioi_mem_nhds hw] with t q; exact p _ ⟨_,h t (Set.mem_Ioi.mp q).le,rfl⟩
 have hv:(L.map (Zoom a 1))=L:=by
    have he:Zoom a 1=id (α:=Item α) := by funext x; simp [Zoom,ZoomTime]
    rw [he,List.map_id]
 apply Eq.trans ?_ hh; unfold f; rw [hv] -- tune
end Haven
end Folio
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Vp
