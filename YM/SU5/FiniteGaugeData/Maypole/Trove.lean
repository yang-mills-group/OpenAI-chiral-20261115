import YM.SU5.FiniteGaugeData.Maypole.Otium
/-! # Long gaps. Eu point operations, joins and priced measures -/
set_option autoImplicit false
set_option maxHeartbeats 340000
set_option synthInstance.maxSize 16000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Vp
open Function Filter Metric Set MeasureTheory OS OS.Semigroup Mink General Lorentz Real
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
variable (G:Canopy H α)(V:OS.Semigroup H timeAxis)(w:H)(hw:∀ x:E4,M V x w=w)(e:Mink.Ray)
local notation "T"=>timeAxis
local notation "Ψ"=> Item G.Chip
open Flute Haven
local notation "P"=> hourE
local notation "z'"=> Icc (-1:ℝ) 1
local notation "A₀"=> G.dep
local notation "θ"=> G.grade
local notation "Spel" => Marked G
section Fraught
variable (L:List (Item G.Chip))(F:∀ s:ℝ,|s|≤1→ ahead T (Marked G (hourE s e) L))
private lemma cprice {X:Type*}[TopologicalSpace X]{U:Set X}(C:X→H.Op)(F:X→ℝ) (p:IsCompact U)(h:ContinuousOn F U)(t: ∀ x∈U, ‖C x‖≤ F x):∃ K:ℝ,0≤K∧∀ x∈U,‖C x‖≤K:=by
 obtain ⟨H,hH⟩:= (p.image_of_continuousOn h).bddAbove; exact ⟨max H 0,le_max_right ..,fun x e=> (t x e).trans ((hH (Set.mem_image_of_mem F e)).trans (le_max_left ..))⟩
private lemma cpr {X:Type*}[TopologicalSpace X]{U:Set X}(C:X→H.Op)(p:IsCompact U)(h:ContinuousOn C U):∃ K:ℝ,0≤K∧∀ x∈U,‖C x‖≤K:=cprice C (fun x=> ‖C x‖) p h.norm fun _ _=> le_rfl
private lemma liveP(e:Ray): Continuous (fun u=> hourE u e):=(spins e).comp (show Continuous εB from Real.continuous_arctan.neg)
private lemma contAngle(x:E4): Continuous (fun s=> Mink.General.walk (hourE s e).val x):=by
    let u:=fun s:ℝ=> circleB e (εB s); have he:Continuous u:= by unfold u circleB εB; fun_prop
    exact he.clm_apply continuous_const -- tune
private lemma stampC (i:Item G.Chip): ∃ Z:ℝ,0≤Z∧∀ s:ℝ, |s|≤1→ ‖stamps V G.dep (cir (hourE s e) G i)‖≤ Z:=by
 let A(s:ℝ):=stamps V G.dep (cir (hourE s e) G i); let U(s):= G.dep (G.βE (hourE s e) i.1); let W(s):= SEP timeAxis (walk (hourE s e).val i.2); have hv: Continuous U:= (G.flash i.1.1).continuous.comp (((G.P i.1.1).Ec.comp (liveP e)).clm_apply continuous_const);
 obtain ⟨u,hα,g⟩:= cprice A (fun s=> ‖U s‖) (isCompact_Icc (α:=ℝ) (a:= -1) (b:=1)) hv.norm.continuousOn (fun s v=> ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x=> vcost V x (W s).val (U s)); exact ⟨u,hα,fun i p=>g i (abs_le.mp p)⟩ -- args vcost
private lemma chron(x:Item G.Chip): Continuous (fun s=> timesA timeAxis (cir (hourE s e) G x)):=  (show Continuous (fun i:E4=> i T) from (by fun_prop)).comp (contAngle e x.2)
private lemma priceL(s:ℝ→ℝ)(n:ℕ)(p:Continuous s)(q:∀ z:ℝ,|z|≤1→0<s z):∃ Z:ℝ,0≤Z∧ ∀ z:ℝ,|z|≤1→ ‖leanX V (s z) n‖≤ Z:=by
 obtain ⟨u,h,H⟩:= cpr (fun z=>leanX V (s z) n) (isCompact_Icc (α:=ℝ) (a:= -1) (b:=1)) (fun i h=> ((Bokeh V n _ (OS.Semigroup.dur.mpr (Real.toNNReal_pos.mpr (q i (abs_le.mpr h))))).continuousAt.comp (x:=i) (f:=fun z=>OS.Semigroup.duration (s z).toNNReal) ((show Continuous (fun z=> OS.Semigroup.duration (s z).toNNReal) from (by unfold OS.Semigroup.duration; fun_prop))|>.continuousAt)).continuousWithinAt) -- braces `|>` tune
 exact ⟨u,h,fun i p=> H i (abs_le.mp p)⟩
private lemma gapPrice(i j:Item G.Chip)(V':∀ t:ℝ,|t|≤1 → timesA T (cir (P t e) G i)< timesA T (cir (P t e) G j)):∃ v:ℝ, 0≤ v ∧ ∀ t:ℝ,|t|≤1 → ‖gapK V G.grade (cir (P t e) G i) (cir (P t e) G j)‖ ≤ v:=by
 let x(s):= timesA T (cir (P s e) G j)- timesA T (cir (P s e) G i); obtain ⟨v,h,u⟩:=priceL V x (θ i.1+θ j.1) ((chron G e j).sub (chron G e i)) (fun i h=>sub_pos.mpr (V' i h)); exact ⟨v,h,fun i q=>u i q⟩
include F
private lemma taxing : ∃ Z:ℝ,0≤Z ∧ ∀ s:ℝ,|s|≤1→ ‖legis V A₀ θ (Marked G (hourE s e) L)‖ ≤ Z:=by
 cases L with
 | nil=>exact ⟨1, zero_le_one,fun _ _=> ContinuousLinearMap.norm_id_le⟩ -- tune
 | cons x L=>
    induction L generalizing x with
    | nil=> obtain ⟨z,h,q⟩:=stampC G V e x; exact ⟨z,h,fun t p=> by unfold Marked legis; rw [List.map_singleton,solitary]; exact q t p⟩
    | cons y L ih=>
       have he(u:ℝ)(p:|u|≤1): ahead T (Spel (P u e) (y::L)):= (List.pairwise_cons.mp (show List.Pairwise _ (cir (P u e) G x::Spel (P u e) (y::L)) from F u p)).2; obtain ⟨v,e',hv⟩:=ih y he; obtain ⟨w,p,W⟩:=stampC G V e x; have hx(t:ℝ)(v:|t|≤1): timesA T (cir (P t e) G x)<timesA T (cir (P t e) G y):=(List.pairwise_cons.mp (show List.Pairwise _ (cir (P t e) G x::Spel (P t e) (y::L)) from F t v)).1 _ List.mem_cons_self
       obtain ⟨X,g,z⟩:=gapPrice G V e x y hx; refine ⟨w*X*v,by positivity,fun i p=>?_⟩; unfold legis Marked; rw [List.map_cons,List.map_cons,twoF]; refine (norm_mul_le ..).trans (mul_le_mul ?_ (hv i p) (norm_nonneg _) (by positivity)); exact (norm_mul_le ..).trans (mul_le_mul (W i p) (z i p) (norm_nonneg _) (by positivity))
omit F
lemma FacePrice(v:goodF T L): ∃ z:ℝ,0≤z∧ ∀ t:ℝ, |t| ≤ 1→ ‖face V w A₀ θ 0 (Spel (P t e) L)‖ ≤ z:=by
 let F':=fun t (p:|t|≤1)=>posit G t e v p; obtain ⟨u,h,U⟩:=taxing G V e L (fun i h=>(F' i h).1); cases L with
 | nil=> exact ⟨‖w‖,norm_nonneg _, fun _ _=>le_rfl⟩ -- defeq?
 | cons i L=>
    let z(s:ℝ):=cir (P s e) G i; let H:=timesA T ∘ z; obtain ⟨w',v,H'⟩:= priceL V H (0+θ i.1) (chron G e i) (fun u h=>(F' u h).2 _ List.mem_cons_self); refine ⟨w'*u*‖w‖,by positivity,fun t h=> le_trans ((Front V A₀ θ 0 (Spel (P t e) (i::L))).le_opNorm w) ?_⟩; refine mul_le_mul_of_nonneg_right ((norm_mul_le ..).trans (mul_le_mul ?_ (U t h) (norm_nonneg _) v)) (norm_nonneg _); rw [Marked,List.map_cons,budgetFoot,sub_zero]; exact H' t h
lemma RolePrice(v:goodB T L): ∃ z:ℝ,0≤z∧∀ t:ℝ,|t|≤1→ ‖role V w A₀ θ 0 (Spel (P t e) L)‖ ≤ z:=by
 let F':=fun t (p:|t|≤1)=>negateT G t e v p; obtain ⟨u,h,U⟩:=taxing G V e L (fun i h=>(F' i h).1); cases L using List.reverseRecOn with
 | nil=>refine ⟨‖w‖,norm_nonneg _,fun t h=>?_⟩; change ‖star ((1:H.Op)*1) w‖≤_; rw [mul_one,star_one]; exact le_rfl
 | append_singleton L i=>
    let z(s:ℝ):=cir (P s e) G i; let H(s):=0-timesA T (z s); obtain ⟨w',v',H'⟩:= priceL V H (θ i.1+0) (continuous_const.sub (chron G e i)) (fun u h=>sub_pos.mpr ((F' u h).2 (z u) (List.mem_map_of_mem (by simp)))); refine ⟨u*w'*‖w‖,by positivity,fun t h=> le_trans ((star (Back V A₀ θ 0 (Spel (P t e) (L++[i])))).le_opNorm w) ?_⟩; rw [norm_star]; refine mul_le_mul_of_nonneg_right ((norm_mul_le ..).trans (mul_le_mul (U t h) ?_ (norm_nonneg _) (by positivity))) (norm_nonneg _); rw [Marked,List.map_append,List.map_singleton,budgetBack]; exact H' t h
end Fraught
end Folio
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Vp
