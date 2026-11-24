import YM.SU5.FiniteGaugeData.Celeritas.ChargeH
import YM.SU5.FiniteGaugeData.Celeritas.Lacem
set_option autoImplicit false
set_option maxHeartbeats 480000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Celeritas
open OS OS.Semigroup Spectral Lattice Function Filter Metric Mist.Utah Complex Set MeasureTheory MeasureTheory.Measure Boundary Probe NormedSpace InnerProductSpace
open scoped Topology NNReal ENNReal InnerProductSpace ComplexOrder BigOperators
set_option quotPrecheck false
namespace Land
variable {K:Axis→Hilbert}(W:∀ a:Axis, OS.Semigroup (K a) a)(Ω:(i:Axis)→(K i).space) {H:Hilbert}
-- WOT bounded.Store center anchored independent.Observer.
structure Wot (f:ℕ→ H.Op)(V:H.Op):Prop where
 norm : ∃ K:ℝ,∀ᶠ i in atTop, ‖f i‖ ≤ K
 funds(x y:H) : Tendsto (fun i=>inner ℂ x (f i y)) atTop (𝓝 (inner ℂ x (V y)))
namespace Wot
variable {f g:ℕ→H.Op}{x y: H.Op}(p:Wot f x)
private lemma afford {f:ℕ→ H.Op}{c:H.Op}(t:Tendsto f atTop (𝓝 c)):∃ K:ℝ,∀ᶠ i:ℕ in atTop, ‖f i‖ ≤ K:= ⟨‖c‖+1,(t.norm.eventually (gt_mem_nhds (lt_add_one _))).mono fun i v=> (show _<_ from v).le⟩
-- prove mult WOT with one varying continuous path.G
include p
lemma price {X Y:H}(K:ℕ→H) (l:Tendsto K atTop (𝓝 Y)): Tendsto (fun i=>inner ℂ X (f i (K i))) atTop (𝓝 (inner ℂ X (x Y))) := by
 let F(i):=f i (K i)-f i Y; have t : Tendsto F atTop (𝓝 0) := by
    obtain ⟨z,h⟩:=p.norm; rw [tendsto_zero_iff_norm_tendsto_zero]; apply squeeze_zero' (Eventually.of_forall fun i=> norm_nonneg _) (g:=fun i=>z*‖K i-Y‖) ?_ ?_
    · filter_upwards [h] with i p; unfold F; rw [←map_sub]; exact ( (f i).le_opNorm _ ).trans (mul_le_mul_of_nonneg_right p (norm_nonneg _))
    have hx:= ((l.sub (tendsto_const_nhds (x:=Y))).norm).const_mul z; rw [sub_self,norm_zero, mul_zero] at hx; exact hx
 have hv:= (Filter.Tendsto.comp ((innerSL ℂ X).continuous.tendsto 0) t).add (p.funds X Y); rw [map_zero,zero_add] at hv; apply hv.congr; intro i; change inner ℂ X (F i)+ _=_; unfold F; rw [inner_sub_right,sub_add_cancel]
include p
lemma body (t:Tendsto g atTop (𝓝 y)) : Wot (fun i=>f i*g i) (x*y):= by
 obtain ⟨z,p'⟩:=p.norm; obtain ⟨b,q⟩:= afford t; refine ⟨⟨z*b,?_⟩,fun i j=> ?_⟩; · filter_upwards [p',q] with i p v; exact (norm_mul_le ..).trans (mul_le_mul p v (norm_nonneg _) ((norm_nonneg _).trans p))
 exact p.price _ ((ContinuousLinearMap.apply ℂ H.space j).continuous.continuousAt.tendsto.comp t) -- argument
lemma starred : Wot (fun i=>star (f i)) (star x) := by
 constructor; · obtain ⟨z,p⟩:=p.norm; exact ⟨z,by simpa using p⟩
 intro i j; have h:= (continuous_star.continuousAt.tendsto.comp (p.funds j i))
 let e(z:H.Op):inner ℂ i (star z j)=star (inner ℂ j (z i)):= by rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right,←inner_conj_symm]; rfl
 simp_rw [e]; exact h
lemma shrew(t:Tendsto g atTop (𝓝 y)) : Wot (fun i=>g i*f i) (y*x):= by
 have h:= ((starred p).body ((continuous_star.continuousAt.tendsto (x:=y)).comp t)).starred; convert h using 1 <;> simp -- tune
omit p
lemma continuity (t:Tendsto f atTop (𝓝 y)) : Wot f y:= ⟨afford t,fun x p=>((innerSL ℂ x).continuous.tendsto _).comp (((ContinuousLinearMap.apply ℂ H.space p).continuous.tendsto _).comp t)⟩
lemma still (Y:H.Op): Wot (fun _=>Y) Y:=continuity tendsto_const_nhds
end Wot
structure Weaves (Y:ℕ→ Shrine K)(A:Shrine K):Prop where
 grows(i:Axis) : Tendsto (fun j=> (Y j).t i) atTop (𝓝 (A.t i))
 looks(i:Axis): Wot (fun j=>(Y j).f i) (A.f i)
lemma weaves_r (A:Shrine K): Weaves (fun _=>A) A:= ⟨fun _=>tendsto_const_nhds, fun _=>Wot.still _⟩
-- NEW Harvest: candidate successor purchase. finite breadth iteration? choose 1 enough.Conservation
variable {σ: Type}[DecidableEq σ] (U:Set (Shrine K))
def Sprout:= {x:Shrine K|∃ f:ℕ→Shrine K,(∀ i,f i∈ U)∧ Weaves f x}
lemma sprout_sub : U ⊆ Sprout U:= fun x t=>⟨_,fun _=>t,weaves_r x⟩
variable (f:σ→ Shrine K) (F:ℕ→ σ→Shrine K)(x:σ→ E4) (L M:List σ) (a:Axis) (v: L.Pairwise (Seers f x a)) (P:∀ i:σ, Weaves (fun j=> F j i) (f i))
include P
lemma hi_limit (i j:σ): Tendsto (fun n=> Hi (F n) x a i j) atTop (𝓝 (Hi f x a i j)):= (continuous_real_toNNReal.tendsto _).comp ((tendsto_const_nhds.sub (NNReal.continuous_coe.continuousAt.tendsto.comp ((P j).grows a))).sub (tendsto_const_nhds.add (NNReal.continuous_coe.continuousAt.tendsto.comp ((P i).grows a))))
lemma hopP (i j:σ)(p:Seers f x a i j): Tendsto (fun n=> Leap W (F n) x a i j) atTop (𝓝 (Leap W f x a i j)):= by
 let y(n):=Hi (F n) x a i j; let z:=Hi f x a i j; let t:=OS.Semigroup.duration; have hv:0<z:= Real.toNNReal_pos.mpr (sub_pos.mpr p)
 have hw:= hi_limit f F x a P i j; let S:=W a; refine Eq.mp (by rw [show Leap W f x a i j= S.F (t z) from ((W a).roots_heat hv).symm] : Tendsto (fun n=> Leap W (F n) x a i j) atTop (𝓝 (S.F (t z))) = _) ?_ -- rw misses? simplify `rw..`
 refine ((S.localHeat (t z) (dur.mpr hv)).continuousAt.tendsto.comp ((continuous_ofReal.continuousAt.tendsto.comp NNReal.continuous_coe.continuousAt.tendsto).comp hw)).congr' ?_; filter_upwards [hw.eventually (Ioi_mem_nhds hv)] with i p; exact S.roots_heat (t:= y i) p -- args
lemma seating : ∀ i:σ, Wot (fun n=> actO W (F n) x a i) (actO W f x a i) := fun i=>(((P i).looks a).shrew tendsto_const_nhds).body tendsto_const_nhds
variable (Q:σ)(y:∀ i:σ,i≠ Q→ ∀ n,F n i=f i) (h:L.Nodup)
open Mist
include v
lemma Seers.along : ∀ᶠ n:ℕ in atTop,L.Pairwise (Seers (F n) x a):= by induction L with
 | nil=> exact Eventually.of_forall fun _=> List.Pairwise.nil
 | cons i t ih=>
    simp_rw [List.pairwise_cons] at v ⊢; obtain ⟨e,g⟩:=v
    apply Eventually.and _ (ih g)
    simp_rw [← List.mem_toFinset]; apply (eventually_all_finset t.toFinset).mpr; intro j p; filter_upwards [(hi_limit f F x a P i j).eventually (Ioi_mem_nhds (show 0<Hi f x a i j from Real.toNNReal_pos.mpr (sub_pos.mpr (e j (List.mem_toFinset.mp p)))))] with k p'; exact sub_pos.mp (Real.toNNReal_pos.mp p') -- notation
include y
lemma smooth_Q (p:Q∉ L): Tendsto (fun n=> TapeT (actO W (F n) x a) (Leap W (F n) x a) L) atTop (𝓝 (TapeT (actO W f x a) (Leap W f x a) L)):=by
 -- exactly constant? Leap widths only for those markers!
 refine tendsto_const_nhds.congr' (Eventually.of_forall fun i=>?_); have hw(j:σ)(e:j∈ L): F i j=f j:= y j (fun h=>p (h ▸ e)) i
 apply Eq.symm; apply Hike.same_tape; · intro j e; unfold actO Plot; rw [hw j e]
 intro j e k t; unfold Leap Hi startX endX; rw [hw j e, hw k t]
include h
lemma sheep : Wot (fun n=> TapeT (actO W (F n) x a) (Leap W (F n) x a) L) (TapeT (actO W f x a) (Leap W f x a) L):=by
 cases L with
 | nil=> exact .still _
 | cons i t=> induction t generalizing i with
        | nil=> exact seating W f F x a P i -- explicit
        | cons j t ih=>
           let f0:= fun n=>actO W (F n) x a; let Cn(n:ℕ):= Leap W (F n) x a i j; let Tc(n):=(TapeT (f0 n) (Leap W (F n) x a) (j::t)); let V:=TapeT (actO W f x a) (Leap W f x a) (j::t)
           obtain ⟨p,v'⟩:= List.pairwise_cons.mp v; obtain ⟨c,l⟩:= List.nodup_cons.mp h; let hk:= hopP W f F x a P i j (p _ List.mem_cons_self); change Wot (fun n=> f0 n i*(Cn n*Tc n)) (_*(Leap W f x a i j*V))
           by_cases e:i=Q; · exact (seating W f F x a P i).body (hk.mul (smooth_Q W f F x (j::t) a v' P Q y (e ▸ c))) -- order smooth
           apply ((ih j v' l).shrew hk).shrew; refine tendsto_const_nhds.congr (fun n=>?_); change _=actO W (F n) x a i; unfold actO Plot; rw [y i e]
lemma longB: Tendsto (fun n=> chorus W Ω (F n) x L a) atTop (𝓝 (chorus W Ω f x L a)):= (sheep W f F x L a v P Q y h).funds ..
#print axioms longB
omit y P h v
abbrev monoReq(F:σ→Shrine K)(X:Finset σ)(U:Set (Shrine K)):=∀ i:σ, if i∈X then F i∈ Sprout U else F i∈U
variable (b:Axis)[Fintype σ] (w:M.Nodup)
include h w
abbrev SameTower (F:σ→Shrine K):= chorus W Ω F x L a = chorus W Ω F x M b
local notation "Tt"=>SameTower W Ω x L M a b
variable (z:∀ f:σ→Shrine K,(∀ i:σ,f i∈ U) → L.Pairwise (Seers f x a)→ M.Pairwise (Seers f x b)→ SameTower W Ω x L M a b f)
include z
lemma grant_s (V:Finset σ) (u:monoReq f V U) (F:L.Pairwise (Seers f x a))(S:M.Pairwise (Seers f x b)) : chorus W Ω f x L a=chorus W Ω f x M b:=by
 induction V using Finset.induction generalizing f with
 | empty => exact z f (by simpa [monoReq] using u) F S
 | insert i V e ih=>
    have he:f i∈ Sprout U:=by simpa using u i
    obtain ⟨P,t,q⟩:= he; let F'(n:ℕ):=Function.update f i (P n); have hF(x:σ):Weaves (fun n=>F' n x) (f x):= by
       by_cases p:x=i; · subst x; simp_rw [F',Function.update_self]; exact q
       simp_rw [F',Function.update_of_ne p]; exact weaves_r (f x)
    have hV(n): monoReq (F' n) V U:=fun j=>by
       by_cases p:j=i; · subst j; simpa [F',e] using t n
       simpa [F',p] using u j
    have hY(x)(p:x≠i): ∀ n,F' n x=f x:= fun n=> Function.update_of_ne p _ _
    refine tendsto_nhds_unique_of_eventuallyEq (longB W Ω f F' x L a F hF i hY h) (longB W Ω f F' x M b S hF i hY w) ?_
    filter_upwards [Seers.along f F' x L a F hF,Seers.along f F' x M b S hF] with i u v; exact ih (F' i) (hV i) u v
lemma transferUp (p: ∀ i:σ,f i∈ Sprout U) (F:L.Pairwise (Seers f x a))(S:M.Pairwise (Seers f x b)):SameTower W Ω x L M a b f:= grant_s W Ω U f x L M a h b w z Finset.univ (by simpa [monoReq]) F S -- simpa tune
#print axioms transferUp
end Land
end YM.CF.Buffered.Afterglow.Hierarchy.Celeritas
