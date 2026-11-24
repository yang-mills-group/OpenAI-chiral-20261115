import GaugeFieldConstruction.SummitFromStars
import YM.SU5.Registration.Ink.WavePort
import YM.Heat.Extend
/-!
 Compare StyriaRel copy to main SatInt versions of strict operators. First quantities
 REAL bounded-operator lags, kept into reconstruction by stripping costs. Then complex
 clocks (same vacuum & moments throughout). Not via equality of independent Wick
 versions of elected EU.
-/
set_option autoImplicit false
set_option maxHeartbeats 170000
noncomputable section
namespace YM.NSF.Boundary
open MeasureTheory Filter Function Set Complex
open scoped Topology BigOperators NNReal ENNReal ContDiff InnerProductSpace
open OS OS.Semigroup

variable {n : ℕ}
-- duplicate of opaque_compare for the two namespaces (the two .F each reduce to roots but
-- need only common positive-time laws).
section
variable {G K:Hilbert}{j i:Axis}(S:YM.OS.Semigroup G j)(T:NSF.OS.Semigroup K i)(L:G→L[ℂ]K)
lemma compareHeat (h:∀ t, L.comp (S.E t)=(T.E t).comp L): EqOn (fun z=> L.comp (S.F z)) (fun z=> (T.F z).comp L) inside:=by
  let F (z:ℂ):G→L[ℂ]K:= L.comp (S.F z)-(T.F z).comp L
  have hp : AnalyticOnNhd ℂ F inside:= fun z hz=> (((ContinuousLinearMap.compL ℂ G G K L).analyticAt _).comp (S.localHeat z hz)).sub ( ((ContinuousLinearMap.compL ℂ G K K).flip L).analyticAt _ |>.comp (T.localHeat z hz))
  let t:ℝ≥0:=1
  have hu : EqOn F 0 inside := by
    apply hp.eqOn_zero_of_preconnected_of_frequently_eq_zero
      (convex_halfSpace_gt Complex.reCLM.toLinearMap.isLinear 0|>.isPreconnected) (dur.mpr (by norm_num : 0<(1:ℝ≥0)))
    intro hn
    have hy : Tendsto duration (𝓝[>] t) (𝓝[≠] (duration t)) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · exact (Complex.continuous_ofReal.comp continuous_subtype_val).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      filter_upwards [self_mem_nhdsWithin] with i hi
      have hI := mem_Ioi.mp hi
      change ¬duration i=duration t; exact fun he => hI.ne' (Subtype.ext (Complex.ofReal_injective he))
    obtain ⟨i,hi,hq⟩ := ((hy.eventually hn).and self_mem_nhdsWithin).exists
    have he:0< i:= (zero_lt_one (α:=ℝ≥0)).trans (mem_Ioi.mp hq)
    exact hi (show F (duration i)=0 by unfold F; rw [show S.F (duration i) = S.E i from S.roots_heat he,T.roots_heat he,h,sub_self])
  intro v x; exact sub_eq_zero.mp (hu x)
end
-- for abstract moment statement use same mix of args seen in Carton. No dependence on actual
-- constructor B_0 yet. `Budget` could be dropped until compare to Ink actual. Avoid cross
-- dependency in earlier file. x' later fill.
variable {G:Gauge}{L:Register G}{S T:Table L}{C:LRoom T timeAxis}{B:Small S C}
variable {V : Type*} [AddCommGroup V][Module ℂ V]
variable {K:Hilbert}(D:YM.OS.Semigroup K timeAxis)
variable (B':ℝ≥0→V→ₗ[ℂ] K.Op)(v₀:K)
open YM.Boundary (Joint)
open YM.SatinWFixed

noncomputable def inkTrain (p:ℝ≥0) : ∀ n, Times n → SpacePoints n → (Fin n→ V) → ℂ→ Space3→ K
 | 0, _,_,_,_,_=>v₀
 | n+1, z,x,v,t,y =>
    let J : K.Op:= (D.F (Small.interval (z 0-t) (p+p))).comp (D.U (Small.bufferF (x 0-y)))
    J (B' p (v 0) (inkTrain p n (Fin.tail z) (Fin.tail x) (Fin.tail v) (z 0) (x 0)))
noncomputable def inkAt (p:ℝ≥0) : ∀ n, Times n→ SpacePoints n → (Fin n→ V)→ ℂ
 | 0, _,_,_=>inner ℂ v₀ v₀
 | n+1,z,x,v=> inner ℂ v₀ (B' p (v 0) (inkTrain D B' v₀ p n (Fin.tail z) (Fin.tail x) (Fin.tail v) (z 0) (x 0)))

structure PreservesSmall (q:V→ₗ[ℂ]S.Union) (U: K→ₗᵢ[ℂ] C.H) (B: Small S C):Prop where
 heat t : U.toContinuousLinearMap.comp (D.E t)=(C.flow.E t).comp U.toContinuousLinearMap
 space (p:Space3): U.toContinuousLinearMap.comp (D.U (Small.bufferF p))=(C.flow.U (Small.bufferF p)).comp U.toContinuousLinearMap
 money: U v₀=C.omega
 links (t:ℝ≥0)(ht:0<t) (v:V): U.toContinuousLinearMap.comp (B' t v)=(B.bar t (q v)).comp U.toContinuousLinearMap
variable {B' D v₀}{q:V→ₗ[ℂ] S.Union}{U: K→ₗᵢ[ℂ] C.H}
variable (h:PreservesSmall D B' v₀ q U B)
include h
lemma PreservesSmall.joint {z:Times n}(x: SpacePoints n)(v:Fin n→ V)(p:ℝ≥0) (hp:Small.lit z p)
    (Z:ℂ)(X: Space3)(ht:∀ i, ((p+p:ℝ≥0):ℝ)< (z i).im-Z.im) :
  U (inkTrain D B' v₀ p n z x v Z X)=B.trainB p n z x (q ∘ v) Z X:=by
 induction n generalizing Z X with
 | zero=> exact h.money
 | succ n ih=>
   let q':= Small.interval (z 0-Z) (p+p); let w:=x 0-X; let F:=Small.bufferF w
   let y:= inkTrain D B' v₀ p n (Fin.tail z) (Fin.tail x) (Fin.tail v) (z 0) (x 0)
   have he: U y= B.trainB p n (Fin.tail z) (Fin.tail x) (Fin.tail (q ∘ v)) (z 0) (x 0):= ih (Fin.tail x) (Fin.tail v) (Work.C03.tail_lit hp) (z 0) (x 0) (Work.C03.tail_ready hp)
   have hz: q'∈ inside:= (Small.down ..).2 (ht 0)
   simp only [inkTrain,Small.trainB]; unfold Small.rip; change U (D.F q' (D.U F (B' p (v 0) y)))= C.flow.F q' (C.flow.U F (B.bar p (q (v 0)) _)); rw [← he]; apply Eq.trans (DFunLike.congr_fun (compareHeat D C.flow _ h.heat hz) (D.U F (B' p (v 0) y)))
   refine congrArg (C.flow.F q') ((DFunLike.congr_fun (h.space w) (B' p (v 0) y)).trans ?_)
   exact congrArg (C.flow.U F) (DFunLike.congr_fun (h.links p hp.1 (v 0)) y)
lemma PreservesSmall.at {z:Times n}(x:SpacePoints n)(v:Fin n→V)(p:ℝ≥0) (hp:Small.lit z p) :
  inkAt D B' v₀ p n z x v=B.matrix p n z x (q ∘ v):=by
 cases n with
 | zero=>rw [inkAt,Small.matrix,←h.money]; exact (U.inner_map_map _ _).symm
 | succ n=>
   rw [inkAt,Small.matrix]; let y:= inkTrain D B' v₀ p n (Fin.tail z) (Fin.tail x) (Fin.tail v) (z 0) (x 0); change inner ℂ v₀ (B' p (v 0) y)=_
   rw [←LinearIsometry.inner_map_map U]; change _=inner ℂ C.omega (B.bar p (q (v 0)) (B.trainB p n (Fin.tail z) (Fin.tail x) (q ∘ Fin.tail v) (z 0) (x 0))); rw [h.money]
   refine congrArg (inner ℂ C.omega) ((DFunLike.congr_fun (h.links p hp.1 (v 0)) y).trans (congrArg (B.bar p (q (v 0))) (h.joint _ _ p (Work.C03.tail_lit hp) _ _ (Work.C03.tail_ready hp))))
variable {F:InkWaves V}{W:WView V}{A:Waves S}{R:Surface S} (p:Bid.Direct B A)
omit h
-- attendee with F callable at these arguments. use one production budget κ every time.
include p h
lemma PreservesSmall.registration
    (d:∀ n,∀ z:Times n,z∈ strict n→ ∀ p,Small.lit z p→ ∀ x v,F.F n z x v=inkAt D B' v₀ p n z x v)
    (v:Fin n→V) : (∀ z:Times n,z∈ strict n→ ∀ x:SpacePoints n,
             F.F n z x v=A.F n z x (q ∘ v)) ∧ (F.NonTangentialFree W → A.NonTangentialFree R → W.W n v=R.W n (q ∘ v)):=by
 have hz(z:Times n)(e:z∈ strict n)(x:SpacePoints n) : F.F n z x v=A.F n z x (q ∘ v):=by obtain ⟨u,y⟩:=Work.C03.exists_lit e; rw[p.tune n _ e u y, d n z e u y]; exact h.at _ _ u y
 refine ⟨hz,fun r t=>?_⟩; ext1 f; haveI : NeBot (𝓝[east n] 0):= awaits (light n)
 have e:= r.corner n v f; rw [show YM.Boundary.east n = east n from rfl] at e
 exact tendsto_nhds_unique_of_eventuallyEq e (t.corner n (q ∘ v) f) (by
    filter_upwards [self_mem_nhdsWithin] with y ey
    apply integral_congr_ae; filter_upwards with x; change F.F n (shift x y) (trace x) v* f x=A.F n (shift x y) (trace x) (q ∘ v)*f x; rw [hz _ (by intro i j hij; simpa [shift] using (show y i<y j from ey hij))])
#print axioms PreservesSmall.registration
end YM.NSF.Boundary
end
