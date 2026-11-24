/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import GaugeFieldConstruction.SummitFromStars
/-!
# Small pads agreement all complex costs on this one channel
- adapted strip technique from YM.Work.C22
-/
set_option autoImplicit false
noncomputable section
namespace YM.NSF.LD
open Mink OS Function MeasureTheory Filter Set Metric Table Boundary Analysis Bid Work.C03 Work.C22 LineDeriv
open scoped Topology BigOperators NNReal ENNReal ContDiff InnerProductSpace
variable {G:Gauge}{L:Register G}{S T:Table L}{R:Rotation S}{s:S.RealSpin}{P:DiffPlan S}
variable {V:LRoom T timeAxis}{B:Small S V}{K:Spins S}{F:Waves S}{W:Surface S}
structure CharterL (B:Small S V):Prop where
 pure {n : ℕ} (p : ℝ≥0) (y : Heights n) (x : SpacePoints n) (v : Fin n → S.Tag) (h : y∈east n) (hp : Small.enough y p) :
    Small.matrix B p n (fun i => ↑(y i)*Complex.I) x (fun i => S.pin (v i).1 (v i).2) = S.useAt T (place x y) v
open Complex
variable {n:ℕ}
lemma pureWayL {P:DiffPlan S}(H:S.Symmetric)(hr:P.Inclusions S)(b:CharterL B) (x:SpacePoints n) (w:Fin n→ S.Union)(z:Times n)(p q:ℝ≥0)(e:Small.lit z p)(f: Small.lit z q): B.matrix p n z x w=B.matrix q n z x w:=by
 let y:Heights n:= fun i=>(z i).im; let l(i:Fin n):=(z i).re; let k (c:ℂ)(i:Fin n):= l i*c+iz (y i); let F(t:ℝ)(i:Fin n):= l i*t+y i
 have he(c): (fun i:Fin n=> (k c i).im)= F c.im:=by ext i; simp [k,F,iz]
 have hh: k 0=iz ∘ y:=by ext1 i; simp only [k,mul_zero,zero_add, Function.comp_apply]
 have hm: k 1=z:=by ext1 i; unfold k l y iz; rw [mul_one]; exact re_add_im _
 have hK:Continuous k:=by unfold k; fun_prop
 have hw(h:ℝ≥0)(u:Small.lit z h):Small.lit (k 0) h:=by change Small.enough _ h; rw [he]; rw [show F (0:ℂ).im=y by ext i; change _*0+_=_; ring]; exact u
 have hp:Continuous iz:=continuous_ofReal.mul continuous_const
 obtain ⟨a,ha,hA⟩:= Metric.eventually_nhds_iff.mp (((hK.comp hp).tendsto 0).eventually (show ∀ᶠ s:Times n in 𝓝 ((k ∘ iz) (0:ℝ)), Small.lit s p ∧ Small.lit s q from by
    rw [Function.comp_apply, show iz 0=0 by simp [iz]]; exact (eventually_lit (hw p e)).and (eventually_lit (hw q f))))
 let U : Set ℂ := im ⁻¹' Ioo (-a) a
 have hu : IsOpen U := isOpen_Ioo.preimage continuous_im
 have hc : IsPreconnected U := Convex.isPreconnected ((convex_Ioo (-a) a).linear_preimage imCLM.toLinearMap)
 have hzero : (0:ℂ)∈U := ⟨neg_lt_zero.mpr ha,ha⟩
 let t(g:ℝ≥0)(c:ℂ):=B.matrix g n (k c) x w; have hv(c:ℂ)(H:c∈U):Small.lit (k c) p∧ Small.lit (k c) q:=by
    have V:= hA (y:=c.im) (show dist c.im 0<a from by simpa only [Real.dist_eq,sub_zero,abs_lt] using (show -a<c.im ∧ c.im<a from H)); change Small.lit (k _) p∧ Small.lit (k (iz c.im)) q at V; have hx:(fun i:Fin n=> (k (iz c.im) i).im)=(fun i:Fin n=> (k c i).im):=by rw[he,he]; simp[iz]
    unfold Small.lit at *; rwa [hx] at V
 have hl:Differentiable ℂ k:=by unfold k; fun_prop
 have hx(c:ℂ)(u:c∈U):DifferentiableAt ℂ (t p) c:=(matrix_diff B w x (hv c u).1).comp c (hl c)
 have hk:= (show DifferentiableOn ℂ (t p) U from fun i g=>(hx _ g).differentiableWithinAt).analyticOnNhd hu; have hb: AnalyticOnNhd ℂ (t q) U:=(show DifferentiableOn ℂ (t q) U from fun i g=> ((matrix_diff B w x (hv i g).2).comp i (hl _)).differentiableWithinAt).analyticOnNhd hu
 have hv':EqOn (t p) (t q) U:=by
    apply hk.eqOn_of_preconnected_of_frequently_eq hb hc hzero; intro hn
    have hh : Tendsto iz (𝓝[>] (0:ℝ)) (𝓝[≠] (0:ℂ)) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · simpa [iz] using ((hp.tendsto 0).mono_left (nhdsWithin_le_nhds (s:=Ioi 0)))
      filter_upwards [self_mem_nhdsWithin] with i hi
      change iz i ≠ 0; simp [iz,(mem_Ioi.mp hi).ne']
    obtain ⟨i,u,o⟩:= ((hh.eventually hn).and ((hh.mono_right nhdsWithin_le_nhds).eventually (hu.mem_nhds hzero))).exists
    apply u
    have hf:(F i) ∈ east n:=by
       have h : (fun j=> (k (iz i) j).im)∈ east n:= lit_strict (hv (iz i) o).2; rw[he,show (iz i).im=i from by simp [iz]] at h; exact h
    have hj:k (iz i)= iz ∘ F i:=by ext1 j; simp only [iz,k,F,Function.comp_apply]; push_cast; ring
    obtain ⟨v,hZ⟩:=tagOrigins P H hr w
    unfold t; rw[hj, ← hZ]; change B.matrix p _ _ _ (pinned ∘ v)=_
    have hP(h:ℝ≥0)(v: Small.lit (k (iz i)) h): Small.enough (F i) h:=by unfold Small.lit at v; rwa [he, show (iz i).im=i from by simp [iz]] at v
    exact (b.pure p (F i) x v hf (hP _ (hv _ o).1)).trans (b.pure q (F i) x v hf (hP _ (hv _ o).2)).symm
 rw [←hm]; exact hv' (show (1:ℂ)∈U from ⟨neg_lt_zero.mpr ha,ha⟩)
#print axioms pureWayL
end YM.NSF.LD
