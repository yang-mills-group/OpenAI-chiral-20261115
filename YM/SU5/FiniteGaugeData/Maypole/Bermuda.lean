import YM.SU5.FiniteGaugeData.Maypole.Lorry
import YM.SU5.FiniteGaugeData.Celeritas.Dynamo
/-! # Costs of OS diagonal flights. -/
set_option autoImplicit false
set_option maxHeartbeats 330000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Vp.Caps
open Mist.Utah Celeritas Function Set MeasureTheory OS OS.Semigroup Complex Filter NormedSpace Metric Bornology Juno Spectral Boundary Probe Measure
open scoped Topology NNReal ENNReal InnerProductSpace ComplexOrder BigOperators
variable {H:Hilbert}{a: Axis}(S: OS.Semigroup H a)(v: OS.Cross a)
local notation "P"=> S.ℚmeasure
local notation "Μ" x:max=> S.ℚmeasure.diagonal x
abbrev Xtr(a:Axis): E4→ℝ:= fun p=>p a
abbrev Ut(v:Cross a): E4→ℝ:= fun x=> ped x v
lemma payer(x:H): Payer (Μ x) (Xtr a) (Ut v):=⟨S.bright x,(ped_c v).measurable,(show Continuous (Xtr a) from (by unfold Xtr; fun_prop)).measurable⟩
lemma fareK (t s q:ℝ)(x:H)(h:0 ≤ t+s): inner ℂ x (S.U ((s*q) • v) (S.E (t+s).toNNReal x))= ∫ p:E4,keyi (Xtr a) (Ut v) q s t p ∂(Μ x):=by
 let u:ℝ≥0:=(t+s).toNNReal; let A:=Xtr a; let U:=Ut v; let y:ℂ:=(↑(u:ℝ):ℂ)*I; let X:= (((s*q) • v.val):E4); have he:= S.heat X x (z:=y) (show y∈Paley.high from (by change 0≤ y.im; simp [y])); have hc(p:E4):Complex.exp (↑(p a)*y*I)=(metal a u p:ℂ):=by
    unfold metal y; rw [ofReal_exp]; congr 1; push_cast; calc _ = ((p a:ℝ):ℂ)*(u:ℝ)*(I*I):=by ring
                                                              _ = _:=by rw [I_mul_I]; ring
 simp_rw [hc] at he; change inner ℂ x ((S.unit.translation X) (S.edge y.re (S.E y.im.toNNReal x)))=(∫ p:E4, _ ∂(Μ x)) at he -- shadow x inner integral!
 rw [show y.re=0 from by simp [y],S.birth,show y.im.toNNReal=u from by simp [y],ContinuousLinearMap.id_apply] at he; rw [show S.unit.translation X=S.U ((s*q) • v) from vacancy S ((s*q) • v)] at he; refine he.trans ?_; apply integral_congr_ae; filter_upwards with p; rw [show X=(s*q)• v.val from rfl,plane_rate]; unfold metal keyi shape Ar Ut Xtr smack kin; simp only [show ↑u=(t+s) from Real.coe_toNNReal (t+s) h]; push_cast; rw [←Complex.exp_add,←Complex.exp_add]; congr 1; ring
abbrev tentE(x:H)(t s q:ℝ):= inner ℂ x (S.U ((s*q) • v) (S.E (t+s).toNNReal x))
def Draft(x:H)(C:ℝ)(t:ℝ):Prop:=∀ q:ℝ,|q|≤1 → ∃ f:ℂ→ℂ, AnalyticOnNhd ℂ f (Lot (t/8)) ∧(∀ z∈Lot (t/8),‖f z‖≤C) ∧ ∀ z:ℝ, |z| ≤ t/8 → f z=tentE S v x t z q
lemma chunky(x:H)(C t:ℝ)(q:Draft S v x C t)(e:0<t): Chunk t C (Μ x) (Xtr a) (Ut v):=by
 refine ⟨e,fun p h=>?_ ⟩; obtain ⟨f,ℓ,H,W⟩:= q p h; exact ⟨f,ℓ,H,fun z t=> (W z t).trans (fareK S v _ _ _ x (by linarith only [e,(abs_le.mp t).1]))⟩ -- tune t binder
abbrev copyE (v: Cross a): Set E4:= {p| |Ut v p| ≤ speed*p a}
lemma copy_c : IsClosed (copyE v) := isClosed_le (ped_c v).abs (show Continuous (fun p:E4=>speed*p a) from by fun_prop)
lemma rung (x:H)(C:ℝ)(h:∀ᶠ t:ℝ in atTop,Draft S v x C t) : (Μ x).support⊆ copyE v:=by
 intro z hz; let A:= Xtr a; let U:= Ut v; by_contra! g; have hx:speed*A z< |U z|:= not_le.mp g; have e:0≤A z:= S.nonneg x hz; obtain ⟨b,w,p⟩:= insideCap _ _ hx e
 let Z := {x:E4|A x<b ∧ speed*b< |U x|}; have hU(x)(p:x∈ Z): A x ≤b ∧ speed*b ≤ |U x|:=⟨p.1.le,p.2.le⟩; have ht:IsOpen Z:= IsOpen.inter (isOpen_lt (show Continuous A from by unfold A Xtr; fun_prop) continuous_const) (isOpen_lt continuous_const (ped_c v).abs)
 have hp:= Measure.mem_support_iff_forall z|>.1 hz Z (ht.mem_nhds (And.intro w p)); exact hp.ne' (spent (a:=b) (payer S v x) (lt_of_le_of_lt e w) ht.measurableSet hU ( (h.and (eventually_gt_atTop 0)).mono fun t i=>chunky S v x C t i.1 i.2 ))
lemma polarE (Z:Set H)(p:Dense (Submodule.span ℂ Z:Set H))(q:∀ x∈Z,∃ C:ℝ,∀ᶠ t in atTop, Draft S v x C t): S.ℚmeasure.region (copyE v)ᶜ=0:=by
 let G:=(P).region (copyE v)ᶜ; have ht: Submodule.span ℂ Z ≤ G.ker:=Submodule.span_le.mpr (fun x u=> let e:= q x u; show G x=0 from ((P).null_pair (copy_c v).isOpen_compl.measurableSet x).1 (measure_mono_null (compl_subset_compl.mpr (rung S v x e.choose e.choose_spec)) measure_compl_support)); ext1 x; exact show x∈G.ker from closure_minimal ht G.isClosed_ker (p x)
#print axioms rung
end YM.CF.Buffered.Afterglow.Hierarchy.Vp.Caps
