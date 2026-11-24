import SatinThinScroll
import YM.CF.Buffered.StepIdentity

set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.QuadClock
open Py Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure Pressure
open Skye Scree Vale Vale.Grace Cube Pastry Lat Fock Rush Scroll Paige Vault Phase Spire Kennel
open Buffered Buffered.Advance Roots Rive
open Ione Cascade Girt
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Classical NNReal ENNReal Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
set_option autoImplicit false

variable {N P B n:Side} {K:Teller SU.group}{L:ChartRatio SU.group} {R:Patch} {d t:ℝ} (V: Grace K R L)(D:Grasp V.U B d)
 (G:Ratio (mid N B) (mid P B)) (S:StepData (Domain N B) (Domain P B)) (A:Scree.Loom (mid N B))(A':Scree.Loom (mid P B))(Y:GramM (mid P B)) (q:Chi)(Q:Op SU.Slot)
local notation "Ω"=> mid N B
local notation "Ξ"=> mid P B
local notation "Ψ"=> Orbit (mid N B)
local notation "Φ"=> Orbit (mid P B)
-- `Version` doesn't commit the density outside its Fleet pricing.
variable {T : Type*}[MeasurableSpace T]{E₀ : Type*}[MeasurableSpace E₀][NormedAddCommGroup E₀]{μ:Measure T}
def Version {T : Type*}[MeasurableSpace T] (μ:Measure T) {E₀:Type*}[MeasurableSpace E₀][NormedAddCommGroup E₀](f:T→E₀):Prop:= ∃ g, f =ᵐ[μ] g ∧ Envelope g
variable {u: T→E₀}
lemma Version.cong {f:T→E₀}(p:Version μ f)(e:f=ᵐ[μ] u): Version μ u:=by obtain ⟨k,p,t⟩:=p; exact ⟨k,e.symm.trans p,t⟩
lemma ver_of (p:Envelope u): Version μ u:=⟨_,EventuallyEq.rfl,p⟩
lemma Version.integrableX [BorelSpace E₀][SecondCountableTopology E₀][IsFiniteMeasure μ] (p:Version μ u): Integrable u μ:=by obtain ⟨k,x,h⟩:=p; exact (Env.integrableX h μ).congr x.symm

lemma plusV {F G:T→ Phys n}(p:Version μ F)(q:Version μ G): Version μ (fun i=>F i+G i):=by
 obtain ⟨g,p,v⟩:=p; obtain ⟨k,h,w⟩:=q; exact ⟨_,p.add h,kitE g k (·+·) (by fun_prop) v w⟩
lemma prodV {F:T→ℂ}{G:T→ Phys n}(p:Version μ F)(q:Version μ G): Version μ (fun i=> F i • G i):=by
 obtain ⟨g,p,v⟩:=p; obtain ⟨k,h,w⟩:=q; exact ⟨_,p.smul h,kitE g k (fun x:ℂ=>fun y:Phys n=> x • y) (by fun_prop) v w⟩ -- parser ambiguous E₀ etc tune
lemma multV {a:ℂ}{u:T→Phys n}(p:Version μ u): Version μ (fun i=> a • u i):=prodV (ver_of (⟨measurable_const, _, fun _=> (le_rfl : ‖a‖≤ ‖a‖)⟩)) p

lemma Version.letterpay {A:Scree.Loom n}{G:Orbit n→ Phys n}(m:Measurable A){f:Mark n}(hp:Envelope f)(q: Version (city n) G): Integrable (fun i:Orbit n=> letterRead (f (i.1,A i)) (G i)) (city n):=by
 obtain ⟨k,h,w⟩:=q; apply Integrable.congr _ (show (fun i:Orbit n=> letterRead (f (i.1,A i)) (k i))=ᵐ[city n] _ from h.symm.mono fun i hi=>by exact congrArg _ hi); exact Env.integrableX (env_letterRead (Env.along hp (drawn_m A m)) w) _

variable {A A' q S D Y G} {b:BaseL D G Y A A' q t}(h:S.patch.Branches S.kernel SU.group)
local notation "knob"=> lynx K S G A' A' A Y q t Q
local notation "skin"=> Orbit Ω × Orbit Ξ
include b V h
open Broc Branch Drapes Peaks Tulip Jet
lemma envelope_fly (F :Orbit (mid P B)→ Phys (mid P B))(p:Envelope F): Envelope (fun i:skin=>knob i.1 i.2 (F i.2)):=by
 let c(Q:Forest (ratio G))(i:skin):= coal_X (K:=K) (Y:=Y) (G₀:=A) (G₁:=A') (kL:=t) (q:=q) i.1 Q i.2 (F i.2); let T'(i:skin):=S.density Y.beta i.2.1 i.1.1
 have hv:Envelope T':=Envelope.sum univ _ (fun i=> env_tagged Y.beta i h (measurable_fst.comp measurable_snd) (measurable_fst.comp measurable_fst)) -- tune
 let m(x:Forest (ratio G))(i:skin):= T' i • scaleZ Q (c x i)
 have ht(x):Envelope (m x):= by
    apply Env.scale hv (pole_w (c x) _ (scaleW _ Q).continuous ?_)
    obtain ⟨k,a,h,d,H,u',g⟩:= b.wick; obtain ⟨s,l,r,p0,t'⟩:= b.cap; let α:= fun i:skin=>(seine G x q t (A' i.2) (A i.1),A i.1); have he:Measurable (fun i:skin=> A i.1):= p0.bill.comp measurable_fst
    apply heat_k b.power _ H u' g b.pe b.size α _ (fun z=>b.trial ..) ?_ (show Envelope (fun z:skin=> F z.2) from Env.along p measurable_snd)
    exact (((brake G q t x b.legal.1 b.legal.2).measurable.comp ((t'.bill.comp measurable_snd).prodMk he)).prodMk he)
 rw [show (fun i:skin=> (knob i.1 i.2) (F i.2)) = fun i=> (((Fintype.card (Forest (ratio G)):ℝ)⁻¹) • ∑ x:Forest (ratio G),m x i) from ?_]
 · exact Env.scale (H:=fun _=>_) (Envelope.const _) (Env.total _ ht)
 funext i; unfold lynx; simp only [ContinuousLinearMap.smul_apply,Complex.coe_smul,ContinuousLinearMap.sum_apply]; rfl -- need annotate

variable (S G A A' Y q t)
def pushCloud (F:Orbit (mid P B)→ Phys (mid P B))(x:Orbit (mid N B)):=∫ y:Φ, knob x y (F y) ∂city Ξ
#check env_marginal
#check Env.marginal
#print pushCloud
-- omit/include e.g. b h leakage via variable S... if wrong.
variable {S G A A' Y q t}
local notation "ΦF"=>pushCloud (K:=K) t G S A A' Y q Q -- tune
omit b V h
lemma push_congr {F G':Orbit (mid P B)→ Phys (mid P B)}(p:F =ᵐ[city Ξ] G'): ΦF F=ΦF G' := funext fun i=> integral_congr_ae (p.mono fun x v=> by exact congrArg _ v)
include V b h
lemma cloud_version {F:Orbit (mid P B)→ Phys (mid P B)}(p:Version (city Ξ) F): Version (city Ω) (ΦF F):=by
 obtain ⟨k,u,f⟩:=p; rw [push_congr Q u]
 exact ver_of (env_marginal (f:= fun z:skin=> knob z.1 z.2 (k z.2)) (envelope_fly V Q (b:=b) h k f) _)
end YM.CF.QuadClock
