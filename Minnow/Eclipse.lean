import Minnow.Front
import AuroraB.Helict
import AuroraB.Scions
import AuroraB.Clockw
import AuroraB.Xphase
import SatinHeatSpecies
import AuroraB.Gill
import Mussel.Seal
import Mussel.Foil
import Mussel.Super
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 250000
set_option quotPrecheck false
noncomputable section

open Filter Function Set Metric MeasureTheory
open scoped Topology InnerProductSpace NNReal ComplexOrder BigOperators
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Casting Six
namespace Habitat
variable {P:Spine} {x:P.Spectrum0 3} {c r:ℕ→ℕ} {K:P.Register} {J:P.Ellis 3 x}
variable (B:P.Experiment K c r x J)(Z:Lead.Clan)
local notation "ξ"=> P.otherSpectrum 3 3 x
local notation "ω"=> P.colorZero 3 (P.otherSpectrum 3 3 x)
local notation "Ω"=> P.heaven 3 ξ
local notation "H"=> P.ManyF 3 ξ
local notation "G"=> P.ColorHil 3 (P.otherSpectrum 3 3 x)
namespace Hemlock
open PledgeT MiterT Broker
namespace AuroraB
open PledgeT MiterT Broker Aloft DoseTravel Calico
open _root_.YM.Preen Py.Rate.Pitching.Focus
variable (d:ℕ)(C D:ℕ→ℕ→ℝ)
variable (U V:SampleDose)(b:ℝ)(hb:0<b)(u:∀t∈tsupport (flipDose U 3).val, 1+b <t 3)(v:∀t∈tsupport V.val,1+b<t 3)(M:Morn P.par.K)(h:∀s:ℕ,d ≤ s→ Accordance P M d s (C s) (D s))(p:RobeRoad P d C D x)
local notation "Ωz"=>P.heaven 3 ξ
local notation "Ζ"=> P.calibration
local notation "L"=> flipDose U 3
local notation "μ" t:max=>P.singleState 3 t x
local notation "i₀" s:max t:max i:max V:max=>schema B i d C D s t (score i) V
local notation "ϕ"=>P.reflectTest 3
local notation "W*" s:max t:max Q:max=> wet B d C D U V s t Q
local notation "X*" s:max t:max Q:max=> rate B d C D U V s t Q
noncomputable def tariffen:CrossRead:= Matrix.of fun i j:Lead.Clan=>inner ℂ (prettyR (P:=P) x d C D (flipDose U 3) b i) (prettyR x d C D V b j)
local notation "F*"=> tariffen (x:=x) d C D U V b
local notation "wQ" s:max i:max A:max=> works B i d C D s (score i) A
local notation "r₁" s:max i:max=>inner ℂ (wQ s i (L)) (Ωz)
local notation "r₂" s:max i:max=>inner ℂ (Ωz) (wQ s i V)
-- generic CL helper
include h p B u v hb
variable (Q:ℕ→P.Test→ₗ[ℂ]ℂ)(f:∀t,Comparison P.calibration (P.singleState 3 t x) (Q t))
omit h p in
-- split copy, now only hosp
lemma mn_price_v(s:ℕ)(q:tidal P d s <1)(q0:4*Hemlock.radius P d s ≤1)(f:∀t,Comparison P.calibration (P.singleState 3 t x) (Q t)):
 Thalo B d C D U V s ∧ ∀t, wide B d C D s t → Cash B d C D U V Q s t:=by
 have p:hosp V:= fun i w=> lt_trans (lt_add_of_pos_right _ hb) (v i w); have a:hosp (L):=fun i t=> lt_trans (lt_add_of_pos_right _ hb) (u i t)
 constructor
 · constructor
   · refine tendsto_pi_nhds.mpr fun i=> tendsto_pi_nhds.mpr fun j=> ?_; exact fine_time B i d C D s (score i) (L) V q j (score j) a p
   · intro i; have ht:= (fine_h B i d C D s (score i) (L) q a).star; simp_rw [← P.opposed_single] at ht; rw [show star (inner ℂ (Ωz) (wQ s i (L)))=inner ℂ (wQ s i (L)) (Ωz) from inner_conj_symm _ _] at ht; exact ht
   exact fun i=>fine_h B i d C D s (score i) V q p
 intro t w
 let d'(i k:Lead.Clan):=avoids B i d C D k (L) V s t Q f a p q0 (w.2 _) (w.2 _) (score i) (score k)
 exact ⟨fun i j=>(d' i j).1, fun i=>(d' i i).2.2, fun i=>(d' i i).2.1⟩
lemma width_dollar (h0:U.Normalized)(h1:V.Normalized): Tendsto (fun s=>grime B d C D U V s) atTop (𝓝 (F*)) ∧ (∀i,Tendsto (fun s=>(r₁ s i)) atTop (𝓝 0))∧ ∀i,Tendsto (fun s=>(r₂ s i)) atTop (𝓝 0):=by
 have hf(i:Lead.Clan):= fine_prepaid B d C D M h p (L) b hb u (flipPay U h0 3) i
 have hg(i:Lead.Clan):= fine_prepaid B d C D M h p V b hb v h1 i
 have hu(O:SampleDose)(i:Lead.Clan):inner ℂ (Ω) (prettyR x d C D O b i)=0:= _root_.Acacia.pay_ortho (P.seasons 3 ξ) Ω _ ((scoring i).1) hb (P.heaven_hot 3 ξ) _
 refine ⟨?_,?_,?_⟩
 · refine tendsto_pi_nhds.mpr fun i=> tendsto_pi_nhds.mpr fun j=> ?_; exact (hf i).inner (hg j)
 · intro i; exact bye₁ (R:=H) (Ωz) false _ _ (hf i) (hu _ _)
 intro i; exact bye₁ (R:=H) (Ωz) true _ _ (hg i) (hu _ _)
where bye₁{R:Hilbert}(x:R)(b:Bool)(f:ℕ→R)(y:R)(h:Tendsto f atTop (𝓝 y))(p:inner ℂ x y=0): Tendsto (fun s=> if b then inner ℂ x (f s) else inner ℂ (f s) x) atTop (𝓝 0):=by
        have he:inner ℂ y x=0:=by rw [← inner_conj_symm (𝕜:=ℂ) y x,p,map_zero]
        cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> first|simpa only [p] using (tendsto_const_nhds (x:=x)).inner (𝕜:=ℂ) h|simpa only [he] using h.inner (𝕜:=ℂ) (tendsto_const_nhds (x:=x))
include f
set_option maxHeartbeats 550000 in
lemma lull (a:U.Normalized)(b':V.Normalized):
 Tendsto (fun s:ℕ=>limUnder atTop (fun t=>W* s t (μ t))) atTop (𝓝 (F*)) ∧
 (∀ᶠ s:ℕ in atTop,∀t,wide B d C D s t→Cash B d C D U V Q s t) ∧
 (∀ i:Lead.Clan, Tendsto (fun s:ℕ=>limUnder atTop (fun t=>(μ t) (ϕ (i₀ s t i (L))))) atTop (𝓝 0) ∧ Tendsto (fun s:ℕ=>limUnder atTop (fun t=>(μ t) (i₀ s t i V))) atTop (𝓝 0)) ∧
 Tendsto (fun s=>summer B d C D U V s Q) atTop (𝓝 (F*)):=by
 have hp:Tendsto (fun s:ℕ=>4*Hemlock.radius P d s) atTop (𝓝 (0:ℝ)):= by simpa only [mul_zero] using (radiusTiny P d).const_mul 4
 have hs:∀ᶠ s:ℕ in atTop, tidal P d s<1:= (recessVanish P d).eventually (gt_mem_nhds zero_lt_one)
 have he:∀ᶠ s:ℕ in atTop, Thalo B d C D U V s ∧ ∀t:ℕ, wide B d C D s t→Cash B d C D U V Q s t:=
    (hs.and (hp.eventually (ge_mem_nhds zero_lt_one))).mono fun s i=>⟨(mn_price_v B d C D U V b hb u v Q s i.1 i.2 f).1, (mn_price_v B d C D U V b hb u v Q s i.1 i.2 f).2⟩
 obtain ⟨t,xL,xR⟩:=width_dollar B d C D U V b hb u v M h p a b'
 let Φ(s:ℕ)(i j:Lead.Clan):=(r₁ s i)*(r₂ s j)
 let F(s):= grime B d C D U V s
 refine ⟨t.congr' (he.mono fun s i=>i.1.joint.limUnder_eq.symm),he.mono (fun _ i=>i.2),fun i=>⟨(xL i).congr' (he.mono (fun s t=> (t.1.leaf i).limUnder_eq.symm)),(xR i).congr' (he.mono (fun s t=>(t.1.flow i).limUnder_eq.symm))⟩,?_⟩
 have hf:Tendsto (fun s:ℕ=>F s-(Matrix.of (Φ s):CrossRead)) atTop (𝓝 (F*)):=matSad (R:= (P.ManyF 3 ξ)) Ωz (b:=fun s i=> wQ s i (L)) (c:=fun s i=> wQ s i V) t xL xR
 apply hf.congr'
 filter_upwards [he] with s ⟨hS,t⟩
 apply Eq.symm
 apply Filter.Tendsto.limUnder_eq
 refine tendsto_pi_nhds.mpr fun i=>tendsto_pi_nhds.mpr fun j=>?_
 have hT:= tendsto_pi_nhds.mp (tendsto_pi_nhds.mp (hS.joint) i) j
 have he:= hT.sub ((hS.leaf i).mul (hS.flow j))
 refine he.congr' ((looms B d C D s).mono fun k p=>?_)
 let E:= t k p
 let a:=ϕ (i₀ s k i (L)); let b:=i₀ s k j V
 change (μ k) (a*b)-(μ k) a*(μ k) b = _- (Q k (a*b)-Q k a*Q k b)
 rw [show Q k (a*b)=0 from E.split i j,show Q k a=0 from E.zeroLeft i, show Q k b=0 from E.zeroRight j]; ring; rfl
where matSad{R:Hilbert}(w:R){a:ℕ→CrossRead}{A:CrossRead}{b c:ℕ→Lead.Clan→(R).space}(h:Tendsto a atTop (𝓝 A))(p:∀ i,Tendsto (fun s=>inner ℂ (b s i) w) atTop (𝓝 0))(v:∀ i,Tendsto (fun s=>inner ℂ w (c s i)) atTop (𝓝 0)): Tendsto (fun s=> a s-(Matrix.of fun i j=> inner ℂ (b s i) w *inner ℂ w (c s j))) atTop (𝓝 A):=by
        have he:Tendsto (fun s=>(Matrix.of (fun i j=>inner ℂ (b s i) w *inner ℂ w (c s j)):CrossRead)) atTop (𝓝 0):=by refine tendsto_pi_nhds.mpr fun i=>tendsto_pi_nhds.mpr fun j=>?_ ; change Tendsto (fun s=> _*_) atTop (𝓝 (0:ℂ)); simpa only [zero_mul] using (p i).mul (v j)
        simpa only [sub_zero] using h.sub he
#check @dataT
#check @width_current
#print axioms lull
end AuroraB
end Hemlock
end Habitat
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
