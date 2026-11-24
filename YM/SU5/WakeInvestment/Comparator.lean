import YM.SU5.WakeInvestment.FoldPower
import YM.SU5.WakeInvestment.DistancePower
set_option maxHeartbeats 450000
set_option synthInstance.maxSize 24000
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py.Rate.LocalLimit.Preparation
open Neon
open Py
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Ione Moto Taxi Hove Haro Vow Bake Lilt Prism Rue Larch Push.AbsoluteSums.Trees Salt Jet
open scoped YM.CF.Mew

set_option autoImplicit false
open Mew QuadClock Roots Rive Oise


open QuadClock FullBill Pitching Focus Buffered Afterglow Journey
open QuadClock FullBill Pitching Focus Buffered Afterglow Journey
variable {P:Preparation}{ℓ:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus ℓ))
attribute [-instance] instDecidableEqLex
namespace Yoke
open Tapestry Advance Papyrus Papyrus.Franc
variable {n:Side}
open Py.Rate.Pannier CF.Pannier Chancel Rous Pressure Worth Worth.Pays Graph

variable {z A c:ℝ}
set_option quotPrecheck false
local notation "L"=> P.R.L
local notation "D"=> P.K.j
local notation "shx" s:max => hat L P.x s
local notation "vℓ" s:max => shieldC (hat L P.x s)
local notation "Ω" s:max i:max => (side Y i s)
local notation "Gξ" s:max i:max k:max => RootBook Y i k s
local notation "ℂk" s:max i:max => (Y.voyage i).CapeT s

open WakeInvestment
local notation "ℰ" s:max => Worth.meterC (shx s)


variable (s i k : ℕ)
local notation "flatP" => spar P.K.j (RootBook Y i k s).J.M (1:Pane (side Y i s))
local notation "N" s:max i:max => side Y i s
local notation "ηP" s:max => Worth.gateC (shx s)
local notation "ptQ" s:max i:max k:max => ((RootBook Y i k s).p)
open Rous


attribute [local instance] opCStarAlgebra

open Lamour.Bridge Celeste Clock Hookah
open Cliplet
open Window Buffered.Afterglow.Tower Ballad SitSpin
open Signal.Interval (separationCost)
variable {H:Real.exp 1≤ P.x} {χ d d':ℝ}
variable {I:Type*} [Fintype I] (u:I→Lead.Clan) (G:List I)(x:I→ Cover)(w:I→Twah.DirSpin)(R:ℕ)

variable {E A v:ℝ} {φ μ π κ:ℕ→ℕ} {E' : ℕ→ Buffered.Family (tent Y H) →ℂ}{X:ℕ→Buffered.Family (tent Y H)→ℕ→ℂ}
variable {D₀:ℕ→Buffered.Family (tent Y H)→Buffered.Family (tent Y H)}
open Lifted
open YM.Stationary (Gaia)
open Onyx SpinReceipt
local notation "K₁" P:max s:max => zoomR P A s
local notation "W₁" P:max s:max=> sPow P s A
-- gaugeRise = nearPoints / fray + 1/X ; include actually announced AP node coords
lemma delta_w (P:Preparation) (x y:Cover) :
   riseX (zoomR P A s) x - riseX (zoomR P A s) y = frayR P A s • (gaugeRise P s A x-gaugeRise P s A y):=by
 let R:=zoomR P A s; let v:=sPow P s A; have he:0<v:=BProof.coin_pos ..; have hr:(v/2)≤ R:=Nat.le_ceil _; have hv:0<(R:ℝ):=(half_pos he).trans_le hr
 ext i; change (x i:ℝ)/(R:ℝ)-(y i:ℝ)/(R:ℝ)=(v/(2* (R:ℝ))) * ((nodeC x i:ℝ)/v-(nodeC y i:ℝ)/v); field_simp; unfold nodeC; simp [two_smul]; ring
omit [Fintype I] in
lemma spin_oasis (R:ℕ): Twah.nearPoints R (SitSpin.rest x w)=(fun i=> riseX R (x i.1)):=funext fun ⟨i,b⟩=>by cases b<;> rfl
lemma calibrated (s:ℕ)(P:Preparation): wakeSum ((gaugeRise P s A)∘x) G u w= ((frayR P A s:ℂ)^3/2)^G.length * wakeOf u x w (zoomR P A s) G := by
 let R:=zoomR P A s; let v i:= riseX R (x i); let y:=gaugeRise P s A ∘ x
 rw [wakePower (u:=v) (v:=y) (a:=frayR P A s) (by exact fray_p ..) (fun i j=> by exact delta_w s P _ _)] -- arg order check
 unfold wakeOf wakeSum; rw [spin_oasis]; rw [pow_mul,div_pow,div_pow,one_pow]; unfold v R; ring

-- the actual $R_s^3 \ q[s]$ operands, still uncentered.
def pill (P:Preparation) (A:ℝ)(s:ℕ)(Z:Lead.Clan)(x:Cover)(b:Twah.DirSpin): Papal.Weaver:= ((sPow P s A:ℂ)^3/16) • SitSpin.raw x Z b.1 b.2
lemma pill_q (P:Preparation)(A:ℝ)(s:ℕ)(Z:Lead.Clan)(x:Cover) : pill P A s Z x 0=(sPow P s A:ℂ)^3 • qRaw Z x:=by unfold pill qRaw; rw [smul_smul]; ring_nf; rfl
lemma pill_voice (P:Preparation)(A:ℝ)(s:ℕ)(Z:Lead.Clan)(x:Cover)(b:Twah.DirSpin): Voice (pill P A s Z x b) {nodeC x}:= (SitSpin.voice ..).hushed _
-- at issued spins 00 only (other spin labels can buy a different Motion phase)
lemma pill_theta (P:Preparation)(Z:Lead.Clan)(o:Cover)(z:ℤ) (n:Side) :
    reflMark (n:=n) 3 z (pill P A s Z o 0 n)=pill P A s Z ((plane 3 z).flee o) 0 n:=by
 rw [pill_q,pill_q]; let a:ℂ:= (sPow P s A:ℂ)^3; have he:= q_reflect Z o n z; ext1 x; let U:= carR 3 z n; change theta U (a • (qRaw Z o n (reflFields 3 z x)))= a • _
 rw [theta_smul,show star a=a by unfold a; simp]; exact congrArg (a • ·) (congr_fun he x)
lemma pill_read (P:Preparation)(s:ℕ)(Z:Lead.Clan)(x:Cover)(b:Twah.DirSpin): pill P A s Z x b=((frayR P A s:ℂ)^3/2) • (Hiro.unifyT x b).groundWord (zoomR P A s) Z:=by
 obtain ⟨c,b⟩:= b; rw [pill,SitSpin.in_Twah,smul_smul]; congr 1
 let v:=sPow P s A; let R:=zoomR P A s; have he:0<v:=BProof.coin_pos ..; have hr:v/2≤ R:=Nat.le_ceil _; have hv:0<(R:ℝ):=(half_pos he).trans_le hr; have hf: frayR P A s* (R:ℝ)=v/2:=by change v/(2*(R:ℝ))*R=v/_; field_simp
 change (v:ℂ)^3/16= (frayR P A s:ℂ)^3/2*(R:ℂ)^3; norm_cast; calc
   _=(frayR P A s * (R:ℝ))^3/2:=by rw [hf]; ring
   _= _:=by push_cast; ring

abbrev pillJar (P:Preparation)(u:I→Lead.Clan)(x:I→ Cover)(b:I→Twah.DirSpin)(A:ℝ)(s:ℕ)(G:List I):= (G.map fun i=> pill P A s (u i) (x i) (b i)).prod
omit [Fintype I] in
lemma pillJar_read (P:Preparation)(s:ℕ)(A:ℝ): pillJar P u x w A s G=((frayR P A s:ℂ)^3/2)^G.length • SitSpin.reader u x w (zoomR P A s) G:=by
 induction G with
 | nil=> simp [SitSpin.reader,pillJar,Twah.plait]
 | cons i G ih=>
    let a:I→Twah:= SitSpin.rest x w; let K:=zoomR P A s; let c:ℂ:=(frayR P A s:ℂ)^3/2
    unfold pillJar; rw [List.map_cons,List.prod_cons,pill_read,List.length_cons,pow_succ' ((frayR P A s:ℂ)^3/2)]; change (c • ((a i).groundWord K (u i))) * pillJar P u x w A s G= (c*c^G.length) • ((a i).groundWord K (u i) * _)
    rw [ih]; -- right reader? defeq
    change _=(c*c^G.length) • ((a i).groundWord K (u i) * Twah.plait (a) u G K); rw [Algebra.smul_mul_assoc,Algebra.mul_smul_comm,smul_smul]

abbrev insideJar (P:Preparation) (K:Calibration)(u:I→Lead.Clan)(G:List I)(x:I→ Cover)(b:I→Twah.DirSpin)(A:ℝ)(s:ℕ):= Papal.household K (pillJar P u x b A s G)
omit [Fintype I] in
theorem pillOnPane (P:Preparation) (K:Calibration)(G:List I)(x:I→ Cover)(s:ℕ):
    TestFamily K true (insideJar P K u G x w A s) ∧ TestFamily K false (insideJar P K u G x w A s) ∧ CovCover K (insideJar P K u G x w A s) ∧ ∀ n y z, (insideJar P K u G x w A s) n y=(insideJar P K u G x w A s) n z:=by
 let J:=K; unfold insideJar; rw [pillJar_read]; let h:= reader_voice u x w (zoomR P A s) G; let f:=((frayR P A s:ℂ)^3/2)^G.length; have hp(m:Side):= (h.hushed f).2 (K.c m); let v:= (h.hushed f).1.narrow K
 exact ⟨aux_test v.widen, ⟨⟨_,v⟩,fun _=> Filter.Eventually.of_forall fun m _=> hp m⟩,hp,fun n y z=> congrArg (f • ·) (reader_link u x w _ _ _ y z) ⟩

variable (V:Universal Y H φ μ X E') (Q:Coherent (i:=φ) (k:=μ) (E:=E') Y H D₀ π κ)
include V Q
lemma pill_uniform (q:Investment P E v)(L_:Dispatchers P)(K:Meritorious P) (p:0<A)(f:0<χ)(b:0<d)(B:ℕ):
   ∀ᶠ s:ℕ in atTop,∀ (x:I→ Cover), Twah.Spill (SitSpin.rest x w) (B:ℝ) d (zoomR P A s) →
     ‖E' s (insideJar P (tent Y H) u G x w A s) - wakeSum (gaugeRise P s A∘x) G u w‖ ≤ χ := by
 filter_upwards [fixedScale Y u G w V Q q L_ K p f b B] with s hp x X
 unfold insideJar; rw [calibrated,pillJar_read]; let Z:= reader_voice u x w (zoomR P A s) G; let F:= Papal.household (tent Y H) (SitSpin.reader u x w (zoomR P A s) G); let T:ℂ:= ((frayR P A s:ℂ)^3/2)^G.length
 change ‖E' s (T • F)-T*wakeOf u x w (zoomR P A s) G‖ ≤ χ; rw [E_scale Y H V s (aux_test ((Z.1.narrow _).widen)),←mul_sub,norm_mul]; apply le_trans (mul_le_of_le_one_left (norm_nonneg _) ?_) (hp x X)
 unfold T; rw [norm_pow]; apply pow_le_one₀ (norm_nonneg _); rw [norm_div,norm_pow,Complex.norm_real,Real.norm_of_nonneg (fray_p ..|>.le)]; norm_num; apply (div_le_one_of_le₀ (le_trans (pow_le_one₀ (fray_p ..|>.le) (fray_le ..)) (by norm_num)) (by norm_num)) -- tune
#print axioms pill_uniform
end Yoke
end YM.CF.Py.Rate.LocalLimit.Preparation
