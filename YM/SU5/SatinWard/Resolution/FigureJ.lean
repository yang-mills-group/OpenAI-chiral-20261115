import YM.SU5.SatinWard.Resolution.Carnation
import YM.SU5.SatinWard.Resolution.Journal
import YM.SU5.SatinWard.Resolution.Synod
import YM.SU5.SatinWard.Resolution.Achilles
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 700000
set_option maxRecDepth 10000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase
open MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound
open Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker
open scoped ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy
open Tapestry Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open CF.Velvet CF.Pannier.Chancel
open Spine Pitching.Focus QuadClock Ione Vow Swell
open _root_.Zephyr.Chern
universe uΩ


open Papal CF.Papyrus.Franc.SatinForce CF.Pannier.Chancel Checkers

open CF.Papyrus.Franc.Loaves
-- CP3 package. PUBLIC, no topology/order changes
open Moon
open Horizons FoliageP BareProgram Moonlit Moonlit.SwitchC
open _root_.YM.Regis.Head.Brecht _root_.YM.Regis.Circuit _root_.YM.Regis.Circuit.SpringDay
open SlabMark VelourBoard Papal.SkyTax Cygnet VelourWiggle
open YM.Stationary (Gaia)
open SwitchC.Garland SwitchC.Garland.Terrace SwitchC.Garland.Terrace.Juniper
open Abacus CheckerFlag SlopeCharge Maxwell
open scoped RealInnerProductSpace ContDiff
namespace Fame
variable {P:Spine}{K:P.Register}{b C:ℝ}{t σ}{W:ℕ→ HorizonLens→ HorizonLens→ℝ}{β:ℕ→ℝ}
variable (T: CouncilGrant P K b C t σ W β)(H:PublicKernel P σ W)(F D: PlaqAxes)
open BProof Pressure
open _root_.YM.Gleam.Luster.Almanac Grade
open Papal.SkyTax
namespace Regulator
local notation "Ω" s:max=> hat P.par.R.L P.par.x s
open CasaF.Signboard CF.Tap SignSlot ShapeLab Emu
local notation "Ξ"=> principalKid
local notation "P₀"=> Op SU.Slot
-- Horizon ∆ spin unit.CP3.Credit.Ann
abbrev planC (P:Spine)(x:Cover)(k:Axis)(A:Op SU.Slot): P.Test:= P.art (gardenFlower P.calibration x k A) (aux_test (gardenShot P.calibration k A x).widen) -- galaxy intended InTest true not false.Gen rename. 
local notation "Φ"=> planC P
noncomputable abbrev gaugeKin (i:Axis)(A:P₀)(j:Axis)(B:P₀)(d:Gaia):ℂ:=64*bouquet i A j B d
include T H
variable (i:Axis)(A:P₀)(j:Axis)(B:P₀) {s:ℕ}
local notation "Xx" i:max=> wane (Ω i)
local notation "ℒ"=> P.calibration
omit T H in
private lemma tapeHealth (s:ℕ)(G:ℝ) {I J:Type}(L:Tab I)(R:Tab J){S:Tab (I×J)}(e:S=mulT L R)(x y z:P.Test)(hx:x.val= L.cookP G P.calibration)(hy:y.val= R.cookP G P.calibration)(hz:z.val=S.cookP G P.calibration){A B C:ℂ}{t:ℝ}{f:P.Test→ℂ}(p:‖f x-A‖≤ t)(q:‖f y-B‖ ≤ t)(v:‖f z-C‖≤t):HealthCase f x y C A B t:= by
 subst S; refine ⟨p,q,?_⟩; have h:x*y=z:=by apply Subtype.ext; change x.val*y.val=z.val; rw [hx,hy,hz,Tab.cook_mul]
 rw [h]; exact v
omit T H in
private lemma tap_op (s:ℕ)(F:Family P.calibration)(pF:TestFamily P.calibration true F){A:ℂ}{a:ℝ} (p:‖P.E s F - A‖≤a):‖(fun x:P.Test=>P.E s x.val) (P.art F pF)-A‖≤a:=p
-- always instantiate on diagram itself.Nothing specialized ✓
omit H T in
set_option quotPrecheck false in
private lemma helps (s:ℕ)(G:ℝ){I J:Type}[DecidableEq I][DecidableEq J](L:Tab I)(R:Tab J){x t:ℝ}{i j:ℕ} {S Q D: Finset Cover}(p:ticket S 1 x i L)(q:ticket Q 1 x j R)(w:ticket D 1 x (i+j) (mulT L R))(A B V:ℂ)
 (a0:‖P.E s (L.cookP G ℒ)- A‖ ≤ t)(b0:‖P.E s (R.cookP G ℒ)-B‖ ≤ t)(c0:‖P.E s ((mulT L R).cookP G ℒ)-V‖≤ t)
 (e:(∀ j:Axis,∀ v:P.Spectrum0 j, ‖P.singleState j s v (P.art (L.cookP G P.calibration) (aux_test (L.thermal p G)))-A‖≤t))(e':(∀ j:Axis,∀ v:P.Spectrum0 j, ‖P.singleState j s v (P.art (R.cookP G P.calibration) (aux_test (R.thermal q G)))-B‖≤t)) (f:(∀ j:Axis,∀ v:P.Spectrum0 j, ‖P.singleState j s v (P.art ((mulT L R).cookP G P.calibration) (aux_test (Tab.thermal _ w G)))-V‖≤t)) : let X:= P.art (L.cookP G P.calibration) (aux_test (L.thermal p G)); let Y:= P.art (R.cookP G P.calibration) (aux_test (R.thermal q G))
 HealthCase (fun t=> P.E s t.val) X Y V A B t ∧ ∀ j:Axis,∀ z:P.Spectrum0 j, HealthCase (P.singleState j s z) X Y V A B t:=by
 intro X Y; let Z:=P.art ((mulT L R).cookP G P.calibration) (aux_test (Tab.thermal _ w G)); constructor
 · exact tapeHealth s G L R (S:=mulT L R) rfl X Y Z rfl rfl rfl a0 b0 c0
 intro j z; exact tapeHealth s G L R (S:=mulT L R) rfl X Y Z rfl rfl rfl (e j z) (e' j z) (f j z)
lemma aphesis (τ:ℕ)(k:P.NightCop)(f:∀ g:SU.E, Commute A (matter g).val)(t':∀ g:SU.E, Commute B (matter g).val)(Q μ:ℝ)(w:0≤Q) :∀ᶠ s:ℕ in atTop,∀ x y:Cover,∀ R:ℝ,∀ d:Gaia,Addressing (nodeC x) (nodeC y) d μ R Q→ R ≤ polishQ P s ^ τ→ let Y:= Φ x i A; let Z:= Φ y j B; let A':= reading₀ i A; let B':=reading₀ j B
 HealthCase (fun t=>P.E s t.val) Y Z (duet i A j B (x-y)+ A'*B') A' B' (Xx s)∧∀ q:Axis,∀ t:P.Spectrum0 q, HealthCase (P.singleState q s t) Y Z (duet i A j B (x-y)+ A'*B') A' B' (Xx s):=by
 let eA:=(lessonZ i A 0).terms; let eB:=(lessonZ j B 0).terms
 have applyRegular {J : Type} [DecidableEq J] (m v : ℕ) :
     ∀ᶠ s : ℕ in atTop, ∀ (S : Finset Cover) (N : Tab J),
       WidthBudget S (budgetWidth (Ω s) v) → ∀ hN : SwitchC.ticket S 1 (Ω s) m N,
       N.terms ≤ Moon.voucher (Ω s) → Tab.holds ℒ (Real.sqrt (β s)) N →
       ‖(fun w : P.Test => P.E s w.val)
         (P.art (N.cookP (Real.sqrt (β s)) ℒ) (aux_test (N.thermal hN (Real.sqrt (β s)))))
         - N.issues (β s) (W s) (Real.sqrt (β s))‖ ≤ Xx s := by
   as_aux_lemma =>
     filter_upwards [T.powerF J 1 zero_lt_one le_rfl m v] with s hb
     intro S N width hN fee hn
     exact tap_op (P:=P) s (N.cookP (Real.sqrt (β s)) ℒ)
       (aux_test (N.thermal hN (Real.sqrt (β s)))) (hb S N width hN fee hn)
 have artProduct (L R Z : Family ℒ) (l : TestFamily ℒ true L)
     (r : TestFamily ℒ true R) (z : TestFamily ℒ true Z) (h : L * R = Z) :
     P.art L l * P.art R r = P.art Z z := by
   as_aux_lemma => exact Subtype.ext h
 have measuredProduct (f : P.Test → ℂ) (x y z : P.Test) (a b v : ℂ) (t : ℝ)
     (h : x * y = z) (hx : ‖f x - a‖ ≤ t) (hy : ‖f y - b‖ ≤ t)
     (hz : ‖f z - v‖ ≤ t) : HealthCase f x y v a b t := by
   as_aux_lemma => exact ⟨hx, hy, (congrArg (fun w => ‖f w - v‖ ≤ t) h).mpr hz⟩
 have changeTests {Y Z Y' Z' : P.Test} {V a b V' a' b' : ℂ}
     (pred : P.Test → P.Test → ℂ → ℂ → ℂ → Prop)
     (hY : Y = Y') (hZ : Z = Z') (hV : V = V') (ha : a = a') (hb : b = b')
     (ok : pred Y' Z' V' a' b') : pred Y Z V a b := by
   as_aux_lemma =>
     cases hY
     cases hZ
     cases hV
     cases ha
     cases hb
     exact ok
 filter_upwards [eventuallyPay P eA,eventuallyPay P eB,eventuallyPay P (eA*eB),rootPermit P Q μ w τ 0,(LocalLimit.turnover P.par).eventually_ge_atTop 1, applyRegular (J:=Ξ) 2 (τ+1),applyRegular (J:=Ξ×Ξ) 4 (τ+1), university (J:=Ξ) P k 2 1 T zero_lt_one le_rfl (τ+1), university (J:=Ξ×Ξ) P k 4 1 T zero_lt_one le_rfl (τ+1)] with s t₁ t₂ t₃ z t p p' u u'
 as_aux_lemma =>
  intro x y R d D r Y Z A' B'; let X:Finset Cover:={nodeC x}; let W':Finset Cover:={nodeC y}; let L:=lessonZ i A x; let L':= lessonZ j B y; let M:=mulT L L'
  let PV:=X∪ W'; have ht: WidthBudget PV (budgetWidth (Ω s) (τ+1)):=widenWidth (union_subset_union (singleton_subset_iff.mpr ((pav_v (nodeC x) (nodeC x) 0).mpr (by simp))) (singleton_subset_iff.mpr ((pav_v (nodeC y) (nodeC y) 0).mpr (by simp)))) le_rfl (z _ _ _ R r D)
  let a:= singer_credit i x A 1 (Ω s); let b:= singer_credit j y B 1 (Ω s); let μ₀:= Ω s; have hp:|(Real.sqrt (β s))| ≤ Moon.fabric μ₀:= Picker.permit P.run P.law P.history T.order.tendsto_atTop T.path_permanent s t
  let Ha:=kid_axis_accepted i x A (Real.sqrt (β s)) ℒ f; let Hb:=kid_axis_accepted j y B (Real.sqrt (β s)) ℒ t'; let Hm:= Tab.holds_mul Ha Hb; have qa : L.terms≤Moon.voucher μ₀:= t₁; have qb:L'.terms≤Moon.voucher μ₀:= t₂; have q:M.terms≤Moon.voucher μ₀:=by unfold M; rw [Tab.mul_cost]; exact t₃
  have hm:SwitchC.ticket PV 1 μ₀ 4 M:= Tab.mul_ticket (A:=L) (D:=L') (fun i h=> improve (a i h) subset_union_left (le_refl 2)) (fun i h=> improve (b i h) subset_union_right (le_refl 2)); have wx:= widenWidth (subset_union_left (s₁:=X) (s₂:=W')) le_rfl ht; have wy:= widenWidth (subset_union_right (s₁:=X) (s₂:=W')) le_rfl ht
  let yA:= P.art (L.cookP (Real.sqrt (β s)) ℒ) (aux_test (L.thermal a (Real.sqrt (β s)))); let yB:= P.art (L'.cookP (Real.sqrt (β s)) ℒ) (aux_test (L'.thermal b (Real.sqrt (β s)))); have he': Y=yA:=Subtype.ext (velvety ..).symm; have hg: Z=yB:=Subtype.ext (velvety ..).symm
  let W0(U:Tab Ξ):= U.issues (β s) (W s) (Real.sqrt (β s)); have hy: A'=W0 L:=(arRos H i x A (Real.sqrt (β s)) _).symm; have hB: B'=W0 L':=(arRos H j y B (Real.sqrt (β s)) _).symm; have ht': duet i A j B (x-y)+ A'*B'=(M.issues (β s) (W s) (Real.sqrt (β s))):= (duetLaw H i x y A (Real.sqrt (β s)) B j _).symm
  have hXY : yA * yB = (P.art (M.cookP (Real.sqrt (β s)) ℒ) (aux_test (M.thermal hm (Real.sqrt (β s))))) := artProduct (L.cookP (Real.sqrt (β s)) ℒ) (L'.cookP (Real.sqrt (β s)) ℒ) (M.cookP (Real.sqrt (β s)) ℒ)
    (aux_test (L.thermal a (Real.sqrt (β s)))) (aux_test (L'.thermal b (Real.sqrt (β s)))) (aux_test (M.thermal hm (Real.sqrt (β s))))
    (Tab.cook_mul (A:=L) (D:=L') (x:=(Real.sqrt (β s))) (K:=ℒ)).symm
  let hExpectL := p X L wx a qa Ha
  let hExpectR := p W' L' wy b qb Hb
  let hExpectPair := p' PV M ht hm q Hm
  let hStateL := u X L a (Real.sqrt (β s)) hp qa Ha wx
  let hStateR := u W' L' b (Real.sqrt (β s)) hp qb Hb wy
  let hStatePair := u' PV M hm (Real.sqrt (β s)) hp q Hm ht
  as_aux_lemma =>
   apply changeTests (fun Y Z V a b => HealthCase (fun w => P.E s w.val) Y Z V a b (Xx s) ∧
     ∀ q : Axis, ∀ t : P.Spectrum0 q, HealthCase (P.singleState q s t) Y Z V a b (Xx s)) he' hg ht' hy hB
   exact ⟨measuredProduct (fun w => P.E s w.val) yA yB (P.art (M.cookP (Real.sqrt (β s)) ℒ) (aux_test (M.thermal hm (Real.sqrt (β s))))) (W0 L) (W0 L') (M.issues (β s) (W s) (Real.sqrt (β s))) (Xx s)
       hXY hExpectL hExpectR
       (tap_op (P:=P) s (M.cookP (Real.sqrt (β s)) ℒ) (aux_test (M.thermal hm (Real.sqrt (β s))))
         (A:=M.issues (β s) (W s) (Real.sqrt (β s))) (a:=Xx s) hExpectPair),
     fun q' v => measuredProduct (P.singleState q' s v) yA yB (P.art (M.cookP (Real.sqrt (β s)) ℒ) (aux_test (M.thermal hm (Real.sqrt (β s))))) (W0 L) (W0 L') (M.issues (β s) (W s) (Real.sqrt (β s))) (Xx s)
       hXY (hStateL q' v) (hStateR q' v) (hStatePair q' v)⟩
#print axioms aphesis
omit T H
-- same P units. R gauge.Now Ω
variable {R μ Q G:ℝ}{x y:Cover}{d:Gaia}
lemma gaugeDay (g:Addressing (nodeC x) (nodeC y) d μ R Q) (pR: μ+16 ≤ R): Addressing x y d (μ/2) (R/2) Q:=by
 let z:=(x-y:Cover); have hp:0<R:=zero_lt_one.trans_le g.pLease
 have he:nodeC x-nodeC y=2 • (x-y:Cover):=by funext i; change ( (2:ℕ) • x i+1)-( (2:ℕ) • y i+1)=(2:ℕ) • (x i-y i); simp_rw [nsmul_eq_mul]; omega
 have hx:patchF (nodeC x-nodeC y) R=patchF (x-y) (R/2):=by unfold patchF; rw [he,show scape ((2:ℕ) • (x-y:Cover))=(2:ℝ) • scape (x-y:Cover) from (by rw [two_smul ℕ, two_smul ℝ, scape_add])]; rw [smul_smul,show R⁻¹*(2:ℝ)=(R/2)⁻¹ from by field_simp]
 refine ⟨div_nonneg g.r₀ (by norm_num),by linarith only [pR],g.area,g.sizes,?_⟩; rw [←hx]; exact g.meters.trans_eq (by ring)
private lemma drumScale (h:0<R) (t:Disp (R/2) G (((R/2:ℝ):ℂ)^6*duet i A j B (x-y)) (bouquet i A j B d)):Disp R (128*G) ((R:ℂ)^6*duet i A j B (x-y)) (gaugeKin i A j B d):=by
 let Z:= ((R/2:ℝ):ℂ)^6*duet i A j B (x-y); have ht:=t.nn; have hz:=t.increase (64:ℂ); rw [show ‖(64:ℂ)‖=(64:ℝ) from by norm_num] at hz; rw [show (R:ℂ)^6*duet i A j B (x-y)=64*Z from by unfold Z; push_cast; ring]; refine ⟨by positivity,hz.shadow.trans (by linarith),hz.amount.trans_eq (?_)⟩; ring
variable {U H₂:ℝ}
private lemma amenda {G A B C D E:ℂ} {K R w:ℝ}(h:1≤R) (u:‖A-B‖≤w)(v:‖D-E‖≤w)(y:‖G-(C+B*E)‖≤w)(t₁:R^9*w≤1)(t₂:w≤1){k:ℂ}(e:Disp R K ((R:ℂ)^6*C) k): Disp R (K+(‖B‖+‖E‖+2)) ((R:ℂ)^6*(G-A*D)) k:=by -- remove p q
 let Z:=(R:ℂ)^6; let f':=Z*((G-(C+B*E))-(A*D-B*E)); let l:=Z*C; let p:=‖B‖; let q:=‖E‖; have hp:0<R:=by linarith
 have wp:0≤ w:= (norm_nonneg _).trans u; have sp:R^7*w≤1:=(mul_le_mul_of_nonneg_right (pow_le_pow_right₀ h (by norm_num : (7:ℕ) ≤9)) wp).trans t₁
 have H:‖A*D-B*E‖≤ (p+q+1)*w:=by
    rw [show A*D-B*E=(A-B)*E + A*(D-E) from by ring]; refine (norm_add_le ..).trans ?_
    rw [norm_mul,norm_mul]; have hu:‖A‖ ≤ p+1:= (norm_le_norm_sub_add A B).trans ((add_le_add (u.trans t₂) le_rfl).trans_eq (add_comm ..)); exact (add_le_add (mul_le_mul_of_nonneg_right u (norm_nonneg _)) (mul_le_mul hu v (norm_nonneg _) ((norm_nonneg _).trans hu))).trans_eq (by unfold p q; ring)
 have g:0≤p+q+2:=by unfold p q; positivity
 have a':Disp R (p+q+2) f' 0:= ⟨g,(norm_zero).trans_le g,by
    rw [sub_zero]; unfold f'; rw [norm_mul]; have hk:‖Z‖=R^6:=by unfold Z; rw [norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hp]
    rw [hk]; apply le_trans (mul_le_mul_of_nonneg_left ((norm_sub_le ..).trans (add_le_add y H)) (by positivity)); rw [le_div_iff₀ hp]; nlinarith only [mul_le_mul_of_nonneg_left sp g]⟩
 rw [show (R:ℂ)^6*(G-A*D)= l+f' from (by unfold l f' Z; ring),← show k+(0:ℂ)=k from add_zero _]; exact e.plus a'
include T H
theorem Lumi (τ:ℕ)(k:P.NightCop)(f:∀ g:SU.E, Commute A (matter g).val)(t':∀ g:SU.E, Commute B (matter g).val) (Q μ:ℝ)(w:0≤Q)(φ:0≤μ) :∃ C:ℝ,0 ≤ C ∧∀ᶠ s:ℕ in atTop,∀ x y:Cover,∀ R:ℝ,∀ d:Gaia, Addressing (nodeC x) (nodeC y) d μ R Q → μ+16 ≤ R→ R ≤ polishQ P s ^ τ → let Y:= Φ x i A; let Z:= Φ y j B; let cost(q:P.Test→ℂ):= ((R:ℂ)^6)*(q (Y*Z)-q Y*q Z)
 Disp R C (cost (fun v=> P.E s v.val)) (gaugeKin i A j B d)∧∀ q:Axis,∀ t:P.Spectrum0 q, Disp R C (cost (P.singleState q s t)) (gaugeKin i A j B d):=by
 obtain ⟨C,v,u⟩:=sketchPay H Q (μ/2) (by positivity) i A j B; refine ⟨128*C+(‖reading₀ i A‖+‖reading₀ j B‖+2),by positivity,?_⟩; filter_upwards [aphesis T H i A j B τ k f t' Q μ w, phaseRent P τ] with s a b x y R d h p₀ p₁; intro X Y q; obtain ⟨q',q''⟩:= a x y R d h p₁; let hw:= b.2.2 _ h.pLease p₁; let hx:=drumScale i A j B (zero_lt_one.trans_le h.pLease) (u x y d _ (gaugeDay h p₀)); refine ⟨amenda h.pLease q'.1 q'.2.1 q'.2.2 hw b.2.1 hx,fun j' t=> ?_⟩; let z:=q'' j' t; exact amenda h.pLease z.1 z.2.1 z.2.2 hw b.2.1 hx
#print axioms Lumi
end Regulator
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
