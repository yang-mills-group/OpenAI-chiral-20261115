import YM.SU5.Registration.Rise.Appraise
import YM.SU5.Registration.Rise.AtFull
import YM.SU5.Registration.Heave.LaceSale
import YM.SU5.Registration.Heave.FlashFresh
import SatinThinFront
import SatinThinVista
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
set_option maxHeartbeats 280000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia) -- tune
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
namespace Spine
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel
open Six Set
open CF.Velvet CF.Pannier.Chancel
open ClockBooking
open Papal Papal.LaceLayer
variable (P:Spine)(j:Axis)(x:P.Spectrum0 j)(k:Lead.Clan)
local notation "ε" => (purePrice k:ℂ)
variable (s n w:ℕ)
local notation "A" => P.thinMat k s n
local notation "w'" => P.probeClock n j
local notation "F₀" => P.frontMat k n
local notation "F" => P.shifts j (w:ℤ) (P.frontMat k n)
local notation "Ψ" => P.shifts j (w:ℤ) (P.frontMat k n-ε • 1)
-- consecutive at level s. Enough room by paying probe clock plus width options.
variable (p:P.probeClock n j≤w)
lemma Apron.full_at (P:Spine)(B:P.Apron): B.full P B.s=B.F:=by unfold full; rw [Nat.sub_self]; rfl
lemma Apron.zoom_at (P:Spine)(j:Axis)(B:P.Apron): B.zoom P B.s j=B.u j:=by unfold zoom; rw [Nat.sub_self,pow_zero,one_mul]
local notation "H"=> P.ColorHil j x
local notation "T"=>P.physicalEnergy j x
local notation "E"=> (P.physicalEnergy j x).E
local notation "t"=>whenly (timeMesh P.par) s w
include p in
lemma invested_front : P.InCase j s (w+w) (F-ε • 1):= by
 have h: (A).zoom P s j ≤ w:= ((A).zoom_at P j).trans_le p
 have he: (A).full P s= F₀:= (A).full_at P
 have v:= (A).entrusted P j s le_rfl w w h h; rw [he] at v; exact v.except ((InCase.units P j s (w+w)).scale ε)
-- solutions to algebra conflict shadow notation p.
def printGaps (a b:ℝ≥0): (P.ColorHil j x).Op:= P.stageH j x (P.thinMat k s n) a b - (purePrice k:ℂ) • (P.physicalEnergy j x).E (a+b)
lemma pay_expensive {u l a b:ℝ≥0}(x':(P.thinMat k s n).allowance P j ≤ u)(hz:u≤l)(y:(P.thinMat k s n).allowance P j≤a)(he:a≤b) : P.printGaps j x k s n l b= E (l-u)*P.printGaps j x k s n u a * E (b-a):=by
 unfold printGaps; rw [P.stage_more _ _ _ x' hz y he,mul_sub,_root_.sub_mul,P.stage_scale_r]; congr 2
 rw [show E (l - u) * E (u + a) = E ((l-u)+(u+a)) from ((T).time ..).symm, show E ((l-u)+(u+a)) * E (b-a)= E (((l-u)+(u+a))+(b-a)) from ((T).time ..).symm, ←add_assoc (l-u),tsub_add_cancel_of_le hz]; rw [add_assoc l,add_tsub_cancel_of_le he]
include p in
lemma print_at_clock (h:P.InCase j s (w+w) (F-ε • 1))(hw:0<w+w): h.charges x hw=P.printGaps j x k s n t t:=by
 have v:(A).zoom P s j≤w:= ((A).zoom_at P j).trans_le p; have e: (A).full P s= F₀:= (A).full_at P
 have u:P.InCase j s (w+w) F:=by have ht:= (A).entrusted P j s le_rfl w w v v; rwa [e] at ht
 let g:= InCase.units P j s (w+w)
 have ht: u.charges x hw=P.stageH j x A t t:= (A).consumes P j x s le_rfl w w u v v hw (by rw [e])
 change (u.except (g.scale ε)).charges x hw =_
 rw [u.charges_except x (g.scale _), g.charges_scale x ε hw,show g.charges x hw=_ from InCase.charges_units x hw,when_add,ht]; rfl
variable {K:P.Register}{Y':Supplier}{Λ B:ℝ}(U:uniform P K Y' Λ B) (PZ:P.NightCop)
include U PZ
lemma price_front (σ:ℝ)(h:0<σ): ∀ᶠ n:ℕ in atTop,∀ᶠ w:ℕ in atTop,P.probeClock n j≤ w ∧ ∀ᶠ s in atTop, ∀ (x:P.Spectrum0 j), ‖P.printGaps j x k s n (whenly (timeMesh P.par) s w) (whenly (timeMesh P.par) s w)‖ ≤ 6*Real.exp 1*σ:=by
 obtain ⟨q,δ,b,z,C,W,v,_⟩:= U.1.paper
 let D:=3*(Real.exp 1*σ); have hD :0 < D:=by unfold D; positivity
 filter_upwards [P.front_fresh k (σ/4) (by positivity)] with n p; let T':= insert 0 (P.flash n).patio
 filter_upwards [selling P.run P.large v U.2 U.1.nerve T' (mem_insert_self _ _) (P.dew_admits k n) σ h p j,eventually_ge_atTop (P.probeClock n j),eventually_gt_atTop 0] with w (e:∀ᶠ s in atTop,_) P' hw
 refine ⟨P',e.mono fun s g x=>?_⟩
 let Y:= P.shifts j (w:ℤ) (P.frontMat k n)-ε • 1; let v:=P.invested_front j k s n w P'; let H₁:=add_pos hw hw
 have hv: Issues P.run P.large s j (w+w) id P.history (fun _=> Y.val) D:=by
    let U:=PZ s;
    have hx:Y.val = relocate P.calibration j (w:ℤ) (household P.calibration (P.dewGauge k n)):=by
       unfold Y; rw [←map_one (P.shifts j (w:ℤ)),← map_smul,←map_sub]; rfl
    filter_upwards [U,P.history.finance s,P.stockGo.eventually g] with i u h f m f'
    change _ → _ → _ → ‖Journey.sharp P.run P.large s (P.nomadic i) (P.engine i) (SlabMark.banner j _ _ _ Y.val)‖ ≤ _
    rw [hx]; exact f _ h u m f'
 rw [← print_at_clock P j x k s n w P' v H₁]
 obtain ⟨S,h,g⟩:= v.aSize; obtain ⟨C,m⟩:= Journey.valuation P.run P.large h
 apply ((v.cap x H₁).trans (ClockBooking.earned P.run P.large P.law s P.history P.projection.clipped j (w+w) S (BQueue.stay h (add_pos_of_nonneg_of_pos (Tower.pay_nonneg m) zero_lt_one) (fun i x=>(m i x).trans (le_add_of_nonneg_right zero_le_one))) g id tendsto_id H₁ hD hv (f₀:=v.card) (congrArg Subtype.val v.entry) (P.room j))).trans_eq
 unfold D; ring
local notation "M" s:max n:max=>whenly (timeMesh P.par) s n
-- spend the extra width tolerance to cast in the common shrinking path before granting any budgets.
-- any j x ANY later padding; only >= (moving) specified anchor (positive fixed here).
def Lightweight (σ:ℝ)(a:ℝ≥0)(s n:ℕ) : Prop:=
    ∀ j:Axis,∀ (k:Lead.Clan), (P.thinMat k s n).allowance P j < a ∧ ∀ u v:ℝ≥0, a≤u → a≤v → ∀ (x:P.Spectrum0 j), ‖P.printGaps j x k s n u v‖ ≤ σ
omit U PZ in
lemma current_gust : Tendsto (fun s:ℕ=>whenly (timeMesh P.par) s w) atTop (𝓝 0):=by
 apply NNReal.tendsto_coe.mp; have h (s':ℕ): ((M s' w):ℝ)=(w:ℝ)*P.macroStep s':= calc _ = bell (timeMesh P.par) s' (w:ℤ):= (natural_time ..).symm
                                                                          _=_:=by unfold macroStep bell; push_cast; rfl
 simpa only [h, NNReal.coe_zero,mul_zero] using P.macroStep_zero.const_mul (w:ℝ)
lemma all_afford (σ:ℝ)(v:0<σ)(a:ℝ≥0)(u:0<a): ∀ᶠ n:ℕ in atTop,∀ᶠ s:ℕ in atTop,P.Lightweight σ a s n:=by
 let W(n s:ℕ)(j:Axis)(k:Lead.Clan):Prop:=(P.thinMat k s n).allowance P j<a ∧ ∀ u v:ℝ≥0,a≤u→a≤v→∀x, ‖P.printGaps j x k s n u v‖ ≤ σ
 let ε':= σ/(6*Real.exp 1); have eh:0<ε':=by unfold ε'; positivity
 have ht(j:Axis)(k:Lead.Clan):∀ᶠ n:ℕ in atTop,∀ᶠ s:ℕ in atTop,W n s j k:= by
    filter_upwards [P.price_front j k U PZ ε' eh] with n v; obtain ⟨w,q,x⟩:=v.exists
    filter_upwards [x,(P.current_gust w).eventually (gt_mem_nhds u)] with s h g
    have he: M s w < a:=g; let A':= P.thinMat k s n
    have hg: A'.allowance P j ≤ M s w:= (when_le ..).2 q
    refine ⟨hg.trans_lt he,fun y z u v x=>?_⟩
    rw [P.pay_expensive j x k s n hg (he.le.trans u) hg (he.le.trans v)]; refine (P.heater_norm ..).trans ((h x).trans_eq ?_); unfold ε'; field_simp
 exact ((eventually_all.mpr fun j=>eventually_all.mpr (ht j))).mono (fun n he=>eventually_all.mpr fun i=> eventually_all.mpr fun k=>he i k) -- notation definition delta
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms Spine.price_front
#print axioms Spine.pay_expensive
#print axioms Spine.all_afford
