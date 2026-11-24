import YM.SU5.SatinWard.Resolution.FigureJ
import YM.SU5.SatinWard.Resolution.BroochA
import YM.SU5.SatinWard.Resolution.Baffle
import YM.SU5.SatinWard.Resolution.Meetup
import YM.SU5.SatinWard.Resolution.ScaleW
import YM.SU5.SatinWard.Resolution.Basin
import YM.SU5.SatinWard.Resolution.Discus
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 700000
set_option maxRecDepth 8000
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
open BProof Pressure
namespace Regulator

open _root_.YM.Gleam.Luster.Almanac Grade
open Papal.SkyTax
open _root_.YM.Regis.Head
open _root_.YM.Gleam.Luster.Almanac Grade
open _root_.YM.CF.Py.Rate.LocalLimit.Preparation _root_.YM.CF.Py.Rate.LocalLimit.Preparation.Tabletop Shrine Ione.Clock Moto
variable (P:Spine)
local notation "W★"=>P.calibration
local notation "Ω★"=>P.run.meter
open Preparation.Yoke Spine.Gingham Spine.Gingham.Diary
open ShapeLab ResolutionFrame Shrine 
open SatinWard
local notation "R"=> Option Tilted.Ramp
local notation "T"=> P.calibration
local notation "ι₀"=>Wage4
local notation "L"=> P.par.R.L
local notation "V"=> P.large
variable (X:R)
variable {s v g w:ℕ}(p:Cover)(e:Almanac P s w p)(h:s≤g)
variable {f0:ℕ} {Z:ℕ→ℕ} {η:Type}[Fintype η]{C H A:ℝ}
variable (pZ:Tendsto Z atTop atTop)(W:Calendrical P C H A f0 η Z){Wq:Bool→ Coords Wage4} {Uq:ℕ→ Bool→ Coords Wage4} {F:ℕ→ℕ}(WX:CriticalClock P C H A g f0 η Wq F Z Uq) (b: Bool)
include pZ W WX h
local notation "Yt" => (sprintCost L)
local notation "k▶" i:max => P.engine ((Z ∘F) i)
local notation "j▶" i:max => P.nomadic ((Z ∘ F) i)
omit W WX pZ h
open Worth Pays BProof Aria Casting MacroGrid
open Selected
local notation "ζ"=>P.sidesPerTick
-- Annotated center. translate with the REAL home clock (not simplified half). Pose Hc later.
variable (M:P.par.R.L.val %16 =1) (k:P.NightCop) (j:Axis)(x:P.Spectrum0 j)
variable {a: Cover} (qa:ResidualPermit a) (y:Coords Wage4) (q:payable P v 2) {u d:ℝ}
variable (f:ℕ)(g₀:f ≤ v)
local notation "τ" i:max=> P.macroStep i
local notation "W₀" => choirWidth P
variable (ρ:Piano P f0 C H A η Z)
variable {C' d' μ Q:ℝ} {t' β Wp} {R':P.Register} (T₁:CouncilGrant P R' d' C' t' Z Wp β) (H': PublicKernel P Z Wp)
local notation "Ψ" i:max=> tollηw P β i
local notation "ℓ" i:max=> moonClock P i
local notation "fρ" i:max=> corridorHeight P i
local notation "R♛" i:max=> corridorR P i
local notation "M♛" i:max=> (R♛ i:ℝ)
local notation "ζ₁" i:max=> (↑(Ψ i):ℂ)
open OS.Semigroup OS.Semigroup.Marble PSE MarbleFace
variable (c:Cover) (t:P.Apron)
-- retain sign phase plus angular mark leg. torch.
open Internal CasaF.Signboard SignSlot
namespace MezzoBill
local notation "ℒ"=> P.calibration
structure Tone where
 coord : Axis
 slot : Wage3
 tint : ℝ
 price : |tint|=1
namespace Tone
variable (T':Tone)
abbrev shape (j:Axis)(a: Wage3) : Tone:=⟨j,a,1,abs_one⟩
def rk (A:Tone)(i:Axis): Tone:= let s:=StressFlux.sign (Signed.mirror i) A.coord; ⟨A.coord,A.slot,s*A.tint,by rw [abs_mul,A.price,mul_one]; unfold s StressFlux.sign; split <;> norm_num⟩
abbrev panelM (A:Tone): Op SU.Slot:= dynamicSpin (ShapeLab.leg A.slot)
lemma penny : ChiralX 0 T'.panelM:= (Θc.equivFun.symm (ShapeLab.leg T'.slot)).property
noncomputable abbrev suit (v:ℕ):= (T'.tint:ℂ)*(vigorΩ P.par v:ℝ)
end Tone
abbrev kinWidth (P:Spine):ℕ:= deltaWing P 0
structure Strip(P:Spine)(v:ℕ)(q:payable P v 2)(c:Cover)(t:P.Apron)(u:Tone):Prop where
 origin:t.s=v
 ink: ∃ a:Cover,nodeC a=c∧ t.F= (Tone.suit P u v) • planC P a u.coord u.panelM
 fare:∀ i:Axis,t.u i= kinWidth P ∧ |c i| ≤ P.sidesPerTick
lemma page_move(Q':Tone)(x y:Cover): P.chartAll y (planC P x Q'.coord Q'.panelM)=planC P (x+P.jump128 • y) Q'.coord Q'.panelM:=calendar_moves P x (horizonEntry Q'.coord Q'.panelM Q'.penny) y
lemma flutter(z:Cover): (plane j 0).motion (nodeC z)= nodeC ((plane j 0).flee z):=by
 funext i; rw [fling_move]; change (if j=i then _ else (2:ℕ) • z i+1)=(2:ℕ) • ((plane j 0).flee z i)+1 -- if condition
 rw [flee_pos]; by_cases h:j=i <;> simp only [show nodeC z i=(2:ℕ) • z i+1 from rfl,h,↓reduceIte,nsmul_eq_mul]; all_goals (push_cast; omega)
variable (mu:Tone)
lemma Strip.kissed (s:Strip P v q c t mu): Strip P v q ((plane j 0).motion c) (t.kiss P j) (Tone.rk mu j):=by
 obtain ⟨a,h,g⟩:= s.ink; have he: P.reflectTest j t.F= (Tone.suit P (Tone.rk mu j) v) • planC P ((plane j 0).flee a) mu.coord mu.panelM:=by
    let z:ℝ:= StressFlux.sign (Signed.mirror j) mu.coord; have ht:P.reflectTest j (planC P a mu.coord mu.panelM) = (z:ℂ) • planC P ((plane j 0).flee a) mu.coord mu.panelM:=by apply Subtype.ext; change mirror P.calibration j 0 (gardenFlower P.calibration a _ _)=(z:ℂ) • (gardenFlower P.calibration ((plane j 0).flee a) mu.coord mu.panelM); rw [Complex.coe_smul]; exact mirrorE mu.coord mu.panelM a mu.penny j 0
    rw [g,P.scale_mirror,ht,smul_smul]; apply congr_arg (· • planC P _ _ _); change star (_*_) *(z:ℂ)= ((z*mu.tint:ℝ):ℂ)*_; simp [mul_comm,mul_left_comm,mul_assoc]
 refine ⟨s.origin, ⟨(plane j 0).flee a,by rw [←h, flutter],he⟩,fun i=> ⟨(s.fare i).1,?_⟩⟩; by_cases h:j=i<;> simpa only [fling_move,h,↓reduceIte,mul_zero, add_zero,abs_neg] using (s.fare i).2
-- use existing M binder
lemma planted (c:Wage3) (q:payable P v 2): Strip P v q (homeTag P a) (JpriceApp P a M qa (ShapeLab.leg c) j v) (Tone.shape j c):=by
 let x:= tauprint P M qa; let I:= Tone.shape j c; refine ⟨rfl,⟨x,(nodeHome P M a qa).choose_spec,?_⟩,fun i=>⟨rfl,homeCost P a qa i⟩⟩; apply Subtype.ext; change spineField P.par P.calibration v j (ShapeLab.leg c) x= Tone.suit P I v • gardenFlower P.calibration x j I.panelM; unfold spineField; rw [ShapeLab.cols_apply, sum_eq_single c];
 · simp_rw [show ShapeLab.leg c c=1 from by simp [ShapeLab.leg],one_smul]; change vigorΩ P.par v • gardenFlower P.calibration x j I.panelM=(↑(1:ℝ)*(vigorΩ P.par v:ℝ):ℂ) • _; rw [Complex.ofReal_one,one_mul,Complex.coe_smul]
 · intro b _ e; rw [show ShapeLab.leg c b=0 from by simp [ShapeLab.leg, Ne.symm e],zero_smul]
 simp
lemma kinMoney (Q':Strip P v q c t mu) : t.realWidth P j=(kinWidth P:ℝ)*P.macroStep v:=by unfold Apron.realWidth MeshClock.bell; rw [(Q'.fare _).1,Q'.origin,Int.cast_natCast]; rfl
include ρ
lemma windMoney (h:f0 ≤ v): (kinWidth P:ℝ)* P.macroStep v+P.macroStep v ≤ moonClock P v:=by apply le_trans (?a) (windowLaw P ρ h); refine add_le_add (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (show _ from (?b))) (P.macroStep_pos _).le) le_rfl; unfold kinWidth deltaWing choirWidth; omega
lemma charge (h:f0≤v):0<vigorΩ P.par v:=div_pos (ρ.date.stock _ h).1.1 (sq_pos_of_pos (zero_lt_one.trans_le P.par.height))
structure YoungBank (P:Spine)(β:ℕ→ℝ)(v:ℕ)(U μ Q:ℝ):Prop where
 positive :0≤U
 coin : μ+16 ≤ corridorR P v
 rank :∀ (a b:Tone)(x y:Cover)(d:Gaia), Addressing (nodeC x) (nodeC y) d μ (corridorR P v) Q→
          ∀ (j:Axis)(t:P.Spectrum0 j), let W:=P.singleState j v t; let A:= planC P x a.coord a.panelM; let B:=planC P y b.coord b.panelM; Disp (corridorR P v) U ((↑(corridorR P v):ℂ)^6*(W (A*B)-W A*W B)) (gaugeKin a.coord a.panelM b.coord b.panelM d)
abbrev planResult (a b:Tone)(d:Gaia):ℂ:=(a.tint:ℂ)*(b.tint:ℂ)*gaugeKin a.coord a.panelM b.coord b.panelM d
variable (pL:64 ≤ P.par.R.L.val) {U:ℝ}
local notation "L₀"=> [b,!b]
local notation "q✯"=> corridorR P v
local notation "Lμ"=> (vigorΩ P.par v)
local notation "Ẑ"=> (↑Lμ:ℂ)
variable (b:Bool)(N:Bool→P.Apron)(O u:Bool→ Cover)(Vo:Bool→Tone)(Bt:∀ i,Strip P v q (O i) (N i) (Vo i))
local notation "U₀"=> P.vtile v ∘ u
local notation "u₀" i:max=> O i+P.sidesPerTick • u i
variable (pw: YoungBank P β v U μ Q)
include T₁ pw ρ Bt
set_option maxHeartbeats 320000 in
lemma narrative (g:f0 ≤ v)(d:Gaia)(S:Addressing (u₀ b) (u₀ (!b)) d μ (q✯) Q) (w:P.Turnstile j N [b,!b] (P.laysM ∘ U₀)): Disp (q✯) U ((↑q✯:ℂ)^6*((Ẑ)^2:ℂ)⁻¹* preMosaic P j x N b U₀) (planResult (Vo b) (Vo (!b)) d):=by
 choose f h hz using fun i=> (Bt i).ink; let W(i:Bool):=f i+P.jump128 • u i; let E(i):= planC P (W i) (Vo i).coord (Vo i).panelM; have he(i):nodeC (W i)=u₀ i:=by unfold W; rw [relation_core,h]
 let vC(i:Bool):ℂ:= ((Vo i).tint:ℂ); let z:= vC b*vC (!b); let y:= Ẑ; let Q:=P.singleState j v x; let G:=Q (E b*E (!b))-Q (E b)*Q (E (!b)); have u'(i):P.chartAll (u i) (N i).F=(vC i*y) • E i:= by rw [hz,map_smul]; change _ • P.chartAll (u i) (planC P (f i) _ _)=_; rw [page_move]
 have hv:‖z‖=1:=by unfold z vC; rw [norm_mul,Complex.norm_real, Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs, Tone.price,Tone.price,one_mul]
 rw [reveal_here P j x N b u v w (fun i=>(Bt i).1)]; dsimp only; rw [u',u',smul_mul_assoc,mul_smul_comm]; simp only [map_smul,smul_eq_mul]
 have ht:= (pw.rank (Vo b) (Vo (!b)) (W b) (W (!b)) d (by rw [he b,he (!b)]; exact S) j x); -- fill metas
 change Disp q✯ U ((q✯:ℂ)^6*(y^2)⁻¹ * (vC b*y*(vC (!b)*y*Q (E b*E (!b)))-(vC b*y*Q (E b))*(vC (!b)*y*Q (E (!b))))) (planResult (Vo b) (Vo (!b)) d)
 have hs:y≠0:=Complex.ofReal_ne_zero.mpr (ne_of_gt (charge P ρ g)); have t:Disp q✯ (‖z‖*U) (z*((q✯:ℂ)^6*G)) (planResult (Vo b) (Vo (!b)) d) := ht.increase z; rw [hv,one_mul] at t; refine Eq.subst (motive:=fun y=> Disp q✯ U y (planResult (Vo b) (Vo (!b)) d)) (?_) t; unfold G z; field_simp <;> ring
omit pw Bt
include T₁ k H' ρ pL
abbrev IdYear:= (Axis × Wage3) × Axis × Wage3
def anni (a:Axis× Wage3): Tone:= Tone.shape a.1 a.2
lemma starBank (Q μ:ℝ)(h:0≤Q)(v':0≤μ):∃ U:ℝ,0≤U ∧∀ᶠ v:ℕ in atTop, YoungBank P β v U μ Q:=by
 obtain ⟨n,w⟩:= polish_Rscope P pL
 choose EZ e WH using fun i:IdYear=> Lumi T₁ H' i.1.1 (anni i.1).panelM i.2.1 (anni i.2).panelM n k ((anni i.1).penny.1) ((anni i.2).penny.1) Q μ h v'
 let D:= ∑ i:IdYear,EZ i; have he:0≤D:=sum_nonneg fun a _=>e a; refine ⟨D,he,?_⟩; filter_upwards [eventually_all.mpr WH,w,(polish_late P).eventually_ge_atTop (μ+16)] with v x e0 q; have q:=q.trans e0.1; refine ⟨he,q,fun a b x' y d t j u=>?_⟩; let i: IdYear:= ( (a.coord,a.slot), (b.coord,b.slot)); exact ((x i x' y _ d t q e0.2).2 _ u).mono (single_le_sum (fun i _=> e i) (mem_univ _)) (zero_le_one.trans t.pLease)
#print axioms narrative
#print axioms starBank
end MezzoBill
end Regulator
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
