import YM.SU5.CompassRose.Basilica
import YM.SU5.CompassRose.Tropics

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 500000
set_option quotPrecheck false
set_option linter.unusedSectionVars false

namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine

open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open Spine Preparation.Yoke
open CF.Velvet CF.Pannier.Chancel CF.Pannier.Chancel.Rous Pressure
open YM.Stationary (Gaia)
open Onyx Regis.Circuit Regis.Head Regis.Head.Brecht Exterior Hiro

namespace Rose
open EmberWind Jewel
open Lamour Lamour.Bridge
variable (P:Spine)(s:ℕ)(A:ℝ)(β:ℕ→ℝ)
local notation "K"=> P.calibration
local notation "R" s:max=> sPow P.par s A
local notation "K!" f:max => Papal.household P.calibration f
local notation "P$" s:max => P.eReadL s
local notation "ζ⇒" => P.reflectTest 3
local notation "M$" => P.halfShift 3
local notation "lamp" X:max => temp (hat P.par.R.L P.par.x X)
open Fixture Shuttle Arrival
open Aria Casting DoseTravel SpinReceipt
open Basilica
namespace Vista
variable (k:ℕ)
local notation "j" => (3:Axis)
local notation "Ls" => timeMesh P.par
local notation "ℓ"=> (K).ℓ
local notation "d"=> ruler P.par.block
abbrev pitchF : Cover:= ![(1:ℤ),2,16,2]
lemma pitch_pos (i:Axis) : 0< pitchF i:=by fin_cases i<;> norm_num [pitchF]
lemma pitch_ley (i:Axis): (pitchF i:ℝ)=leyline i:=by fin_cases i <;> norm_num [pitchF,leyline]
local notation "ζ" s:max=> (zoomR P.par A s)
def request (A:ℝ)(s:ℕ):ℕ:= ⌊(zoomR P.par A s:ℝ)/(d : ℝ)⌋₊
local notation "N" s:max => request P A s
abbrev downLey : Cover:= -(k • pitchF)
-- k = integer matter-slot ruler distances. in Apron pose coordinates double this.
abbrev KEntrance (x:Cover): Cover:= (d) • x
abbrev entryA : Cover:= KEntrance P (downLey k)
abbrev arrivalW (F:Fixture) (i:Cover): P.Test:= Fixture.litP P s A β F (KEntrance P i)
lemma laneR (s k:ℕ)(_h:k= N s)(i:Axis) : riseX (ζ s) (entryA P k) i= (k:ℝ) * (d:ℝ)/(ζ s:ℝ) * (-leyline i):=by change (↑(d * (-( (k:ℤ)*pitchF i ))):ℝ)/(ζ s:ℝ)=_; push_cast [pitch_ley]; ring
variable (p:0<A)
include p
lemma takesOff : Tendsto (request P A) atTop atTop:= tendsto_nat_floor_atTop.comp (Tendsto.atTop_div_const (show 0<(d:ℝ) from Int.cast_pos.mpr (ruler_gene _)) (tendsto_natCast_atTop_atTop.comp (zoom_grows P.par p)))
lemma fork_lease : P.PencilLease A (-leyline) 0 (fun s=> entryA P (N s)) (fun _=> KEntrance P 0):=by
 let R'(s:ℕ):ℝ:= ζ s; let C:ℝ:=d; let K'(s:ℕ):ℝ:= N s; let f(s):= K' s*C/R' s; have hC:0<C:= Int.cast_pos.mpr (ruler_gene _); have hp:=zoom_pos (A:=A) P; have hv: Tendsto R' atTop atTop:= tendsto_natCast_atTop_atTop.comp (zoom_grows P.par p); have hu:Tendsto (fun x=> C/R' x) atTop (𝓝 0):=by simpa [div_eq_mul_inv,Function.comp_def] using (tendsto_inv_atTop_zero.comp hv).const_mul C
 have ht:Tendsto f atTop (𝓝 1):=by
    have hc(s:ℕ):0 < R' s:= Nat.cast_pos.mpr (hp s)
    have h(s:ℕ):1-C/R' s ≤ f s ∧ f s≤1:=by
       have hx: K' s ≤ R' s/C:= Nat.floor_le (div_pos (hc s) hC).le; have hw:R' s/C<K' s+1:= Nat.lt_floor_add_one _; rw [div_lt_iff₀ hC] at hw; unfold f; rw [sub_div' (hc s).ne',div_le_div_iff_of_pos_right (hc s), div_le_iff₀ (hc s)]; constructor <;> linarith only [hw,(le_div_iff₀ hC).1 hx]
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le _ tendsto_const_nhds (fun s=>(h s).1) (fun s=>(h s).2); simpa using (tendsto_const_nhds (x:=1)).sub hu
 refine ⟨(appoint_as P.par p _ _).2 ?_,(appoint_as P.par p _ _).2 ?_,fun t=> absurd t (neg_ne_zero.mpr ley_seen)⟩
 · have hu:= ht.smul_const (-leyline); rw [one_smul] at hu; apply hu.congr; intro i; ext k; rw [laneR P]; swap; · rfl
   rfl
 apply tendsto_const_nhds.congr; intro n; ext i; simp [KEntrance,riseX,moor]
omit p

variable (F:Fixture)(Z₀:Cover)
abbrev reachP :ℕ := F.r+10+ ℓ
noncomputable def squareS : Finset Cover:= P.placeSet (F.inkP (KEntrance P Z₀)) Vacancy.ordinate (-(2 • Z₀))
lemma withinS {p:Cover}(v:p∈squareS P F Z₀)(i:Axis) : -(d)*(reachP P F:ℤ)+ℓ ≤ p i ∧ p i +ℓ≤(d)*(reachP P F:ℤ):=by
 obtain ⟨u,h,e⟩:= P.charterSize Vacancy.ordinate (-(2 • Z₀)) Vacancy.ordinate_one (F.inkP (KEntrance P Z₀)) _ v i; rw [e, if_pos (Vacancy.ordinates i), show (-(2 • Z₀):Cover) i= -(2* Z₀ i) from (by simp)]; obtain ⟨h,u'⟩ := (pav_v (nodeC (KEntrance P Z₀)) u (F.r+8)).1 h i
 have ht : nodeC (KEntrance P Z₀) i=2*((d)*Z₀ i)+1 := by simp [nodeC,KEntrance]
 have he:1≤d:=ruler_gene _; rw [ht] at h u'; unfold reachP; push_cast at *; have hx : (F.r:ℤ)≥ 0 := Int.natCast_nonneg _; have hw:(ℓ:ℤ)≥ 0:= Int.natCast_nonneg _; constructor <;> nlinarith only [he,h,u',mul_le_mul_of_nonneg_right he hx,mul_le_mul_of_nonneg_right he hw]
noncomputable def ritzy : P.Apron:= let x:=(KEntrance P Z₀); let v:= Fixture.litP P s A β F x; let X:= (-(2 • Z₀)); ⟨s,fun _=> reachP P F,fun _=> by unfold reachP; omega,P.chartAll X v, squareS P F Z₀,P.place_test _ Vacancy.ordinate X ((Tapestry.locates ..).mpr (F.inInk P s A β x).1), P.cruise_color _ _ (show v∈enclave K from F.inInk P s A β x|>.2), fun i p h=> withinS P F Z₀ h i⟩
lemma rit_code : (ritzy P s A β F Z₀).s=s:= rfl
lemma exact_rit : P.issuing s (ritzy P s A β F Z₀) (2 • Z₀) = arrivalW P s A β F Z₀:=by
 let G:= arrivalW P s A β F Z₀; change P.chartAll _ (P.conveying s (s-s) (P.chartAll _ G))=_; rw [Nat.sub_self]; change P.chartAll _ (P.chartAll _ G)=G; rw [P.chart_ids, add_neg_cancel]; exact Subtype.ext ((P.followsChart ..).trans (Vacancy.cad_zero _ _ ((marque ..).1 G.property)))
lemma clock_cost (i:Axis): clockP P (ritzy P s A β F Z₀) i= (reachP P F :ℝ)*P.macroStep s:=by unfold clockP Apron.realWidth; change MeshClock.bell Ls s (reachP P F)=_; simp only [MeshClock.bell,MeshClock.mill,Int.cast_natCast]; rfl

local notation "Pre" s:max => ritzy P s A β copper (downLey (N s))
local notation "Post" s:max => ritzy P s A β copper 0
abbrev sunset : P.Apron:= Pre s
abbrev sunrise : P.Apron:= Post s
abbrev pre0 (k:ℕ): Cover:= 2 • downLey k
abbrev sunrise0 : Cover:= 2 • (0:Cover)
abbrev viewQ : Vantage:= P.meshPose s (pre0 (N s))
abbrev viewT : Vantage:= P.meshPose s sunrise0
include p
lemma openDoors : ∀ᶠ s in atTop, Plaza P (Pre s) (Post s) (viewQ P s A) (viewT P s):=by
 let f(s:ℕ)(i:Axis):= (-(2:ℝ))*(N s:ℝ)*(pitchF i:ℝ); have he(s:ℕ)(i:Axis): viewQ P s A i=f s i * P.macroStep s:= by unfold viewQ; rw [tile_pose]; change (↑((2:ℤ)*( - ( (N s:ℤ)*pitchF i))))*(P.macroStep s)=_; push_cast; unfold f; ring
 have ht(s:ℕ)(i:Axis): viewT P s i=0:=by unfold viewT; rw [tile_pose]; simp [MacroGrid.atTick, sunrise0]
 filter_upwards [(takesOff P A p).eventually_gt_atTop (reachP P copper)] with s v
 let z:ℝ:= reachP P copper; let Q:ℝ:=N s; have hv:z<Q:= Nat.cast_lt.mpr v; constructor
 · intro i; rw [clock_cost,clock_cost,he,ht]; let y:ℝ:= pitchF i; have hh:1≤y:=by unfold y; exact_mod_cast (show 1≤ (pitchF i:ℤ) from pitch_pos i)
   let a:=P.macroStep s; change z*a+z*a< 0-(-2*Q*y)*a; let G:=P.macroStep_pos s
   rw [←add_mul,zero_sub, ←neg_mul, mul_lt_mul_iff_left₀ G]; nlinarith only [hv, mul_le_mul_of_nonneg_left hh (show 0≤Q from Nat.cast_nonneg _)]
 rw [clock_cost,clock_cost,clock_cost,clock_cost,he,he,ht,ht]; unfold f; rw [show (pitchF 3:ℤ)=2 from rfl,show (pitchF 2:ℤ)=16 from rfl]; rw [Int.cast_ofNat,Int.cast_ofNat]; let a:=P.macroStep s; change 0-(-2*Q*2*a)+z*a+z*a<0-(-2*Q*16*a)-z*a-z*a; nlinarith only [mul_lt_mul_of_pos_right hv (show 0<a from P.macroStep_pos s), mul_nonneg (show 0≤Q from Nat.cast_nonneg _) (show 0≤a from (P.macroStep_pos s).le)] -- tune
end Vista
#print axioms Vista.openDoors
#print axioms Vista.fork_lease
end Rose
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
