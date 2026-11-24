import YM.SU5.SatinWard.Resolution.SomaLap
import YM.SU5.SatinWard.Resolution.Meetup
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 75000
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
namespace Internal
open Preparation.Tabletop Harmonic CasaF Signboard Ceremo LitCurrent LitCurrent.Chamber
local notation "Y"=> P.run
local notation "L★"=> P.par.R.L
local notation "B$"=> P.calibration
variable {v j f0 s w:ℕ}(p x:Cover)(wp:nodeC x=P.clockPlate s v p){a b A c φ H:ℝ}{F T: Family P.calibration}{S S': Finset Cover}
local notation "U$"=> pavilion (P.clockPlate s v p) (rentWidth P j v)
variable {G R:ℕ→Family P.calibration}{D:ℕ→ℕ}(q:Tendsto D atTop atTop)(e:BQueue S G F)(e':BQueue S' R T)
local notation "ι₀"=> Wage3
local notation "iv" i:max=> P.nomadic (D i)
local notation "kv" i:max=> P.engine (D i)
local notation "Mp" i:max=> side P.run (P.nomadic (D i)) v
variable (hb:Almanac P s w p) (hz: Closeted P j p s v w) (pc:S ⊆ pavilion (P.clockPlate s v p) (rentWidth P j v)) (pc':S' ⊆ pavilion (P.clockPlate s v p) (rentWidth P j v)) (k:P.NightCop) (i:Axis)
local notation "κ"=> sprintCost P.par.R.L
variable (h:s<v) (f:f0 ≤ s) (Hc:1≤H)(Ac:1≤A) (fA:0<a)
local notation "εμ"=> Wage4
local notation "j⊗"=> yardF (spinFrame 3)
local notation "v!"=> hourBound P.run v
variable (η:Type)[Fintype η]
variable {Z:Visit → Cover→ Family P.calibration}{M: PitchZ} {d:Division}(L:Ceremo P η v j f0 a b φ H A d D Z M)
local notation "O⋆" => fullStar P.par v j Z
local notation "ΨH" s:max=>pinpr P.par.R.L (hat P.par.R.L P.par.x s)
open Selected Reconstruction.Atlas CasaF
variable (D₀:Cover) (M0:P.par.R.L.val %16=1) (qa:ResidualPermit D₀)(x₀:P.Spectrum0 i)
variable (uv:StretchClock P j s v D₀ p)
variable (B:P.Apron)(X:P.Card i v (P.reachLeaf s v (moonSpan P s)))(pX:P.voxTest i v X.val∈enclave P.calibration)
variable {H_:Cover→ Family P.calibration} (vH: Domicile w H_)(qh: w ≤ rentWidth P j v)
variable {u₁ v₁:ℝ} (p₁:moonClock P s≤u₁) (p₂:moonClock P s≤v₁) {v0:ℕ}(hp:v0 ≤ v)(u:payable P v 2)
local notation "s$"=> moonSpan P s
local notation "Y$"=> P.reachLeaf s v (moonSpan P s)
local notation "W$"=> uv.located.cost
local notation "hⓐ" i:max=>home P D₀ i

variable (vo:Axis)(ti:Axis)(lι:Wage3){Zt:Coords Wage3}(VV:Velas P η A H f0 v j vo ti lι Zt D)
open Motet
local notation "U_" x:max i:max=> spineField P.par P.calibration v vo x i
local notation "Kℓ"=> ShapeLab.leg lι
-- capsule evidence
noncomputable abbrev stencilJ (v j:ℕ)(vo ti:Axis)(x: Coords Wage3): Cover→ Family P.calibration:= Motet.dewy P.par v • ((fun y=> spineField P.par P.calibration v vo x (y+ pmZ j ti true))+(fun y=>spineField P.par P.calibration v vo x (y+pmZ j ti false)))
local notation "Ap"=> stencilJ P v j vo ti Kℓ
lemma substar (M:Coords Wage3): Domicile (2*j) (stencilJ P v j vo ti M):=by
 let F:= Signboard.spineField P.par P.calibration v vo M; have h(b:Bool): Domicile (2*j) (fun x=> F (x+pmZ j ti b)):= by simpa only [zero_add] using Domicile.flow_d (pmZ j ti b) (fun i=>shiftQo ..) (letterShape (J:=P.calibration) (Λ:=P.par) vo v M) -- argument order tune
 exact Domicile.tinted _ ((h true).more (h false))
lemma named_ver (i:ℕ): exhibit Y P.large v i (stencilJ P v j vo ti (ShapeLab.leg lι) x)= clearArc Y v i j ti vo lι (wrap (side Y i v) x):=by
 let n:=side Y i v; let W:= clearArc Y v i j ti vo lι
 unfold stencilJ; simp only [←Complex.coe_smul,Pi.smul_apply,Pi.add_apply,map_smul,map_add]
 let F:=spineField P.par P.calibration v vo Kℓ; let x₀:=wrap n x
 change (↑(Motet.dewy P.par v):ℂ) • (exhibit Y P.large v i (F _)+exhibit Y P.large v i (F _))= W x₀
 unfold F; simp_rw [Signboard.spinogram,ShapeLab.columns_one]; rw [show x+pmZ j ti true=x+j • step ti from (by simp [pmZ]), show x+pmZ j ti false=x-j • step ti from (by simp [pmZ,sub_eq_add_neg]),map_add,map_sub,map_nsmul,wrap_step]; rfl -- goal x_ notation
local notation "Θv"=> (spinFrame vo)
local notation "HΘ"=> (yardF (spinFrame vo))
noncomputable abbrev xcap (v:ℕ)(A H:ℝ)(i:Axis):ℝ:= let F:=spinFrame i; rentP P.par.R.L A (yardF F) H F*lapQ P.run v
noncomputable abbrev θx (s v:ℕ)(A H:ℝ)(i:Axis):ℝ:=monthlyRent P (totalBudget A (Announcement Wage3 η)) (xcap P s A H i) s v
-- copy proof assist.Vel.Act.
private lemma normFog (P:Hilbert)(x y z:P.Op)(t:ℝ)(u:y=z)(v:‖x-z‖≤ t):‖x-y‖≤t:=u.symm ▸ v
include wp h f
set_option maxHeartbeats 160000 in
lemma brewJ (a:ℕ)(Q:Coords Wage3)(u:pathArc P η f0 v vo ti j lι A H (iv a) (kv a) Q) : ∃ Z:Site (side P.run (iv a) s)→ Mark (side P.run (iv a) v), SeatsPriced (totalBudget A (Announcement Wage3 η)) P.run s (iv a) (kv a) v Z (xcap P s A H vo) ∧ TwistP P.run (iv a) s v Z∧ exhibit P.run P.large v (iv a) (cycleRoot (sprintCost P.par.R.L) s v (Ap x) (Signboard.spineField P.par P.calibration v vo Q x))= Z (P.rootAt s (iv a) p):=by
 let V:= u.pricing s f h; refine ⟨armF Y (spinClass Y v (iv a) vo) (clearArc Y v (iv a) j ti vo lι) Q h.le,V,lapTwist _ _ _ _ _ _ (stageSpin P.run vo lι j ti) V,?_⟩
 rw [cycleAt, named_ver,Signboard.spinogram]; unfold armF; rw [plaza_node P h.le p x wp (iv a)]
local notation "Mh"=> (pavilionWidth P p x wp (show 2*j≤ rentWidth P j v from (by unfold rentWidth; omega)))
include k VV q in
set_option maxHeartbeats 160000 in
lemma velocityU (dv:0 < xcap P s A H vo) : ‖poleDay P p (W$) i (cloakCard P p x wp i D₀ uv (substar (v:=v) (j:=j) P vo ti Kℓ) (show 2*j≤rentWidth P j v from by unfold rentWidth; omega))-poleDay P p (W$) i (spinDoor P p x uv.art i wp vo Zt)‖ ≤ θx P η s v A H vo:=by
 obtain ⟨T,hT,hi⟩:= VV.survey; let S':=pavilion (nodeC x) 0; let y:= Ap x; let U:=P.pallet ((substar (j:=j) (v:=v) P vo ti Kℓ).valid x); let F':= (U_ Zt x); have t:= lessonU P x T Zt vo hT (v:=v) 0; let p':=uv.art; let KS:= Mh; let hh:S'⊆ pavilion (P.clockPlate s v p) (rentWidth P j v):= pavilionWidth P p x wp (by omega); have g : poleDay P p uv.located.cost i (spinDoor P p x uv.art i wp vo Zt)= daySpend P p uv.located.cost uv.art hh t.landing i:=rfl
 have V':= cycle_compare (R:=fun i=> (spineField P.par P.calibration v vo (T i)) x) (pc:=Mh) (pc':=hh) (T:=F') (S':=S') (j:=j) (c:=xcap P s A H vo) (A:=totalBudget A (Announcement Wage3 η)) P p q U t uv.located.cost uv.art k i h.le dv (Eventually.of_forall fun i=> brewJ P p x wp h f η vo ti lι i _ (hi i)) -- order
 let w':= normFog (P.Hil i) (daySpend P p uv.located.cost uv.art KS U.landing i) (poleDay P p uv.located.cost i (spinDoor P p x uv.art i wp vo Zt)) (daySpend (S:= S') P p uv.located.cost uv.art hh t.landing i) (θx P η s v A H vo) g V'; exact w'
noncomputable abbrev braceX : P.Apron:= cloakF P M0 qa (substar (v:=v) (j:=j) P vo ti Kℓ) v -- unused params h f? include h,f,wp allowed? Lean def includes unused? check.
include k VV q Ac Hc p₁ p₂ uv
local notation "TX"=>frontPrice P i D₀ M0 qa x₀ hp
local notation "Ω" A:max => lined P M0 i x₀ v0 D₀ hp A
lemma clock_x (z:0<lapQ P.run s): ‖frontPrice P i D₀ M0 qa x₀ hp (substar (v:=v) (j:=j) P vo ti (ShapeLab.leg lι)) u₁ v₁- frontPrice P i D₀ M0 qa x₀ hp (Signboard.letterShape (J:= P.calibration) (Λ:=P.par) vo v Zt) u₁ v₁‖ ≤ θx P η s v A H vo:=by
 let t':= velocityU (w:=moonSpan P s) (v0:=v0) P p x wp q k i h f η D₀ uv vo ti lι VV (mul_pos (rentP_pos (P:=P.par) (yardF _) H A Ac (stretch_funded _).choose_spec.large Hc) z)
 let X:= substar (v:=v) (j:=j) P vo ti Kℓ; let T':=letterShape (J:=P.calibration) (Λ:=P.par) vo v Zt; let vL:=(show 2*j≤ rentWidth P j v from by unfold rentWidth; omega); let c0:= cloakCard P p x wp i D₀ uv X vL; let c1:=cloakCard P p x wp i D₀ uv T' (Nat.zero_le _); let sZ:=moonClock P s
 have c:‖poleDay P p uv.located.cost i c0-(1:ℂ) • poleDay P p uv.located.cost i c1‖≤ θx P η s v A H vo:=by rw [one_smul]; exact t'
 let e:= fee_line P p x wp i D₀ M0 qa x₀ uv (cloakF P M0 qa T' _) c1 (cloak_paidCard P p x wp i D₀ uv T' (Nat.zero_le _)) X vL p₁ p₂ hp 1 (cloak_chart P p x wp i D₀ M0 qa uv T' (Nat.zero_le _)) (cloak_support P p i D₀ M0 qa uv T' (Nat.zero_le _)) c; rw [one_smul] at e; exact e
#print axioms clock_x
end Internal
end Regulator
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
