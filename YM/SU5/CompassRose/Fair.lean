import YM.SU5.CompassRose.Atrium

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
namespace Arrival
variable (Z:Papal.Weaver)(V:Finset Cover)
lemma E_fund (x:P.Test) (j:Axis) : (P$ s) x=inner ℂ (P.groundZero j) ((P.reading j s x).val (P.groundZero j)):= (P.occupied j s x).symm
lemma stationary (x:P.Test)(u:ℤ): (P$ s) ((M$) u x)=(P$ s) x:=by rw [E_fund P s _ 3,P.halfReads]; exact (E_fund P s x 3).symm
lemma facing (x:P.Test) : (P$ s) ((ζ⇒) x)=star ((P$ s) x):=by rw [E_fund P s x 3,E_fund P s _ 3,←P.reading_star]; let U:= P.groundZero 3; let G:= (P.reading 3 s x).val; change inner ℂ U (G.adjoint U)=_; rw [ContinuousLinearMap.adjoint_inner_right]; exact (inner_conj_symm ..).symm
lemma one_esteem : (P$ s) 1=1:= E_unit P.run P.large P.law s
abbrev funded (p: InTest K true V false (K! Z)):= P.art (K! Z) (aux_test p)
lemma half_rise (x:P.Test)(Y:Papal.Weaver) (v:ℕ)(p:x.val=K! Y): ((M$) v x).val=K! (takeoff P.par.block Y 3 v):=by rw [P.halfShift_val,p]; rfl
lemma reflect_form (x:P.Test)(v:ℂ):(ζ⇒) (x-v • 1)=(ζ⇒) x-star v • 1:=by
 apply Subtype.ext; change mirror _ _ _ (x.val - v • (1:Family K))=_; rw [sub_eq_add_neg,← neg_smul,mirror_plus,mirror_scale,mirror_unit,star_neg,neg_smul,← sub_eq_add_neg]; rfl
lemma compute_angle (F:P.Test)(k:ℤ)(a:ℂ):(P$ s) (((ζ⇒) ((M$) k (F-a • 1))) * ((M$) k (F-a • 1)))=(P$ s) (((ζ⇒) ((M$) k F))* ((M$) k F)) - a*star ((P$ s) F) - star a*(P$ s) F + star a*a:=by
 let V:=(M$) k F
 rw [map_sub,map_smul,map_one,reflect_form]; simp only [_root_.sub_mul,mul_sub,Algebra.mul_smul_comm,Algebra.smul_mul_assoc,mul_one,one_mul,map_sub,map_smul,smul_eq_mul,one_esteem,facing,stationary]; ring
lemma rosary (F:P.Test) (u:∃ V:P.Vox 3 s, P.voxTest 3 s V=F) : (∫ x, ‖P.singleState 3 s x F‖^2 ∂P.pillars 3) ≤ ‖(P$ s) (((ζ⇒) F)*F)‖ := by
 exact P.rosaryV 3 s F u
lemma ok_wing {f:P.Test}(k:ℕ) (h:InTest K true V false (((M$) k f).val)) (q:Tower.region 3 0 (K).ℓ V) (b:ℂ) : ∃ v:P.Vox 3 s, P.voxTest 3 s v=(M$) k (f-b • 1):=by
 let p:(M$) k f∈ bay K V true:= (Tapestry.locates ..).2 h
 rw [map_sub,map_smul,map_one]
 exact ⟨P.positiveVox 3 s V _ ((bay K V true).sub_mem p ((bay K V true).smul_mem ((bay K V true).one_mem) b)) q,rfl⟩

-- abstract double length calendar. no local Voicing required. estimate from Mirror of Test.
omit s
variable (F:ℕ→P.Test)(c:ℕ→ℕ→ℕ)(b:ℂ)(H:ℕ→ℂ)(S:ℕ→ℕ→Finset Cover)
local notation "f⇒" c:max s:max => (M$) c (F s)
local notation "μ" s:max x:max=> P.singleState 3 s x
lemma adequacy (q:Tendsto (fun s=> (P$ s) (F s)) atTop (𝓝 b))(p:Tendsto H atTop (𝓝 (star b*b)))(u:∀ᶠ k:ℕ in atTop, (∀ᶠ s:ℕ in atTop, InTest K true (S k s) false (f⇒ (c k s) s).val ∧ Tower.region 3 0 (K).ℓ (S k s)) ∧ Tendsto (fun s=> (P$ s) (((ζ⇒) (f⇒ (c k s) s)) * (f⇒ (c k s) s))) atTop (𝓝 (H k))) : WakePoll P F b:=by
 refine ⟨fun x v=>?_⟩
 obtain ⟨k,p',u',hp⟩:= ((Metric.tendsto_nhds.mp p x v).and u).exists; let G s:=F s-b • 1; let Y(s):=(M$) (c k s) (G s); let t(s):=(P$ s) (((ζ⇒) (Y s))*Y s); have hv:Tendsto t atTop (𝓝 (H k-star b*b)):=by
    have he:= (((hp.sub (q.star.const_mul b)).sub (q.const_mul (star b))).add_const (star b*b)); rw [show H k-b*star b-star b*b+star b*b=H k-star b*b by ring] at he; exact he.congr fun s=>(compute_angle P s (F s) _ _).symm
 rw [dist_eq_norm] at p'
 filter_upwards [u',hv.norm.eventually (gt_mem_nhds p')] with s w e
 have he(x:P.Spectrum0 3):(μ s x) (F s)-b=(μ s x) (Y s):=by
    unfold Y; rw [P.single_state 3 s x ((M$) _ (G s)),P.halfReads,← P.single_state]; unfold G; rw [map_sub,map_smul]; simp [single_state]
 simp_rw [he]; exact lt_of_le_of_lt (rosary P s (Y s) (ok_wing P s (S k s) (c k s) w.1 w.2 b)) e
end Arrival
-- #print axioms adequacy

-- keep receipts with fixed masks (ceil-plus), investor discount sign. Can rent after boosting r too.
structure Fixture where
 lampS : Sconce
 r : ℕ
 fitting : lampS.rent≤ r

namespace Fixture
open Shuttle Arrival
variable (F:Fixture)(x:Cover)
abbrev reflectedF : Fixture:=⟨F.lampS.waltz,F.r,(F.lampS.rent_waves.le.trans F.fitting)⟩
abbrev trench (B:Fixture)(y:Cover): Staff:= B.lampS.supportS y
abbrev inkP (x:Cover) : Finset Cover:= (trench F x).skyRent F.r
lemma height_f : (trench F x).Pays F.r F.r:= F.lampS.covered _ F.r F.fitting
abbrev naked (Y:Fixture) (vX:Cover) (ρ:ℝ):=offers P A s (trench Y vX) Y.r ρ
lemma engrave (ρ:ℝ): InTest K true (F.inkP x) false (naked P s A F x ρ) ∧ CovCover K (naked P s A F x ρ):=by
 refine ⟨InTest.smul _ ((trench F x).letterBudget _ _ _ (height_f F x)), ?_⟩; intro i h z; let c: ℂ:= winding P A s; unfold naked offers; simp only [Pi.smul_apply, twist_scalar]; exact congrArg (c • ·) ((trench F x).registration ρ (lamp s) K (height_f F x) i h z)
local notation "dn" s:max=> κFix β s
abbrev poseP (F:Fixture)(x:Cover): P.Test:= P.art (naked P s A F x (dn s)) (aux_test ((engrave P s A F x _).1))
abbrev dye := (F.lampS.signs:ℂ)
def litP (F:Fixture)(x:Cover) := F.dye • poseP P s A β F x
abbrev litW := (winding P A s : ℂ) • F.lampS.shaded x (dn s) F.r (lamp s)
lemma poses_V : (litP P s A β F x).val = K! (litW P s A β F x):= by
 let c: ℂ:= winding P A s; change F.dye • (c • grist _ _ _ _ _) = c • (F.dye • _); rw [smul_comm]; rfl
lemma litR (z:ℤ) : fluent 3 z (litW P s A β F x)=litW P s A β F.reflectedF (Sconce.γ z x):=by
 let c : ℂ:= winding P A s; let V:= F.lampS.shaded x (dn s) F.r (lamp s); unfold litW; change fluent _ _ (c • V)= c • _; rw [show fluent 3 z (c • V)=star c • fluent 3 z V from funext fun _=> funext fun _=> theta_smul .., show star c = c from Complex.conj_ofReal _]; exact congrArg (c • ·) (F.lampS.ballad ..)
lemma litNextR (f:ℕ) : (M$) f (litP P s A β F x)=litP P s A β F (Shuttle.march x f P.par.block):=by
 apply Subtype.ext; rw [half_rise P _ _ f (poses_V P s A β F x),poses_V]; unfold takeoff traction; rw [litR,litR,show (F.reflectedF.reflectedF)= F from ?_,show Sconce.γ _ (Sconce.γ _ _)=_ from (commute_f x f (P.par.block))]
 cases F; unfold reflectedF; simp
lemma reflectR : (ζ⇒) (litP P s A β F x)=litP P s A β F.reflectedF (Shuttle.flip x):=by
 apply Subtype.ext; change mirror _ _ _ _=_; rw [poses_V,poses_V]; exact congrArg (Papal.household K) (litR P s A β F x 0)
lemma inInk : InTest K true (inkP F x) false (litP P s A β F x).val ∧ CovCover K (litP P s A β F x).val:=by
 refine ⟨((engrave P s A F x _).1).smul _,?_⟩; intro i g y; change (F.dye • naked P s A F x (dn s)) i _= twist _ ((F.dye • naked P s A F x _) i _); simp only [Pi.smul_apply,twist_scalar]; exact congrArg (F.dye • ·) ((engrave P s A F x _).2 i g y)

end Fixture
#print axioms Fixture.height_f
#print axioms Fixture.litNextR
end Rose
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
