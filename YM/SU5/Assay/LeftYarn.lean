import YM.SU5.Assay.Yarn
set_option maxHeartbeats 400000
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 5000
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
open Aria Set
open Six

variable {P:Spine}{f g:P.Test}{S T D:Finset Cover}{s t:ℕ}{W:Bool}
local notation "K"=> P.calibration
variable {c:Option Bool}{a b x y:P.Test}
/-! Reflection of both factors, then shifts. Charge witness reflected and
inverted so representation marker can remain exactly as was. -/
variable (i:Axis)(z:ℤ)
local notation "Θ"=>aureole K i z
local notation "d"=> reflectedBox i z D
lemma Yarn.left (q:P.Yarn D x):P.Yarn d (Θ x):= by
 -- MirrorCharge/pair_scalar
 obtain ⟨f,p,e⟩:=q
 let F := Lifted.moveC i z; let g(x:PairsC):=star (f (F x.1,F x.2))
 refine ⟨g,⟨fun v=> ?_, Girt.pole_w _ star continuous_star (Env.along (g:=Prod.map F F) p.env ((move_cont ..).prodMap (move_cont ..)).measurable),fun x y c b=>?_⟩,?_⟩
 · obtain ⟨c,h,e⟩:= p.narrow v; refine ⟨fun x=>star (c (F x)),(h.comp (move_cont ..)).star,?_⟩; rw [show g=fun x=>star (f (F x.1,F x.2)) from rfl,e]; rfl
 · exact congrArg star (p.locus (F x.1,F x.2) (F y.1,F y.2) (moved_agree _ _ c) (moved_agree _ _ b))
 change mirror K i z x.val = _; rw [e]
 funext m x; unfold scalar mirror reflMark; rw [Fock.theta_smul,Fock.theta_one]; apply congrArg (fun u :ℂ=> u • (1:Fock.FC (Single _))); unfold g; simp only [reflFields,Prod.map_fst, Prod.map_snd,reflect_onC]; rfl
namespace Fibre
lemma turncharge {q:ℂ}{g:GVertex}(h:pennant K g x=q•x)(u:‖q‖=1): pennant K (reflectGauge i z g⁻¹) (Θ x)=q • Θ x:=by
 have e:=congrArg (pennant K g⁻¹) h
 rw [pennantCompose,mul_inv_cancel,pennantId,map_smul] at e
 have hp:pennant K g⁻¹ x=star q • x:=by
   nth_rw 2 [e];rw [smul_smul,scale_unit_self u,one_smul]
 rw [pennantReflect,gauges_of_mirror,hp,show Θ (star q • x)=star (star q)• Θ x from (aureole ..).map_smulₛₗ ..,star_star]
lemma left (p:P.Fibre c D a b):P.Fibre c d (Θ a) (Θ b):=by
 refine ⟨p.glass.left _ _,?_,aureoleBay K D false i z b p.park,fun W u=>?_⟩
 · exact fun m v w=> congrArg (theta (carR i z ((K).c m))) (p.letter m (reflFields i z v) (reflFields i z w))
 obtain ⟨g,w,t⟩:=p.couples W u
 exact ⟨_,turncharge i z w (by rw [norm_inv,pname_unit,inv_one]),turncharge i z t (pname_unit W)⟩
local notation "τ"=> P.shifts i z
lemma slide (p:P.Fibre c D a b): P.Fibre c (plow K i z D) (τ a) (τ b):=by
 have h:= (p.left i 0).left i (gaugeT K z)
 rw [support_translation,sub_zero] at h
 exact h
end Fibre
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
