import YM.SU5.SatinWard.Resolution.ShoreE
import Bay.E.Axis
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 350000
noncomputable section
namespace YM.CF.LitCurrent
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour
open Stax Skye Jet Scroll Finset Palot Cadre Vow RG Rive Nor Hake MeasureTheory
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical Kronecker
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Rill
open Kennel Swell StressExchange
variable {N:Side}{X Y:SOp N}{o:Seat N}{a b c d v:ℝ}{r:ℕ}
local notation "Γ" => Single N
open Buffered _root_.Zephyr.Chern
open IndexMag Chamber Surplus
namespace AuroraX
local notation "I"=> _root_.Zephyr.Chern.IS
variable (D:Division)
variable {P T:SOp N}(E:Pattern P T r d a v)(y:Site N)
local notation "𝒲"=> Openc (More N) d
lemma shore_plus (z:Cover)(F:Op (Single N))(x y:Cover): shore N x y (ech (taxiPlus (wrap N z)) F)= shore N (x+z) (y+z) F:=by
 ext i j; change lint (twist _ F) x y i j= _; rw [←Bay.Silk.tiltTax z F]; exact tug_lint F z x y i j -- η prep inert may not defeq; tune
lemma bareRoom (z:Cover): flashA (taxiPlus (wrap N z)) (1:Pane N)=1:=by
 rw [Bay.Silk.stepTax]; funext i; rcases i with ⟨x,a⟩; rfl -- check
lemma shore_pose (x t:Cover): pose (taxiPlus (wrap N x)) (wrap N t)=wrap N (t-x):=by
 apply unaryN; rw [pose_node, Equiv.symm_apply_eq]; -- rhs equality orientation
 have hp: wrap N t= wrap N (t-x)+ wrap N x:=by simp
 rw [platforms]; -- actually goal p =box p(t-x) ! tune
 exact congrArg _ hp
lemma shore_dir (z: Cover)(d:FaceDir) : faceAt (taxiPlus (wrap N z)) d=d:= face_one (N:=N) d
local notation "H"=>hall D
open Salt
lemma gainTreasure (s:Sweep N)(i:Ensemble N)(x:Pane N)(o: 𝒲)(u:o.val=profile x): sky (grantJ D E (teamTravel s i)) (Sour.fog s d o)=realR s false (sky (grantJ D E i) o):=by
 unfold sky; rw [real_f]; symm; refine sum_bij (fun i _=>actY s i) (fun i _=>mem_univ _) (fun i _ j _ p=>map_injective _ p) (fun i _=>⟨actY s⁻¹ i,mem_univ _,?_⟩) ?_; · ext; simp [actY,sitU] -- ordering? holes first/second
 intro z _; change realR s false (H _)=H _; rw [travelR,(E.chartJ s i z x o u).symm]
lemma rigid_pose (w:𝒲)(e:w.val=profile (1:Pane N))(s:Sweep N)(p:flashA s (1: Pane N)=1): Sour.fog s _ w=w:=by apply Subtype.ext; exact (real_box s _ _ _ e).trans ((congrArg profile p).trans e.symm) -- p substitution
noncomputable abbrev fullL (w:𝒲)(i:FaceDir) := sky (grantJ D E (y,i)) w
lemma sky_zero (w:𝒲)(e:w.val=profile (1:Pane N))(i:FaceDir)(x y o t:Cover):
 let V(x y z:Cover): Op I:= shore N x y (fullL D E (wrap N z) w i); V x y o= V (x+t) (y+t) (o+t):=by
 intro V; let s:=taxiPlus (wrap N t); let h:= gainTreasure D E s (wrap N (o+t),i) 1 w e; have g:teamTravel s (wrap N (o+t),i)=(wrap N o,i):=by
    rw [teamTravel]; apply congr_arg₂; · rw [shore_pose,add_sub_cancel_right]
    exact shore_dir ..
 rw [g,rigid_pose w e s (bareRoom t)] at h; have ht:det_S s=false:=det_i
 unfold V; rw [←shore_plus (N:=N) t]; apply congrArg (shore N x y); change _=ech s _; change sky _ _=(if det_S s then star _ else _) at h; simp only [ht,Bool.false_eq_true,if_false] at h; exact h
-- at unit links P.V. eventual
lemma bulkFlip (w:𝒲)(e:w.val=profile (1:Pane N))(i:FaceDir) : fullL D E y w (axisFlip i)= -fullL D E y w i :=by
 unfold fullL grantJ; rw [stack,stack]; simp_rw [sky,E.revJ y i _ _ w e, sum_neg_distrib]; simp [hall]
#print axioms sky_zero
end AuroraX
end YM.CF.LitCurrent
