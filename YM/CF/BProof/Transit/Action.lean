import YM.CF.BProof.Transit.Note
import YM.CF.Fixed.MirrorFunctional
import YM.CF.Tye.Spin
import YM.CF.BProof.Physical
set_option autoImplicit false
noncomputable section
set_option synthInstance.maxSize 28000
namespace YM.CF.BProof.Bide
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Urn Hake Levier Spire Scree Stilo Hive
attribute [local instance] opCStarAlgebra
open MeasureTheory Skye
local instance (I : Type) [Fintype I] [DecidableEq I] : MeasurableSpace (Op I) := borel _
local instance (I : Type) [Fintype I] [DecidableEq I] : BorelSpace (Op I) := ⟨rfl⟩
variable {N:Side} (s t:Sweep N)
/-- leftward action: `boxA` reads ahead; moves regions by inverse. Includes action on links
 (and on tags below) by full sweep. Only charge=false used in Reflection and Chess. -/
def move (s:Sweep N): Obs N →+* Obs N where
 toFun F x:= teen s (F (flashA s⁻¹ x))
 map_add' _ _ := funext fun _=>map_add ..
 map_mul' _ _ := funext fun _=>map_mul ..
 map_zero':= funext fun _=>map_zero _
 map_one' := funext fun _=>map_one _
abbrev plainP (F:Obs N):Prop := ∀ x, Keys (F x)
variable {F:Obs N}
lemma dance (h:plainP F):move t (move s F)=move (s*t) F:=by ext1 U; change teen _ (teen _ (F (flashA _ (flashA _ U))))= teen _ (F (flashA _ U)); rw [yetL s t _ (h _), lights, _root_.mul_inv_rev]
lemma move_e (h:plainP F): move 1 F=F:=by ext1 U; change teen 1 (F (flashA _ _))=_; rw [inv_one, rev1 U,lot_i _ (h _)]
lemma keys (h:plainP F):plainP (move s F):=fun x=> Keys.tour_b _ _ _ _ (h _)

def regionD (s:Sweep N)(T:Support (More N)):= T.map (boxA s).symm.toEmbedding
lemma eligible (u:UNI SpinIdx)(Y:Support (More N)) : twist (siteU (castX s) s.charge u N) (cutM (modes Y))=cutM (modes (regionD s Y)):=by
 let V:=siteU (castX s) s.charge u N; change twist V _=_; apply Mir.twist_comm; ext i j; rw [cutM,cutM, Matrix.mul_diagonal,Matrix.diagonal_mul]; by_cases h: V.val i j=0; rw [h,zero_mul,mul_zero]; have hx:boxA s (node i.1.1)=node j.1.1:= Tye.birth_l i j (castX s) u s.charge h
 simp [mem_modes,regionD]; rw [hx]
variable {s}
lemma dip (x:Obs N) (q:Pane N) (t:s.charge=false) : move s x q= Spire.tourP (siteU (castX s) false (spinU false s.s) N) false (detX s.s) (x (flashA s⁻¹ q)):=by change yodel _ _ _=_; rw [show s.charge=_ from t]; rfl
lemma normD {w:ℝ} (p:Paid F w) (t:s.charge=false) : Paid (move s F) w:= fun x=> (by rw [dip _ _ t,pay_s]; exact p _) -- implicit binder tune
lemma movement {Y:Support (More N)} (v:Allowed Y F)(p:s.charge=false): Allowed (regionD s Y) (move s F):=by
 refine ⟨?_,fun U V z=> congrArg (teen s) (v.reads (flashA s⁻¹ U) _ (flashD s⁻¹ U V Y ?_)),fun U=>?_⟩
 · let V:=F ∘ flashA s⁻¹; exact Girt.pole_w (X:=FC (Single N)) V (teen s) (tour_c s.charge (detX s.s) _) (Girt.snap (X:=flashA s⁻¹) (F:=F) v.bounded (revM s⁻¹ |>.measurable)) -- instance
 · rwa [sitU s] -- tune
 rw [dip _ _ p]; apply twist_sector _ _ (v.modes_use _); have u:=eligible s (spinU false s.s) Y; rw [p] at u; exact u
lemma plain {Y: Support (More N)} (p:Allowed Y F): plainP F:= fun x=> Chord.keys_of_chord (Chord.full (p.modes_use x))
lemma mode_p {Y T: Support (More N)} (v:Allowed Y F)(h:Y⊆ T):Allowed T F:=⟨v.bounded,fun i j p=> v.reads i j (agrees_mono p h), fun i=> Garden.scope (v.modes_use i) (fun i u=> mem_modes .. |>.mpr (h ((mem_modes ..).1 u)))⟩
/-- equate origin mirror and the displacement actions later. -/
lemma origin (i:Axis) (p:plainP F): move (Fixed.reflectSweep N i) F=Fixed.reflectTest i false F:=by
 ext1 U; let s:= Fixed.reflectSweep N i; change teen _ (F (flashA _ U))=_; rw [Fixed.inv_reflectSweep,Fixed.flash_reflect]; unfold teen; rw [Fixed.castX_reflect]; let k:=detX (Fixed.reflShape i).s; have hk:k=true:=Spire.det_t i
 let V:=Fixed.reflConfig N i U; let Y:= Fixed.reflectP N i
 change yodel false _ (F V)= (1:ℂ) • _; rw [one_smul]; unfold yodel 
 apply (stag_s false _ _ (Fixed.pinSpin i) _ (p _) (spinZ ..) ?_).trans
 · rw [show detX (Fixed.reflShape i).s= _ from hk]; rfl
 rw [show detX (Fixed.reflShape i).s= _ from hk]; exact mirrorX i
end YM.CF.BProof.Bide
