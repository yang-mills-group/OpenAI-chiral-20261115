import YM.CF.Haro.Silk
import YM.CF.Salt.Felt
import YM.CF.Tye.Wheel
import YM.CF.Salt.Dial
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 21000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Salt
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Scroll Thera Branch Laic Cube Relation
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker Classical
attribute [local instance] opCStarAlgebra
open Scree Pastry Stilo Urn Palot Hake Scion Levier Hive Nacre Tye Skye RG Pressure Next.SectorChange Planned.AtomRegular Girt Spire
open Eire Skye Levier Scion Urn Pastry Rill Kennel Pec
open Eire Girt Tulip Spire Proa RG Pressure Stilo Scree Palot Tye Cour Broc Hive Hake
variable {P N B: Side}(G:Ratio (mid N B) (mid P B))(S:StepData (Domain N B) (Domain P B))(p:S.ratio=ratio G)(f:Sweep (mid N B))(k:ℕ)(A:Eire.Ride S)(hp:Odd G.count.val) {δ v d m r w:ℝ}(hx:0<δ)
local notation "D"=> (mid N B)
local notation "Y"=> (mid P B)
local notation "F"=> reSweep G f
variable (X:Rill.Arch G δ)(u:Seat (mid P B)→E)(C: Cipher (mid P B))(Z:FC (Single (mid P B)))(t:ℕ)(P0:Meter TailB G δ)(Q:Meter Grave G δ)
local notation "H"=>cala G S hp _ hx P0 Q
local notation "W"=>switchG G
local notation "U"=> castX f
local notation "β"=> f.charge
local notation "Yv"=> spinU β f.s
lemma weir(BBv:UNI (Single Y)) : (foot G BBv.val).submatrix (switchG G).symm (switchG G).symm=BBv.val:=by ext i j; unfold foot; simp -- tune
lemma eel_P (v:∀ i, Bisca G δ true true r w (heal G δ Q i))(y:∀ i, OccuS G δ true false t d m r (P0 i)):
 issue (H (Haro.herb G u X) k A) ((paintR false false (tradew Y u) C).val) (Gaze u Z)=lotY false false (tradew D (scaleG G u)) (issue (H X k A) C.val Z):=by
 let h:=town_P G δ u P0 (bring hx X) (gleans S k A) t y; have h0:=vibe_s G δ u Q (bring hx X) (gleans S k A) v; rw [←Haro.hover_G] at h h0
 exact (cloakK (switchG G).symm _ _ _ _ _ _ false false _ _ _ C.val (fineShape C|>.allP) Z (weir G _).symm h h0).symm
-- correct convention unsweep→lift with center θ. Capsule Y radii
lemma ferry : wrap Y (Shape.broad G U).t=(reSweep G f).b:=by
 rw [show (Shape.broad G U).t= G.count.val • (U).t from rfl]; rw [←Ratio.embed_wrap,show wrap D (U).t=f.b from wrap_lift _]; rfl
lemma pump : reSweep G f=Levier.ray β (Shape.broad G (castX f)):=by rw [Levier.ray, ferry]; rfl -- tune
lemma trek(T0:Pane Y): stir (xtra β) (Shape.broad G U) T0=flashA F T0:=by rw [pump, flashA]; exact (Spire.stir_e ..).symm
abbrev thunder(s:Sweep (mid N B)):= paintR s.charge (detX s.s) (siteU (castX s) s.charge (spinU s.charge s.s) D) -- N implicit inference? make general
lemma royal : paintR (F).charge (detX (F).s) (siteU (castX F) (F).charge (spinU (F).charge (F).s) Y) C= paintR β (detX f.s) (siteU (Shape.broad G U) β Yv Y) C:=by
 let t:= Shape.broad G U; have he : wrap Y (castX F).t=wrap Y t.t:=by unfold t; rw [ferry]; exact wrap_lift _
 let z:= fee (Rush.periods Y (castX F).t-Rush.periods Y t.t); apply spin_k _ _ _ (z:=z); exact utu _ _ _ _ _ _ he; exact (pow_two ..).trans (fee_one _); exact fee_real _
include p
variable (V:Rill.Arch G δ)(T:Rill.Arch G δ) -- both
variable (wV: T.val=(stanza G (castX f) (xtra f.charge) X.val.1, flashA (reSweep G f) X.val.2))
include wV
lemma lath (hV:aura G δ P0)(hQ:Levier.hue G δ Q)(z:Keys Z):
 issue (H T k (quill (chart f) A)) (thunder (reSweep G f) C).val (Hive.teen (reSweep G f) Z)= lotY β (detX f.s) (siteU U β Yv D) (issue (H X k A) C.val Z):=by -- include
 have he:bring hx T=toWish G δ f (bring hx X):=by
    apply Subtype.ext; rw [wish_g G δ f (bring hx X) X.val.1 X.val.2 rfl]; change (unionP T.val.1, profile T.val.2)=_; rw [wV,trek]
 have hp':= su_p G hp δ f P0 (bring hx X) (gleans S k A) hV; have ht:= Levier.playG G hp δ f Q (bring hx X) (gleans S k A) hQ; rw [←he,←lootT _ _ p] at hp' ht -- tune ht V
 unfold thunder; rw [royal G]; -- careful C
 rw [show Hive.teen (reSweep G f) Z = _ from (show Hive.teen (reSweep G f) Z=lotB β (detX f.s) (siteU (Shape.broad G U) β Yv Y) Z by rw [pump]; exact Hive.hono _ _ Z z)]
 refine (cloakK (switchG G).symm _ _ _ _ _ _ β (detX f.s) _ _ _ C.val ((fineShape C).allP) Z ?_ hp' ht).symm; rw [puff _ hp]; exact (weir G _).symm
#check lath
end YM.CF.Salt
