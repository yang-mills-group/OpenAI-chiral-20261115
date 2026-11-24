import Merino.Bravura.Resounds
import Merino.Bravura.Bravo
set_option autoImplicit false
set_option synthInstance.maxSize 26000
set_option maxRecDepth 2500
set_option maxHeartbeats 600000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.Bravura
open Function Filter Metric SU Lat Lattice Cube Finset Spire Scroll Tulip Skye Window Vale Girt Buffered Fock
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
open BProof Hive Swell Hem Merino.Mitre Plume
open Afterglow Tower Lifted Journey

open Tiara Py.Rate.LocalLimit Preparation Tower.VacuumSelection
open Medal Lace Cuff
open scoped InnerProductSpace
universe v w

open Garter Py Rive RG Papal

variable (P:Spine)(p:Bolts)(s:ℕ)
 {r:ℕ→ℕ} {F:ℕ→LinksC→ℂ} {g:LinksC→ℂ}{C:Constellation}
 {X:ℕ→Reins P.calibration}{J:Reins P.calibration}
local notation "D"=>P.calibration
local notation "j"=>Lace.pole
local notation "U"=>P.run
local notation "x"=>scaleM P s

local notation "ᚠ"=> clearM P s
lemma middle (t:ℕ)(i k:ℕ)(W:LinksC→ℂ) (b:warrant P p C s i k W)
    (h₁:Strut x t)(h₂:Strut x (2*t))(h₃:Strut x (3*t)):
    let Q(m:ℕ):=(compass U i k s (photo (glance (RegNum P s i) m ᚠ W))).re
    Heard C (cost₀ P s t) (Q t) (Q (2*t)) (Q (3*t)):=by
 dsimp only
 obtain ⟨v,d,_,⟨T,h⟩,_,l⟩:=b
 rw [l,l,l,cost₀,show ∀y, Qprice P s/(x * (tempM P s)^2*y)=ᚠ/(x*y)
    from fun y=>by unfold clearM;rw [div_div];congr 1;ring]
 have z:0<x:=lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one P.run.oneP) (Vale.crown P.par.R.L P.par.x s)
 exact ripples P s i k C _ T h₁ h₂ h₃ h.billing h.chern h.reading.cloth.rent
    (calibrated P v.1.2.le).2 z ᚠ

lemma Heard.passing {Q:ℕ→ℕ→ℝ}{q:ℕ→ℝ}
   {t n m:ℕ}{u:ℝ}
   (v:∀i,Tendsto (Q i) atTop (𝓝 (q i)))
   (h:∀ᶠ i in atTop, Heard C u (Q t i) (Q n i) (Q m i)):
   Heard C u (q t) (q n) (q m):= by
 have k:= ((v t).sub ((v n).const_mul (2:ℝ))).add (v m)
 exact ⟨ge_of_tendsto ((v t).sub (v n)) (h.mono fun _ a=>a.1),ge_of_tendsto k (h.mono fun _ a=>a.2.1),
    le_of_tendsto k (h.mono fun _ a=>a.2.2)⟩

abbrev doll (t:ℕ)(g:LinksC→ℂ):ℝ:= (P.E s (both P s t g)).re
lemma stops (t:ℕ)(v:StrictMono r)(u:Ala P p C r s F g)
    (h₁:Strut x t)(h₂:Strut x (2*t))(h₃:Strut x (3*t)):
    Heard C (cost₀ P s t) (doll P s t g) (doll P s (2*t) g) (doll P s (3*t) g):=by
 have k (m):=(Complex.continuous_re.continuousAt).tendsto.comp (combined P u.rolls m v)
 refine Heard.passing k ?_
 exact u.path.mono fun i a=> middle P p s t _ _ _ a h₁ h₂ h₃

open SlabMark
lemma situated (t:ℕ)(u:Ala P p C r s F g):
 InTest D true (wall P s t) false (half P s t g):=by
   exact (fat u.rolls |>.rampC (Lace.noon t) (clearM P s)).law D

lemma flit {t w:ℕ} {a:ℤ}(d:a*2+t=w):
  Tower.chime D j a (half P s t g)=half P s w g:=by
  unfold half
  rw [Tiara.at_pose]
  have h:chaste (Lace.noon t) ᚠ g ∘ Lattice.pull 1 (danceAt j a)=
         chaste (Lace.noon w) ᚠ g:=by
    ext1 x'
    have v:Lace.noon w=danceAt j a+ Lace.noon t:=by
       unfold Lace.noon danceAt;rw [←d,add_smul,mul_comm a]
    simp [v,chaste,Plume.snow,Lattice.pull_pull,Lattice.affine, add_comm]
  rw [h]

lemma overlap {t:ℕ} {a:ℤ}(e:2*Heat.gaugeShift P.par.block a= -(t:ℤ))
   (u:Ala P p C r s F g) :
 P.E s (mirror D j 0 (half P s t g) * half P s (3*t) g)=
 P.E s (both P s (2*t) g):=by
 have y:=aux_test (axial D j 0 (situated P p s t u))
 have z:=aux_test (situated P p s (3*t) u)
 rw [← SWay U P.large P.law s j a (y.mul z),chime_product,chime_diag _ _ _ _ (situated P p s t u)]
 rw [flit P s (w:=2*t),flit P s (w:=2*t)]
 · omega
 · omega

def signal (P:Spine)(s t:ℕ)(g:LinksC→ℂ)(C:Constellation):Prop:=
 ∃ V W Z:P.Vox j s,
   V.val=half P s t g ∧ W.val=half P s (2*t) g ∧ Z.val=half P s (3*t) g ∧
   Ct C * cost₀ P s t^2≤ ‖P.piece j s V‖^2-‖P.piece j s W‖^2 ∧
   Ct C * cost₀ P s t^2≤ ‖P.piece j s V-P.piece j s Z‖^2 ∧
   ‖P.piece j s V-P.piece j s Z‖^2 ≤24*geyser C*cost₀ P s t^2

lemma chimes {t:ℕ} (v:StrictMono r) (u:Ala P p C r s F g)
   (h₁:Strut x t)(h₂:Strut x (2*t))(h₃:Strut x (3*t))
   {a:ℤ}(e:2*Heat.gaugeShift P.par.block a= -(t:ℤ)) :
   signal P s t g C:=by
 have z:= stops P p s t v u h₁ h₂ h₃
 obtain ⟨_,_,V,j1,j2,_⟩:=u.stellar h₁
 obtain ⟨_,_,W,j3,j4,_⟩:=u.stellar h₂
 obtain ⟨_,_,Z,j5,j6,_⟩:=u.stellar h₃
 unfold doll at z
 rw [j2,j4,j6] at z
 refine ⟨V,W,Z,j1,j3,j5,z.1,?_⟩
 rw [@norm_sub_sq ℂ]


 have q: RCLike.re ⟪P.piece j s V,P.piece j s Z⟫_ℂ=‖P.piece j s W‖^2:=by
    have qa:=contracts P.run P.large P.law P.history.circuit j 0 false (P.room j)
        s s s le_rfl le_rfl V Z
    rw [area0,Nat.sub_self,j1,j5] at qa
    rw [←j4]; exact congrArg Complex.re (qa.trans (overlap P p s e u))
 rw [q];exact z.2

lemma octave_sets(a:ℕ)(i:0<a):
 ∀ᶠ s:ℕ in atTop, Strut (scaleM P s) (a*setoff P s):=by
 have k:=P.par.block.property
 simp_rw [setoff,Medal.hike,← Nat.mul_assoc a]
 exact (turnover P.par).eventually (Medal.hike_yes (B:=a*2*(priceTick P))
     (by unfold priceTick; exact mul_pos (mul_pos i (by decide))  (mul_pos (by decide) k)))

def Setout(P:Spine)(s:ℕ)(C:Constellation)(g:LinksC→ℂ):Prop:=
 signal P s (setoff P s) g C

lemma dancing:
 ∀ᶠ b:ℕ in atTop,∀(C:Constellation)
  (r:ℕ→ℕ)(F:ℕ→LinksC→ℂ)(g:LinksC→ℂ),
  StrictMono r→ Ala P p C r b F g → Setout P b C g:=by
  filter_upwards [octave_sets P 2 (by decide),octave_sets P 3 (by decide)] with w h q A m B f i z
  apply chimes P p w i z z.lit h q (a:= -2*(⌈(wp (scaleM P w))^100⌉₊:ℤ))
  unfold Heat.gaugeShift Medal.hike priceTick; push_cast;ring


abbrev Fanfare(P:Spine)(p:Bolts)(C:Constellation):Prop:=
 ∃ (r:ℕ→ℕ)(F:ℕ→ℕ→LinksC→ℂ)(g:ℕ→LinksC→ℂ)
  (Y:ℕ→ℕ→Reins P.calibration)(J:ℕ→Reins P.calibration),
    StrictMono r ∧ Diva.{0,0} P C g J ∧
       ∀f,∀ᶠ s in atTop,Unison P p C r f s (F s) (g s) (Y s) (J s) ∧
        Setout P s C (g s)

lemma outlay (w:Finish P p C):Fanfare P p C:=by
 obtain ⟨r1,F1,g1,Y1,J1,i,h,b⟩:=w
 refine ⟨r1,F1,g1,Y1,J1,i,h,fun f=>?_⟩
 filter_upwards [b f,dancing P p] with m q a
 exact ⟨q, a _ _ _ _ i q.1.toAla⟩

end YM.CF.Merino.Bravura
