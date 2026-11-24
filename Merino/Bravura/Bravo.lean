import Merino.Bravura.Overture
import Merino.Tiara.Majesty
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
variable {ι:Type v}[Fintype ι]
 {V:Type w}[NormedAddCommGroup V][NormedSpace ℂ V]
variable (P:Spine) (C:Constellation) (s t:ℕ)
   (g:LinksC→ℂ)(J:Reins P.calibration)
   (χ:Horse P.calibration→ₗ[ℂ]V)
local notation "H"=>Lace.pole
local notation "D"=>P.calibration
local notation "n"=> (priceTick P)

def gout (a:Axis)(u:ℤ):V:=
 χ ((Tcoef P s:ℂ) • central D H t (chime D a u (beret P s J a)))


def vittles (u:ℤ):Axis→V:= fun i=>gout P s t J χ i u
def dirge:=august P s (2*t) g J-half P s (2*t) g
lemma thematic :octaveV (vittles P s t J χ n) (vittles P s t J χ (- (n:ℤ)))=
 χ (dirge P s t g J):=by
 rw [dirge,scepter _ _ _ _ _ (by omega),add_sub_cancel_left]
 rw [show 2*t/2=t from by omega]
 change _=χ ((_:ℂ) • central D H t (rolling D n _))
 rw [rolling,map_sum,smul_sum,map_sum]
 unfold octaveV
 refine sum_congr rfl fun a _=>?_
 rw [map_sub,smul_sub,map_sub]
 rfl


/-- each axial on the rounded stencils (limit J in Tiara) at
resolution pose along H. χ is a joint measurement cost interpreted
on the pose. Multi-payment allowed. -/
def Sung (B:ι→Axis→ℝ→V)(r δ b:ℝ)(l:ι→ℂ):Prop:=
   sumSize l ≤ allowance b r ∧
   Tunes B l (gap δ r) (vittles P s t J χ n) (tolerance b r) ∧
   Tunes B l (-gap δ r) (vittles P s t J χ (- (n:ℤ))) (tolerance b r)

def setoff : ℕ := Medal.hike (2*n) (scaleM P s)
lemma offset :setoff P s % 2=0:=by unfold setoff Medal.hike; erw [mul_assoc,Nat.mul_mod];norm_num

def amati:ℝ:= √(Ct C)*cost₀ P s (setoff P s)


/-- Remaining interference and transmission estimates, on
precisely the moving (unselected, axis3) R.P. pieces for the
stencils priced in Carol/Unison (no identification between P.E
and selected prices assumed). **Do not claim** paid on election;
the positivity we combined this with IS paid. -/
def Reverberates (r b:ℝ):Prop:=
   ∀U W:P.Vox H s,
     U.val=august P s (setoff P s) g J →
     W.val=half P s (setoff P s) g →
     let y:=P.piece H s U
     let z:=P.piece H s W
     Skew y z ∧ Resonance y z b (amati P C s) r (χ (dirge P s t g J))

def Sings (P:Spine) (C:Constellation)
  (m:ℕ→ℕ)(g:ℕ→LinksC→ℂ)(J:ℕ→Reins P.calibration)
  (χ:ℕ→Horse P.calibration→ₗ[ℂ]V)
  (B:ι→Axis→ℝ→V)(p:ℕ→ℝ)(δ b:ℝ)(l:ℕ→ι→ℂ)
 :Prop:=∀ᶠ s in atTop,
   Reverberates P C s (m s) (g s) (J s) (χ s) (p s) b ∧
   Sung P s (m s) (J s) (χ s) B (p s) δ b (l s)



lemma rings
 {P:Spine} {w:Bolts} {C:Constellation} {r:ℕ→ℕ}
 {m:ℕ→ℕ}{g:ℕ→LinksC→ℂ}{J:ℕ→Reins P.calibration}
 {χ:ℕ→Horse P.calibration→ₗ[ℂ]V}
 {F:ℕ→ℕ→LinksC→ℂ}{X:ℕ→ℕ→Reins P.calibration}
 {B:ι→Axis→ℝ→V}{p:ℕ→ℝ}{δ b R h:ℝ}{l:ℕ→ι→ℂ}
 (u:∀ᶠ s in atTop,Unison P w C r 0 s (F s) (g s) (X s) (J s))
 (swell:Cadence B p δ b R h) (song:Sings P C m g J χ B p δ b l):
 Canta B p δ b l:=by
  apply letSing swell
  filter_upwards [u,smallR swell,song] with s i j k
  have t:=i.1.lit
  obtain ⟨R0,a,d,e⟩:=k
  refine fortissimo swell.pian swell.pen swell.ideal (swell.pink s)
     j.2.2 swell.composes j.1 a d e j.2.1 ?_
  rw [thematic P s (m s) (g s)]
  obtain ⟨_,U,W,y,z,_,pz⟩:=i.2.2 (setoff P s) t (offset ..)
  have j0:=positiveCt C
  have j1:=cost_pos P t
  have m0:0<amati P C s:=mul_pos (Real.sqrt_pos.mpr j0) j1
  have m1:amati P C s ^2 ≤ ‖P.piece H s W‖^2 :=by
      rw [amati, mul_pow, Real.sq_sqrt j0.le]
      exact pz

  have m2:=le_of_sq_le_sq m1 (norm_nonneg _)
  obtain ⟨q0,q1⟩:=R0 U W y z
  exact carries m0 m2 (swell.pink _) q0 q1

/-- **Conditional** criterion exposed universally, on chosen prices. For smooth
candidate slots vs fixed χ, three inequality target (Skew, Resonance, and
remaining Tune approximation); forces *measured*
not mere-symbol divergence. Not asserting any such comparisons installed. -/
def Diva (P:Spine) (C:Constellation) (g:ℕ→LinksC→ℂ)
  (J:ℕ→Reins P.calibration): Prop:=
 ∀{ι:Type v}[Fintype ι]
  {V:Type w}[NormedAddCommGroup V][NormedSpace ℂ V]
  (m:ℕ→ℕ)(χ:ℕ→Horse P.calibration→ₗ[ℂ]V)
  (B:ι→Axis→ℝ→V) (p:ℕ→ℝ)(δ b R h:ℝ)(l:ℕ→ι→ℂ),
   Cadence B p δ b R h → Sings P C m g J χ B p δ b l →
   Canta B p δ b l

abbrev Finish (P:Spine)(p:Bolts)(C:Constellation):Prop:=
 ∃ (r:ℕ→ℕ)(F:ℕ→ℕ→LinksC→ℂ)(g:ℕ→LinksC→ℂ)
  (X:ℕ→ℕ→Reins P.calibration)(J:ℕ→Reins P.calibration),
    StrictMono r ∧ Diva.{0,0} P C g J ∧
       ∀f,∀ᶠ s in atTop,Unison P p C r f s (F s) (g s) (X s) (J s)


theorem laureate (p:Bolts)(h:Throne P p C):Finish P p C:=by
 obtain ⟨r,F,Yn,G,Z,i,j⟩:=h
 refine ⟨r,F,Yn,G,Z,i,?_,j⟩
 intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ h u
 exact rings (j 0) h u

def halfBar : ℝ := ((P.par.R.L.val:ℝ)⁻¹)^((1:ℝ)/16)
def eighthM : ℝ := (halfBar P)^s
theorem tuneCount : (∀s:ℕ,0<eighthM P s) ∧ Tendsto (eighthM P) atTop (𝓝 0) ∧
  ∀s:ℕ,(eighthM P s)^16=((↑P.par.R.L.val:ℝ)^s)⁻¹:=by
  have t:=P.par.R.coarse
  have l:1 < (P.par.R.L.val:ℝ):=by exact_mod_cast (show 1<P.par.R.L.val by omega)
  have p:0<(P.par.R.L.val:ℝ)⁻¹:=inv_pos.mpr (by linarith)
  have r:0<halfBar P:=Real.rpow_pos_of_pos p _
  have v:halfBar P < 1:= Real.rpow_lt_one p.le ((inv_lt_one₀ (zero_lt_one.trans l)).mpr l) (by norm_num)
  refine ⟨fun s=>pow_pos r s,tendsto_pow_atTop_nhds_zero_of_lt_one r.le v,fun s=>?_⟩
  rw [eighthM,pow_right_comm,halfBar,←Real.rpow_mul_natCast p.le]
  norm_num
end YM.CF.Merino.Bravura
