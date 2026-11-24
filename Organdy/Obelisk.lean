import Organdy.Solo
import Organdy.Sunrise
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.Organdy.Optic
open Function Filter MeasureTheory Finset

open Regis.Head.Brecht YM.Regis.Head NormedSpace ProbabilityTheory
open scoped InnerProductSpace ENNReal
variable {E ι τ:Type} [NormedAddCommGroup E][InnerProductSpace ℝ E]
 [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι] [Fintype τ]


variable (π:ι→τ)
variable {D β ε:ℝ}{u w:ι→E}

open scoped ComplexConjugate
lemma billowing (d:τ→ℝ){c k b δ B:ℝ}
 (pos:0<b)(w':0<δ)
 (e:0≤ε)(x:lapse ε (64*b)*c^2≤trophy d b δ/4)
 (pk:0<k)(hB:0≤B)
 (Y:D^8*(due (2*B)/k) ≤ ε)
 (A:Ink ι)(S:Finset ι)(N:A.Within S)
 (R: A.qty ≤ c)
 (W: δ ≤ (A.gilt (d ∘ π)).re)
 (G:∀i,‖u i‖ ≤ B)(H:∀p:Freq ι, ‖combine w p‖=‖combine u p‖)
 (C:b≤β)(T:β≤16*b)
 (P:∀i∈S,∀j∈S,|D^4*inner ℝ (u i) (w j)-β*bell π j (π i)| ≤ ε/4):
 Cameo (trophy d b δ)
   (unlitK (write A) (combine u)) (ablazeK (write A) (octave π) β) D
    (∫x,(air k A (spec u x)*conj (air k A (spec w x))).re∂stdGaussian E):=by
 simp_rw [begins]

 refine cameo_fee pk d pos C w' (by positivity) (by positivity) e x Y _ (octave π)
   ((tally A).trans R) ?_ (fun _=>combine_bound (G _) (G _)) H ?_ (rivulet π S A N P)
 · rwa [seen]
 intro p q
 rw [abs_mul,abs_of_pos (pos.trans_le C)]
 exact (mul_le_mul T (duet_bound ..) (abs_nonneg _) (by positivity)).trans_eq (by ring)


end YM.CF.Organdy.Optic
end
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.Organdy.Optic
open Function Filter MeasureTheory Finset

open Regis Head Lattice Precision Wilson Pressure Work.F03 Exterior
open Larva (Chip Tint dot blush stains decree wet_iff)
variable {n N:Side}
local notation "G" => SU.group

open RG Gleam ProbabilityTheory
open scoped InnerProductSpace ComplexConjugate
variable {M:Bed}{Z:PathData G}{q: Clip}{ρ θ v a η C:ℝ}


open Brecht Circuit
variable (B:Z.Bounds q θ v a)(P:Attached M Z)(L:Floor M q n η C)(O:Bid.Sworn M n G)
local notation "tBody" => Body 2 n
local notation "t" => stamen B P n 

variable {σ D m ε:ℝ}
variable (U:M.covered σ C)(e:0<σ)(J:Even n.val)
include U e L O J in
theorem dewDrops (y:Site n){c k δ:ℝ}{w:ℕ} (A:Ink (Chip n))
 (p:A.qty ≤ c)(u:δ≤Larva.dint A)(v:A.Within (stains 0 w))
 (sz:0< m)(pos:0<δ)
 (l:1/2 ≤ |ρ|)(r:|ρ|≤2)
 (e':0≤ε)(x:lapse ε (64*(m/4))*c^2 ≤ premium m δ/4)
 (pk:0<k)(price:D^8 * (due (2*kilnBound q)/k) ≤ ε)
 (w':Whisper n M w D m (ε/16) y):
 Cameo (premium m δ)
    (unlitK (write A) (combine (start B P ρ)))
    (ablazeK (write A) (octave dot) (m*ρ^2)) D
    (Optic.monetary B P k ρ A y):=by
 let h:=m*ρ^2
 rw [tapeta]

 have hn:0≤q.direct:= q.quadratic_pos.le
 have hb:0≤kilnBound q:=by unfold kilnBound;positivity
 have h₁:m/4 ≤ h:=by
    have f:= pow_le_pow_left₀ (by positivity:0≤(1:ℝ)/2) l 2
    rw [sq_abs] at f
    unfold h
    linarith [mul_le_mul_of_nonneg_left f sz.le]
 have h₂:h ≤16*(m/4):=by
    have f:=pow_le_pow_left₀ (abs_nonneg ρ) r 2
    rw [sq_abs] at f
    unfold h
    linarith [mul_le_mul_of_nonneg_left f sz.le]
 refine billowing dot decree (by positivity) pos e' x pk hb price A _ v p u
   (fun i=>tame B P 1 0 i r)
   (fun i=> simmer B P L O ρ mir y i) h₁ h₂
   (fun i a j l'=>hear B P L U e J r e' w' a l')

end YM.CF.Organdy.Optic
end
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.Organdy.Optic
open Function Filter MeasureTheory Finset

open Regis Head Lattice Precision Wilson Pressure Work.F03 Exterior
open Larva (Chip Tint dot blush stains decree wet_iff)
variable {n N:Side}
local notation "G" => SU.group

open RG Gleam ProbabilityTheory
open scoped InnerProductSpace ComplexConjugate
variable {M:Bed}{Z:PathData G}{q: Clip}{ρ θ v a η C:ℝ}


open Onyx Ember Lat Circuit Brecht
open Stationary (Gaia)
open scoped Topology 


variable {u w k r ε σ c δ:ℝ}

def Radiation(q:Clip)(σ η C c δ u:ℝ) :Prop:=
 ∀ (w k:ℝ),u≤w→w^1000 ≤ k→
    ∀ n:Side, Even n.val→w^102 * pinch n≤u⁻¹→
      ∀ D l:ℕ, Plait w D → (l:ℝ)≤w→
      ∀ {M:Bed},M.covered σ C→Floor M q n η C→Bid.Sworn M n SU.group→
        ∀ {Z:PathData G}{θ v a:ℝ}(P:Attached M Z)(B:Z.Bounds q θ v a)
         (ρ:ℝ),1/2≤|ρ|→ |ρ|≤2→
           ∀ A:Ink (Chip n), A.qty≤c→ A.Within (stains 0 l)→ δ≤Larva.dint A→
             Cameo (premium argent δ)
             (unlitK (write A) (combine (start B P ρ)))
             (ablazeK (write A) (octave dot) (argent*ρ^2)) (D:ℝ)
             (Optic.monetary B P k ρ A (ice n D))

theorem giltEdge (q:Clip)(η:ℝ)(c:ℝ)(p:0<σ)(h:0<C)(j:0<δ):∃u≥1,Radiation q σ η C c δ u:=by
 have pos:=argent_pos
 obtain ⟨ε,e,x⟩:=usable c (64*(argent/4)) (premium argent δ) (premium_pos pos j)
 obtain ⟨r,a,b⟩:=halo_north q η p h (show 0<ε/16 by positivity)
 let m:=due (2*kilnBound q)
 let u:=max 1 (max (8*r) (m/ε))
 have h₀:1≤u:=le_max_left ..
 have h₁:8*r≤u:= le_trans (le_max_left ..) (le_max_right ..)
 have h₂:m/ε≤u:=le_trans (le_max_right ..) (le_max_right ..)
 refine ⟨u,h₀,?_⟩
 intro w k hw hk n n' v D l D' l' M m' t o Z ϑ φ α P B ρ ρ' ρ'' A c' y z
 have w':=h₀.trans hw
 have k':0<k:=(pow_pos (show 0<w by linarith only [w']) _).trans_le hk
 have hz:Whisper n M l D argent (ε/16) (ice n D):=by
   obtain ⟨g,f⟩:=pace_north D' w' l' (h₁.trans hw) a
   exact wins b n' m' t a g 
      (le_trans (mul_le_mul_of_nonneg_right D'.2 (pinch_pos _).le)
         (v.trans (inv_anti₀ a (by linarith only [a,h₁])))) f

 have hi:m ≤ ε*w:=(div_le_iff₀' e).mp (h₂.trans hw)
 exact dewDrops B P t o m' p n' _ A c' z y pos j ρ' ρ'' e.le x k'
    (fringe D' w' hk e.le hi) hz
