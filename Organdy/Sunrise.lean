import Organdy.Arctic
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

/-- Wide target range. w roughly exp double log squared. -/
abbrev Plait (w:ℝ)(D:ℕ):Prop:= w^99 ≤ (D:ℝ) ∧ (D:ℝ)≤w^102

-- geometry
variable {u w k r ε σ c δ:ℝ}{D l:ℕ}

lemma march (p:Plait w D) (x:1≤w): w≤(D:ℝ) ∧ 0<(D:ℝ):=by
 have h:w ≤ (D:ℝ):=(pow_one w).symm.trans_le ((pow_le_pow_right₀ x (show 1≤99 by decide)).trans p.1)
 constructor; exact h; linarith

lemma pace_north (p:Plait w D) (x:1≤w)
  (h: (l:ℝ)≤w)(y:8*r≤w)(a:0<r): r≤(D:ℝ) ∧
     4*((l:ℝ)+1)/D≤r⁻¹:=by
 obtain ⟨b,d⟩:=march p x
 constructor; linarith
 have g: w^2≤(D:ℝ):= (pow_le_pow_right₀ x (by decide: (2:ℕ)≤99)).trans p.1
 rw [inv_eq_one_div,div_le_div_iff₀ d a]
 have t: 4*((l:ℝ)+1)*r ≤ w*(8*r):=by
     linarith only [mul_le_mul_of_nonneg_right (show (l:ℝ)+1 ≤2*w by linarith) a.le]
 rw [one_mul]
 exact t.trans ((mul_le_mul_of_nonneg_left y (zero_le_one.trans x)).trans ((sq w) ▸ g))

lemma fringe {m:ℝ} (p:Plait w D) (x:1≤w)
  (high:w^1000 ≤ k)(h:0≤ε)(e:m≤ε*w): 
  (D:ℝ)^8 * (m/k)≤ε:=by
 have hw:0<w:=zero_lt_one.trans_le x
 have hk:0<k:= (pow_pos hw _).trans_le high
 rw [←mul_div_assoc,div_le_iff₀ hk]
 calc
   _≤(w^102)^8*(ε*w):= (mul_le_mul_of_nonneg_left e (by positivity)).trans
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) p.2 _) (by positivity))
   _= ε*w^(102*8+1):= by rw [pow_add,pow_one,pow_mul];ring
   _ ≤ _:= mul_le_mul_of_nonneg_left ((pow_le_pow_right₀ x
       (show (102*8+1:ℕ)≤1000 by decide)).trans high) h

def Evening(q:Clip)(σ η C c δ u:ℝ) :Prop:=
 ∀ (w k:ℝ),u≤w→w^1000 ≤ k→
    ∀ n:Side, Even n.val→w^102 * pinch n≤u⁻¹→
      ∀ D l:ℕ, Plait w D → (l:ℝ)≤w→
      ∀ {M:Bed},M.covered σ C→Floor M q n η C→Bid.Sworn M n SU.group→
        ∀ {Z:PathData G}{θ v a:ℝ}(P:Attached M Z)(B:Z.Bounds q θ v a)
         (ρ:ℝ),1/2≤|ρ|→ |ρ|≤2→
           ∀ A:Ink (Chip n), A.qty≤c→ A.Within (stains 0 l)→ δ≤Larva.dint A→
             premium argent δ ≤ (D:ℝ)^8 * Optic.monetary B P k ρ A (ice n D)

theorem aurum (q:Clip)(η:ℝ)(c:ℝ)(p:0<σ)(h:0<C)(j:0<δ):∃u≥1,Evening q σ η C c δ u:=by
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
 exact droplets B P t o m' p n' _ A c' z y pos j ρ' ρ'' e.le x k'
    (fringe D' w' hk e.le hi) hz
