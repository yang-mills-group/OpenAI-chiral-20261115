import Organdy.Venetian
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


open Push.Local Next.Rank.Spindle Next.SectorChange
open Scree
open scoped Classical
variable {c:Side}{r:Ratio c n}{L:Support c}
  {α b ζ e k β τ:ℝ}{m l:ℕ}
  {W:Config G n→ℂ}{A:Ink (Chip n)}
  {R: Rules G}
  {F X Y:Larva.Dir n}{U:Config G n}{o:Site n}

variable {x d u y :ℝ}
open Larva (Domaine)
variable {J:Type*}

namespace Ballroom
variable (D: Ballroom J n)
def transom (s:Signed)(e:Site n) : Ballroom J n where
 path:=fun i=>s*D.path i
 post:=fun i=>affine s e (D.post i)
lemma jamb (s:Signed)(b z:Site n)(i:J):
 (D.transom s b).back z i=affine s b (D.back z i):=inlay ..
lemma tympanum (s:Signed)(b z:Site n)(i:J):
 (D.transom s b).area l z i=(D.area l z i).image (turnSites s b):=by
 ext k
 obtain ⟨w,rfl⟩:=(turnSites s b).surjective k
 simp only [area, jamb, show (D.transom s b).post i=affine s b (D.post i) from rfl]
 simp [show affine s b=(turnSites s b) from rfl, halo_spec,(turnSites s b).injective.eq_iff]
lemma transom_room(s:Signed)(e z:Site n)(g:D.Space l z): (D.transom s e).Space l z:=by
 intro i j v
 change Disjoint ((D.transom s e).area l z i) ((D.transom s e).area l z j)
 simp only [tympanum]
 apply disjoint_left.mpr
 intro w h k
 obtain ⟨a,v₁,rfl⟩:=mem_image.mp h
 obtain ⟨b,v₂,p⟩:=mem_image.mp k
 exact disjoint_left.mp (g v) v₁ ((turnSites s e).injective p ▸ v₂)

end Ballroom
variable [Fintype J]

def nectar (x:ℝ)(W:Config G n→ℂ)(z:Site n)(D:Ballroom J n) (U:Config G n):ℝ:=
 ∑i,(cistern x W z (D.path i) (D.post i) U).re

lemma nectarine (h:Domaine l ζ τ α b W A)(C:Wicket R ζ b k x α τ v d u y)
 (z:Site n)(D:Ballroom J n):
 Envelope (nectar x W z D) ∧ GaugeInvariant (nectar x W z D):=by
 refine ⟨⟨?_,↑(Fintype.card J)*u^2,?_⟩,?_⟩
 · apply Finset.measurable_sum
   exact fun i _=> Complex.continuous_re.measurable.comp (cistern_meas h.meas ..)
 · intro t; rw [Real.norm_eq_abs]; unfold nectar
   exact (abs_sum_le_sum_abs ..).trans
    ((sum_le_sum (g:=fun _=> u^2) (fun i _=> (Complex.abs_re_le_norm _).trans (cistern_rate h C _ _ _ t))).trans_eq (by simp))
 · intro i t; unfold nectar
   simp_rw [cistern_inv h.move _ _ _ i t]

lemma tendril(x:ℝ)(W:Config G n→ℂ)(z:Site n)(D:Ballroom J n)
 (s:Signed)(b:Site n)(U:Config G n):
 nectar x W z D (pull s b U)= nectar x W z (D.transom s b) U:=by
 unfold nectar
 simp only [cistern_swing]
 rfl

def canvas (τ t w:ℝ)(φ:Config G n→ℝ)(U:Config G n):ℝ:=
 if Drier G τ U then φ U else if 0≤t then -w else w
lemma primed{φ:Config G n→ℝ}(f:Envelope φ) (g:GaugeInvariant φ)
 (τ t w:ℝ):
 Envelope (canvas τ t w φ) ∧ GaugeInvariant (canvas τ t w φ):=by
 refine ⟨?_,?_⟩
 · exact Envelope.piece (drier_set G τ) f (Envelope.const (if 0 ≤ t then -w else w))
 · intro i U; simp [canvas,drier_gauge,g i U]
lemma darkness(τ t w:ℝ)(φ:Config G n→ℝ)(v:ℝ)(h:|v|≤w)
 (u:¬Drier G τ U) :
 t*canvas τ t w φ U≤t*v:=by
 rw [canvas,if_neg u]
 split
 · exact mul_le_mul_of_nonneg_left (abs_le.mp h).1 (by assumption)
 · rename_i v
   exact mul_le_mul_of_nonpos_left (abs_le.mp h).2 (le_of_not_ge v)
