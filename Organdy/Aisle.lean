import Organdy.Virgin
import Organdy.Sunrise
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

open Tempest Worth BProof
open Pays
-- w used in Plait defined flagon 1; BPress.drift.
abbrev webX:=flagon 1
-- board covers width
abbrev walkF (x:ℝ):ℕ:=⌈flagon 105 x⌉₊

lemma web_pow (k:ℕ)(x:ℝ):webX x^k=flagon k x:=by
 unfold webX flagon; rw [coin_pow]; ring_nf
lemma walkF_pays:Pays 0 105 0 (fun x=>(walkF x:ℝ)):=by
 have h:= plus (merit (constant 1) (w:=0) (p:=105) (q:=0) (by norm_num [Earlier])) (whole 0 105 0)
 obtain ⟨g,p⟩:=Asymptotics.isBigO_iff.mp h
 apply Asymptotics.isBigO_iff.mpr
 refine ⟨g,p.mono fun i t=>(le_trans ?_ t)⟩
 rw [Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg _),
     Real.norm_eq_abs]
 apply le_trans _ (le_abs_self _)
 exact ((Nat.ceil_lt_add_one ((coin_pos i 0 105 0).le)).le.trans_eq (add_comm ..))

lemma funded (k:ℕ) :
 ∀ᶠ x:ℝ in atTop,14*meterC x*(4*((walkF x:ℝ)+k))^4 ≤ yieldt x:=by
 refine leap (times (Pays.scale 14 (whole r_meter 0 0))
    (pot (Pays.scale 4 (plus walkF_pays (merit (constant (k:ℝ)) (by norm_num [Earlier])))) 4))
     (by norm_num [Earlier,r_meter])

structure Aisle (x z:ℝ):Prop where
   gw:z≤webX x
   depth:(radiusB x:ℝ)+20≤webX x
   veil:webX x^1000≤clipper x
   yard{D l:ℕ} : Plait (webX x) D →(l:ℝ)≤webX x → 10*(D+l+10)≤walkF x
set_option maxRecDepth 4000
lemma aisleWide(z:ℝ):∀ᶠ x:ℝ in atTop,Aisle x z:=by
 have a:=plus (merit rising (w:=0) (p:=(1/2)) (q:=0) (by norm_num [Earlier]))
     (merit (constant 20) (by norm_num [Earlier]))
 have y:=Pays.scale 10
   (plus (plus (whole 0 102 0)
           (merit (whole 0 1 0) (by norm_num [Earlier])))
     (merit (constant 10) (by norm_num [Earlier])))
 filter_upwards [
    leap (constant z) (w:=0) (p:=1) (q:=0) (by norm_num [Earlier]),
    leap a (w:=0) (p:=1) (q:=0) (by norm_num [Earlier]),
    leap (whole 0 1000 0) (w:=0) (p:=2000) (q:=0) (by norm_num [Earlier]),
    leap y (w:=0) (p:=105) (q:=0) (by norm_num [Earlier])]
    with x i j k v
 refine ⟨i,j,?_,?_⟩
 · rw [web_pow];exact mod_cast k
 intro D l p q
 apply Nat.cast_le (α:=ℝ)|>.mp
 push_cast
 apply le_trans _ (Nat.le_ceil (flagon 105 x))
 apply le_trans _ v
 have h := p.2;rw [web_pow] at h
 norm_num at h
 gcongr

lemma oceania (ε:ℝ)(p:0<ε):
 ∀ᶠ x:ℝ in atTop, ∀ D:ℕ, Plait (webX x) D→(D:ℝ)^8*lakeZ x≤ε:=by
 have i:=times (pot (whole 0 102 0) 8) (whole 0 (-1000) 0)
 filter_upwards [
   (limit i (by norm_num [Earlier])).eventually (ge_mem_nhds p)]
  with x t D s
 have h:=s.2; rw [web_pow] at h
 norm_num at h
 refine le_trans ?_ t
 exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg D) h 8)
   (coin_pos ..).le
