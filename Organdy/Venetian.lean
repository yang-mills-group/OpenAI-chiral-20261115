import Organdy.Terrier
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

abbrev wares(x:ℝ)(W:Config G n→ℂ) (s:Signed)(o:Site n)(U:Config G n):ℂ:=
 (x:ℂ)*W (pull s o U)
lemma gilt_scale(x:ℝ)(p:0≤x)(A:Ink (Chip n))(B:Chip n→ℝ):
 A.gilt (fun i=>Real.sqrt x *B i)=(x:ℂ)*A.gilt B:=by
 unfold Ink.gilt
 rw [mul_sum]; apply sum_congr rfl;intro i _
 rw [mul_sum]; apply sum_congr rfl;intro j _
 push_cast
 nth_rw 3 [←Real.sq_sqrt p]
 push_cast
 ring
open Larva (Domaine)

-- costs for one copy edge
structure Wicket (R:Rules SU.group)(ζ b k x α τ v depth pier skim:ℝ):Prop where
 kpos:0<k
 rise:0<x
 v0:0<v
 rev:2*v < ζ
 fits:v ≤ R.c
 tab: x*(α+b*τ^2) ≤ pier
 depth0:0 ≤ depth
 ch_feel: Real.sqrt x*(τ+faceCutError R v) ≤ depth
 fine:x*(α+b*(2*v)^3)+b*((2*depth)^4/k) ≤ skim

variable {x d u y :ℝ}

lemma sealW (C:Wicket R ζ b k x α τ v d u y)
 (h:Domaine l ζ τ α b W A) (s:Signed)(o:Site n)(U:Config G n):
 ‖wares x W s o U‖ ≤ u:=by
 rw [wares,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos C.rise]
 exact (mul_le_mul_of_nonneg_left (h.uniform _) C.rise.le).trans C.tab

lemma wares_bid (B:Z.Bounds q θ η a)(P:Attached M Z)
 (C:Wicket R ζ b k x α τ v d u y)
 (h:Domaine l ζ τ α b W A)
 (s:Signed)(o:Site n)
 (j:Onyx r L (mists τ U) m l o)
 (t:TrustLogs (X+Y) U r L v)
 (p:Drier G τ U)
 (e:ProbeBox (X+Y) (2*v))
 (g:0<β):
 let D:=unfurl q k (Real.sqrt x * coupling β) A s o
     (starFeed B P r L (mists τ U) m Y β X)
 ‖wares x W s o U-D‖ ≤ y:=by
 intro D
 let V:=sough q (Real.sqrt x * coupling β) s o
     (starFeed B P r L (mists τ U) m Y β X)
 let T:=bank s o (X+Y)
 have c(i)(w:i∈stains 0 l):V i= Real.sqrt x*blush T i ∧ |V i| ≤d:=by
    obtain ⟨h,t⟩:=sough_still B P j t C.fits C.v0.le (Real.sqrt_nonneg x) s g w
    exact ⟨h,t.trans C.ch_feel⟩
 have ht:A.gilt V=x*A.gilt (blush T):=by
    rw [←gilt_scale x C.rise.le]
    exact Ink.same h.inside (fun i w=>(c i w).1)
 refine (norm_sub_le_norm_sub_add_norm_sub _ (A.gilt V) _).trans ((add_le_add ?_ (air_sheds C.kpos h.purse h.inside C.depth0 V (fun i w=>(c i w).2))).trans C.fine)

 rw [ht, wares,←mul_sub,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos C.rise]
 apply mul_le_mul_of_nonneg_left _ C.rise.le
 have hT:‖T‖≤2*v:=(seats ..).trans (probe_cost (by linarith only [C.v0]) e)
 exact (h.priced _ T (leafHere s j t C.fits) (hT.trans_lt C.rev) (rowHere s j p)).trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hT _)
       ((A.qty_nonneg).trans h.purse)))

def cistern(x:ℝ)(W:Config G n→ℂ)(z:Site n)(s:Signed)(o:Site n)(U:Config G n):ℂ:=
 wares x W s o U * conj (wares x W (s*mir) (affine s o z) U)

lemma cistern_rate(h:Domaine l ζ τ α b W A)
 (C:Wicket R ζ b k x α τ v d u y)
 (z:Site n)(s:Signed)(o:Site n)(U:Config G n):
 ‖cistern x W z s o U‖ ≤ u^2:=by
 rw [cistern,norm_mul,RCLike.norm_conj,sq]
 exact mul_le_mul (sealW C h _ _ _) (sealW C h _ _ _) (norm_nonneg _)
   ((norm_nonneg _).trans (sealW C h s o U))

private lemma bucket{a b c d:ℂ}
 (p:‖a-c‖ ≤ y)(h:‖b-d‖ ≤ y)(ha:‖a‖ ≤ u)(hb:‖b‖ ≤ u):
 |(a*conj b).re - (c*conj d).re| ≤ y*(2*u+y):=by
 rw [←Complex.sub_re]
 have hu:0 ≤ u:=(norm_nonneg _).trans ha
 have hy:0 ≤ y:=(norm_nonneg _).trans p
 have hx:‖c‖ ≤ y+u:=by
   rw [norm_sub_rev] at p
   exact (norm_le_norm_sub_add c a).trans (add_le_add p ha)
 refine (Complex.abs_re_le_norm _).trans ?_
 rw [show a*conj b-c*conj d=(a-c)*conj b+c*conj (b-d) by rw [map_sub]; ring]
 refine (norm_add_le ..).trans ?_
 simp only [norm_mul,RCLike.norm_conj]
 exact (add_le_add (mul_le_mul p hb (norm_nonneg _) hy)
   (mul_le_mul hx h (norm_nonneg _) (add_nonneg hy hu))).trans_eq (by ring)

lemma cistern_cost(B:Z.Bounds q θ η a)(P:Attached M Z)
 (C:Wicket R ζ b k x α τ v d u y)
 (h:Domaine l ζ τ α b W A)
 (z:Site n)(s:Signed)(o:Site n)
 (j:Onyx r L (mists τ U) m l o)
 (i:Onyx r L (mists τ U) m l (affine s o z))
 (t:TrustLogs (X+Y) U r L v)
 (p:Drier G τ U)
 (e:ProbeBox (X+Y) (2*v))
 (g:0<β):

 |(cistern x W z s o U).re -
   compose q k (Real.sqrt x * coupling β) A z s o
     (starFeed B P r L (mists τ U) m Y β X)| ≤ y*(2*u+y):=
 bucket (wares_bid B P C h s o j t p e g)
    (wares_bid B P C h _ _ i t p e g) (sealW C h s o U)
    (sealW C h _ _ U)

lemma cistern_inv (w:GaugeInvariant W) (z o:Site n)(s:Signed):
 GaugeInvariant (cistern x W z s o):=by
 intro k U
 have h(t b): wares x W t b (gauge k U)=wares x W t b U:=
    congrArg ((x:ℂ)* ·) (invariant_pull w t b k U)
 simp [cistern,h]
lemma cistern_meas (w:Measurable W) (z o:Site n)(s:Signed):
 Measurable (cistern x W z s o):=
 let h (s:Signed) (o:Site n):Measurable (wares x W s o):=
    measurable_const.mul (w.comp ((Wilson.continuous_pull ..).measurable))
 (h ..).mul (Complex.continuous_conj.measurable.comp (h ..))

variable (x W)
lemma wares_pose(s t:Signed)(o b:Site n)(U):
 wares x W s o (pull t b U)=wares x W (t*s) (affine t b o) U:=by unfold wares;rw [pull_pull]
lemma inlay (s t:Signed)(o b z:Site n):affine (t*s) (affine t b o) z = affine t b (affine s o z):=by
 simp [affine, Signed.act_mul, add_assoc]
lemma cistern_swing(s t:Signed)(o b z:Site n)(U):
 cistern x W z s o (pull t b U)=cistern x W z (t*s) (affine t b o) U:=by
 simp [cistern,wares_pose,mul_assoc, inlay]
