import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.Bravura
open scoped Topology Classical InnerProductSpace
open Finset Filter
universe u v w
variable {A:Type u}[Fintype A] {ι:Type v}[Fintype ι]
 {V:Type w}[NormedAddCommGroup V][NormedSpace ℂ V] -- NormedSpace ℝ?
variable (B:ι→A→ℝ→V)


section
-- Want DerivAt ℝ from complex V; RestrictScalars ℝ
def solo (ℓ:ι)(a:A):V:=deriv (B ℓ a) 0
def cantata (ℓ:ι):V:=∑a:A,solo B ℓ a
def motif (ℓ:ι)(a:A)(t:ℝ):V:=B ℓ a 0+(t:ℂ)•solo B ℓ a

/-- Only quadratic approximation in each axial displacement is required
(C² Schwinger prices can fit this locally, no contour estimate on all
Mark prices here). -/
def Timbre (R D :ℝ):Prop:=
   ∀ℓ a,DifferentiableAt ℝ (B ℓ a) 0 ∧
      ∀t:ℝ,|t|≤R→‖B ℓ a t-motif B ℓ a t‖≤D*t^2

variable (l:ι→ℂ) (T:A→V) (t p C D R :ℝ)
def harmony : V := ∑j:ι, l j • cantata B j
def intonation (l:ι→ℂ)(a:A)(t:ℝ):V:=∑j:ι, l j • motif B j a t
def version (l:ι→ℂ)(a:A)(t:ℝ):V:=∑j:ι, l j • B j a t
def Tunes (l:ι→ℂ)(t:ℝ)(T:A→V) (E:ℝ):Prop:=
 ∀a:A, ‖T a-version B l a t‖≤E

variable {B l T t D R}
omit [Fintype A] in
lemma toned {E:ℝ} (h:Timbre B R D)(r:|t|≤R)(e:Tunes B l t T E)(a:A):
 ‖T a-intonation B l a t‖≤E+(∑j,‖l j‖)*(D*t^2):=by
    rw [show T a-intonation B l a t=T a-version B l a t+
           (version B l a t-intonation B l a t) by abel]
    refine (norm_add_le ..).trans (add_le_add (e a) ?_)
    unfold version intonation
    rw [←sum_sub_distrib,sum_mul]
    refine (norm_sum_le ..).trans (sum_le_sum fun j _=>?_)
    rw [←smul_sub,norm_smul]; exact mul_le_mul_of_nonneg_left ((h j a).2 t r) (norm_nonneg _)

def octaveV (U W:A→ V):V:=∑a:A, (U a-W a)

lemma octaveC :octaveV (fun a=>intonation B l a t)
  (fun a=>intonation B l a (-t))=(t+t:ℂ) • harmony B l:=by
   unfold octaveV harmony intonation cantata
   -- rearrange ∑ℓ ∑a
   simp_rw [smul_sum]
   rw [sum_comm (f:=fun i a=>(t+t:ℂ) • l i • solo B i a)]
   refine sum_congr rfl fun a _=>?_
   rw [←sum_sub_distrib]
   refine sum_congr rfl fun i _=>?_
   rw [←smul_sub]
   conv_rhs => rw [smul_comm]
   unfold motif
   simp only [Complex.ofReal_neg, neg_smul,add_smul]; congr 1; abel

def sound (A:Type u)[Fintype A](l:ι→ℂ)(D t E:ℝ):ℝ:=Fintype.card A*
  (2*(E+(∑j,‖l j‖)*(D*t^2)))

lemma plays {U W:A→V}{E:ℝ} (h:Timbre B R D)(r:|t|≤R)
  (e:Tunes B l t U E)(g:Tunes B l (-t) W E):
 ‖octaveV U W-(t+t:ℂ) • harmony B l‖≤sound A l D t E:=by
  rw [←octaveC]
  unfold octaveV
  rw [←sum_sub_distrib]
  apply (norm_sum_le ..).trans
  refine (sum_le_card_nsmul _ _
     ( 2*(E+(∑j,‖l j‖)*(D*t^2))) ?_).trans_eq (by simp [sound])
  intro a _
  rw [sub_sub_sub_comm, two_mul]
  refine (norm_sub_le ..).trans (add_le_add (toned h r e a) ?_)
  simpa using toned h (show |-t|≤R by rwa [abs_neg]) g a

def gap (δ r :ℝ):=δ*r^16
def allowance (C r:ℝ):=C*r^47
def tolerance (C r:ℝ):=C*r^66
def sumSize (l:ι→ℂ):ℝ:=∑j,‖l j‖
def costS (A:Type u)[Fintype A](C D δ:ℝ):ℝ:=Fintype.card A*(2*(C+C*D*δ^2))

lemma swell {C δ r:ℝ}(d:0≤D)(c:0≤C)
 (p:0<r)(v:r≤1)(e:sumSize l≤allowance C r) :
 sound A l D (gap δ r) (tolerance C r) ≤ costS A C D δ*r^66 :=by
 rw [sound, tolerance, costS,mul_assoc]
 apply mul_le_mul_of_nonneg_left _ (by positivity)
 rw [mul_assoc,add_mul]
 refine mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) (by norm_num)
 have u:=mul_le_mul_of_nonneg_right e
   (mul_nonneg d (sq_nonneg (gap δ r)))
 refine u.trans ?_
 rw [allowance,gap,mul_pow]
 have z:r^47 * (r^16)^2=r^79:=by ring
 rw [show C * r ^ 47 * (D * (δ ^ 2 * (r ^ 16) ^ 2))=C*D*δ^2*(r^47*(r^16)^2) from by ring,z]
 exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one p.le v (by decide)) (by positivity)

def emitted (C δ r:ℝ) (W:V):Prop:=
     r^49≤8*C*δ*‖W‖
def Loud (C r:ℝ) (W:V):Prop:= r^65≤2*C*‖W‖
def Piano (A:Type u)[Fintype A](C D δ r:ℝ):Prop:=4*C*costS A C D δ*r ≤ 1
lemma quieter {C δ r:ℝ}(p:0≤r)
 (h:Piano A C D δ r):
     2*C*(costS A C D δ *r^66) ≤ r^65/2:=by
 unfold Piano at h
 calc
   _ = (4*C*costS A C D δ*r)* (r^65/2) := by ring
   _ ≤ _ := mul_le_of_le_one_left (by positivity) h

lemma voiced {C δ r:ℝ}(c:0<C)(u:0<δ)(p:0<r){W Y:V}
  (s:Loud C r W) (h:Piano A C D δ r)
  (k:‖W - (@Complex.ofReal (gap δ r)+@Complex.ofReal (gap δ r)) • Y‖ ≤ costS A C D δ *r^66):
 emitted C δ r Y:=by
 let t:=gap δ r
 have q:0≤t:= mul_nonneg u.le (pow_nonneg p.le _)
 change ‖W - ((t:ℂ)+ (t:ℂ)) • Y‖≤_ at k
 let x:=(t+t:ℂ) • Y
 have eq:‖x‖=(t+t)*‖Y‖:=by
   rw [show x=((t+t:ℝ):ℂ) • Y from by rw [Complex.ofReal_add],norm_smul,Complex.norm_of_nonneg (add_nonneg q q)]

 have a: ‖W‖ ≤ costS A C D δ * r^66 + (t+t)*‖Y‖:= by
      nth_rw 1 [show W=(W-x)+x by abel]
      exact (norm_add_le ..).trans (add_le_add k eq.le)
 have b:= s.trans (mul_le_mul_of_nonneg_left a (show 0≤2*C by positivity))
 apply le_of_mul_le_mul_right _ (pow_pos p 16)
 change r^49*r^16≤8*C*δ*‖Y‖*r^16
 dsimp only [t,gap] at b
 linarith [quieter p.le h]

theorem fortissimo {C δ r:ℝ} (c:0<C)(d:0≤D)(u:0<δ)(p:0<r)(v:r≤1)
  {U W:A→V}(emin:Timbre B R D)(r0:|gap δ r|≤R)
  (l0:sumSize l≤allowance C r)
  (e:Tunes B l (gap δ r) U (tolerance C r))
  (g:Tunes B l (-gap δ r) W (tolerance C r))
  (h:Piano A C D δ r)(s:Loud C r (octaveV U W)):
 emitted C δ r (harmony B l):=
  voiced c u p s h ((plays emin r0 e g).trans (swell d c.le p v l0))
end
end YM.CF.Merino.Bravura
