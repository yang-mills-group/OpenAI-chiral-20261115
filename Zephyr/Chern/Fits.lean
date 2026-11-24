import Zephyr.Chern.Jet
set_option autoImplicit false
noncomputable section
namespace Zephyr.Chern

open YM YM.Lattice Silk YM.CF


def gainR (x y: Cover) : ℝ :=
  -(bow fun a b=>(x a:ℝ)*y b)
def gain (x y: Cover) : ℂ := gainR x y
lemma rune_bow (x y : Cover) :
    bow (fun a b=>rune a x*rune b y)=gain x y := by
  have h i j : rune i x*rune j y= -( (x i:ℂ)*y j) := by
    rw [rune,rune, mul_mul_mul_comm,Complex.I_mul_I,neg_one_mul]
  simp only [h,bow,gain,gainR]
  push_cast;ring

variable {ι:Type*}

/-- Joint HasSum at each displacement x with sum indexed by y on cover. -/
def Fits (a:Coats ι) (f:Cover→Cover→Op ι) :=
  ∀ x i j, HasSum (fun y=> f y (x-y) i j) (seam x a i j)

variable {a b:Coats ι}{f g:Cover→Cover→Op ι}

lemma Fits.same (h:Fits a f) (q:Fits b f) : a=b :=
  seam_ext <| fun x=> Matrix.ext <| fun i j=> (h x i j).unique (q x i j)

lemma Fits.add (h:Fits a f)(q:Fits b g) :
    Fits (a+b) (fun x y=> f x y+g x y) := by
  intro x i j; rw [map_add]; exact (h x i j).add (q x i j)

lemma Fits.sub (h:Fits a f)(q:Fits b g) :
    Fits (a-b) (fun x y=> f x y-g x y) := by
  intro x i j; rw [map_sub]; exact (h x i j).sub (q x i j)


lemma Fits.scale (h:Fits a f)(k:ℂ) :
    Fits (k • a) (fun x y=>k • f x y) := by
  intro x i j; rw [map_smul]; exact (h x i j).mul_left k

lemma fits_bow {u: Axis→Axis→Coats ι} {v:Axis→Axis→Cover→Cover→Op ι}
    (h:∀ a b,Fits (u a b) (v a b)) :
    Fits (bow u) (fun x y=>bow fun a b=>v a b x y) :=
  ((h 0 1).sub (h 1 0)).add ((h 2 3).sub (h 3 2))

lemma fits_gain {u:Axis→Axis→Coats ι} (h:∀ a b,Fits (u a b) fun x y=>
      rune a x • rune b y • f x y) :
    Fits (bow u) (fun x y=> gain x y • f x y) := by
  simp_rw [←rune_bow]
  have e x y:
    (bow fun a b=> rune a x*rune b y) • f x y = bow fun a b=> rune a x • rune b y • f x y := by
      simp only [bow,add_smul,sub_smul,smul_smul]
  simp_rw [e]
  exact fits_bow (v:=fun a b x y=>_) h

variable [Fintype ι]

def braidE (a b:Coats ι) x y := seam x a * seam y b

lemma fits_mul (a b:Coats ι) : Fits (a*b) (braidE a b) := by
  intro x i j
  rw [seam_entries]
  exact (pack_entries a b x i j).hasSum

lemma fits_crossB (a b:Coats ι) :
    Fits (crossB a b) (fun x y=> gain x y • braidE a b x y) := by
  apply fits_gain
  intro i j
  have h:= fits_mul (Δ i a) (Δ j b)
  unfold braidE at *
  simp_rw [seam_Δ, Matrix.smul_mul, Matrix.mul_smul] at h
  exact h

lemma fits_curly (a:Coats ι) : Fits (curly a)
    (fun x y=>gain x y • gain x y • braidE a a x y) := by
  apply fits_gain
  intro i j
  have h:= fits_crossB (Δ i a) (Δ j a)
  unfold braidE at *
  simp_rw [seam_Δ, Matrix.smul_mul, Matrix.mul_smul] at h
  simp_rw [smul_comm (gain _ _) (rune i _), smul_comm (gain _ _) (rune j _)] at h
  exact h

variable [DecidableEq ι]

lemma seam_spun_left (z:Op ι)(p:Coats ι)(x:Cover) :
    seam x (spun z*p)=z*seam x p := by
  ext i j
  change coeff x ((spun z*p) i j)=_
  rw [Matrix.mul_apply,map_sum,Matrix.mul_apply]
  refine Finset.sum_congr rfl (fun k _=>?_)
  change coeff x ((algebraMap ℂ Silk (z i k))*_)=_
  rw [←Algebra.smul_def,map_smul, smul_eq_mul];rfl

lemma Fits.sp (h:Fits a f)(z:Op ι) :
    Fits (spun z*a) (fun x y=>z * f x y) := by
  intro x i j
  rw [seam_spun_left]
  simp only [Matrix.mul_apply]
  exact hasSum_sum fun k _=> (h x k j).mul_left (z i k)

/-- displacement laws in the conventions of the fold. -/
structure Gains (p r s:Coats ι) (Z:Op ι) : Prop where
  zero : Fits p (braidE p p)
  one : Fits r (fun x y=> braidE p r x y + braidE r p x y +
    Z * (gain x y • braidE p p x y))
  two : Fits s (fun x y=> braidE p s x y+ braidE s p x y+braidE r r x y +
    (Z * (gain x y • braidE p r x y+gain x y • braidE r p x y) +
    (2:ℂ)⁻¹ • (Z*Z* (gain x y • gain x y • braidE p p x y))))

lemma Gains.jet {p r s:Coats ι}{z:Op ι} (h:Gains p r s z) : Jet p r s (spun z) where
  zero:=h.zero.same (fits_mul p p)
  one:=h.one.same (((fits_mul p r).add (fits_mul r p)).add ((fits_crossB p p).sp z))
  two:=by
    rw [secondTwist,←map_mul]
    exact h.two.same ((((fits_mul p s).add (fits_mul s p)).add (fits_mul r r)).add
      ((((fits_crossB p r).add (fits_crossB r p)).sp z).add
        (((fits_curly p).sp (z*z)).scale _)))
