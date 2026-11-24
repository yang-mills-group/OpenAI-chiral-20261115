import Organdy.Mansard
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
-- tilt ± t with tame magnitude ≤ knock; extra op cost (plenit):
abbrev tithe (x:ℝ):=(knock x)^2*(rail x)^4
abbrev toll (x:ℝ):=insure x+tithe x
lemma tithe_pos(x:ℝ):0≤tithe x:=by unfold tithe;positivity
lemma toll_pos(x:ℝ):0<toll x:=
 add_pos_of_pos_of_nonneg (coin_pos ..) (tithe_pos _)
-- chair loss via ε := yieldt
abbrev fee (x:ℝ):=toll x+3*yieldt x
lemma fee_pos(x:ℝ):0<fee x:=add_pos (toll_pos _) (mul_pos (by norm_num) (coin_pos ..))
-- target accuracy
abbrev lakeZ:=flagon (-1000)
lemma fee_larger:toll x≤fee x:=le_add_of_nonneg_right (mul_nonneg (by norm_num) (coin_pos ..).le)

lemma monetary_lid (B:Z.Bounds q θ v a)(P:Attached M Z)
 (x ρ b:ℝ)(A:Ink (Chip n))(z:Site n)(h:A.qty ≤ b):
 |monetary B P (clipper x) ρ A z| ≤ (b*clipper x)^2:=by
 rw [←Real.norm_eq_abs]
 let X:stamen B P n→ℝ:= fun i=>compose q (clipper x) ρ A z 1 0 i.val
 refine (norm_integral_le_of_norm_le (μ:=stdGaussian (stamen B P n))
   (f:=X) (g:=fun _=>(b*clipper x)^2) (integrable_const _) ?_).trans_eq ?_
 swap
 · simp
 · filter_upwards with i
   rw [Real.norm_eq_abs]
   exact compose_limit (coin_pos ..) h z 1 0 i.val
lemma tithePays:Pays 0 (-39988) 0 tithe:=by
 change Pays _ _ _ (fun t=>coin t 0 (-20000) 0^2*coin t 0 3 0^4)
 convert times (pot (whole 0 (-20000) 0) 2) (pot (whole 0 3 0) 4) using 1 <;> norm_num
lemma feePays:Pays 0 (-21100) 0 fee :=
 plus (plus (whole _ _ _) (merit tithePays (by norm_num [Earlier])))
      (merit (Pays.scale 3 (whole 0 (-21500) 0)) (by norm_num [Earlier]))

-- σ := knock x, self certificate:
abbrev Virgin (x b:ℝ):Prop:=
 let T:=knock x*(b*clipper x)^2+fee x
 T ≤ 1 ∧ fee x + 2*T^2 ≤ knock x * lakeZ x
lemma virgin (b:ℝ):∀ᶠ x:ℝ in atTop,Virgin x b:=by
 have h: Pays 0 (-16000) 0 (fun x=> knock x*(b*clipper x)^2+fee x):=by
    refine plus ?_ (merit feePays (by norm_num [Earlier]))
    convert (times (whole 0 (-20000) 0) (pot (Pays.scale b (whole 0 2000 0)) 2)) using 1 <;> norm_num

 filter_upwards [
 (limit h (by norm_num [Earlier])).eventually (ge_mem_nhds zero_lt_one),
 leap (w:=0) (p:=-21000) (q:=0)
   (plus feePays (merit (Pays.scale 2 (pot h 2)) (by norm_num [Earlier]))) (by norm_num [Earlier])] with x i j
 refine ⟨i, ?_⟩
 rw [show knock x*lakeZ x = coin x 0 (-21000) 0 from by unfold knock lakeZ flagon;rw [coin_mul];norm_num]
 exact j

lemma Virgin.stable (v:Virgin x b){i j:ℝ}
 (h:|i| ≤ (b*clipper x)^2)
 (p:∀ t:ℝ, |t|≤knock x → 1+t*j ≤ Real.exp ((t*i+toll x)+3*yieldt x)):
 |j-i|≤lakeZ x:=by
 let T:= knock x*(b*clipper x)^2+fee x
 have z:0<knock x:=coin_pos ..
 have g(t)(w:|t|≤knock x):t*(j-i)≤ knock x*lakeZ x:=by
   let k:=t*i+toll x+3*yieldt x
   have a: |k|≤T:=by
      rw [show k=t*i+fee x from add_assoc ..]
      refine (abs_add_le ..).trans ?_
      rw [abs_mul,abs_of_pos (fee_pos x)]
      exact add_le_add (mul_le_mul w h (by positivity) z.le) le_rfl
   have c:=Real.abs_exp_sub_one_sub_id_le (a.trans v.1)
   have cc:k^2 ≤ T^2:=by rw [←sq_abs];exact pow_le_pow_left₀ (abs_nonneg _) a _
   apply le_trans _ v.2
   have hx:t*j≤Real.exp k-1:=le_sub_iff_add_le'.mpr (p t w)
   rw [mul_sub]
   have hv:= (abs_le.mp c).2
   linarith only [hx,hv,cc,show k=t*i+fee x from add_assoc ..,sq_nonneg T]
 refine abs_le.mpr ⟨neg_le.mp ((mul_le_mul_iff_right₀ z).1 ?_), (mul_le_mul_iff_right₀ z).1 (g _ (le_of_eq (abs_of_pos z)))⟩
 rw [mul_neg, ←neg_mul]
 exact g _ (by rw [abs_neg,abs_of_pos z])

lemma faceup (x b:ℝ){i t:ℝ}
 (h: |i|≤(b*clipper x)^2)(p:|t|≤knock x):
 -(knock x*(b*clipper x)^2)≤t*i+toll x:=by
 apply le_trans _ (le_add_of_nonneg_right (toll_pos x).le)
 have a:=mul_le_mul p h (abs_nonneg i) ((coin_pos ..).le)
 rw [←abs_mul] at a
 exact (abs_le.mp a).1
