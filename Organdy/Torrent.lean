import Organdy.Daylight
import YM.SU5.Circuit.Quartet
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

/-- clipped square -/
abbrev mist (k x:ℝ):ℝ:=viewμ k (x^2)
open scoped ComplexConjugate
def haze (a:ι→ℂ)(k:ℝ)(x:ι→ℝ):ℂ:=∑i,a i*(mist k (x i))

lemma bud_mist{k:ℝ}(pk:0<k)(x:ℝ):0 ≤ mist k x∧mist k x ≤ k∧mist k x≤x^2 ∧ x^2-mist k x ≤ x^4/k:=by
 convert clipμ pk (x^2) (sq_nonneg _) using 5
 ring_nf
lemma abs_mist{k:ℝ}(pk:0<k)(x:ℝ):|mist k x|≤k:=by
 rw [abs_of_nonneg (bud_mist pk x).1]
 exact (bud_mist pk x).2.1
lemma mist_smooth{k:ℝ}(pk:0<k):ContDiff ℝ 1 (mist k) := by
 refine ContDiff.div ?_ ?_ ?_
 · fun_prop
 · fun_prop
 intro x;positivity

/-- polar form α(X) on standard Gaussian at u -/
abbrev spec (L:ι→E)(x:E):ι→ℝ:=fun i=> inner ℝ (L i) x

variable {k:ℝ} (pk:0<k)
local notation "μ" => stdGaussian E
def zephyr (k:ℝ)(L R:ι→E)(i j:ι):ℝ:=
 ∫x, (mist k (spec L x i))*(mist k (spec R x j))∂μ
def cirrus (a:ι→ℝ)(k:ℝ)(L:ι→E)(x:E):ℝ:=
 ∑i,a i * mist k (spec L x i)

/-- constant sequence trick meets Quartet -/
abbrev nip (u:E):Unit→E:=fun _=>u
lemma nip_val(u:E)(x:E):coalK (nip u) x=inner ℝ u x^2:=by
 simp [coalK,talents,nip]

include pk in
lemma sip(u:E): MemLp (fun x:E=>mist k (inner ℝ u x)) 2 μ:=by
 simpa only [nip_val] using clipped (nip u) pk

include pk in
lemma draft (a:ι→ℝ)(L R:ι→E)(i j):
 Integrable (fun x:E=> a i*a j*(mist k (spec L x i)*mist k (spec R x j))) μ:=
 ((sip pk (L i)).integrable_mul (sip pk (R j))).const_mul _

lemma clouds_swell (a:ι→ℝ)(k:ℝ)(L R:ι→E)(x:E):
 cirrus a k L x * cirrus a k R x = fleet a (fun i j=>mist k (spec L x i)*mist k (spec R x j)):=by
 rw [cirrus,cirrus, sum_mul_sum, fleet]
 apply sum_congr rfl;intro i _
 apply sum_congr rfl;intro j _
 ring

include pk in
lemma draft_all (a:ι→ℝ)(L R:ι→E):
 Integrable (fun x:E=>cirrus a k L x * cirrus a k R x) μ:=by
 simp_rw [clouds_swell,fleet]
 apply integrable_finsetSum;intro i _
 apply integrable_finsetSum;intro j _
 exact draft pk .. 

include pk in
lemma snow (a:ι→ℝ)(L R:ι→E):
 (∫x, cirrus a k L x * cirrus a k R x∂μ)=fleet a (zephyr k L R):=by
 simp_rw [clouds_swell, fleet]
 rw [integral_finsetSum univ (fun i _=>integrable_finsetSum univ (fun j _=>draft pk a L R i j))]
 apply sum_congr rfl;intro i _
 rw [integral_finsetSum univ (fun j _=>draft pk a L R i j)]
 simp_rw [integral_const_mul,zephyr]

include pk in
lemma icicles (a:ι→ℂ)(L R:ι→E):
 (∫x,(haze a k (spec L x) * conj (haze a k (spec R x))).re∂μ)=
 fleet (fun i=>(a i).re) (zephyr k L R)+fleet (fun i=>(a i).im) (zephyr k L R):=by
 simp_rw [Complex.mul_re, Complex.conj_re, Complex.conj_im,mul_neg,sub_neg_eq_add]
 let b:=fun i=>(a i).re; let c:=fun i=>(a i).im
 have hr(L:ι→E)(x:E):(haze a k (spec L x)).re=cirrus b k L x:=by simp [haze,cirrus,b]
 have hi(L:ι→E)(x:E):(haze a k (spec L x)).im=cirrus c k L x:=by simp [haze,cirrus,c]
 simp_rw [hr,hi]
 rw [integral_add (draft_all pk b _ _) (draft_all pk c _ _),snow pk,snow pk]

abbrev due(B:ℝ):= sizingμ Unit B
lemma due_non{B:ℝ}(h:0≤B):0≤due B:=by unfold due sizingμ balboa;positivity

include pk in
lemma accord {B:ℝ}(b:0≤B)
 (L R:ι→E)(i j)(h:‖L i‖≤B)(u:‖R j‖≤B):
 |zephyr k L R i j - (‖L i‖^2*‖R j‖^2+2*(inner ℝ (L i) (R j))^2)|
  ≤due B/k:=by

 rw [←duet]
 have hj := clipE (nip (L i)) (nip (R j)) b (fun _=>h) pk (fun _=>u)
 dsimp only at hj
 simp_rw [nip_val] at hj 
 unfold zephyr mist spec
 rw [abs_of_nonpos (sub_nonpos.mpr hj.1),neg_sub]
 exact hj.2

variable {c B ε D β t:ℝ}{L R:ι→E}
def lapse (ε t:ℝ):ℝ:= ε + 2*ε*(ε+2*t)
include pk in
lemma accord₂ (b:0≤B) (d: D^8 * (due B/k) ≤ ε) (e:0≤ε)
 (i j)(h:‖L i‖≤B)(u:‖R j‖≤B)(H:‖R j‖=‖L j‖)
 (p:ℝ)(g:|β*p|≤t)(f:|D^4*inner ℝ (L i) (R j)-β*p| ≤ ε):
 |D^8 * zephyr k L R i j-
 (D^4*‖L i‖^2*(D^4*‖L j‖^2)+2*β^2*p^2)| ≤ lapse ε t:=by
 let Q:= D^4 * inner ℝ (L i) (R j)
 have hx: |D^8 * (zephyr k L R i j-
       (‖L i‖^2*‖R j‖^2+2*(inner ℝ (L i) (R j))^2))| ≤ ε:=by
      rw [abs_mul, abs_of_nonneg (by positivity:0≤D^8)]
      exact (mul_le_mul_of_nonneg_left (accord pk b _ _ _ _ h u) (by positivity:_)) |>.trans d
 let x:= D^8 * (zephyr k L R i j-
       (‖L i‖^2*‖R j‖^2+2*(inner ℝ (L i) (R j))^2))

 rw [show D^8 * _ - _ = x + (2*Q^2-2*(β*p)^2)
      from (by unfold x Q;rw [H];ring :
      D^8 * zephyr k L R i j-
       (D^4*‖L i‖^2*(D^4*‖L j‖^2)+2*β^2*p^2)=_)]
 exact (abs_add_le ..).trans (add_le_add hx (square_close Q _ t _ e f g))

def trophy(d:τ→ℝ)(b δ:ℝ):ℝ:= b^2*(δ^2/floorCharge d)
lemma trophy_pos(d:τ→ℝ){b δ:ℝ}(x:0<b)(y:0<δ):0<trophy d b δ:=by
 have p:= floor_pos d
 unfold trophy; positivity

lemma usable (c t η:ℝ)(h:0<η):∃ε>0,lapse ε t * c^2 ≤ η/4:=by
 have x: Continuous (fun z=>lapse z t*c^2):=by unfold lapse;fun_prop
 have p:lapse 0 t*c^2<η/4:=by simp [lapse]; positivity
 obtain ⟨z,q,r⟩:= Metric.continuousAt_iff.mp (x.continuousAt (x:=0)) (η/4) (by positivity)
 refine ⟨z/2,by positivity,?_⟩
 have hx:= r (show dist (z/2) (0:ℝ)<z from by rw [Real.dist_eq]; simp [abs_of_pos (show 0< z/2 by linarith)];linarith)
 rw [Real.dist_eq] at hx
 linarith [(abs_lt.mp hx).2,show lapse 0 t*c^2=0 by simp [lapse]]

include pk in
theorem award {b δ:ℝ}
 (d:τ→ℝ)(b':0<b)(β':b≤β)(w:0<δ)(pos:0≤B)(positive:0≤t)
 (e:0≤ε)(x:lapse ε t*c^2≤ trophy d b δ/4)(h:D^8 * (due B/k) ≤ ε)
 (a:ι→ℂ)(v:ι→τ→ℝ)(C:∑i,‖a i‖≤ c)
 (Y:δ≤ glint (fun i=>(a i).re) v d)
 (N:∀i,‖L i‖≤B)
 (O:∀j,‖R j‖=‖L j‖)
 (p:∀i j,|β*pair (v i) (v j)|≤t)
 (u:∀i j,a i≠0→a j≠0→|D^4 * inner ℝ (L i) (R j)-β*pair (v i) (v j)| ≤ ε):
 trophy d b δ ≤ D^8 *
    ∫x,(haze a k (spec L x)*conj (haze a k (spec R x))).re∂μ :=by
 let a':= fun i=>(a i).re
 let a'':= fun i=>(a i).im
 have zz:=trophy_pos d b' w
 have r:0≤lapse ε t:=by unfold lapse;positivity
 have he(f:ι→ℝ)(z:∀i,|f i| ≤ ‖a i‖):
  2*β^2*((glint f v d)^2/floorCharge d)-trophy d b δ/4 ≤D^8 *fleet f (zephyr k L R):=by
   have g:∑i,|f i| ≤ c:=(sum_le_sum (fun i _=>z i)).trans C

   have t'(i)(l:f i≠0):a i≠0:=by
       exact norm_pos_iff.mp ((abs_pos.mpr l).trans_le (z i))
   rw [←fleet_mul]
   refine le_trans (sub_le_sub le_rfl x) (delight f v d r g _ (fun i=> D^4*‖L i‖^2) (fun i j l m=>?_))
   exact accord₂ pk pos h e i j (N i) ((O j).trans_le (N j)) (O j) _ (p i j)
          (u _ _ (t' i l) (t' j m))
 rw [icicles pk, mul_add]
 have G:= he a' (fun i=>Complex.abs_re_le_norm _)
 have I:= he a'' (fun i=>Complex.abs_im_le_norm _)
 have f:0≤β:=b'.le.trans β'
 have W:=floor_pos d
 have z:trophy d b δ ≤ β^2*((glint a' v d)^2/floorCharge d):=by
   unfold trophy;gcongr
 have l:0≤ (2*β^2)*((glint a'' v d)^2/floorCharge d):=by positivity
 change _ ≤ D^8*fleet a' _ + D^8*fleet a'' _
 linarith only [z,G,I,l,zz]
