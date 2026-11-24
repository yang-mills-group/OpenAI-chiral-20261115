import Organdy.Torrent
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

open scoped ComplexConjugate
local notation "μ" => stdGaussian E
variable {k c B ε D β t:ℝ}{L R:ι→E}(pk:0<k)

/-- uniform lower difference estimate comparing same source nearer vs
     farther (marginal self-price canceled-before-error). -/
structure Cameo (η σ χ D Y:ℝ):Prop where
 enhanced:2*η ≤ χ
 literal: |D^8*(Y-σ) - χ|≤η/2

lemma reducegap{η σ χ D D₂ y z:ℝ}(v:Cameo η σ χ D y)
 (w:Cameo η σ χ D₂ z)
 (h:0<η)(e:0<D)(p:2*D≤D₂):
   η ≤ D^8*(y-z):=by
 have g:=((pow_le_pow_left₀ (by positivity) p 8))
 rw [mul_pow] at g;norm_num at g
 have t: 8*D^8 ≤ D₂^8:=by linarith only [g,pow_pos e 8]
 have q: D^8*(z-σ) ≤ (χ+η/2)/8:=by
    by_cases a:z-σ<0
    · exact (mul_nonpos_of_nonneg_of_nonpos (by positivity) a.le).trans (by linarith [w.enhanced])
    have v:= (abs_le.mp w.literal).2
    linarith only [mul_le_mul_of_nonneg_right t (le_of_not_gt a),v]
 have a:=(abs_le.mp v.literal).1
 have u:=v.enhanced
 linarith only [a,u,q,h]

abbrev rios (a:ι→ℂ) (p:(ι→ℝ)→ℝ):=
  p (fun i=>(a i).re)+p (fun i=>(a i).im)

def unlit (f:ι→ℝ)(L:ι→E):ℝ:= fleet f (fun i j=>‖L i‖^2 * ‖L j‖^2)
def ablaze (f:ι→ℝ)(v:ι→τ→ℝ)(t:ℝ):ℝ:= 2*t^2 * adore f v
abbrev unlitK (a:ι→ℂ)(L:ι→E):=rios a fun f=>unlit f L
abbrev ablazeK (a:ι→ℂ)(v:ι→τ→ℝ)(t:ℝ):=rios a fun f=>ablaze f v t

lemma gemming (f:ι→ℝ)(L:ι→E)(v:ι→τ→ℝ):
 D^8*(unlit f L) + ablaze f v β =
     fleet f (fun i j=> D^4*‖L i‖^2*(D^4*‖L j‖^2)+2*β^2*(pair (v i) (v j))^2):=by
 unfold unlit ablaze adore
 rw [←fleet_mul,←fleet_mul, fleet_add]
 congr 2
 funext i j;ring

include pk in
theorem cameo_fee {b δ:ℝ}
 (d:τ→ℝ)(b':0<b)(β':b≤β)(w:0<δ)(pos:0≤B)(positive:0≤t)
 (e:0≤ε)(x:lapse ε t*c^2≤ trophy d b δ/4)(h:D^8 * (due B/k) ≤ ε)
 (a:ι→ℂ)(v:ι→τ→ℝ)(C:∑i,‖a i‖≤ c)
 (Y:δ≤ glint (fun i=>(a i).re) v d)
 (N:∀i,‖L i‖≤B)
 (O:∀j,‖R j‖=‖L j‖)
 (p:∀i j,|β*pair (v i) (v j)|≤t)
 (u:∀i j,a i≠0→a j≠0→|D^4 * inner ℝ (L i) (R j)-β*pair (v i) (v j)| ≤ ε):
 Cameo (trophy d b δ) (unlitK a L) (ablazeK a v β) D
    (∫x,(haze a k (spec L x)*conj (haze a k (spec R x))).re∂μ):=by
 let a':= fun i=>(a i).re
 let a'':= fun i=>(a i).im
 have zz:=trophy_pos d b' w
 have r:0≤lapse ε t:=by unfold lapse;positivity
 have he(f:ι→ℝ)(z:∀i,|f i| ≤ ‖a i‖):
  |D^8 * fleet f (zephyr k L R)-(D^8*unlit f L+ablaze f v β)| ≤ trophy d b δ/4:=by
   have g:∑i,|f i| ≤ c:=(sum_le_sum (fun i _=>z i)).trans C

   have t'(i)(l:f i≠0):a i≠0:=by
       exact norm_pos_iff.mp ((abs_pos.mpr l).trans_le (z i))
   rw [←fleet_mul,gemming]
   refine le_trans (skew r g _ _ (fun i j l m=>?_)) x 
   exact accord₂ pk pos h e i j (N i) ((O j).trans_le (N j)) (O j) _ (p i j)
          (u _ _ (t' i l) (t' j m))
 have G:= he a' (fun i=>Complex.abs_re_le_norm _)
 have I:= he a'' (fun i=>Complex.abs_im_le_norm _)
 have f:0≤β:=b'.le.trans β'
 have W:=floor_pos d
 have z:trophy d b δ ≤ β^2*((glint a' v d)^2/floorCharge d):=by
   unfold trophy;gcongr
 have j:=uphold a'' v
 constructor
 · have p:=affluent a' v d
   change _ ≤ 2*β^2*adore a' v + 2*β^2*adore a'' v
   have zz:=mul_le_mul_of_nonneg_left p (sq_nonneg β)
   linarith only [z,zz,mul_nonneg (sq_nonneg β) j]
 rw [icicles pk]
 change |D^8*(fleet a' (zephyr k L R)+fleet a'' (zephyr k L R)-(unlit a' L+unlit a'' L)) - (ablaze a' v β+ablaze a'' v β)|≤ _
 obtain ⟨i,j⟩:=abs_le.mp G; obtain ⟨p1,p2⟩:=abs_le.mp I
 exact abs_le.mpr ⟨by linarith only [i,p1], by linarith only [j,p2]⟩
