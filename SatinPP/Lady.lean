import SU5SatinVerifiedNovember6
import SatinPP.Duchess
set_option autoImplicit false
set_option maxHeartbeats 260000
set_option maxRecDepth 2800
noncomputable section
namespace YM.ConePrice
open Function Set Filter MeasureTheory Measure InnerProductSpace Spectral OS Semigroup Real
open scoped BigOperators NNReal ENNReal Topology InnerProductSpace ComplexOrder
variable {H : Hilbert} (S : OS.Semigroup H 3)
local notation "P" => S.ℚmeasure
local notation "𝔪" x:max => S.ℚmeasure.diagonal x

def velvetSector := {x:E4 | ‖SEP (3:Axis) x‖ < x 3}
lemma velvet_meas : MeasurableSet velvetSector:=
  (isOpen_lt (by fun_prop) (by fun_prop)).measurableSet

def heelChord(t:ℝ≥0)(p:E4) := (1-exp (-(p 3)*(t:ℝ)))^2
lemma heat_chord(x:H)(t:ℝ≥0):
 ‖x-S.E t x‖^2 = ∫ p, heelChord t p ∂𝔪 x :=
 by
 have ty:=pressure_amount S x 0 t
 rw [S.uZero, ContinuousLinearMap.id_apply,sub_self,norm_zero,zero_pow (by decide),
    zero_sub] at ty
 apply neg_injective
 rw [ty,←integral_neg]
 apply integral_congr_ae
 filter_upwards with p; rw [trig_rel]
 unfold heelChord; simp



def spurChord(j:Axis)(t:ℝ)(p:E4):=(t⁻¹*(2*sin (t*(p j /2))))^2
lemma spur_chord_lim(j:Axis)(p:E4):
 Tendsto (fun t=>spurChord j t p) (𝓝[>] (0:ℝ)) (𝓝 ((p j)^2)):=by
 let f(t:ℝ):ℝ:= 2*sin (t*((p j)/2))
 have h : HasDerivAt f (p j) 0:=by
   convert (((hasDerivAt_id' (0:ℝ)).mul_const ((p j)/2)).sin.const_mul 2) using 1
   all_goals try rfl
   simp ;ring
 simpa [spurChord,f,smul_eq_mul] using h.tendsto_slope_zero_right.pow 2

def SumChord(t:ℝ)(p:E4) := spurChord 0 t p +spurChord 1 t p +spurChord 2 t p
lemma chord_nonneg(t:ℝ)(p:E4): 0 ≤ SumChord t p :=by unfold SumChord spurChord;positivity
lemma sum_chord_lim(p:E4):
 Tendsto (fun t=>SumChord t p) (𝓝[>] (0:ℝ)) (𝓝 (‖SEP (3:Axis) p‖^2)):=by
 rw [sep_size,PiLp.norm_sq_eq_of_L2,Fin.sum_univ_four]
 simp only [Real.norm_eq_abs,sq_abs,add_sub_cancel_right]
 exact ((spur_chord_lim 0 p).add (spur_chord_lim 1 p)).add (spur_chord_lim 2 p)

abbrev walk(j:Axis)(p:j≠3)(t:ℝ):=(S.U (t • Picket.cross 3 j p))
lemma spur_chord(x:H)(j:Axis)(h:j≠3)(t:ℝ):
 Integrable (spurChord j t) (𝔪 x) ∧ (t⁻¹*dist x (walk S j h t x))^2 = ∫ p,spurChord j t p ∂𝔪 x:=by
 let u:= t • Picket.cross 3 j h
 let a:=can_enter S x u 0
 have g: spurChord j t = fun p=> (t⁻¹)^2*tension u 0 p:= by
    funext p
    rw [trig_rel,mul_pow]
    have hx : inner ℝ (SEP 3 p) u = t*(p j):=by
       unfold u
       rw [←cone_mean]
       exact (real_inner_smul_right p (basis j) t).trans (congrArg (t*·) (Picket.innerB j p))
    unfold spurChord
    simp only [hx,mul_div_assoc,mul_pow,NNReal.coe_zero,mul_zero,exp_zero,mul_one,one_pow,sub_self,zero_pow (by decide: 2≠0),sub_zero]
 rw [g]
 refine ⟨a.const_mul _,?_⟩
 rw [integral_const_mul,mul_pow,←pressure_amount,S.eZero]
 simp only [ContinuousLinearMap.id_apply,sub_self,norm_zero,zero_pow (by decide:2≠0),sub_zero]
 rw [dist_comm,dist_eq_norm]

/-- If (origin) net total axis spatial slope² paid at rate m², then
  at any time-width chord, *complement* of strict timelike region cannot
  account for more than (rate × width)². -/
lemma few_accounts(x:H)(h:ℝ≥0)(c:ℝ)
 (spurs:∀ᶠ t:ℝ in 𝓝[>] 0,
     dist x (walk S 0 (by decide) t x)^2+dist x (walk S 1 (by decide) t x)^2+dist x (walk S 2 (by decide) t x)^2≤(t*c)^2):
 dist x (S.E h x)^2 ≤ (h*c)^2+ ‖(P).region velvetSector x‖^2:=by
 let m := 𝔪 x
 let Q:=(h:ℝ)^2
 let D t p := Q*SumChord t p + velvetSector.indicator (fun _=> (1:ℝ)) p
 let g p := heelChord h p
 let d p := Q*‖SEP 3 p‖^2 + velvetSector.indicator (fun _=> (1:ℝ)) p
 have non:∀ t p,0≤D t p:= fun t p=> add_nonneg (mul_nonneg (sq_nonneg _) (chord_nonneg _ _)) (Set.indicator_nonneg (fun _ _=>zero_le_one) _)
 have cap(p:E4)(u:0≤p 3): g p ≤ 1 ∧ g p ≤ d p:= by
    have v:=exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg u h.coe_nonneg))
    have v':exp (-(p 3)*(h:ℝ))≤1:=by rwa [neg_mul]
    have Y : g p ≤ 1:=by unfold g heelChord; nlinarith only [v',Real.exp_nonneg (-(p 3)*(h:ℝ))]
    refine ⟨Y,?_⟩
    unfold d
    by_cases y:p∈velvetSector
    · rw [Set.indicator_of_mem y];exact Y.trans (le_add_of_nonneg_left (by unfold Q;positivity))
    rw [Set.indicator_of_notMem y,add_zero]
    change _ ≤ (↑h:ℝ)^2 * _
    rw [←mul_pow]
    refine (sq_le_sq₀ (sub_nonneg.mpr v') (by positivity)).mpr ?_
    have y':p 3 ≤ ‖SEP 3 p‖:= le_of_not_gt y
    linarith only [Real.add_one_le_exp (-(p 3)*(h:ℝ)), mul_le_mul_of_nonneg_left y' h.coe_nonneg]
 let L t p := min (D t p) (g p)
 have R : Tendsto (fun t => ∫ p,L t p ∂m) (𝓝[>] 0) (𝓝 (∫ p,g p ∂m)):=by
    refine tendsto_integral_filter_of_dominated_convergence (fun _=>1) ?_ ?_ (integrable_const _) ?_
    · refine Eventually.of_forall fun t=> Measurable.aestronglyMeasurable ?_
      unfold L D g SumChord heelChord spurChord
      refine Measurable.min (Measurable.add (by fun_prop) (Measurable.indicator measurable_const velvet_meas)) (by fun_prop)
    · exact Eventually.of_forall fun t=> (S.bright x).mono fun p hp=> by
        rw [Real.norm_eq_abs,abs_of_nonneg (le_min (non t p) (sq_nonneg _) : 0≤ L t p)]
        exact le_trans (min_le_right _ _) (cap p hp).1
    exact (S.bright x).mono fun p hp=> by
        have t: Tendsto (fun s=>D s p) (𝓝[>] 0) (𝓝 (d p)) :=
          ((sum_chord_lim p).const_mul _).add tendsto_const_nhds
        exact (min_eq_right (cap p hp).2:(min (d p) (g p))=(g p)) ▸ t.min tendsto_const_nhds
 rw [dist_eq_norm,heat_chord]
 refine le_of_tendsto R ?_
 filter_upwards [spurs,self_mem_nhdsWithin] with t hp h'
 have a:=spur_chord S x 0 (by decide) t
 have b:=spur_chord S x 1 (by decide) t
 have e:=spur_chord S x 2 (by decide) t
 have v := (a.1.add b.1).add e.1
 have u: Integrable (velvetSector.indicator (fun _=>1:E4→ℝ)) m:= (integrable_const _).indicator velvet_meas
 refine le_trans ?_ (show (∫ p:E4,D t p ∂m)≤_ from ?_)

 · exact integral_mono_of_nonneg (Eventually.of_forall fun p=> le_min (non t p) (sq_nonneg _) :0 ≤ᵐ[m] L t) ((v.const_mul Q).add u) (Eventually.of_forall fun p=>min_le_left _ _)
 have i: Integrable (SumChord t) m := v
 unfold D
 rw [integral_add (i.const_mul Q) u, integral_const_mul,integral_indicator_const _ velvet_meas,smul_eq_mul,mul_one]
 have g:m.real velvetSector = ‖(P).region velvetSector x‖^2:=by
   unfold Measure.real m
   rw [← restrict_apply_univ,← restrictP S velvet_meas]
   exact all_norm S _
 rw [g,mul_pow]
 unfold SumChord m
 rw [integral_add (show Integrable (fun p=> spurChord 0 t p+spurChord 1 t p) _ from a.1.add b.1) e.1, integral_add a.1 b.1,←a.2,←b.2,←e.2]
 refine add_le_add (mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)) le_rfl
 have h':0<t:=h'
 field_simp
 nlinarith only [hp]

open YM.Multiplier

open Boundary Probe

abbrev guards := (P).region velvetSector
lemma guard_comm(y:Cross 3):Commute (S.U y) (guards S) :=(Roy.costU S y).comm velvet_meas
lemma guard_hit(y:Cross 3):
 Registers (P) (velvetSector.indicator (fun p=>plane p y.val)) (guards S * S.U y):= (Roy.costU S y).mask velvet_meas (guard_comm S y)

variable (y:Cross 3)
local notation "A"=>guards S * S.U y
def first(p:E4) := velvetSector.indicator (fun p=>plane p y.val) p
def coeff₀(z:ℂ):=(1+z^2)/4
def plusCoeff(z:ℂ):=(1-Complex.I*z)/16
def minusCoeff(z:ℂ):=(1+Complex.I*z)/16
def shadePrice(z:ℂ):E4→ℂ:= coeff₀ z • (velvetSector.indicator 1)+plusCoeff z • first y + minusCoeff z • star (first y)
def shade(z:ℂ):H.Op:=
    coeff₀ z • guards S + plusCoeff z • A + minusCoeff z • star A
lemma shade_pay(z:ℂ): Registers (P) (shadePrice y z) (shade S y z):=
 ((((Registers.box (P) velvet_meas).scale (coeff₀ z)).add ((guard_hit S y).scale (plusCoeff z))).add ((guard_hit S y).adjoint.scale _))

lemma shade_i:shade S y Complex.I= ((1:ℂ)/8) • A := by
 unfold shade
 
 norm_num [coeff₀,plusCoeff,minusCoeff,Complex.I_sq]

lemma shade_ana(z:ℂ):AnalyticAt ℂ (shade S y) z :=
    by unfold shade coeff₀ plusCoeff minusCoeff; fun_prop
lemma shade_good{s:ℝ}(h:|s|<1) (p:E4) :
 (0 ≤ shadePrice y s p ∧ shadePrice y s p ≤ 1) ∧
 (p ∉ velvetSector → shadePrice y s p =0):= by
 unfold shadePrice
 simp only [Pi.add_apply,Pi.smul_apply,Pi.star_apply, smul_eq_mul,Complex.star_def]
 by_cases e:p∈velvetSector
 · rw [Set.indicator_of_mem e,Pi.one_apply,mul_one]
   let u:=plusCoeff s * first y p
   have b:‖u‖≤1/8:=by
      unfold u plusCoeff first
      rw [norm_mul, norm_div,Set.indicator_of_mem e,plane_norm,mul_one]
      apply le_trans (div_le_div_of_nonneg_right (norm_sub_le ..) (norm_nonneg _))
      rw [norm_mul,Complex.norm_I,norm_one,Complex.norm_real,Real.norm_eq_abs]
      norm_num [Complex.norm_ofNat]
      linarith only [h]
   let t:=(1+s^2)/4
   have hc:minusCoeff s= starRingEnd ℂ (plusCoeff s):=by
      unfold minusCoeff plusCoeff;simp [map_ofNat]
   have g: u+starRingEnd ℂ u=(↑(2 * u.re):ℂ):=by apply Complex.ext<;>simp<;>ring
   rw [add_assoc,hc,←map_mul,g,show coeff₀ s= (t:ℝ) by unfold coeff₀ t;push_cast;rfl,←Complex.ofReal_add]
   have r:=abs_le.mp ((Complex.abs_re_le_norm _).trans b)
   unfold t
   refine ⟨⟨?_,?_⟩,fun h=>False.elim (h e)⟩

   · norm_cast;nlinarith only [r.1]
   have h':s^2 ≤1:=(by nlinarith [abs_lt.mp h])
   norm_cast;linarith only [h',r.2]
 simp [first,e]

#print axioms few_accounts
#print axioms shade_good