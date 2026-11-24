import Bay.D.Peak
import Bay.D.Cake
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Bay
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet Scroll Finset Palot Cadre Vow
open RG MeasureTheory Rue
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Tap Levier Thera Oath Font Spire Dial Rill
open Kennel Swell

namespace D
open Exterior Precision Nacre
open scoped ContDiff
open Regis Regis.Head Etch Gleam Next.SectorChange Next.SectorChange.Gaussian
open Pressure Work.F03 ProbabilityTheory
local notation "T4"=>SU.group
open Resonance Brecht Circuit
open CF.Onyx CF.Ember
open Stationary (Gaia)
open Maxwell

/-- Price tuple (signal, mirror, compound) -/
abbrev Group3:= Fin 3 → ℂ
def synopsis(u:Group3):ℂ:=u 2-u 0*u 1
abbrev ranked(R:ℝ)(u:Group3):ℂ:= (R:ℂ)^8 * synopsis u
lemma ranked_cont{R:ℝ}:Continuous (ranked R):=by unfold ranked synopsis;fun_prop

lemma within3(u v:Group3){M d:ℝ}
   (t:0≤M)(s:0≤d)(h:‖u 0‖≤M)(g:‖u 1‖≤M)(p:∀ i,‖v i-u i‖≤d):
   ‖synopsis v-synopsis u‖≤ d+2*(M+d)*d:= by
 have l:‖v 1‖≤M+d:= (norm_le_norm_sub_add _ _).trans ((add_le_add (p 1) g).trans_eq (add_comm ..))
 rw[synopsis,synopsis,
  show _ - _ = (v 2-u 2)-((v 0-u 0)*v 1+u 0*(v 1-u 1)) from by ring]
 refine (norm_sub_le ..).trans (add_le_add (p 2) ((norm_add_le ..).trans ?_))
 rw[norm_mul,norm_mul]
 refine (add_le_add (mul_le_mul (p 0) l (by positivity) s)
        (mul_le_mul (h.trans (le_add_of_nonneg_right s)) (p 1) (by positivity) (by positivity))).trans_eq ?_
 ring

/-- Target allowance rank. x term due to pressure and clipping.
    R up to x^2 in rates (/200000). -/
abbrev twB:=atRate (-20)

abbrev bigM(q:Clip)(f:ℝ):ℝ:= f*rivax q ^2
abbrev bigB :ℝ:= 4*loom_price
abbrev din(f z:ℝ):= f*(f*(4*(4*z)*(bigB+4*z)))
abbrev nick(q:Clip)(f x:ℝ):= 
    2*twB x + ((1+|f|)^2*roughW (rivax q))*(bWindow x)⁻¹^2
abbrev r_R := atRate 2
def crust(q:Clip)(f x:ℝ):=
 (r_R x)^8 * (nick q f x + 2*(bigM q f + nick q f x)*nick q f x)
lemma din_le(f:ℝ)(ε:ℝ)(e:0<ε):∃z:ℝ,0<z ∧ din f z≤ε:=by
  have h:Tendsto (din f) (𝓝[>] 0) (𝓝 0):=by
    have h:Continuous (din f):=by unfold din;fun_prop
    have h₀:din f 0=0:=by simp[din]
    exact (show Tendsto (din f) (𝓝[>] 0) (𝓝 (din f 0)) from h.continuousWithinAt) |>.mono_right (le_of_eq (congrArg nhds h₀)) -- output? 0 ↦din f 0 if rw?
  have hp : ∀ᶠ z in 𝓝[>] (0:ℝ),0<z:=self_mem_nhdsWithin
  exact (hp.and (h.eventually (ge_mem_nhds e))).exists
open Sleigh Cake
lemma crust_lim(q:Clip)(f ε:ℝ)(h:0<ε):
  ∀ᶠ x:ℝ in atTop, crust q f x≤ε:=by
   have u:Sugar (-20) (nick q f):=
    ((bowl (-20)).icing _).honey (((bowl_inv 20).bake 2 (by norm_num :
         -(20:ℝ)*(2:ℕ) ≤ -20)).icing _)

   have w:Sugar (-4) (crust q f):=
     ((bowl 2).bake 8 (b:=16) (by norm_num)).stew 
      (u.honey
        ((((spice _).honey (u.raise (by norm_num))).icing _).stew u (by norm_num))) (by norm_num)
   unfold Sugar at w
   exact (Paddled.lim w (by unfold thinRate;norm_num)).eventually (ge_mem_nhds h)

lemma ribbon_LE {ρ:ℝ}(u:ρ∈Set.Icc (1/2:ℝ) 2):
    0 < loom_price /4 ∧ loom_price/4 ≤ ribbon ρ ∧ ribbon ρ≤bigB:=by
 have p:=loom_price_c
 have h:1/4≤ρ^2:= (by norm_num: (1/4:ℝ)=(1/2)^2).trans_le (pow_le_pow_left₀ (by norm_num) u.1 _)
 have g:ρ^2≤4:=(pow_le_pow_left₀ (u.1.trans' (by norm_num)) u.2 _).trans_eq (by norm_num)
 unfold ribbon bigB;constructor;positivity
 constructor <;> nlinarith

abbrev acreB:ℝ:=Fintype.card Pureton
lemma mass_fee {n:Side}{s:Finset (Cella n)}{f:ℝ}{A:Icey (Cella n)}(p:Rake s f A):
 mass A ≤ acreB^2*f^2:=by
 have h(i j):‖drain A i j‖≤f:=by
    rw [←oboe]
    refine (dip_fee p _ zero_le_one ?_).trans_eq (mul_one _)
    intros; unfold reed; split_ifs <;> simp
 refine (sum_le_sum (g:= fun _=>∑_:Pureton,f^2) (fun i _=>sum_le_sum (fun j _=>pow_le_pow_left₀ (norm_nonneg _) (h i j) 2))).trans_eq ?_
 simp only[acreB,sum_const,nsmul_eq_mul,card_univ];ring
/-- Leading plane score with lattice lag R along Axis3. -/
def lscore {n:Side}(ρ:ℝ)(A:Icey (Cella n)):ℝ:=2*ribbon ρ^2*mass A
def lcap(f:ℝ):ℝ:=2*bigB^2*(acreB^2*f^2)
def lbott(δ:ℝ):ℝ:=2*(loom_price/4)^2*(δ/bytes)^2
lemma lbott_pos(δ:ℝ)(t:0 < δ):0 < lbott δ:=by
 unfold lbott; have := bytes_pos; have := loom_price_c; positivity
lemma lcosts {n:Side}{s:Finset (Cella n)}{f ρ δ:ℝ}{A:Icey (Cella n)}
 (p:Rake s f A) (h:(δ/bytes)^2 ≤ mass A)(t:ρ∈Set.Icc (1/2:ℝ) 2):
    lscore ρ A∈ Set.Icc (lbott δ) (lcap f):=by
 obtain ⟨a,b,c⟩:=ribbon_LE t

 have g:=mass_fee p
 have h₂ : 0≤ mass A:= h.trans' (sq_nonneg _)
 have u:0≤ribbon ρ:=a.le.trans b
 constructor
 · unfold lscore lbott; gcongr
 unfold lscore lcap;gcongr

lemma nick_fit(q:Clip){f:ℝ}(t:0≤f){x:ℝ}(h:0<x):
    0≤ nick q f x ∧
    2*twB x + f*(roughW (rivax q)/bWindow x^2) ≤ nick q f x ∧
    2*twB x + f*(f*(roughW (rivax q)/bWindow x^2))≤ nick q f x:=by
 let U:=roughW (rivax q) / bWindow x^2
 have u:0≤U:=by unfold U roughW;positivity
 rw [show nick q f x= 2*twB x+(1+f)^2*U from by unfold nick U; rw[abs_of_nonneg t];ring]
 have h':0 < twB x:=by unfold twB atRate; positivity
 exact ⟨by positivity,add_le_add le_rfl
  (mul_le_mul_of_nonneg_right (by nlinarith) u),
  add_le_add le_rfl ((mul_assoc f f U).symm.trans_le 
    (mul_le_mul_of_nonneg_right (by nlinarith) u))⟩
end YM.CF.Bay.D
#print axioms YM.CF.Bay.D.lcosts
