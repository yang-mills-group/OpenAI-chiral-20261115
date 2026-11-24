import Bay.D.Coast
import YM.SU5.Thin.Avalanche.Shelter
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

/-- purifying four-coordinate receipts. -/
lemma fringed (x y x' y' B d:ℝ) (hx : |x-x'|≤d)(hy:|y-y'|≤d)
   (u:|x|≤B)(v:|y'|≤B):
   |x*y-x'*y'|≤2*B*d:=by
 have z: 0≤d:=(abs_nonneg _).trans hx
 rw [show x*y-x'*y'= x*(y-y')+(x-x')*y' from by ring]
 apply (abs_add_le ..).trans
 rw[abs_mul, abs_mul]
 exact (add_le_add (mul_le_mul u hy (abs_nonneg _) ((abs_nonneg _).trans u)) (mul_le_mul hx v (abs_nonneg _) z)).trans_eq (by ring)
variable {E:Type*}[NormedAddCommGroup E][InnerProductSpace ℝ E][MeasurableSpace E][BorelSpace E][FiniteDimensional ℝ E]
local notation "V"=>stdGaussian E
local notation "ℭ"=>Valued (stdGaussian E)
variable {K B:ℝ}
/-- Raw versus clipped. -/
structure Furl (K B:ℝ) (x y:E→ℝ):Prop where
 raw:ℭ x
 refined:ℭ y
 short(a:E):|y a|≤|x a|
 tend(a:E):|x a - y a| ≤|x a|^3/K^2
 high: (∫ a,x a^8 ∂V)≤ B
lemma one_furl(h:1≤B):Furl K B (E:=E) 1 1:=by
 refine ⟨Valued.cash _,Valued.cash _,fun _=> le_refl _, ?_,?_⟩
 · intro a;rw[sub_self,abs_zero]; positivity
 simpa

variable (a:E)
local notation "Y" => 105*B^8
lemma purrFurl (p:‖a‖≤B) (f:0<K):Furl K (1+Y) (spanX a) (pur K ∘ spanX a):=by
 refine ⟨fromV a,⟨fun _=>MemLp.of_bound ?_ K (ae_of_all _ fun z=>pur_max _ f)⟩,
       fun _=>pur_clip ..,fun z=> (abs_sub_comm ..).trans_le (pur_bent _), ?_⟩
 · have hE := (pur_smooth K).continuous
   unfold spanX; fun_prop
 rw [spanX,houston]
 refine le_trans ?_ (le_add_of_nonneg_left (show (0:ℝ)≤1 by norm_num))
 gcongr
variable {l m:Fin 4→E→ℝ}
private lemma curls (_x:ℕ)(y:ℝ): |y|^6≤1+y^8:=by
 rw [← (show Even (8:ℕ) by decide).pow_abs y]
 rcases le_total |y| 1 with h|h
 · exact (pow_le_one₀ (abs_nonneg _) h).trans (le_add_of_nonneg_right (by positivity))
 exact (pow_le_pow_right₀ h (show 6≤8 by decide)).trans (le_add_of_nonneg_left (by norm_num))
lemma fringeworth (x y:Fin 4→ℝ)(h:∀i,|x i-y i|≤|x i|^3/K^2)
       (p:∀ i,|y i|≤|x i|):
    |x 0*x 1*(x 2*x 3) - y 0*y 1*(y 2*y 3)| ≤
      4*(1+∑i,x i^8)/K^2:=by
 obtain ⟨a,_,z⟩:=exists_max_image Finset.univ (fun i=>|x i|) univ_nonempty

 let u:=|x a|
 have v:0≤u:= abs_nonneg _
 have t(i): |x i| ≤u:=z _ (mem_univ _)
 have d(i): |y i| ≤u:= (p i).trans (t i)
 have e(i): |x i-y i|≤u^3/K^2:= (h i).trans (by gcongr; exact t _)
 have ef: |x 0*x 1|≤u^2:=by rw[abs_mul,sq];gcongr <;> exact t _
 have eh: |y 2*y 3|≤u^2:=by rw[abs_mul,sq]; gcongr <;> exact d _
 have g:u^6≤ 1+∑i,x i^8:=(curls 1 _).trans (add_le_add le_rfl (single_le_sum (f:=fun i=>x i^8) (fun _ _=>by positivity) (mem_univ a)))
 refine (fringed _ _ _ _ _ _ (fringed _ _ _ _ _ _ (e 0) (e 1) (t 0) (d 1))
    (fringed _ _ _ _ _ _ (e 2) (e 3) (t 2) (d 3)) ef eh).trans ?_
 refine le_trans ?_ (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left g (show (0:ℝ)≤4 by norm_num)) (sq_nonneg _))
 apply le_of_eq;ring

abbrev roughW(B:ℝ):= 4*(1+4*(1+105*B^8))
lemma furl_price(h:∀i,Furl K B (l i) (m i)):
 |(∫ a,l 0 a*l 1 a*(l 2 a*l 3 a)∂V) -
   ∫ a,m 0 a*m 1 a*(m 2 a*m 3 a)∂V| ≤ 4*(1+4*B)/K^2:=by

 have c:(∀i,Integrable (fun a=>l i a^8) V) := fun i=>((h i).raw.upward _).accepted
 let t(a:E):=∑i,l i a^8
 have hc:Integrable t V:=integrable_finsetSum _ (fun i _=>c i)
 have he:(∫a,t a∂V)≤4*B:=by
   unfold t; rw[integral_finsetSum _ (fun i _=>c i)]
   exact (sum_le_sum (s:=univ) fun i _=>(h i).high).trans_eq (by simp)
 have f(a:E):=fringeworth (l · a) (m · a) (fun i=>(h i).tend a) (fun i=>(h i).short a)
 erw [←integral_sub (((h 0).raw.times (h 1).raw).times ((h 2).raw.times (h 3).raw)).accepted
                (((h 0).refined.times (h 1).refined).times ((h 2).refined.times (h 3).refined)).accepted,
    ←Real.norm_eq_abs]
 apply (norm_integral_le_of_norm_le (((Integrable.fun_add (integrable_const (1:ℝ)) hc).const_mul 4).div_const (K^2))
          (ae_of_all _ f)).trans
 rw[integral_div,integral_const_mul,integral_add (integrable_const _) hc,integral_const,probReal_univ,one_smul]
 gcongr

lemma loft (a b c d:E): (∫ x,spanX a x *spanX b x*(spanX c x*spanX d x)∂V)=
 (inner ℝ a b * inner ℝ c d + inner ℝ a c * inner ℝ b d + inner ℝ a d * inner ℝ b c) :=by
 have h(x):spanX a x*spanX b x*(spanX c x*spanX d x)=payday [a,b,c,d] x:=by
    simp[payday,mul_assoc]
 simp_rw [h];change memo _=_
 simp only [gramStein,roster,List.nil_append,List.cons_append]
 simp [memo,payday,add_assoc]
local notation "⎡" y "⎤"=> (Complex.ofReal y)
abbrev ivoryL(a b:E) := ⎡inner ℝ a b⎤
def dum(K:ℝ)(a b:E)(x:E):ℝ:= pur K (spanX a x) * pur K (spanX b x)
lemma toot (p:0<K)(s:‖a‖≤B){b:E}(q:‖b‖≤B):
 ‖(∫ x,⎡dum K a b x⎤∂V) - ivoryL a b‖≤roughW B/K^2:=by
 rw [integral_complex_ofReal,ivoryL,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_sub_comm]
 rw [←appraisal]
 let f(x:E):=pur K ∘ spanX x
 have h:=furl_price (l:= ![spanX a,spanX b,1,1]) (m:=![f a,f b,1,1])
    (fun i : Fin 4=>(show Furl K (1+105*B^8) _ _ from by 
       have g:1≤1+105*B^8:=le_add_of_nonneg_right (by positivity)
       fin_cases i
       exacts [purrFurl _ s p,purrFurl _ q p,one_furl g,one_furl g]))

 simp at h
 exact h
lemma toots (b c d:E)(p:0<K)(s:‖a‖≤B)(t:‖b‖≤B)(r:‖c‖≤B)(q:‖d‖≤B):
 ‖(∫ x,⎡dum K a b x⎤ * ⎡dum K c d x⎤∂V) -
    (ivoryL a b*ivoryL c d+(ivoryL a c*ivoryL b d+ivoryL a d*ivoryL b c))‖≤ roughW B/K^2:=by
 simp_rw [ivoryL,←Complex.ofReal_mul, ←Complex.ofReal_add,integral_complex_ofReal,
    ←Complex.ofReal_sub,Complex.norm_real, Real.norm_eq_abs,←add_assoc,←loft]
 rw[abs_sub_comm]
 let f(x:E):=pur K ∘ spanX x
 exact furl_price (l:=![spanX a,spanX b,spanX c,spanX d]) (m:=![f a,f b,f c,f d])
    (fun i : Fin 4=>(show Furl K (1+105*B^8) _ _ from by 
       fin_cases i; exacts [purrFurl _ s p,purrFurl _ t p,purrFurl _ r p,purrFurl _ q p]))


lemma dum_go (b:E)(p:0<K): ℭ (dum K a b):=
 (purrFurl a le_rfl p).refined.times (purrFurl b le_rfl p).refined
end YM.CF.Bay.D
#print axioms YM.CF.Bay.D.toots
