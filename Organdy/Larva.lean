
import YM.PCalc.Chart
import YM.CF.Tulip.Lens
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.CF.Organdy
open Filter Topology Metric Lattice Exterior Precision SU Tulip

namespace Larva
variable {N:Side}
open scoped Matrix.Norms.L2Operator Kronecker Matrix
attribute [local instance] opCStarAlgebra
local notation "G" => SU.group
def laurel (X:Op F): Twig :=
  ((1:Op (Fin 3)) ⊗ₖ Join.both (ExTwo.wedgeOp (NormedSpace.exp X)) ((NormedSpace.exp (-X)).transpose),
    NormedSpace.exp X)

private lemma dpi {i:Type}[Fintype i][DecidableEq i]{p:Op F→Op i}:
 Differentiable ℂ p ↔ ∀ a b, Differentiable ℂ fun x=>p x a b:=by
 let get (a b:i) : Op i →ₗ[ℂ] ℂ := ⟨⟨fun X=>X a b,fun _ _=>rfl⟩,fun _ _=>rfl⟩
 let send : (i→i→ℂ)→ₗ[ℂ] Op i:= ⟨⟨Matrix.of,fun _ _=>rfl⟩,fun _ _=>rfl⟩
 constructor
 · exact fun h a b=> (get a b).toContinuousLinearMap.differentiable.comp h
 intro h
 have H:Differentiable ℂ (fun x a b=>p x a b):=differentiable_pi.mpr fun a=> differentiable_pi.mpr fun b=>h a b
 exact send.toContinuousLinearMap.differentiable.comp H

lemma flex:Differentiable ℂ laurel:=by
 have h:Differentiable ℂ (NormedSpace.exp:Op F→Op F):=fun x=>(NormedSpace.exp_analytic _).differentiableAt
 unfold laurel
 apply Differentiable.prodMk _ h
 rw [dpi]; rintro ⟨a,i⟩ ⟨b,j⟩
 simp only [Matrix.kronecker_apply]
 apply Differentiable.const_mul
 cases i <;> cases j
 · simp only [Join.both,Matrix.fromBlocks_apply₁₁,ExTwo.wedge_entry]
   exact ((dpi.mp h _ _).mul (dpi.mp h _ _)).sub ((dpi.mp h _ _).mul (dpi.mp h _ _))
 · exact differentiable_const 0
 · exact differentiable_const 0
 · exact dpi.mp (h.comp differentiable_id.neg) _ _

def engrave:(G).Color →L[ℝ] Op F:=(G).colorMat.toContinuousLinearMap
def tendril (x y:(G).Color) (z:ℂ):Twig:= laurel (engrave x+z•engrave y)

lemma exp_neg (x:(G).Color) : (G).lieExp (-x)=((G).lieExp x)⁻¹:= by
  apply (G).mat_injective; rw [(G).mat_lieExp,(G).mat_inv,(G).mat_lieExp,NormedSpace.star_exp,(G).colorMat_skew,map_neg]
lemma twistNeg (x:(G).Color): NormedSpace.exp (-engrave x)=star ((G).mat ((G).lieExp x)):=by
 have k:=congrArg (G).mat (exp_neg x)
 rw [(G).mat_lieExp,map_neg,(G).mat_inv] at k;exact k
lemma unfoldB (x:(G).Color): laurel (engrave x)=brand ((G).lieExp x):=by
 unfold laurel brand
 rw [twistNeg,show NormedSpace.exp (engrave x)=(G).mat ((G).lieExp x) from ((G).mat_lieExp _).symm];rfl
lemma thread (x y:(G).Color)(t:ℝ):tendril x y t= brand ((G).lieExp (x+t•y)):=by
 rw [←unfoldB,map_add,map_smul]; unfold tendril;rw [Complex.coe_smul]

abbrev Dir (N:Side) := fieldDir (G) N 1
def vane (x:Dir N)(e:Edge (Site N))(b:Bool):(G).Color :=
 if b then collect (G) x e else -(collect (G) x e)
def spun (x y:Dir N)(z:ℂ) : Stem N:= fun e b=>tendril (vane x e b) (vane y e b) z
lemma knit (x y:Dir N): Differentiable ℂ (spun x y):=by
 apply differentiable_pi.mpr;intro e;apply differentiable_pi.mpr;intro b
 exact flex.comp ((differentiable_const _).add ((show Differentiable ℂ (id:ℂ→ℂ) from differentiable_id).smul (show Differentiable ℂ (fun _:ℂ=>engrave (vane y e b)) from differentiable_const _)))

lemma play (x y:Dir N)(t:ℝ):
 spun x y t=profile (represent (x+t•y)):=by
 funext e b
 have f:represent (x+t•y) e = (G).lieExp (collect (G) x e + t• collect (G) y e):=by
   simp [represent,collect,RG.increment]
 rw [spun,thread]; unfold profile; rw [f]
 cases b
 · simp only [vane,Bool.false_eq_true, ↓reduceIte, smul_neg,←neg_add,exp_neg,brand_inv]
 · rfl

lemma realCont: Continuous (fun x:Dir N=>profile (represent x)):=by
 rw [show (fun x:Dir N=>profile (represent x))=fun x=>spun x 0 0 from funext fun x=>(by simpa using (play x 0 0).symm)]
 apply continuous_pi;intro e;apply continuous_pi;intro b
 unfold spun tendril
 apply flex.continuous.comp
 apply Continuous.add _ continuous_const
 apply engrave.continuous.comp
 cases b <;> simp only [vane,Bool.false_eq_true, ↓reduceIte,collect] <;> fun_prop

def Spool (d r:ℝ):Prop:= 0<r ∧ ∀ {N}(x y:Dir N)(z:ℂ), ‖x‖ < 2*r→‖z‖ * ‖y‖ < 4*r → spun x y z∈Openc N d

lemma vaneN(x:Dir N)(e b):‖vane x e b‖ ≤ ‖x‖:=by
 cases b
 · change ‖- (collect (G) x e)‖ ≤ _
   rw [norm_neg]
   exact norm_le_pi_norm x (e.1,coord e.2) 
 · exact norm_le_pi_norm x (e.1,coord e.2) -- expected

lemma reel {d:ℝ}(v:0<d): ∃r,Spool d r:=by
 have h:laurel 0=1:=by simpa [brand_one] using unfoldB 0
 obtain ⟨R,k,f⟩:=Metric.continuousAt_iff.mp (flex.continuous.continuousAt (x:=0)) d v
 let K:=‖engrave‖+1
 have hk:0<K:=by unfold K;positivity
 let r:=R/(6*K)
 have t:0<r:=by positivity
 refine ⟨r,t,?_⟩
 intro N x y z a b
 refine ⟨1,guard0 v.le,?_⟩
 rw [profile_trivial]
 refine (pi_norm_lt_iff v).mpr fun e=> (pi_norm_lt_iff v).mpr fun g=> ?_
 apply show ∀{X}, dist X 0<R→‖laurel X-1‖<d from fun {X} xx=>by rw [← h,←dist_eq_norm_sub];exact f xx
 rw [dist_zero_right]
 have hp(w:Dir N):‖engrave (vane w e g)‖ ≤ K*‖w‖:=
   (engrave.le_opNorm _).trans (mul_le_mul (le_add_of_nonneg_right zero_le_one)
       (vaneN ..) (norm_nonneg _) hk.le)
 apply (norm_add_le ..).trans_lt;rw [norm_smul]
 apply (add_le_add (hp x) (mul_le_mul_of_nonneg_left (hp y) (norm_nonneg z))).trans_lt
 rw [mul_left_comm ‖z‖]
 apply (add_lt_add (mul_lt_mul_of_pos_left a hk) (mul_lt_mul_of_pos_left b hk)).trans_eq
 unfold r; field_simp;ring
