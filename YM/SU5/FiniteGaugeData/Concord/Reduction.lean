import YM.SU5.FiniteGaugeData.Concord.Slips
/-!
# Bill for sharp readings and persistent signal: compiled reduction on the real prescription

E.g. can submit Land&Ready (eventual), the numeric native-price inputs at **these** two paid
marks. Target numbers borrowed from scaffold BillInput, but here a DIFFERENT reduction is proved
(no requirement of these periods participating in a matching Printed), on Y. `Deposit`
is an outstanding estimate, stronger than the mere claim of strict nonzero (not a redefinition
assuming the conclusion). It is enough to obtain even along a path (we give via frequents on the
whole cone in case the buyers can't pay all). It is sufficient FOR THIS nonzero Wilson-contracted
gauge-matter (3-left construction) read and centered reflected form in the Borel multisystem;
not asserting it is NECESSARY or that it by itself proves reconstruction, retains a nonzero
observable in a VACUUM component, or proves dynamics of gauge curvature/chirality or nonfreeness
in the reconstructed theory. At level0 even showcase on the full halo. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 400000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Concord
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker
  Topology ComplexOrder Classical TensorProduct ComplexConjugate
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent
  Next.Free Bloch Drapes Spire Lifted Skye Precision Tree Push.SectorMeasure Next.SectorChange Fock Heat
open Afterglow Afterglow.Common Afterglow.Sound Afterglow.Satin
attribute [local instance] opCStarAlgebra
open Py Py.Rate LocalLimit Preparation Journey Vale
namespace Banner
open Bilinear
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1 ≤ Λ.x)
variable {F:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}{P:Playhouse Λ l}
variable {i k:ℕ→ℕ}(W:Traced Y H i k F E P)
variable (s n d:ℕ)
local notation "K"=> tent Y H
local notation "ζ'"=> (tent Y H).ζ
local notation "z'"=> (tent Y H).plane0
local notation "θ'" => turn (tent Y H) 3 (tent Y H).plane0
local notation "w'"=>bulb (tent Y H)
local notation "qQ"=>centered_echo (tent Y H) 0 0
local notation "Ω"=> ConeFilter Y i k
local notation "U"=> wing (tent Y H) 3 (tent Y H).plane0 (tent Y H).ℓ
local notation "D"=> intake Y H s W.own
include W
def estate :ℂ:= intake Y H s W.own (bulb (tent Y H))
lemma estate_pays : estate Y H W s=E s (word (tent Y H)):= intake_eq ..
local notation "Xe"=> estate Y H W s
lemma center_pay : intake Y H s W.own (center (tent Y H) (estate Y H W s))=0:=by
 rw [center,map_sub,map_smul,intake_one]; change Xe-Xe*(1:ℂ)=0; rw [mul_one,sub_self]

private def smallP : U →ₗ⋆[ℂ] (U →ₗ[ℂ]ℂ) where
  toFun f:= { toFun g:= intake Y H s W.own ((θ') f.val * g.val)
              map_add' := fun x y=> by change D (_*(x.val+y.val))=_; rw [mul_add,map_add]
              map_smul' := fun a x=> by change D (_*(a • x.val))=_; rw [Algebra.mul_smul_comm,map_smul]; rfl }
  map_add' x y:= by apply LinearMap.ext; intro t; change D ((θ') (x.val+y.val)*t.val)=D ((θ') x.val*t.val)+D ((θ') y.val*t.val); rw [map_add (θ'),add_mul,map_add] -- notation D applied might fail parser
  map_smul' a x:= by apply LinearMap.ext; intro t; change D ((θ') (a • x.val)*t.val)=star a • D ((θ') x.val*t.val); rw [map_smulₛₗ (f:=θ'), Algebra.smul_mul_assoc,map_smul]; rfl
local notation "Q'"=> smallP Y H W s
private lemma smallPos (x:U) : 0 ≤ (Q') x x:= diagonals Y H s (3:Axis) ζ' W.own x.val x.property -- tune args order
private lemma beam_one : intake Y H s W.own ((θ') w')=star (estate Y H W s):=by
 let u:U:=1; let b:U:=⟨w',bulb_place K⟩; have he:= Consent.herm (Q') (smallPos Y H W s) u b; change star (D ((θ') 1* w')) = D ((θ') w'*1) at he; rw [turn_one,one_mul,mul_one] at he; exact he.symm

lemma framing :
    intake Y H s W.own (centered_echo K (estate Y H W s) (estate Y H W s)) = intake Y H s W.own (centered_echo K 0 0) - ((‖Xe‖^2:ℝ):ℂ):=by
 unfold centered_echo; rw [center_zero]; rw [center, map_sub (θ'), map_smulₛₗ (f:=θ'), starRingEnd_apply, turn_one]
 rw [_root_.sub_mul, mul_sub ((θ') _), map_sub,map_sub,Algebra.smul_mul_assoc,map_smul,Algebra.mul_smul_comm,map_smul,mul_one,beam_one Y H W s]
 have he:= center_pay Y H W s; unfold center at he; rw [one_mul,he]; simp only [mul_zero,sub_zero,smul_eq_mul]; rw [←Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self, mul_comm Xe]<;> rfl -- smul xz

-- include payoff criterion at every contributing level
omit W
def Deposit (e:ℝ) (i k:ℕ→ℕ):Prop:=
  ∃ᶠ v in ConeFilter Y i k, Land Y H (momentm Y (i v.1) s) ∧ Ready Y H (zone K) s (i v.1) (k v.2) ∧
    ‖sample Y H s (i v.1) (k v.2) (bulb K)- P20‖ ≤ e ∧
    ‖sample Y H s (i v.1) (k v.2) (centered_echo K 0 0)-(compared:ℂ)‖ ≤ e

lemma often_dest {IP:Type*}{F:Filter IP}{f:IP→ ℝ}{x c:ℝ} (h:Tendsto f F (𝓝 x))(p: ∃ᶠ i in F,f i ≤ c): x ≤ c:= by by_contra! t; exact p ((h.eventually (lt_mem_nhds t)).mono (fun j v=>not_le.mpr v))

include W
local notation "Pr"=> portfolio Y H W
local notation "d₀"=> Pr (cameo Y H s w')
theorem scented (e:ℝ)(h:Tol e)(p:Deposit Y H s e i k) : E s (word K)≠0 ∧
    0 < portfolio Y H W (cameo Y H s (centered_echo K (estate Y H W s) (estate Y H W s))) := by
 have he:= cone_sample Y H W s w'; have hv:= cone_sample Y H W s qQ
 rw [←intake_eq Y H s W.own w'] at he; rw [←intake_eq Y H s W.own qQ] at hv
 have ht: ‖estate Y H W s-P20‖≤e:= often_dest ((he.sub_const P20).norm) (p.mono (fun _ v=> v.2.2.1))
 let z:= D qQ
 have hg: ‖z-(compared:ℂ)‖≤ e:= often_dest ((hv.sub_const (compared:ℂ)).norm) (p.mono (fun _ v=> v.2.2.2))
 have hb: ‖Xe‖≤‖P20‖+e:=by have hh:= (norm_sub_norm_le Xe P20).trans ht; linarith
 rw [←estate_pays Y H W,placing Y H W,←intake_eq Y H s W.own]
 have hA: 0 ≤ D (centered_echo K Xe Xe):= smallPos Y H W s ⟨center K Xe,center_admit K Xe⟩
 constructor
 · intro h₀; rw [h₀,zero_sub,norm_neg] at ht; linarith only [ht,h.small,normP20]
 apply Complex.lt_def.mpr; refine ⟨?_,(Complex.le_def.mp hA).2⟩
 have ha : compared-e ≤ z.re:= by have t:= Complex.abs_re_le_norm (z-compared); rw [Complex.sub_re,Complex.ofReal_re, abs_le] at t; linarith only [t.1,hg]
 rw [framing, Complex.sub_re, Complex.ofReal_re]; change 0<z.re- ‖Xe‖^2; nlinarith only [ha,h.gap,hb,norm_nonneg Xe, norm_nonneg P20,h.pos]

-- note Φ(center)=0 too
lemma empty_row : portfolio Y H W (cameo Y H s (center K (estate Y H W s)))=0:=by rw [placing Y H W,←intake_eq Y H s W.own,center_pay]

-- embed showcase s=0 into halo all-os. Equality of reflections across linear stepFactor
section
omit W
lemma midway_turn (a:Axis)(t:ℤ)(f:junior K) : midway Y H a t (cameo Y H s f)= cameo Y H s (turn K a (steady Λ t s) f) :=by
 apply Subtype.ext; change acrossAll K a (steady Λ t) (Style.stepFactor s f) = _
 change Style.inversion (fun i=>turn K a (steady Λ t i)) (Style.stepFactor s f) = Style.stepFactor s (turn K a (steady Λ t s) f); rw [Style.insert_at,Style.insert_at,Style.inv_at]
 unfold Style.rotating; apply congrArg; funext v; by_cases h:v=s <;> simp [h,update_of_ne,turn_one]
lemma steady_pivot : steady Λ (tent Y H).ζ 0=(tent Y H).plane0:=by rw [steady_aligned,pow_zero,one_mul]; rfl

local notation "A'"=> cameo Y H 0
local notation "P'"=> haloRule Y H (3:Axis) ζ'
lemma celebrates (t:ℂ) : (cameo Y H 0 (center (tent Y H) t)).val ∈ haloRule Y H 3 (tent Y H).ζ:= by
 apply Style.to_pub _ 0; refine resident (BookRule (tent Y H) 3 (steady Λ ζ') (reserve Λ l)) 0 (center (tent Y H) t) ?_
 unfold BookRule; rw [steady_pivot Y H]; exact center_admit ..

def emptyBulb (t:ℂ): haloRule Y H 3 (tent Y H).ζ:= ⟨(cameo Y H 0 (center K t)).val,celebrates Y H t⟩
lemma empty_input (z:ℂ): input Y H 3 (tent Y H).ζ (emptyBulb Y H z)= (cameo Y H 0 (center K z)):= by apply Subtype.ext; rfl
include W

lemma showcase (e:ℝ)(h:Tol e)(p:Deposit Y H 0 e i k) :
    portfolio Y H W (cameo Y H 0 (bulb K)) ≠ 0 ∧ 0 < formPanel Y H W 3 (tent Y H).ζ (emptyBulb Y H (estate Y H W 0)) (emptyBulb Y H (estate Y H W 0)):=by
 have hh:= scented Y H W 0 e h p
 constructor; · rw [placing Y H W]; exact hh.1
 let u:= center K (estate Y H W 0); let x:= input Y H 3 (tent Y H).ζ (emptyBulb Y H (estate Y H W 0))
 change 0< Pr (midway Y H 3 (tent Y H).ζ x * x); rw [show x=cameo Y H 0 u from empty_input Y H (estate Y H W 0),midway_turn,steady_pivot Y H,←map_mul]; exact hh.2
end
end Banner
end YM.CF.Buffered.Concord
#print axioms YM.CF.Buffered.Concord.Banner.scented
#print axioms YM.CF.Buffered.Concord.Banner.showcase
#print axioms YM.CF.Buffered.Concord.Banner.center_pay
