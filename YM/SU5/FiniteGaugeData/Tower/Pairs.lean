import YM.SU5.FiniteGaugeData.Tower.OnePlane
import YM.Hilbert.Kolmogorov
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K" => tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(s:ℕ)
/-!
# Distance-free 2-mark estimate (corr-R)

Even before selection, unnormalized partners of this actual election: use
Satin/Journey's box prices (`Metered.homestead`) and `one_plane`. The
maximum principle can be paid even when the changing union doesn't satisfy
the static support threshold of the norm corollary. This estimate is for
products, including interaction words if each fits, not supremum over
arbitrary operator marks supported on the growing bi-box whose LG-operators
and coefficients needn't be factorized. No pairing/factoring the laws, this
is by exact RP. Denominator same: `X` below is an abstraction to be instantiated
by Journey's charged ratio.
-/
open Fock Heat Reed
open Analysis
section k
private lemma coreSchwarz {X:Type} [AddCommGroup X][Module ℂ X](F:X→ₗ⋆[ℂ] X→ₗ[ℂ] ℂ)(h:∀ x,0≤F x x)(x y:X):
 ‖F x y‖^2 ≤ ‖F x x‖ * ‖F y y‖:=by
 let K₁(a b:X):=F a b
 have hv:_root_.YM.Analysis.NNKernel K₁:=fun _ v=>halfSpaceKernel F h v
 obtain ⟨V⟩:=_root_.YM.Kernel.host hv
 let f:= V.plant x; let g:= V.plant y
 have hx(x:X): ‖F x x‖= ‖V.plant x‖^2:=by change ‖K₁ x x‖=_; rw [←V.measure,inner_self_eq_norm_sq_to_K,norm_pow]; change ‖((‖V.plant x‖:ℝ):ℂ)‖^2 = _; simp
 rw [hx,hx,← mul_pow]; apply pow_le_pow_left₀ (norm_nonneg _); change ‖K₁ x y‖≤ _; rw [←V.measure]; apply norm_inner_le_norm
end k

variable {Z:Calibration}{n:Side}
local notation "N"=>Z.c n
variable {X:Mark (Z.c n)→ℂ}{L:Loom (Z.c n)}{d:ℝ}(p:Journey.Metered Z n L X d)

private def belt (a:Axis) (s:ℤ): Submodule ℂ (Mark (Z.c n)) where
 carrier:={f|AtSupport false (band N a (gaugeShift Z.B s) Z.ℓ) f}
 zero_mem':=AtSupport.zeroM
 smul_mem':=fun v _ h=>AtSupport.smulM h v
 add_mem':=fun p q=>AtSupport.addM p q
local notation "B" a:max s:max=>belt (Z:=Z) (n:=n) a s
local notation "R" a:max s:max=>reflMark (n:=N) a (gaugeShift Z.B s)
include p
private def loft (a:Axis)(s:ℤ):(B a s)→ₗ⋆[ℂ](B a s)→ₗ[ℂ]ℂ:=by
 let V:=B a s; let r(f g:B a s):= X (reflMark a (gaugeShift Z.B s) f.val*g.val)
 have z₀(f g:B a s):Envelope ((R a s) f.val*g.val):=env_mult ((AtSupport.refl a _ f.property).env) (AtSupport.env g.property)
 refine ⟨⟨fun f=> ⟨⟨fun g=>r f g,fun g v=>?_⟩,fun z h=>?_⟩,fun f g=>LinearMap.ext fun h=>?_⟩,fun z f=>LinearMap.ext fun g=>?_⟩
 · unfold r; rw [AddSubmonoid.coe_add,mul_add]; exact p.sum _ _ (z₀ ..) (z₀ ..)
 · change r f _=_; unfold r; rw [Submodule.coe_smul,Algebra.mul_smul_comm]; exact p.mult _ _
 · change X ((R a s) ((f:Mark (Z.c n))+(g:Mark (Z.c n)))*h.val)=r f h+r g h
   rw [show (R a s) ((f:Mark (Z.c n))+(g:Mark (Z.c n))) = (R a s) f.val+(R a s) g.val from funext fun _=> theta_add ..,add_mul]; exact p.sum _ _ (z₀ ..) (z₀ ..)
 change X ((R a s) (z • (f:Mark (Z.c n)))*g.val)=star z * r f g
 rw [show (R a s) (z • (f:Mark (Z.c n)))=star z • (R a s) f.val from funext fun _=>theta_smul ..,Algebra.smul_mul_assoc,p.mult]
private lemma loft_paid(a:Axis)(s:ℤ)(v:B a s):0≤loft p a s v v:=p.fund a s v.val v.property -- include p in def? include ignored for def and references p used.

-- costs
section product
variable (e:ℕ)
def closefare (Z:Calibration)(d:ℝ)(e:ℕ):ℝ:= Real.exp (d*((2*(widthPair Z e+addgap Z):ℕ):ℝ)^4)
local notation "U" => closefare Z d e

def curated(Z:Calibration)(n:Side)(X: Mark (Z.c n)→ℂ)(d:ℕ):Set ℝ:={x|∃ (S T:Support (More (Z.c n)))(f g:Mark (Z.c n)),
   AtSupport false S f ∧ AtSupport false T g ∧ (∀ i,rest Z n S i d) ∧ (∀ i,rest Z n T i d) ∧
   (∀ i,‖f i‖≤1) ∧ (∀ i, ‖g i‖≤1) ∧ x=‖X (f*g)‖ }

private lemma cash_one(f:Mark N)(u:∀i,‖f i‖≤1):cash L f≤1:= (integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _=>norm_nonneg _)) (integrable_const (1:ℝ)) (Filter.Eventually.of_forall fun i=>u _)).trans_eq (by simp)
private lemma limited:BddAbove (curated Z n X e):=by
 let k:=Real.exp (d*((n.val:ℕ):ℝ)^4)
 refine ⟨k,?_⟩; rintro _ ⟨S,T,f,g,x,y,h,e,a,b,rfl⟩; refine (p.tally _ (env_mult x.env y.env)).trans ?_
 have ht: cash L (f*g) ≤1:= cash_one p _ fun i=> (norm_mul_le (f i) (g i)).trans (mul_le_one₀ (a i) (norm_nonneg _) (b i)) -- cash_one p includes p
 exact mul_le_of_le_one_right (Real.exp_pos _).le ht
lemma list_reset: (curated Z n X e).Nonempty:=by
 let f:Mark N:=0
 have h(i:Axis): rest Z n (∅) i e:= ⟨0,fun a=>by simp⟩
 exact ⟨‖X (f*f)‖,∅,∅,0,0,AtSupport.zeroM,AtSupport.zeroM,h,h,fun i=>norm_zero.le.trans zero_le_one,fun _=>norm_zero.le.trans zero_le_one,rfl⟩
noncomputable def sky (Z:Calibration)(n:Side)(X: Mark (Z.c n)→ℂ)(d:ℕ):ℝ:= sSup (curated Z n X d)
local notation "S₀"=> sky Z n X e
private lemma store {r:ℝ}(h:r∈curated Z n X e):r≤S₀:= le_csSup (limited p e) h
private lemma sky_n:0≤S₀:=by obtain ⟨a,ha⟩:= list_reset (p:=p) e; refine le_trans ?_ (store p e ha); obtain ⟨v,t,f,g,e,x,u,h,k,l,rfl⟩:=ha; exact norm_nonneg _
variable {S T:Support (More (Z.c n))}{F G:Mark (Z.c n)}(h:widthPair Z e+addgap Z ≤(Z.c n).val)
include h
private lemma local_pair (x:AtSupport false S F)(t:AtSupport false T G)(z:∀ i,rest Z n (S∪T) i (widthPair Z e))(A:∀ i, ‖F i‖ ≤ 1)(B₀:∀ i, ‖G i‖ ≤ 1): ‖X (F*G)‖ ≤ U := by
 have he:= p.homestead z h ((x.mono (subset_union_left (s₂:=T))).mulM (t.mono subset_union_right))
 have ht: cash L (F*G)≤1:=cash_one p _ fun i=>(norm_mul_le (F i) (G i)).trans (mul_le_one₀ (A i) (norm_nonneg _) (B₀ i))
 exact he.trans (mul_le_of_le_one_right (Real.exp_pos _).le ht)
private lemma split_pair {a:Axis}{b:ℤ}(x: clears Z n a e S T b)(v:AtSupport false S F)(t:AtSupport false T G)(wg:∀ i,rest Z n T i e)(l:∀ i, ‖F i‖≤1)(r:∀ i, ‖G i‖≤1): ‖X (F*G)‖^2 ≤ U * S₀:=by
 let V:=R a b; let σ:G ∈ B a b:= t.mono x.pos -- g membership
 let Z':=gaugeShift Z.B b; let V₀:=(S.image ((plane a Z').anon N)); let T₀:=T.image ((plane a Z').anon N)
 let i:B a b:=⟨V F,(v.refl a Z').mono x.neg⟩; let j:B a b:=⟨G,σ⟩
 have he:= coreSchwarz (loft p a b) (loft_paid p a b) i j
 change ‖X (V (V F)*G)‖^2 ≤ ‖X (V (V F)*V F)‖ * ‖X (V G*G)‖ at he
 rw [show V (V F)=F from AtSupport.refl_refl _ _ v] at he
 refine he.trans (mul_le_mul (local_pair p e h v (v.refl a Z') x.short l ?_) (store p e ?_) (norm_nonneg _) (Real.exp_pos _).le)
 · intro i; rw [show ‖V F i‖=_ from theta_fee (carR a Z' N) (F (reflFields a Z' i))]; exact l _
 exact ⟨T₀,T,V G,G,t.refl a Z',t,fun i=>stays (wg i) Z',wg,fun i=> (theta_fee (carR a Z' N) _).le.trans (r _),r,rfl⟩

omit p h in
private lemma mark_comm {S T:Support (More (Z.c n))}{f g:Mark (Z.c n)}(p:AtSupport false S f)(t:AtSupport false T g):f*g=g*f:=by
 funext x
 have he:= ((p.mono (subset_univ _)).allV x); have hg:= ((t.mono (subset_univ _)).allV x); change f x*g x=g x*f x; rw [show f x*g x=_ from he.sign_com hg]; simp [Sector.grainB] -- arg p shadow

lemma all_pair(x:AtSupport false S F)(t:AtSupport false T G)(ws:∀i,rest Z n S i e)(wt:∀i,rest Z n T i e)(f g:ℝ)(hf:∀i,‖F i‖≤f)(hg:∀i,‖G i‖≤g): ‖X (F*G)‖ ≤ U*(f*g) :=by
 have he (v:ℝ)(g:v∈ curated Z n X e): v^2≤ max (U^2) (U*S₀):=by
    obtain ⟨S,T,F,G,q,x,w,t,hf,hg,rfl⟩:= show v∈ _ from ‹v∈ curated Z n X e›
    rcases one_plane w t h with up|⟨i,z,h'|h'⟩
    · exact (pow_le_pow_left₀ (norm_nonneg _) (local_pair p e h q x up hf hg) 2).trans (le_max_left ..)
    · exact (split_pair p e h h' q x t hf hg).trans (le_max_right ..)
    rw [mark_comm (Z:=Z) (n:=n) q x] -- tune name args incl p/h conflicts
    exact (split_pair p e h h' x q w hg hf).trans (le_max_right ..)
 have hx: 0<U:=Real.exp_pos _
 have hu: S₀ ≤ U:=by
    let k:=max (U^2) (U*S₀); have hV:0≤k:=(sq_nonneg U).trans (le_max_left ..)
    have hh:S₀≤ Real.sqrt k:=csSup_le (list_reset (p:=p) e) (fun v g=> Real.le_sqrt_of_sq_le (he v g)) -- name
    by_contra! L'; have hd:= Real.sq_sqrt hV; have hS:=sky_n p e; have hp: U^2≤ U*S₀:=by nlinarith
    have hd':k=U*S₀:=max_eq_right hp; nlinarith [Real.sqrt_nonneg k, mul_pos hx (sub_pos.mpr L')]
 rcases ((norm_nonneg _).trans (hf (1,1))).eq_or_lt with v|v
 · have v':F=0:=by funext i; exact norm_eq_zero.mp (le_antisymm (v ▸ hf i) (norm_nonneg _)) -- cast direction
   have hl:X (0:Mark N)=0:=by simpa using p.mult 0 1
   rw [v',zero_mul,hl,norm_zero,←v]; simp
 rcases ((norm_nonneg _).trans (hg (1,1))).eq_or_lt with t₀|t₀
 · have t':G=0:=by funext i; rw [←t₀] at hg; exact norm_eq_zero.mp (le_antisymm (hg i) (norm_nonneg _))
   have hl:X (0:Mark N)=0:=by simpa using p.mult 0 1
   rw [t',mul_zero,hl,norm_zero,←t₀]; simp
 let A:ℂ:= (f:ℂ)⁻¹; let l:ℂ:=(g:ℂ)⁻¹
 have H(c:ℝ)(F:Mark N)(x:0<c)(h:∀i, ‖F i‖≤c)(i:Fields N):‖((c:ℂ)⁻¹ • F) i‖≤1:=by rw [Pi.smul_apply,norm_smul,norm_inv,Complex.norm_real,Real.norm_of_nonneg x.le]; exact (mul_le_mul_of_nonneg_left (h i) (by positivity)).trans (inv_mul_cancel₀ x.ne').le
 have ht:= (store p e (show ‖X ((A • F)*(l • G))‖∈curated Z n X e from ⟨S,T,A • F,l • G,x.smulM _,t.smulM _,ws,wt,H _ F v hf,H _ G t₀ hg,rfl⟩)).trans hu
 rw [Algebra.mul_smul_comm,Algebra.smul_mul_assoc,smul_smul,p.mult,norm_mul,norm_mul] at ht
 unfold A l at ht; rw [norm_inv,norm_inv, Complex.norm_real, Real.norm_of_nonneg t₀.le, Complex.norm_real,Real.norm_of_nonneg v.le] at ht -- order
 field_simp at ht; nlinarith

end product
end YM.CF.Buffered.Afterglow.Tower
#print axioms YM.CF.Buffered.Afterglow.Tower.all_pair
