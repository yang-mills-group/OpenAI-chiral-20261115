import YM.SU5.FiniteGaugeData.Lapis.Olympia
/-! # WP22. Eu physical kinetic signal. Torus response for the comparator. No gauge determinant convention
changed. First derive C includes all four harmonic erasures correctly. Read with ANY center/colors.
-/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 520000
set_option synthInstance.maxSize 22000
noncomputable section
namespace YM.SU5.FiniteGaugeData.LapisQ
open Function Finset Filter MeasureTheory ProbabilityTheory Matrix Lattice Wilson RG Precision Tree Next.Fluctuations Work.F03
open Pressure Exterior Laurent Bloch Drachma Galope Avenue Galope.Press Wrist Poeme Haute Lapis Punch  Affiche Next.Rank.Axial
open scoped Topology InnerProductSpace Matrix MatrixOrder RealInnerProductSpace ContDiff BigOperators NNReal ENNReal Kronecker Classical
namespace Vulcan
variable {n:Side}{G:Gauge} {P:Bed}{u:Stage}{R:PathData G} {z:LogField G n}{ρ C Δ:ℝ}
local notation "V"=> Vault (Plush G (denim n))
local notation "M"=> P.metric.acts n
local notation "D"=> d 1 n
local notation "T"=> LogField G n
variable (F:Floor P u.clip n ρ C)(dp:0<ρ)(W:R.Bounds u.clip u.width u.paths Δ)(A: Attached P R) (a b:G.ColorIndex)
-- `F` shadows section var clip; remove
abbrev hair (a:G.ColorIndex): LogField G n→ₗ[ℝ] form 2 n where
 toFun y:=d 1 n *ᵥ parts G 1 y a
 map_add' x y:= mulVec_add ..
 map_smul' c x:= mulVec_smul ..
local notation "O"=> olive F dp G
def beams : V →ₗ[ℝ] form 2 n:= (hair a).comp (olive F dp G)
local notation "K" i:max=>beams F dp i
abbrev linearBeam (i:Body 2 n): V→L[ℝ]ℝ:= ((LinearMap.proj i).comp (beams F dp a)).toContinuousLinearMap -- LinearMap.proj typing
noncomputable def rayBeam (i:Body 2 n): V:= (InnerProductSpace.toDual ℝ V).symm (linearBeam F dp a i)
local notation "Kq" i:max=> rayBeam F dp i
lemma beamPrice (x:V)(i:Body 2 n): beams F dp a x i=inner ℝ ((Kq a) i) x:=(congrArg (fun f:V→L[ℝ]ℝ=> f x) (LinearIsometryEquiv.apply_symm_apply (InnerProductSpace.toDual ℝ V) (linearBeam F dp a i))).symm -- tune Equiv
noncomputable def pulseB (x: form 2 n): V:= ∑ i,x i • (Kq a) i
lemma heartB (x:V)(y:form 2 n): dotProduct (beams F dp a x) y=inner ℝ (pulseB F dp a y) x:=by
 unfold pulseB dotProduct; rw [sum_inner]; apply sum_congr rfl; intro i _; rw [real_inner_smul_left,beamPrice,mul_comm] -- tune
abbrev sineB : Matrix (Body 2 n) (Body 2 n) ℝ:= Matrix.of fun x y=> beams F dp a (rayBeam F dp b y) x
local notation "Ĉ" a:max b:max=> sineB F dp a b
lemma sineB_sym : (sineB F dp a b).transpose=sineB F dp b a:=by ext i j; simp only [transpose_apply, sineB, Matrix.of_apply]; simp_rw [beamPrice]; exact real_inner_comm ..
lemma peaking (x:form 2 n): (sineB F dp a b)*ᵥ x= beams F dp a (pulseB F dp b x) :=by funext i; unfold sineB pulseB; simp only [map_sum,map_smul,mulVec,dotProduct,Matrix.of_apply,Finset.sum_apply,Pi.smul_apply, smul_eq_mul]; apply sum_congr rfl; intro j _; ring
lemma Agenda(x y:LogField G n): Bid.gaugeFiscal P x y=∑ i:G.ColorIndex, dotProduct (hair i x) (P.metric.acts n*ᵥ hair i y):=by unfold Bid.gaugeFiscal; apply sum_congr rfl; intro i p; exact plaid_cost .. -- local K notation conflict
lemma bile (x y:V): Bid.gaugeFiscal P (olive F dp G x) (olive F dp G y)=∑ i:G.ColorIndex,dotProduct (beams F dp i x) (P.metric.acts n*ᵥ beams F dp i y):= Agenda ..
-- generic equality saturation lemma for all floor budgets (real Numeric)
private lemma quadr (a b:ℝ)(h:∀ r :ℝ,0≤r*a+r^2*b): a=0 :=by
 by_contra! v
 have he:0<(a^2:ℝ):=sq_pos_of_ne_zero v
 let t:=1/(|b|+1); have hy:0<t:=by unfold t; positivity
 have hx:t* (|b|+1)=1:= div_mul_cancel₀ _ (by positivity)
 have hb:t*b < 1:=by rw [← hx]; exact mul_lt_mul_of_pos_left (by linarith only [le_abs_self b]) hy
 have hP:0<t*a^2:= mul_pos hy he
 have hv:= h (-t*a); apply absurd hv (not_le_of_gt ?_); nlinarith only [hP, mul_lt_mul_of_pos_left hb hP]
include F in
private lemma shine_cost (x y:form 2 n): dotProduct x (P.metric.acts n*ᵥ y)= dotProduct y (P.metric.acts n*ᵥ x):=by
 -- h floor; add include
 rw [dotProduct_mulVec]; rw [← dotProduct_comm _ y]; congr 1; rw [← Matrix.mulVec_transpose, F.symmetric.1] -- ordering
include F W A
lemma cocoa (x:V)(p:Bid.gaugeFiscal P (O x) (O x)= ‖x‖^2) : ∀ y:V, Bid.gaugeFiscal P (O y) (O x)= inner ℝ y x :=by
 let Q(u v:V):= Bid.gaugeFiscal P (O u) (O v); have he(u v:V):Q u v=Q v u:=by unfold Q; rw [bile,bile]; exact sum_congr rfl (fun i _=> shine_cost F ..)
 have hx(u u' v:V)(z:ℝ) : Q (u+z • u') v=Q u v+z*Q u' v:=by
    unfold Q; simp_rw [bile,map_add,map_smul,add_dotProduct,smul_dotProduct,sum_add_distrib,mul_sum, smul_eq_mul] -- tune: simp map_smul also olive may break
 have ht(r:ℝ)(y:V): Q (x+r•y) (x+r•y)= Q x x + r*2*Q y x + r^2*Q y y:=by rw [hx,he x (x+r•y), he y (x+r•y),hx,hx,he x y]; ring
 intro y; let s:= 2*(inner ℝ y x-Q y x); let t:= ‖y‖^2-Q y y; apply _root_.eq_of_sub_eq_zero (show Bid.gaugeFiscal P (O y) (O x)-_ =0 from ?_)
 have hg:s=0:= quadr _ t fun r=> by
    have hp:= sunflower F dp W A (x+r•y)
    change Q _ _≤ _ at hp; rw [ht r y, show Q x x=‖x‖^2 from p] at hp
    simp only [← real_inner_self_eq_norm_sq] at hp; rw [inner_add_left,inner_add_right,inner_add_right,real_inner_smul_left, real_inner_smul_left,real_inner_smul_right,real_inner_smul_right,real_inner_comm x y] at hp -- tune duplicates rw
    unfold s t; rw [← real_inner_self_eq_norm_sq,real_inner_comm x y]; linarith -- tune nlin mixed terms
 unfold s at hg; change Q _ _-_ = _; linarith
lemma coverProfile (x:form 1 n): ∃ y:V, (∀ i:G.ColorIndex,beams F dp i y=if i=a then d 1 n *ᵥ x else 0) ∧ Bid.gaugeFiscal P (O y) (O y)=‖y‖^2 :=by
 let q:LogField G n:=fun j=> WithLp.toLp 2 (fun i=>if i=a then x j else 0)
 have he(i:G.ColorIndex): parts G 1 q i= if i=a then x else 0:=by by_cases t:i=a <;> simp only [t,↓reduceIte] <;> ext j <;> simp [parts,q,t]
 obtain ⟨v,h,u⟩:= fillC F dp q; refine ⟨v, fun i=>?_ , (sapph h).trans u⟩; unfold beams; change d 1 n *ᵥ parts G 1 _ _=_; rw [h i,he i]; split_ifs <;> simp
lemma return_π(x:form 1 n): sineB F dp a b*ᵥ (P.metric.acts n*ᵥ (d 1 n*ᵥ x))= if a=b then d 1 n*ᵥ x else 0:=by
 obtain ⟨y,hz,u⟩:= coverProfile F dp W A b x;
 let p:= M *ᵥ (D*ᵥ x)
 have he(v:V): inner ℝ (pulseB F dp b p) v= inner ℝ y v:=by
    rw [← heartB,real_inner_comm,←cocoa F dp W A _ u, bile]; -- apply comm at right local may rewrite first inner `dot` not now.
    simp_rw [hz]; rw [sum_eq_single b]; · simp only [p,if_true]; -- p defeq clos.W
    · intro x w q; rw [if_neg q,mulVec_zero,dotProduct_zero]; -- check sym eq
    simp
 have hg:= ext_inner_right ℝ he; dsimp only [p] at hg
 rw [peaking,hg, hz]; -- hg p defeq
end Vulcan
end YM.SU5.FiniteGaugeData.LapisQ
#print axioms YM.SU5.FiniteGaugeData.LapisQ.Vulcan.return_π
