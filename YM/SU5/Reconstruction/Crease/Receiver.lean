import YM.SU5.Reconstruction.Crease.Decanter
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.BridgeClub.Club
open Function Set Filter MeasureTheory Spectral Analysis Metric ContinuousLinearMap Anvil Picket CrossedFrame
open scoped BigOperators Topology InnerProductSpace ComplexOrder NNReal ENNReal Complex Classical
variable {H D K:Hilbert}{M: Net H}{C: Clasp K H D}{J:Flash H}{Γ:Set H.Op}{Ω:H}
variable (h:Club C J M Ω Γ)(z a:ℂ)(e:a.re=1/2)(g:z*a=star a)
local notation "P"=>C.plume
local notation "R"=>C.shadow
local notation "J₀"=>J.f
abbrev WPort (C:Clasp K H D)(Ω:H)(z:ℂ)(x y:H.Op) := C.plume (C.plume (x Ω)) = C.shadow (C.shadow (y Ω))+z • C.plume (C.plume (y Ω))
local notation "Υ"=> WPort C Ω z
include h a e g
lemma walksSelf (N:H.Op)(q:N∈ M.commutant)(m:‖N‖≤1)(hk:IsSelfAdjoint N): ∃ y∈M,Υ N y:= by
 obtain ⟨X,k,u⟩:= allScripts a e q m Ω hk; refine ⟨a • X,m_smul _ k.1,?_⟩; let xt:= J.f (X Ω); have hb : P xt=R (X Ω):= by simpa only [xt,k.2.star_eq] using h.charge X k.1
 unfold WPort; rw [smul_apply,map_smul,map_smul,map_smul,map_smul,smul_smul,g]; apply ext_inner_right ℂ; intro y
 have hu(y:H) : inner ℂ (N Ω) (P y)= star a * inner ℂ xt (R y)+ a*inner ℂ (X Ω) (P y):= by
   let L:H→L[ℂ]ℂ:= (innerSL ℂ (N Ω)).comp P; let V:H→L[ℂ]ℂ:=star a • ((innerSL ℂ xt).comp R) + a • ((innerSL ℂ (X Ω)).comp P)
   apply h.economize {y:H| L y=V y} (isClosed_eq L.continuous V.continuous) _ _ _ _ y
   · intro t p; change inner ℂ (N Ω) (P _)=_*inner ℂ xt (R _)+_*inner ℂ (X Ω) (P _); rw [h.pose t p,h.rePose t p,show inner ℂ xt _=_ from J.light (X Ω) (star t Ω)]
     have hb:= congrArg (fun z:ℂ=>star z) (u t (h.pin p)); simp only [star_add,star_mul',star_star, Complex.star_def,Complex.conj_conj, inner_conj_symm] at hb; rw [hb,add_comm]; rfl
   · change L 0=V 0; simp
   · exact fun x (p:L x=V x) y (q:L y=V y) => show L (x+y)=V (x+y) by rw [map_add,map_add,p,q]
   exact fun x (p:L x= V x) c=> show L (c • x)=V (c • x) by rw [map_smul,map_smul,p]
 have ht: inner ℂ xt (R (P y))= inner ℂ (R (R (X Ω))) y:= by rw [show R (P y)= P (R y) from Eq.symm (DFunLike.congr_fun C.opponents.eq y),← Clasp.through_self _ C.plume_self,hb, ← Clasp.through_self R C.shadow_self (R (X Ω)) y]
 rw [Clasp.through_self P C.plume_self,Clasp.through_self P C.plume_self,hu, ht, inner_add_left,inner_smul_left,inner_smul_left]; -- conjug star and PP
 rw [← Clasp.through_self P C.plume_self,← Clasp.through_self P C.plume_self] -- direction issues rewrites
 simp
omit h a e g
private lemma WPort_add {B D' A A':H.Op}(p:Υ B A)(v:Υ D' A'): Υ (B+D') (A+A'):= by simp only [WPort,add_apply,map_add,smul_add]; rw [p,v]; abel
private lemma WPort_smul {B A:H.Op}(p:Υ B A)(c:ℂ): Υ (c • B) (c • A):= by simp only [WPort,smul_apply,map_smul,p,smul_add]; rw [smul_comm c]
include h a e g
lemma cranes (A:H.Op)(q:A∈M.commutant):∃ y∈M,Υ A y:=by
 have ht(A:H.Op)(k:Taut M.commutant A): ∃ y∈ M, Υ A y:=by
    let s:=1+‖A‖; have hs:0<s:=by unfold s; positivity
    let A':=(s⁻¹:ℝ); let q:= (A':ℂ) • A; have hk:= k.wide A';
    obtain ⟨y,p,h0⟩:=h.walksSelf z a e g q hk.1 (show ‖q‖≤ 1 from (by
           unfold q A'; rw [norm_smul,Complex.norm_real,norm_inv,Real.norm_of_nonneg hs.le, ← div_eq_inv_mul,div_le_one hs]; unfold s; linarith)) hk.2
    refine ⟨ (s:ℂ) • y,m_smul _ p,?_⟩; exact (show (s:ℂ) • q=A from (by unfold q A'; rw [smul_smul, ← Complex.ofReal_mul,mul_inv_cancel₀ hs.ne',Complex.ofReal_one,one_smul])) ▸ (WPort_smul z h0 (s:ℂ))
 obtain ⟨x,y,t,u,rfl⟩:= halves M.commutant A q; obtain ⟨l,h,p⟩:=ht x t; obtain ⟨k,t,v⟩:= ht y u; exact ⟨l+Complex.I • k, add_mem h (m_smul _ t), WPort_add z p (WPort_smul z v _)⟩
end YM.BridgeClub.Club
