import GaugeFieldConstruction.Breath
import GaugeFieldConstruction.Triads
import GaugeFieldConstruction.Sardana
/-!
# W2 macroscopic aperture. Taylor binoculars on the on-shell jet ink.
-/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.Wick
open StressFHeat MeasureTheory Analysis Function Filter Metric Maxwell Finset Gap Complex Cauchy Row Wick Phys
open scoped Topology ContDiff BigOperators
namespace Yacht
variable {α β: Type*}(D: Axis→ Module.End ℂ (J α))(a:J α)
-- directional moment integrals
abbrev Φ (n:ℕ):= Fin n→ Axis
def tower : ∀ n, Φ n→ J α
 | 0,_ => a
 | n+1,p=>D (p 0) (tower n (fun i=>p i.succ))
def dock {n:ℕ} (u:E4)(p:Φ n):ℝ := ∏ i,u (p i)
def gust (n:ℕ)(u:E4):J α:=∑ p:Φ n,(dock u p:ℂ) • tower D a n p
lemma gust_succ (n:ℕ)(u:E4): gust D a (n+1) u=∑ i:Axis,(u i:ℂ) • D i (gust D a n u):=by
 unfold gust; let P:=Fin.consEquiv (fun _:Fin (n+1)=>Axis); rw [←Equiv.sum_comp P (fun p:Φ (n+1)=> (dock u p:ℂ) • tower D a (n+1) p),Fintype.sum_prod_type]; refine sum_congr rfl fun i _=> ?_; rw [map_sum, Finset.smul_sum]; refine sum_congr rfl fun j _=>?_ ; rw [map_smul, smul_smul]
 rw [tower, dock,Fin.prod_univ_succ]; simp [dock,P,Fin.consEquiv]
lemma gust_first (u:E4):gust D a 0 u=a:=by simp [gust,tower,dock] -- tune
abbrev tariff (s:ℝ)(n:ℕ):ℝ := s^n*(n.factorial:ℝ)⁻¹
def Tapper (n:ℕ)(t:ℝ)(x:E4):J α:=∑ i∈range (n+1),(tariff t i:ℂ) • gust D a i x
lemma T0 (n:ℕ)(x:E4): Tapper D a n 0 x=a:=by
 induction n with | zero=> simp [Tapper,gust_first,tariff] | succ n hp=> rw [Tapper,sum_range_succ,←Tapper,hp]; simp [tariff]
lemma inc0 (n:ℕ)(t:ℝ)(x:E4): Tapper D a (n+1) t x=Tapper D a n t x+(tariff t (n+1):ℂ) • gust D a (n+1) x:=by simp only [Tapper,sum_range_succ]
-- Real parameter V.H derivative with coeff plus displacement direction
lemma bend (t r:ℝ)(n:ℕ): HasDerivAt (fun q:ℝ=> tariff (t-q) (n+1)) (-tariff (t-r) n) r:=by
 unfold tariff; apply HasDerivAt.congr_deriv ((((hasDerivAt_const r t).sub (hasDerivAt_id r)).pow _).mul_const _); simp only [Nat.factorial_succ]; push_cast; simp [id]; field_simp
variable {p: Bil α β}{D}{L:Axis→ Module.End ℂ (J β)}
-- p tests signed step. want derivative. $E4$ basis Real
abbrev Lefty (p:Bil α β)(D:Axis→ Module.End ℂ (J α)):Prop:=∀ i a b,p (D i a) b = -Gap.step i (p a b)
abbrev Rorky (p:Bil α β)(L:Axis→ Module.End ℂ (J β)):Prop:=∀ i a b,p a (L i b)= Gap.step i (p a b)
variable (h:Lefty p D)(g:Rorky p L)
-- append derivative vectors define Dir.motions
abbrev Rise (D:Axis→ Module.End ℂ (J α))(u:E4)(a:J α):=∑ i:Axis,(u i:ℂ) • D i a
lemma closed_on (X:E4): ∑ i:Axis,X i • basis i=X:=by apply PiLp.ext; intro i; simp -- tune
include h g
lemma stir (b:J β)(u v d:E4)(r:ℝ)(e:d+r • (v-u)≠0): let z:=d+r • (v-u); HasDerivAt (fun t:ℝ=> eye (d+t • (v-u)) (p a b)) (eye z (p (Rise D u a) b)+eye z (p a (Rise L v b))) r:=by
 intro z; let f:=(p a b).val; have hp:fderiv ℝ f z (v-u)=∑ i:Axis,(v i:ℝ) • grad i f z- ∑ i:Axis,(u i:ℝ) • grad i f z:=by rw [map_sub]; nth_rw 1 [←closed_on v,←closed_on u]; rw [map_sum,map_sum]; simp_rw [map_smul]; rfl
 have he: HasDerivAt (fun x:ℝ=> d+x • (v-u)) (v-u) r:=by exact HasDerivAt.congr_deriv ((hasDerivAt_const r d).add ((hasDerivAt_id r).smul_const (v-u))) (by simp)
 refine (((Gap.healthy (p a b) e).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt r he).congr_deriv ?_
 change fderiv _ f z _=_; rw [hp]; unfold Rise; simp only [map_sum,map_smul,LinearMap.sum_apply,LinearMap.smul_apply,h,g,map_neg,Complex.real_smul,smul_eq_mul]; simp_rw [show ∀ i:Axis, eye z (Gap.step i (p a b))= grad i f z from (fun i=> flash i (p a b) e),mul_neg]; rw [sum_neg_distrib,add_comm]; rfl
omit h g
lemma ri_start (x y:J α)(i:E4): Rise D i (x+y)=Rise D i x+ Rise D i y:=by simp only [Rise,map_add,smul_add,sum_add_distrib]
lemma ri_s (s:ℂ)(x:J α)(i:E4): Rise D i (s • x)=s • Rise D i x:=by unfold Rise; rw [smul_sum]; refine sum_congr rfl fun p _=> ?_; rw [map_smul]; exact smul_comm ..
-- generic multilinear evaluation computation along one aperture input
variable (u:E4)(r t:ℝ)
lemma solo (X:ℝ→ J α→ₗ[ℂ]ℂ)(V:J α→ₗ[ℂ]ℂ) (h:∀ a:J α, HasDerivAt (fun v=> X v a) (X r (Rise D u a)+V a) r)(n:ℕ): let H:= Tapper D a n (t-r) u; HasDerivAt (fun v=>X v (Tapper D a n (t-v) u)) (V H+(tariff (t-r) n:ℂ)*X r (gust D a (n+1) u)) r:=by
 intro H; induction n with
 | zero=>simpa [H,tariff,Tapper,gust_succ,gust_first,Rise, add_comm] using (h a)
 | succ n hp=>
   let G:=gust D a (n+1) u; let c(j:ℕ):=(tariff (t-r) j:ℂ)
   change HasDerivAt _ (_ + c (n+1) * X r (gust D a (n+2) u)) r
   have v:= (bend t r n).ofReal_comp.mul (h G)
   have val:= HasDerivAt.add hp v -- tune
   simp_rw [inc0 (n:=n),map_add,map_smul,smul_eq_mul]; apply HasDerivAt.congr_deriv val
   simp only [Complex.ofReal_neg]; unfold H; simp_rw [inc0 (n:=n),map_add,map_smul,smul_eq_mul] -- tune
   rw [show gust D a (n+2) u=Rise D u G from gust_succ ..]; unfold G; unfold c; ring
-- motion formula
abbrev port (p:Bil α β)(d:E4):= p.compr₂ (eye d)
include h g
lemma sprint (b:J β)(v d:E4)(e:d+r • (v-u)≠0)(n:ℕ): let z(q:ℝ):=d+q • (v-u); let A(q:ℝ):=Tapper D a n (t-q) u; let B(q:ℝ):=Tapper L b n (t-q) v; let X(q:ℝ):=port p (z q); HasDerivAt (fun q=>X q (A q) (B q)) ((tariff (t-r) n:ℂ)*(X r (gust D a (n+1) u) (B r)+X r (A r) (gust L b (n+1) v))) r:=by
 intro z A B X; let c:=(tariff (t-r) n:ℂ); let U:=gust L b (n+1) v; let Y:=fun q=> (X q).flip (B q); let W:= c • (X r).flip U
 have hb(m): HasDerivAt (fun q:ℝ=> X q m (B q)) (X r (Rise D u m) (B r)+ c * X r m U) r:= by
    apply solo b v r t (fun q=> X q m) (X r (Rise D u m)) _ n
    intro s; rw [add_comm]; exact stir m h g s u v d r e
 have hp:=solo a u r t Y W (show ∀ m:J α, HasDerivAt (fun q=>Y q m) (Y r (Rise D u m)+W m) r from hb) n
 refine HasDerivAt.congr_deriv hp ?_; change c * X r (A r) U+_= c*(_+ X r (A r) U); rw [mul_add,add_comm]; rfl
end Yacht
end YM.GaugeFieldConstruction.Wick
end
