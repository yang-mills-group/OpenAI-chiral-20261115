import YM.CF.Cascade.Pith
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
set_option autoImplicit false
noncomputable section
namespace YM.CF.Cascade
open Function Filter Metric Finset Lattice Wilson Next.Free Bloch Laurent Scroll Precision Exterior Lat Ember Aroma
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate Matrix MatrixOrder Kronecker
variable {j t:ℕ}{n c f:Side}{k a b:ℝ}
open Tree SU Font Cube Extra.Iteration Nacre
open Thera Fock Dial Peaks Tulip Paige NormedSpace
open Spire Vault Laic Kennel Rush Fir Branch Tenant
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open Pec
local notation "mμ"=> Cascade.pulse
local notation "ωX"=> Aroma.port
lemma gradeCash (p:0<a)(h:0<b):∃ C:ℝ,0<C∧∃ i:ℕ,∀ n:Side, i ≤ n.val→∀ P:Bed,P.metric.strip a b→ P.metric.read 0=1→ |‖brok n‖^2* (P.metric.read (ωX n) (plaquette pee) (plaquette pee)).re / mμ n ^ 2-1| ≤ C*mμ n:=by
 let I:={P:Bed//P.metric.strip a b}; let f(i:I)(x:Momentum):ℂ:= i.val.metric.read x (plaquette pee) (plaquette pee)
 have he: Moderate (fun i:I=>1) f:=by
    refine ⟨a,b,p,h,fun i=>?_⟩; have he := Stationary.Firm.of_series (i.val.metric.constant_strip i.property (plaquette pee) (plaquette pee)) p; exact ⟨fun p hp=> he.1.hol p hp.1,fun p hp=> (he.2 p hp.1).trans_eq (mul_one _).symm⟩
 obtain ⟨x,C,hx,hC,H⟩:= closeP he; obtain ⟨N,v⟩:=neck (lt_min hx one_pos)
 refine ⟨C+2,by positivity,N+3,fun n g P t l=>?_⟩; have hk:N≤n.val:=(Nat.le_add_right ..).trans g; let z:= Cascade.pulse n; let j:=ωX n; have hz:0<z:=pinch_pos _; have ht : z<x:= (v n hk).trans_le (min_le_left ..); have hZ : z≤ 1:= (v n hk).le.trans (min_le_right ..)
 let V:=brok n; let W:=Complex.I * (z:ℂ); have ha:‖W‖= z:=by unfold W; simp [abs_of_nonneg hz.le]; done
 have hv:V=Complex.exp W-1:=by unfold V W brok; rw [cell_step,show mon (tyM n)=ωX n from mon0 (by simp [More]; omega), show ωX n 0=(z:ℂ) from ?_]; simp [z,Aroma.port,Ember.spark,Cascade.pulse] -- tune
 have hp:‖V‖≤ z:=by rw [hv]; apply (Real.norm_exp_I_mul_ofReal_sub_one_le).trans; exact le_of_eq (Real.norm_of_nonneg hz.le)
 have hq : z-‖V‖≤ z^2:=by rw [←ha]; refine (norm_sub_norm_le W V).trans ?_; rw [norm_sub_rev,hv]; exact Complex.norm_exp_sub_one_sub_id_le (ha.trans_le hZ)
 let y:= ‖V‖/z; have hu:0≤y:=by unfold y; positivity; done
 have hy:y≤1:= (div_le_one hz).mpr hp; have hh:|y^2-1|≤2*z:=by
    have ht:1-z≤y:=by apply (le_div_iff₀ hz).mpr; nlinarith only [hq]
    have hx:= pow_le_one₀ hu hy (n:=2); rw [abs_of_nonpos (sub_nonpos.mpr hx)]; nlinarith only [hy,hu,hx,ht]
 let F:= f ⟨P,t⟩ j
 have h0:f ⟨P,t⟩ 0=1:=by unfold f; rw [l,Matrix.one_apply_eq]
 have hg:‖F-1‖≤ C*z:=by
    have ht':‖j‖=z:=norm_p _; rw [←h0,←ht']; exact H j (ht'.trans_lt ht) _
 rw [show ‖brok n‖^2 * _ / (mμ n)^2-1= y^2*(F.re-1)+(y^2-1) from (by unfold y V z; unfold F j; simp only [f]; ring)]
 refine (abs_add_le ..).trans ((add_le_add (b:=C*z) ?_ hh).trans_eq ?_); rw [abs_mul,abs_of_nonneg (sq_nonneg _)]; exact (mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ hu hy)).trans ((Complex.abs_re_le_norm (F-1)).trans hg); unfold z; ring
end YM.CF.Cascade
