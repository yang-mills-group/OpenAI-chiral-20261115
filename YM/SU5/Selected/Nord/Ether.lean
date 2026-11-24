import YM.CF.Kea.Pith
import YM.SU5.FiniteGaugeData.Signal.OceanPort
import YM.CF.BPress.Spin.Invest
import YM.CF.Vale.Inca
import YM.SU5.Selected.Nord.Trace
/-! Free (fock) moment in pricing. Preserve its dependence on period Male. -/
set_option autoImplicit false
set_option synthInstance.maxSize 12000
set_option maxHeartbeats 480000
noncomputable section
namespace YM.CF.Py.Rate.LocalLimit.Fragment
open Function Filter Lattice Wilson Precision Tree SU Fock Lat Cube Tulip Scroll Drapes Dial Spire Vault Paige
open scoped Topology BigOperators InnerProductSpace ComplexOrder Matrix MatrixOrder Matrix.Norms.L2Operator Kronecker Classical
attribute [local instance] opCStarAlgebra
open Peaks Thera Cascade Hom Kea Nacre Font Kennel Laic
open Finset Broc
variable {L B:Side}{j:ℕ}{o:Odd L.val}{e:ℝ}{X:Pricing j L o (Thread j)}(P:Grasp X B e)(M : Tulip.Male) {m n:Side}
local notation "K"=> CSide m B
local notation "U"=> CSide n B
variable (h0:0<e)(h:1≤j) (A:Pearl P)(p:Stamped j L o X)(hm:P.roundZ ≤(CSide m B).val)

def token (j:ℕ)(N:Side)(M:Tulip.Male):ℝ:= - OrbT (tickA N) (spar j M (1:Bkg (More N))) 0
lemma blank_ok(v:0≤e): Guard (1:Bkg (More n)) e:= by rw [← Signal.Sparkle.LocalPlane.free1]; exact tax_guard _ _ _ v
include h h0 hm
lemma present : token j (CSide m B) M=Real.log (Kea.angel m P M) := by
 unfold token Kea.angel Kea.AMP; rw [Signal.Sparkle.LocalPlane.free1]; let B:= tickA (CSide m B); let V:= spar j M (1:Bkg (More K)); let e':= blank_ok h0.le (n:=K); let f:=changeM P (1:Bkg (More K)) M; have he:IsStarProjection V:= (P.broadness _ hm M).projection _ e'; have ht: Matrix.trace B=Matrix.trace V:= (Cascade.rank_z K h M).symm
 simpa only [add_zero, skyGlow, quant_one,act_one] using (orb_snap V B 0 f (sea_g (P:=P) hm 1 e' M) (mateK K) (tickB _) he (cut_t _) ht).symm
omit h h0 hm
variable (G:Ratio (CSide m B) (CSide n B))(hg:G.count=L)
lemma hue (f:Pec.Pride n): Pec.pigment f 1=0:=by
 have hx(s:Signed): Yg (incX s) (1:Bkg (More n))=1:=by rw [Ywin]; ext; simp [Lattice.pull,Step.read]; -- tune
 unfold Pec.pigment Pec.lexn Pec.zinger Pec.tag; simp [hx]
lemma pulse' {D:Aim U}: Thera.desire L j o G M 1 0=0 ∧ Pec.coatG _ o j G M D.den 1=0:=by
 constructor
 · unfold Thera.desire bentT; rw [mul_zero]
 unfold Pec.coatG gate Thera.desire bentT crux capT; change _*( _* _)*(_* foot G (D.den (1:Bkg _)) * _)=_; rw [BPress.Spin.aim_zero, show foot G (0:Op _)=0 from rfl,mul_zero,zero_mul,mul_zero] -- tune syntax
include h hg
lemma flux(hj:Even j) : fruit L j o G M 1 0=0:=by
 unfold fruit traitP creep; rw [show unionP (1:Paige.nomA m n B)=1 from ?_]; swap; · change (profile (1:Bkg _),profile (1:Bkg _))= _; simp [profile_trivial]
 simp only [bentT,mul_zero,add_zero,one_mul,mul_one,inv_one]; apply Thera.endorseI G; rw [Thera.spry]; change lum j L o (Thread j) true M G 1=endorse G 0; rw [cologne j L o hj h (Thread j) (canUse _ _ o) _ G hg M, Kennel.betP (0:Op _)] -- tune
omit hg
include G hm
lemma summit_u (X0:Guard (1:Bkg (More U)) e)(Z:0<Kea.angel n P M) : IsUnit ((love _).symm (Zoom U (tickA U * (1+0) * spar j M (1:Bkg (More U))))) :=by
 have hx: P.roundZ ≤ (U).val := P.clock_fine G hm; let p:= spar j M (1:Bkg (More U)); let w:= tickA U; let F:=changeM P (1:Bkg (More U)) M; have hp:IsStarProjection p:= (P.broadness _ hx M).projection _ X0
 suffices h:IsUnit (Zoom _ (w*(1:Op (Single (CSide n B)))*p)) by
    rw [add_zero]; apply h.map
 have hr : ‖skyGlow (mateK U) 1 F‖= Kea.angel n P M:=by rw [skyGlow, quant_one,act_one]; unfold Kea.angel Kea.AMP; rw [Signal.Sparkle.LocalPlane.free1]
 apply (Matrix.isUnit_iff_isUnit_det _).mpr; apply IsUnit.mk0; unfold Zoom; rw [← prismK hp (cut_t U) (Cascade.rank_z U h M).symm 1 F (sea_g (P:=P) hx 1 X0 M) (mateK U) (tickB _),hr]; exact Complex.ofReal_ne_zero.mpr (pow_pos Z 2|>.ne')
include A h0 p h hm hg
lemma route (Y:Aim U)(hj:Even j) (I:Pec.Pride (CSide n B))(J:Pec.Pride (CSide m B))(a:Kea.Pad j U) : (Cour.shipA G P M Y.den I J (1,1)).re= token j (CSide m B) (upMale L o M) - token j (CSide n B) M := by
 let F:=(1:Op (Single U)); let N:= (1:nomA m n B); have hv: Matrix.trace (tickA U)=Matrix.trace (spar j M N.1):= (rank_z U h M).symm; have ht: JointB G N e:= (near_j G e h0).self_of_nhds; have hfoil: foot G (0:Op (Single U))=0:=rfl
 obtain ⟨hQ,hC⟩:= pulse' (D:=Y) M G (o:=o) (j:=j)
 have hE: ‖Thera.desire L j o G M N (foot G (0:Op (Single U)))‖<1:=by rw [hfoil,hQ,norm_zero]; exact zero_lt_one
 have hp: skyGlow (oceanA G) (1+foot G (0:Op (Single U))) (graft G P N.1 M)≠0:= Cascade.koh N ht hg hm (0:Op _) hE (summit_u P M h hm G (blank_ok h0.le) (Kea.angel_p A p (P.clock_fine G hm) h h0 M a)) hv
 have he:= laser h0 G hg hm M N ht (show TagG (spar j M N.1) 0 from ⟨mul_zero _,zero_mul _⟩) hE hv hp
 unfold token; have hz:invoice (0:Op (Iota G))=0:=by simp [Fock.invoice,Fock.slope]
 rw [hfoil,hQ,hz,add_zero, flux M h G hg hj] at he; unfold Cour.shipA; rw [Pec.lush]; change (Pec.pigment I 1 + (-Spire.altar G P N M - invoice (Pec.coatG L o j G M Y.den 1))-Pec.pigment J 1).re= -OrbT (tickA K) (spar j (upMale L o M) N.2) 0- -OrbT (tickA U) (spar j M N.1) 0; rw [hC,hz,sub_zero,hue I,hue J,sub_zero,zero_add,Complex.neg_re]
 linarith
end YM.CF.Py.Rate.LocalLimit.Fragment
#print axioms YM.CF.Py.Rate.LocalLimit.Fragment.route
