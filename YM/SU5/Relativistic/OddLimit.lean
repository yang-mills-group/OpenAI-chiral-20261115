import YM.SU5.Relativistic.OddDonor
import YM.SU5.Relativistic.Joint

/-! # On this very history, odd sign rules. Do not use positivity on true finite-volume as hypothesis. -/
set_option autoImplicit false
set_option synthInstance.maxSize 25000
set_option maxRecDepth 5500
set_option maxHeartbeats 450000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction
namespace FermionSlab
open Function NormedSpace Filter Metric Lattice Cube Finset MeasureTheory RG Wilson
open Lat Mir Phase RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Scree Window Vale Girt Lifted
open Py Py.Rate LocalLimit Preparation Satin Heat Fock SlabMark PhaseChoice Push.SectorMeasure
open Tapestry Tapestry.Altitude Tapestry.Exhibition
open CF.Pannier.Chancel CF.Pannier.Chancel.Cliplet
open Reliance ShortWave
open Tower.Selected Vacancy Journey
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1 ≤ Λ.x)
local notation "K"=>tent Y H
variable (s i k:ℕ)
local notation "δ" n:max=>deltaL Y H n s
local notation "μ" i:max=>momentm Y i s
local notation "α" i:max=>side Y i s
local notation "Χ" p:max=> solder Y i k p s
variable {F: Family (tent Y H)}
lemma gradedLaw {p:Ferry Y s i k} (a:Axis)(z:ℤ)(v: AtSupport true (band ((K).c (μ i)) a (Heat.gaugeShift (K).B z) (K).ℓ) (F (μ i))) : 0 ≤ hot Y H s i k (Complex.I • (mirror K a (Heat.gaugeShift (K).B z) F*F)):=by
 unfold hot; rw [dif_pos p.depth]
 let q:= fullness Y i k p.depth
 let x:= distribute Y H s i F
 let g:= mirror (tent Y H) a (Heat.gaugeShift Λ.block z) F
 change 0≤ (solder Y i k p.depth s) (distribute Y H s i (Complex.I • (g*F)))
 unfold g 
 rw [(distribute_arith Y H s i (mirror (tent Y H) a (gaugeShift Λ.block z) F*F) F Complex.I).2.2.1,(distribute_arith Y H s i _ _ 1).2.1,(distribute_arith Y H s i F F 1).2.2.2.2]
 unfold solder; rw [mark_smul]
 let T:= Heat.gaugeShift Λ.block z
 refine div_nonneg ?_ ?_
 · have hv:AtSupport true (band (α i) a T ((K).ℓ)) x:=transmit _ _ _ (terrain Y H (Y.ir i) s) v
   exact onwardFermi _ _ _ _ _ _ _ _ (Journey.legal Λ) Λ.R.coarse q.warm_grant (fun k _=> tissue Y i k) (Journey.prepared Λ l) q.heat.choose a s p.enters z x hv
 have he:= Journey.throbbing Y i k p.depth s p.enters a z 1 (AtSupport.oneM _)
 rw [mul_one,show reflMark a _ (1:Mark (α i))=1 from funext fun _=> Fock.theta_one _,markvac] at he; exact he
where
 transmit {A B:Side}(a:Axis)(z:ℤ)(v:ℕ)(t:A=B) {f:Mark A}(p:AtSupport true (band A a z v) f):AtSupport true (band B a z v) (ship t f):=by subst t; exact p

lemma singleFermiNil {p:Ferry Y s i k} {f:Mark (α i)}{S}(t:AtSupport true S f) : (solder Y i k p.depth s) f=0:=by
 unfold solder; let r:=fullness Y i k p.depth; rw [onwardNil _ _ _ _ _ _ _ _ (Journey.legal Λ) r.warm_grant (fun k _=>tissue Y i k) r.heat.choose s p.enters f (t.mono (subset_univ _)),zero_div]

lemma odd_bill (e:ℝ)(h:0<e):∀ᶠ k:ℕ in atTop,∀ (i:ℕ), Ferry Y s i k → ∀ (S:Support (More (side Y i s))) (f:Mark (side Y i s)),AtSupport true S f→∀ (C:ℝ),(∀ x, ‖f x‖≤ C)→ ‖Journey.compass Y i k s f‖ ≤ e*C:=by
 filter_upwards [Y.thaw s e h] with k t i p S f H' C w
 let a:= f ∘ drawn ((Y.voyage i).CapeT s)
 have hx:Envelope a:=Env.along H'.env (drawn_m _ ((Y.voyage i).ownership s).paid.bill)
 have he:‖Journey.compass Y i k s f-(solder Y i k p.depth s) f‖≤ e*C:= t i p.depth a C hx.meas (fun x=>w _)
 rwa [singleFermiNil Y s i k (p:=p) H',sub_zero] at he

section prior
variable {S:Finset Cover}
variable {a b:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H a b I E)
include V
lemma chargedGram {j:Axis}{z:ℤ}(t:InTest K true S true F)(p:Tower.region j (gaugeShift Λ.block z) (K).ℓ S):0 ≤ E s (Complex.I • (mirror K j (Heat.gaugeShift Λ.block z) F * F)):=by
 let f:=Complex.I • (mirror K j (Heat.gaugeShift Λ.block z) F * F)
 let X:= reflectedBox j (Heat.gaugeShift Λ.block z) S
 have hp: InTest K true (X∪S) false f:= .smul _ (((axial K j _ t).mono (Finset.subset_union_left)).mul (t.mono subset_union_right))
 have hv:= warm_limit Y H V s (aux_test hp)
 apply ge_of_tendsto hv.periods
 filter_upwards [((momentum Y s).comp V.pick.grow_i.tendsto_atTop).eventually (recedes (tent Y H) p)] with r b
 apply ge_of_tendsto (hv.inner (a r))
 filter_upwards [V.pick.pass Y H s _] with u v
 exact gradedLaw Y H s _ _ (p:=v) j z ((t.support _).mono b)
end prior
end FermionSlab
end YM.CF.Buffered.Afterglow.Tower.Reconstruction
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab.chargedGram
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab.odd_bill
