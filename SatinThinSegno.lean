import SatinThinErie
import SatinThinHalo

set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry

open TopologicalSpace
namespace Spine
open Lamour.Bridge.Celeste
open Lamour.Bridge.Celeste.Morn
open Py.Rate.LocalLimit.Papal (Weaver household)
open TopologicalSpace Tapestry.Exhibition
variable (P:Spine)(R : P.Register)(j:Axis)
local notation "φ"=> P.groundZero j
local notation "μ"=> P.pillars j
local notation "W"=> P.calibration
local notation "Q"=> P.par.block
local notation "ℓ"=> P.calibration.ℓ
open Papal Regis.Head Gleam
/-! # Price of ensemble-of-trips. Exactly composed on printed test level before estimation. -/
open Clock Clock.Hookah Clock.Hookah.Blaze
open Preparation.Yoke Yoke.Travel Regis.Head.Garland
open QuadClock Again Pressure
variable {s t f r v i k:ℕ}
local notation "Y"=> P.run
local notation "Λ"=> P.par
local notation "L"=> P.par.R.L
local notation "H"=>P.large
local notation "F" s:max=>hat P.par.R.L P.par.x s
local notation "N" s:max i:max => Journey.side P.run i s
/-! # Train cost comparison on elected printed heights. -/
-- support of tested pair. Need dSpacing condition eventually at roots. Using real checkpoint geometry. Only prices here. 
variable (X:Cover){C e A:ℝ}{d:ℕ}
open CF.Pannier.Chancel CF.Py.Rate.LocalLimit.Preparation.Yoke
local notation "aK"=>P.nomadic
local notation "bK"=>P.engine
set_option linter.unusedSectionVars false
-- One common regulator convergence workflow. P HERE chosen Station. 
variable {a s1 s2 t1 t2:ℕ}
abbrev planeCost (F0 F' :Family P.calibration): Family P.calibration :=mirror P.calibration j 0 F0 * F'
abbrev sharpCost(s i:ℕ):= Journey.sharp P.run P.large s (P.nomadic i) (P.engine i)
abbrev bills (s i:ℕ)(F0 G0:Family P.calibration):= P.sharpCost s i (P.planeCost j F0 G0)
lemma estimator {S T:Finset Cover}(y:P.Vox j s)(z:P.Vox j t)(h:InTest P.calibration true S false y.val)(g:InTest P.calibration true T false z.val)(p:s ≤ v)(q:t ≤ v):
  Tendsto (fun i=> P.bills j v i (P.coastT s v i S y.val) (P.coastT t v i T z.val)) atTop (𝓝 (inner ℂ (P.piece j s y) (P.piece j t z))):=by
 let C:=P.history.circuit; let y': Choir Y H j 0 false:=⟨s,y⟩; let z': Choir Y H j 0 false:=⟨t,z⟩; let W':=show _root_.YM.Kernel.Gram _ from P.room j; let A:=freeze Y H s j 0 false y; let B:=freeze Y H t j 0 false z
 have ht:= sees Y H P.law P.history j 0 s t S T (x:=A) (y:=B) h g v p q;
 unfold stageGram at ht; rw [area0] at ht; rw [show inner ℂ (P.piece j s y) (P.piece j t z)= _ from W'.measure y' z']; exact ht
-- bound pay on stacked
variable {u z t':ℂ}(i:ℕ){t₀:ℕ}
lemma price_delta₀ (u z:ℂ)(p:Ferry P.run s (P.nomadic i) (P.engine i)){x y:Family P.calibration}{S T:Finset Cover}(v:InTest P.calibration true S false x)(q:InTest P.calibration true T false y) :
  P.bills j s i (u • (z • x - y)) (u • (z • x-y))= star u*(u*(star z*(z*P.bills j s i x x-P.bills j s i x y)-(z*P.bills j s i y x-P.bills j s i y y))):=by
 let b(x y:Family W) := bills P j s i x y; let d:=mirror W j 0; let τ:=sharpCost P s i; have hf:∀ (x y a:Family W), d (x-y)=d x-d y:=fun x y _=> foil W
 have a_ (v:ℂ)(x y:Family W): b (v • x) y= (star v)*b x y:=by unfold b bills planeCost; rw [mirror_scale,Algebra.smul_mul_assoc]; exact sharp_scale ..
 have b_ (v:ℂ)(x y:Family W): b x (v • y)= v*b x y:=by unfold b bills planeCost; rw [Algebra.mul_smul_comm]; exact sharp_scale ..
 let V:= volumeAround Λ P.width 0 S; have ht(x y z:Family W)(u:TestFamily W true (d x))(t:TestFamily W true (d y))(q:TestFamily W true z): b (x-y) z=b x z-b y z:=by change τ (d (x-y)*z)=_; rw [hf x y z,_root_.sub_mul]; exact sharp_sub Y H s (u.mul q) (t.mul q) p -- V implicit?
 have h2(x y z:Family W)(u:TestFamily W true (d x))(v:TestFamily W true y)(w:TestFamily W true z): b x (y-z)=b x y-b x z:=by change τ (d x*(y-z))=_; rw [mul_sub]; exact sharp_sub Y H s (u.mul v) (u.mul w) p
 let y':= d y; have r0(x:Family W)(S:Finset Cover)(t: InTest W true S false x): TestFamily W true (d x):= aux_test (axial W j 0 t); have p1:=r0 _ S v; have p2:=r0 _ T q; have h0:= aux_test v; have h1:=aux_test q; have tt:= InTest.smul z v; -- TestFamily subtract lemma
 let x':= z • x; change b _ _= star u*(u*(star z*(z*b _ _-b _ _)-(z*b _ _-b _ _)))
 rw [a_,b_,ht _ _ _ (r0 _ S tt) p2 (aux_test (Tower.InTest.subOp (tt.mono (show S⊆ S∪ T from subset_union_left)) (q.mono subset_union_right))), a_, h2 _ _ _ p1 (aux_test tt) (aux_test q), h2 _ _ _ p2 (aux_test tt) (aux_test q),b_,b_]; -- expected order? a_ outer with y smul right
abbrev vivid (f r v:ℕ)(a:ℝ)(y: P.Vox j v)(z:P.Vox j r): (P.Hil j):= (↑(zoomM P.par.R.L^(r-f)):ℂ) • ((a:ℂ) • P.piece j v y-P.piece j r z)
variable {i}{b A:ℝ}{δ:ℕ→ℝ}{κ:ℕ→ℕ}(K:lender A C f r v δ b κ P)(p:Plans j X f P)
local notation "τ" s:max=> P.flume j X s p
local notation "λξ" s:max i:max=>sharpCost P s i
local notation "πx" s:max=> frameOne (P.clockPlate f s X)
local notation "X₀"=>P.vivid j f r v b (τ v) (τ r)
abbrev voter (i:ℕ) (f r v:ℕ)(X:Cover)(b:ℝ):=P.bills j v i (P.bookT i f r v b X) (P.bookT i f r v b X)
include K
lemma thread_count : Tendsto (fun i=>P.voter j (κ i) f r v X (δ (κ i))) atTop (𝓝 (inner ℂ X₀ X₀)):=by
 let y:= τ r; let z:= τ v; let Z(s:ℕ):= τ s; let S(s):= (frameOne (P.clockPlate f s X)); let NU(s:ℕ)(i):=P.coastT s v i (S s) ((Z s).val); let T (s t c):= bills P j v c (NU s c) (NU t c); let WZ(s:ℕ):=(P.piece j s (Z s)); let F'(s t:ℕ):= inner ℂ (WZ s) (WZ t)
 let a(s:ℝ):=(s:ℂ); let A:= a (zoomM L^(r-f)); let g(w x y z u:ℂ):= (star A)*(A*(star w*(w*x-y)-(w*z-u))); have hp:=K.earn.tendsto_atTop; have hv:=K.treasury.step; have Hq(s t:ℕ)(p:s≤v)(q:t≤v): Tendsto (T s t ∘ κ) atTop (𝓝 (F' s t)):= (P.estimator j (Z s) (Z t) (P.basesT (s:=s)) (P.basesT (s:=t)) p q).comp hp;
 let τ':=a ∘ δ; let y₂:= a b; have ht:Tendsto (τ'∘κ) atTop (𝓝 y₂):= Complex.continuous_ofReal.continuousAt.tendsto.comp K.future; let f':= (fun i=> g (τ' (κ i)) (T v v (κ i)) (T v r (κ i)) (T r v (κ i)) (T r r (κ i))); have h:Tendsto f' atTop (𝓝 (g y₂ (F' v v) (F' v r) (F' r v) (F' r r))):=( (ht.star.mul ((ht.mul (Hq v v le_rfl le_rfl)).sub (Hq v r le_rfl hv))).sub ((ht.mul (Hq r v hv le_rfl)).sub (Hq r r hv hv))).const_mul _|>.const_mul _
 unfold vivid; rw [inner_smul_left,inner_smul_right,inner_sub_left,inner_smul_left]; simp only [inner_sub_right,inner_smul_right]; -- ring? inner Right multiplier on complex at outer a
 refine h.congr' ?_
 filter_upwards [hp.eventually (P.history.finance v)] with i VZ; change _= bills _ _ _ _ _ _; apply Eq.symm
 have he:NU v (κ i)= (Z v).val:=by unfold NU coastT; rw [Nat.sub_self]; rfl
 have hu:= P.price_delta₀ j (κ i) A (τ' (κ i)) VZ (show InTest _ true (S v) false (NU v (κ i)) from he.symm ▸ (show InTest _ true (S v) false (Z v).val from P.basesT)) (show InTest _ true (volumeAround Λ P.width (v-r) (S r)) false (NU r (κ i)) from prepared_train Y H r (S r) _ _ _ P.basesT); conv_lhs at hu => simp only [he]
 exact hu
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.thread_count
