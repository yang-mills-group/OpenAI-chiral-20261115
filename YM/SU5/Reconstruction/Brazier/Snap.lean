import YM.SU5.Reconstruction.FirstWindows.Sharp
/-! All the way to a microscopic realization of the chosen character.

The UV horizon may change with the visit. At every cap, can really dispense with all consultations of second link/tags **in the evaluation there** even though the scaffolds permit **arbitrary bounded Borel** tests on the joint Gauge. We use the actual UV-path -coherence of taking `$D=0` of this denZ on all flagged configs and use the clear-case form otherwise; don't assert narrow queries advance only to narrow footprints among period-independent Mark morphology! This is WHOLE sharp path evaluation on individual torus, not conditioning on any invented scenario nor asking that Mark itself well-defined there without funding. `collapse` to actual evaluations. -/
set_option autoImplicit false
set_option synthInstance.maxSize 31000
set_option maxRecDepth 6200
set_option maxHeartbeats 400000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.Brazier
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry Altitude Exhibition Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation SlabMark MeshClock
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
variable {L : Rack Λ l} {B : Clay Λ l} (Z : Exhibition Y H i k I E L B)
variable (j : Axis) (C : Arena Y H G.history.circuit j 0 false)
  (χ : displayAlgebra Y H V G.history G.clipped j false C →⋆ₐ[ℂ] ℂ)
local notation "Gt" => marks (timeMesh Λ)
local notation "t₀" => insideAt Λ l (tent Y H)
local notation "D" => Domain Y H G
local notation "A"=> Ark.Ht Y H G.history.circuit j 0 false C
local notation "Π"=>Aurora Y H V G.history j false C
local notation "Kx" t:max=> vistaFinish Y H t Z
open Fock Lat Laurent Wilson Cube Finset Branch Scree RG Spire Vale Pastry Peaks Dial Phase
  Lifted Skye Tapestry.Exhibition Tapestry.Altitude Tenant Rush Tulip
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
namespace SingleFrame
variable {n:Side}
abbrev collapse (X':Mark n) : Pane n → FC (Single n):=fun x=> X' (x,x)
lemma narrow {b:Bool}{S:Support (More n)}{X':Mark n}(p:AtSupport b S X'): AtSupport b S (toMark (collapse X')):=
 AtSupport.fromEval (collapse X') (Push.SectorMeasure.Env.along p.env (show Measurable (fun x:Pane n=> (x,x)) from measurable_id.prodMk measurable_id)) (fun x y t=> p.dep (x,x) (y,y) t t) (fun x=>p.allV (x,x)) -- namespaces
lemma preserve_gauge {f:Mark n}(p:Buffered.covariant f): Buffered.covariant (toMark (collapse f)) := fun g x=> p g (x.1,x.1)
variable (m u:ℕ)
local notation "z₀"=> Y.uv u
local notation "v'"=> Journey.side Y m
local notation "R"=> Journey.side Y m (Y.uv u)
local notation "P₀"=> Y.meter.a (Y.uv u)
local notation "L₀"=> (Y.voyage m).CapeT z₀
local notation "Gr"=> ((Y.voyage m).X z₀).gram z₀
local notation "D₀"=>Λ.U
local notation "Zn"=> capP (K:=Λ.K) Λ.U (Gr).beta (P₀) (m:=mesh (Y.ir m) Λ.R.L (Y.uv u))
lemma drawMask (x:Orbit (Journey.side Y m (Y.uv u))) (p: RG.flags (Y.meter.a (Y.uv u)).threshold x.1=∅) : drawn ((Y.voyage m).CapeT (Y.uv u)) x=(x.1,x.1):=by
  obtain ⟨y,v⟩:=x; refine Prod.ext rfl (funext fun i=>?_)
  exact (Papal.roofage Y m z₀).lamp y v i (by simp [PhaseChoice.growFlags Y m u (p : RG.flags (Y.meter.a z₀).threshold y=∅)])
noncomputable def frameCharge (X':Pane (Journey.side Y m (Y.uv u))→ FC (Single (Journey.side Y m (Y.uv u))))(x:Pane (Journey.side Y m (Y.uv u))) : ℂ:=
 inner ℂ (mateK R) (acts (X' x) (Zn x))
-- not integrating over frames. The phase is the actual prescribed one.
lemma charged_real (f:Mark (Journey.side Y m (Y.uv u))) (x:Orbit (Journey.side Y m (Y.uv u))) :
    inner ℂ (mateK R) (acts (f (drawn L₀ x)) (denZ (Gr) Λ.U L₀ x)) = frameCharge Y m u (collapse f) x.1 :=by
 by_cases p: RG.flags (P₀).threshold x.1=∅
 · rw [drawMask Y m u x p, Y.whole]; rfl
 rw [bare_dark Y m u x f p]; unfold frameCharge; rw [capP, Set.indicator_of_notMem (show x.1∉_ from p),map_zero,inner_zero_right]
noncomputable def capAccount (X': Pane (Journey.side Y m (Y.uv u)) → FC (Single (Journey.side Y m (Y.uv u)))): ℂ :=
 ∫ x, frameCharge Y m u X' x ∂ (prior SU.group (More (Journey.side Y m (Y.uv u))))
noncomputable abbrev topBond : ℂ := partitionZ (( (Y.voyage m).X (Y.uv u)).gram (Y.uv u)) Λ.U ((Y.voyage m).CapeT (Y.uv u))
-- Account integrable on single-link law. also topBond can be processed as account 1.
local notation "X₀"=> Altitude.Cloud (Dome (tent Y H))
noncomputable abbrev Tag (f:Altitude.Cloud (Dome (tent Y H))) : Mark (Journey.side Y m (Y.uv u)):= attire (breathing Y H (Y.uv u) m u f)
noncomputable abbrev priorY (Λ:Preparation){l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(m u:ℕ) := prior SU.group (More (Journey.side Y m (Y.uv u)))
set_option maxHeartbeats 600000 in
lemma bond_budget (f : Altitude.Cloud (Dome (tent Y H))) (p:f∈shorter (Dome (tent Y H)) (Y.uv u))(q:Tapestry.Pay Y (Y.uv u) m u):
    Integrable (frameCharge Y m u (collapse (Tag Y H m u f))) (priorY Λ Y m u) ∧ topBond Y m u ≠ 0 ∧ taking Y H m u f=capAccount Y m u (collapse (Tag Y H m u f))/topBond Y m u:= by
 obtain ⟨a,b,h⟩:= taking_formula Y H (Y.uv u) m u f q p; let T:= Tag Y H m u f
 let G'(x: Pane R):= frameCharge Y m u (collapse T) x
 let V'(x:Orbit R):= inner ℂ (mateK R) (acts (T (drawn L₀ x)) (denZ Gr Λ.U L₀ x))
 change Integrable V' (city R) at a; change _= (∫ x,V' x∂city R)/_ at h
 have he(x:Orbit R): V' x= G' x.1:= charged_real ..
 have ht(x:Pane R): (∫ t : Ids R,V' (x,t)∂depot R)=G' x:=by simp_rw [he]; rw [integral_const, probReal_univ, one_smul] -- tune
 refine ⟨?_,b,?_⟩
 · have hp:= (show Integrable V' ((priorY Λ Y m u).prod (depot R)) from a).integral_prod_left
   have hh : (fun x:Pane R=> (∫ t:Ids R,V' (x,t)∂depot R))=G':=funext ht
   erw [hh] at hp; exact hp
 rw [h, city, integral_prod V' a]; simp_rw [ht]; rfl
include H in
lemma uncondition (q:Tapestry.Pay Y (Y.uv u) m u): capAccount Y m u 1= topBond Y m u:=by
 obtain ⟨a,b,h⟩:= bond_budget Y H m u 1 ((shorter ..).one_mem) q; rw [show Tag Y H m u 1=(1:Mark R) from ?_] at h; rw [show taking Y H m u 1=1 from ?_] at h
 · exact (eq_div_iff b).mp h |>.symm.trans (one_mul _) -- direction? `(1*b=k)` ⇒ he.trans..? 
 · exact takingUnit Y H m u q.1
 unfold Tag breathing; rw [Decking.crown1]; rfl
end SingleFrame
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.Brazier
