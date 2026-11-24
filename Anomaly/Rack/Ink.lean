import Anomaly.Rack.Singleton
import Anomaly.Rack.Letters
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Vow.TreasuryFog
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tenant Tulip
open Pastry Hake Peaks Fock Branch Drapes Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Palot Cadre Rill Stax Rive Ione Larch Roots Push.AbsoluteSums.Trees Sour Py Py.Rate Py.Rate.BScale Mew PowerSeries
open scoped Mew
open Swell Buffered Exa Sault

variable {n N B:Side}
local notation "Ω" => mid N B
variable {K:Scree.Loom (mid N B)} {j:ℕ}{L:Side}{ho:Odd L.val}{Y:Pricing j L ho (Thread j)}{e:ℝ}(U:Grasp Y B e)
variable (R:GramM (mid N B))(A : Scree.Loom (mid N B))
variable {d h g:ℝ}{I:Type}[LinearOrder I][Fintype I]
    (o:I→Site (mid N B))(δ:ℕ)(M':I→Vow.Cusp (mid N B)) -- unused
variable (V:I→ phy (mid N B))(F:I→ Mark (mid N B))(S:I→Support (More (mid N B))) (W:I→ Bag (mid N B))
variable (C:Occlus R.p)(σ:I→Seat (mid N B)) {a:ℝ}
    {p_ D:I→Aura (mid N B)→ℝ}
    (T:∀ (i:I)(X:Aura (mid N B)),Flight R.p δ X h (W i X) (p_ i X) (D i X))
variable (Karm: Key I→ Cadre.Rinse (Seat (mid N B)) (Copy (mid N B)))
local notation "FineP"=> fun z:Key I=>pinSeries W z
variable (r: Cadre.Tape (A:=Seat (mid N B)))
variable (X: OrbitRack C σ δ R.K h Karm (∑ i:I,p_ i) (∑ i:I,D i) r (fun z x Y=> pinSeries W z Y x))
variable {E:I→ RegBudget (mid N B)}
variable (t:Ids (mid N B))(k s:ℕ)
local notation "FΛ" => awake σ (lensD (P:=R.p) R.K Karm k t) E
local notation "KΛ" => bustle σ (lensPort (P:=R.p) R.K Karm k)
variable (l:List I)(v: ψS σ l) (hh:l.length ≤ k)
variable (hS: l.Pairwise fun i j=>Disjoint (S i) (S j))(H:∀ i,Contact A (S i) (F i) (V i)) (h_:1≤h)
variable (coneR:∀ i:I,Nest U R A δ 24 (σ i) h a (V i) (W i) g d)(hp:1≤k)
include v hh hS H h_ coneR X hp

lemma endK (u:Orbit (mid N B))(w:Rue.FleetS R.p.threshold u.1) -- tune
 (s:IsStarProjection (Dial.spar j R.J.M (A u)))(b:∀ i:I, SpanTip R.p (E i) (σ i) Karm t i):
    letterRead ((l.map F).prod (u.1,A u)) (denZ R U A u)= beamZ _ (tipI (fun z=> denZ (slither (R:=R) Karm σ k t E z) U A u) l) := by
  have he:∀ z:Key I,z∈hill I→∀ p:Wave (Dwell Ω), pilotH U R A u s (acts (∑ i:Aura Ω,pinSeries W z i u) p)= acts (Liss.waveΦ (fun i=> V i u) z) (pilotH U R A u s p):=by
    intro z _ p
    unfold pinSeries Liss.waveΦ; simp_rw [Finset.sum_apply,Pi.smul_apply]; rw [Finset.sum_comm]
    have hy(i:I): (∑ X:Aura Ω, z i • W i X u)=z i • (∑ X:Aura Ω,W i X u):=(smul_sum ..).symm
    simp_rw [hy, act_sum, map_sum]; refine sum_congr rfl ?_; intro i _; rw [act_smul,act_smul,map_smul,(coneR i).science u s p]
  have hz:= rackKey U A u C Karm σ δ _ X k h_ t s l v E (fun i w=> conducts C Karm σ δ _ X k h_ t i hp E (b i) w) -- tune order
  rw [hz (fun i=> V i u) w hh (Contact.commuteStack H hS u) he]; exact Contact.stencil H hS u _

lemma endVector (u:Orbit (mid N B))(w:Rue.FleetS R.p.threshold u.1) -- tune
 (s:IsStarProjection (Dial.spar j R.J.M (A u)))(b:∀ i:I, SpanTip R.p (E i) (σ i) Karm t i):
    tipI (fun z=> denZ (slither (R:=R) Karm σ k t E z) U A u) l=acts ((l.map fun i=>V i u).prod) (denZ R U A u) := by
  have he:∀ z:Key I,z∈hill I→∀ p:Wave (Dwell Ω), pilotH U R A u s (acts (∑ i:Aura Ω,pinSeries W z i u) p)= acts (Liss.waveΦ (fun i=> V i u) z) (pilotH U R A u s p):=by
    intro z _ p
    unfold pinSeries Liss.waveΦ; simp_rw [Finset.sum_apply,Pi.smul_apply]; rw [Finset.sum_comm]
    have hy(i:I): (∑ X:Aura Ω, z i • W i X u)=z i • (∑ X:Aura Ω,W i X u):=(smul_sum ..).symm
    simp_rw [hy, act_sum, map_sum]; refine sum_congr rfl ?_; intro i _; rw [act_smul,act_smul,map_smul,(coneR i).science u s p]
  have hz:= rackKey U A u C Karm σ δ _ X k h_ t s l v E (fun i w=> conducts C Karm σ δ _ X k h_ t i hp E (b i) w) -- tune order
  exact hz (fun i=> V i u) w hh (Contact.commuteStack H hS u) he

omit v hh hS H h_ hp coneR
include X h_
local notation "ηG" => lensD (P:=R.p) R.K Karm k t
local notation "ηF" => lensPort (P:=R.p) R.K Karm k

lemma fleshNotes (hU : σ= Cube.node ∘ o)(v:∀ i (A:Scree.Hub (mid N B)), E i A≠0 → σ i∈ A.val.2) : -- tweak
    QuadClock.Notice o FΛ KΛ ∧ ∀ i,νTip FΛ i=E i ∧ QuadClock.emberTip KΛ i= νΦK ηF {i}:=by
  let e:= sealE C Karm σ δ _ X k h_ t
  let f:= sealF C Karm σ δ _ X k h_
  have u(i:I):νTip FΛ i=E i:= value_E σ E ηG i
  have z(i:I):= value_F σ ηF i
  refine ⟨⟨cash0 σ E ηG ηF, fun i=> ?_, eReady σ E ηG,fun i=>?_, fReady σ ηF,fun i w => ?_ ⟩,fun i=> ⟨u i,z i⟩⟩
  · nth_rw 1 [←hU]; exact quietE σ E ηG e v i
  · nth_rw 1 [←hU]; exact quietF σ ηF f i
  rw [u,z]; exact ⟨crest_E σ E ηG i w,crest_K σ ηF i w⟩

lemma eraTender (p:∀ i,IncX primeU (E i) R.p h a) (y:∀ i:I,∀ S:Scree.Hub Ω, S.val.1≠σ i → E i S=0) (Wo:Force_M R.p.B σ s) (w:9*3*s ≤ C.η*(R.p.B:ℝ)^2) (g:0≤a)(z:Key I)(v:∀ i, ‖z i‖ ≤ 2):
    IncX primeU (FΛ z) R.p h (s*(2*a)+sigma (C.η+C.η) R.p.B*yσE R.p C) ∧ Dark primeU (KΛ z) R.p h (Real.exp (3*(s:ℝ))*yσF R.p C):=by
  have hw:4 ≤ Real.exp 3:= le_trans (by norm_num) (Real.add_one_le_exp 3)
  refine ⟨Larch.add_v _ _ _ (composeInc σ E s a g Wo p (zero_le_one.trans h_) (fun i j=>y j i) z 2 (by norm_num) v) (many_e C Karm σ δ _ X k h_ t z v 3 hw (by norm_num) w Wo),force_inc C Karm σ δ _ X k h_ z v 3 hw (by norm_num) ?_ Wo⟩; linarith only [w,Nat.cast_nonneg (α:=ℝ) s]
end YM.CF.Vow.TreasuryFog
