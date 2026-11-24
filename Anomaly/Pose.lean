import Anomaly.PitchMark
/-!
Translations across the matter torus. Besides the account for moving the
kernel expansion (`Trunk.transportSweep`), these are pointwise, pinned
valuation laws at all Pane pairs. No tying assumptions on Tests.
-/
set_option synthInstance.maxSize 24000
set_option autoImplicit false
noncomputable section
namespace YM.CF.Swell
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Skye Jet Scroll Finset
open RG MeasureTheory Salt Metric Drapes Tulip Lat Branch Cube Tenant Rill
open Buffered StressExchange
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Tap Levier Moto Oath Font Haro Spire Dial
variable {N : Side}
local notation "Ω" => Single N

lemma tick_taxi (t:Site N) : twist (γS (taxiPlus t)) (tickA N)=tickA N := by
  have hu:JetS 1 false false (spinU false 1):=det_i ▸ spinZ false 1
  rw [touchP]; exact tickR (castX (taxiPlus t)) (xtra false) (spinU false 1) hu N -- tune

lemma taxi_chain (t u:Site N): taxiPlus t*taxiPlus u=taxiPlus (t+u) := by
  change Sweep.mk (1*1) (t+ Signed.act 1 u) (false.xor false)=Sweep.mk 1 (t+u) false
  simp

lemma co_compose (t u v:Site N)(X:SOp N)(V: Pane N) :
    co_Ψ t u (co_Ψ u v X) (profile V)=co_Ψ t v X (profile V) := by
  let a:= t-u; let b:=u-v
  have he:taxiPlus a*taxiPlus b= taxiPlus (t-v):=by rw [taxi_chain,show a+b=t-v from (by unfold a b; abel)]
  let L:= γS (taxiPlus (t-v))
  apply (twist L).injective
  change ech (taxiPlus (t-v)) (co_Ψ t u (co_Ψ u v X) (profile V)) = ech (taxiPlus (t-v)) (co_Ψ t v X (profile V))
  rw [show ech (taxiPlus (t-v)) (co_Ψ t v X _)=X _ from julius (taxiPlus (t-v)) X V]
  rw [← he, ← Sour.paceK (taxiPlus a) (taxiPlus b) (co_Ψ t u (co_Ψ u v X) (profile V)), show ech (taxiPlus a) (co_Ψ t u (co_Ψ u v X) _)=_ from julius (taxiPlus a) (co_Ψ u v X) V,
    show ech (taxiPlus b) (co_Ψ u v X _)=_ from julius (taxiPlus b) X (flashA (taxiPlus a) V), lights]

lemma taxi_action (t u v:Site N)(X:SOp N)(V: Pane N) :
    twist (γS (taxiPlus (t-u))) (co_Ψ t v X (profile V))= co_Ψ u v X (profile (flashA (taxiPlus (t-u)) V)) := by
  rw [← co_compose t u v X V]; exact julius _ _ V

lemma co_unit (t:Site N)(X:SOp N)(V:Pane N) : co_Ψ t t X (profile V)=X (profile V):=by
  have q:= julius (taxiPlus (t-t)) X V
  simp only [sub_self,show taxiPlus (N:=N) 0=1 from rfl, rev1,beat_x] at q
  simpa only [co_Ψ,sub_self,show taxiPlus (N:=N) 0=1 from rfl] using q

lemma preJ_moves (M:Op (Single N))(t:Site N): twist (quantU (γS (taxiPlus t))) (preJ (tickA N) M)=preJ (tickA N) (twist (γS (taxiPlus t)) M) := by
  let S:=tickA N; let L:=γS (taxiPlus t)
  have u:twist L S=S:=tick_taxi _
  have he:= trace_twist L (S*M)
  change twist _ (Matrix.trace (S*M) • 1+dg (S*M*(1-S)))= Matrix.trace (S*twist L M) • 1 +dg (S*twist L M*(1-S))
  rw [map_mul,u] at he; rw [he,map_add,twist_scalar,map_one,dg_cov]; simp only [map_mul,map_sub,map_one,u,L]

-- Act of a *pose at y*, from field values at translated test
-- (orientation from taxiPlus cities, incl wrap). Not imposing any
-- Pose-changing-counter charge in the birth budget here. Multipliers,
-- adjoint updates checked separately for true RP poses.
variable (O y:Site N) {b:BudgetPoint}{r k : ℕ}{t d a v:ℝ}

variable {F G : SOp N} {K:Scree.Loom N}
    {a' v' : ℝ} (h:Roof N t d r K) (l:0<d)(f:Trunk (node O) F k a v d)(g:Trunk (node y) G k a' v' d) (p:b.threshold ≤ t)(q:k+r+10≤b.B)
    (gt:∀ U:Pane N, G (profile U)=co_Ψ y O F (profile U))
local notation "H" => γS (taxiPlus (y-O))
include h l f g p q gt

lemma pin_taxi (x : Pane N) : twist H (pinMatrix b K (node y) G x) = pinMatrix b K (node O) F (flashA (taxiPlus (y-O)) x) := by
  obtain ⟨Z,gZ⟩ := (Skye.sepT (n:=N)).exists
  let s:=taxiPlus (y-O)
  let z:Orbit N:=(x,Z); let w:Orbit N:=(flashA s x,bun s Z)
  change twist H (pinMatrix b K (node y) G z.1)=pinMatrix b K (node O) F w.1
  have hm: halo b.B {node O}=actY s (halo b.B {node y}):=by
    rw [←walkA]; apply congrArg
    unfold actY; rw [map_singleton]
    change ({node O}:Support (More N))={ (boxA s).symm (node y) }
    rw [show node y = boxA s (node O) from (by rw [platforms,add_sub_cancel]),Equiv.symm_apply_apply]
  have hz:w∈ pingMask b (halo b.B {node O})↔z∈ pingMask b (halo b.B {node y}):=by
    rw [hm]; exact glowA ..
  rw [pinMatrix_eval h l g p q z,pinMatrix_eval h l f p q w]
  by_cases u:z∈ pingMask b (halo b.B {node y})
  · rw [Set.indicator_of_mem u,Set.indicator_of_mem (hz.mpr u),gt, show K w=flashA s (K z) from h.move x Z s gZ]
    exact julius _ F _
  rw [Set.indicator_of_notMem u,Set.indicator_of_notMem (mt hz.mp u),map_zero]

def translatedFields {N:Side}(t:Site N)(X:Fields N):Fields N:=Prod.map (flashA (taxiPlus t)) (flashA (taxiPlus t)) X

lemma spin_taxi (x:Fields N) : twist (quantU H) (spinMark b K y G x)= spinMark b K O F (translatedFields (y-O) x) := by
  rw [spinMark,spinMark,preJ_moves,pin_taxi O y h l f g p q gt]; rfl

lemma gauge_taxi (x:Fields N) : twist (quantU H) (gaugeMark b K y G x)=gaugeMark b K O F (translatedFields (y-O) x) := by
  change twist _ (Matrix.trace _ • _)= Matrix.trace (pinMatrix b K (node O) F (flashA (taxiPlus (y-O)) x.1)) • _
  rw [twist_scalar,map_one,←pin_taxi O y h l f g p q gt,trace_twist]

lemma move_taxi (x:Fields N)(m:Site N):
    twist (quantU H) (moveMark b K y (y+m) G x)=moveMark b K O (O+m) F (translatedFields (y-O) x) := by
  have hv(U:Pane N) : co_Ψ (y+m) y G (profile U)=co_Ψ (y+m) (O+m) (co_Ψ (O+m) O F) (profile U) := by
    rw [co_compose (y+m) (O+m) O F U]
    let a:=taxiPlus ((y+m)-y)
    apply (twist (γS a)).injective
    change twist (γS a) (co_Ψ (y+m) y G (profile U))=twist (γS a) (co_Ψ (y+m) O F (profile U))
    rw [taxi_action (y+m) y O F U]
    rw [← gt (flashA _ U)]
    exact julius _ _ _
  have hp := spin_taxi (O+m) (y+m) h l (f.station (O+m)) (g.station (y+m)) p q hv x
  rw [show y+m-(O+m)=y-O from (by abel)] at hp; exact hp

omit h l f g p q gt
lemma mark_here (V:Fields N): moveMark b K y y G V=spinMark b K y G V:=by
  unfold moveMark spinMark pinMatrix
  by_cases z : pingS b.threshold (halo b.B {node y}) V.1
  · have hz : V.1 ∈ {U:Pane N|pingS b.threshold (halo b.B {node y}) U} := z
    simp_rw [Set.indicator_of_mem hz,co_unit]
  have hz : V.1 ∉ {U:Pane N|pingS b.threshold (halo b.B {node y}) U}:= z
  rw [Set.indicator_of_notMem hz,Set.indicator_of_notMem hz]

variable {Y Z:Axis→ SOp N}(wg : ∀ i:Axis, Trunk (node O) (Y i) k a v d)(wZ: ∀ i:Axis, Trunk (node y) (Z i) k a' v' d)
include h l f g p q gt wg wZ

lemma joint_taxi (H' : ∀ i:Axis,∀ U:Pane N,Z i (profile U)=co_Ψ y O (Y i) (profile U)) (m:ℕ)(x:Fields N) :
    twist (quantU H) (jointMark b K y m G Z x)=jointMark b K O m F Y (translatedFields (y-O) x) := by
  simp only [jointMark,diffMark,Pi.add_apply,Finset.sum_apply,map_add,gauge_taxi O y h l f g p q gt x,map_sum]; apply congrArg; apply sum_congr rfl; intro i _
  rw [Pi.sub_apply,Pi.sub_apply,map_sub]; simp only [sub_eq_add_neg (b:=gapPlus (N:=N) i m), move_taxi O y h l (wg i) (wZ i) p q (H' i)]
end YM.CF.Swell
