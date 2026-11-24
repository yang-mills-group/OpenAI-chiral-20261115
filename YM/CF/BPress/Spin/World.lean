import YM.CF.BPress.Spin.Cooks
import YM.CF.BPress.Actual
/-! End of `VolumeB-op` step of manuscript: packaging phase on trajectories. Needs the path and pair bits qualifying pointwise; this theorem does not say the naked unconditioned pairing has this value. Any M∗ Teller. Receipts exported from Spin (joint cost certificates feed linked estimates). -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Spin
open Function MeasureTheory Filter Finset Lattice RG Precision Pressure
open NormedSpace SU Lat Cube Py Vale Vale.Grace Paige Scree Skye Tulip Fock Fixed Dial Spire Hole Pf Stride Paint Nacre Laic Tenant
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Hole
attribute [local instance] opCStarAlgebra
variable {B M s:Side} {K:Teller SU.group}{R:Patch}{L:ChartRatio SU.group}
  (V:Grace K R L){d:ℝ}{U:Grasp V.U B d}{W:GivenX V U}(N0:ℕ){Mstar:Side}(J:Robes Mstar V W)(q:Push.SectorMeasure.Chi)(h:ℝ)(R0 δ:ℝ→ℝ)
def First(V: Grace K R L): Pledge:= ⟨V.f,V.F1,V.width1,V.pos1⟩
def Second(V: Grace K R L): Pledge:= ⟨V.g,V.F2,V.width2,V.pos2⟩

variable {x : ℝ}{n : ℕ}
variable {V N0 J q h R0 δ} (X: History V N0 J q h R0 δ x M n)

lemma binderT{Y:GramM (mid M B)}{T:Loom (mid M B)}(X:Mantle (x:=x) V J h M Y T) : (Y.J.P).toll (First V).rate (Second V).rate (First V).price (Second V).price:=by
 change Y.J.P.toll V.f V.g V.F1 V.F2; rw [←W.h1,←W.h2,←W.h3,←W.h4]; exact X.close.leanJ.1 -- tune Γ implicit

-- use after history bound, volume s arbitrary under sizing; auxiliary realization supplied through career-level Lamp (the Loom threshold required here isn't the angular threshold itself).
variable {A:Type}{r':ℝ}{e ρ σ u v κ b : ℝ}{P:Pledge}{p₀ n₀ χ:ℕ}{TellerH:Worthy P (First V) (Second V) K.j e b u χ}{D:Side} (Vw:Voucher TellerH D ρ σ v p₀ n₀ κ r')
local notation "Nδ(" j ")" => cell M B R.L j
include Vw
lemma reading_point (w:ℕ)(g:w≤n)(p:n₀ ≤ (Nδ(w)).val){G: BandWidth}{N:Bands (More (Nδ(w))) G}(t:G.D=D.val)(h:d≤ e)(a:Orbit (Nδ(w))) (H: Support (Nδ(w)))(f:Dark N H) (Y:Stun (Nδ(w)))(z:Slow (X.Y w a) (hook Y) W.pearl.q) (C C' : ℝ→Paint (More (Nδ(w))))(J:Looks (X.Y w a) H C C' p₀ ρ σ b r') (y:C 0= fun i=> SU.Pair.fullM (hook Y i)) : let S:= Locks H true; let T:=Locks H false; let R':= X.Y w a; let N₀:= X.E w; let M':=N₀.J.M; let Y':= spar K.j M' R'; let Z':= Ts N₀.J.P Y' R'; let ω:= zen (Spire.hum (Vale.mesh M R.L w) B (U.cost (Vale.mesh M R.L w) M') R' Y); let X':= coupling ∘ C; let D':= coupling ∘ C'
   Issued S T Y' Z' X' D' v κ ∧ inner ℂ (braC S T (X' 2)) (relV U N₀.J R')= Complex.exp (Pf.totalBill S T Y' Z' X' D'-ω) :=by
 intro S T R' Vg M' Y' Z' ω X' D'
 let Q:=mantel X g; let F:= Q.crown; have hx:Shelf (Nδ(w)) d K.j P:=(TellerH.speed _ W.health h (Vw.ok.trans p)).1; let A:OpenW (Nδ(w)) d:= ⟨_,F.paid a⟩ -- tune
 have pL:= Q.rest; have he:Issued S T Y' Z' X' D' v κ:= point Vw p W.health h M' (X.E w).J.P (binderT Q) A t H f C C' J; refine ⟨he,?_⟩
 let u:= changeM (m:=Vale.mesh M R.L w) U R' M'; have hu:Sea Y' u:=sea_g pL R' A.property M'; have hl: X' 0=postC Y:=by unfold X' Function.comp; rw [y]; rfl -- tune
 have hk:= Issued.pivot_cost he.birth; let t:= uPivot Y' (X' 0); have ht:‖coneP K.j M' R' Y‖= ‖filled Y' (X' 0)‖:=by rw [hl]; rfl
 have Ht:= Spire.change_v W.pearl V.note pL TellerH.above M' R' A.property Y z _ (hk.trans ht.symm); let p:=he.offset_bill (topOnSea he.proj hu) hu.2 ω (by simp [ω,zen]) (by rw [show filled Y' (X' 0)= coneP K.j M' R' Y from (by rw [hl]; rfl)]; exact Ht) -- pin tune
 change inner ℂ _ (acts (exp (dg Z')) u)=_; rw [tallied Z' he.she.nil]; change inner ℂ _ (acts (quant (1+Z')) u)=_; rw [show acts (quant (1+Z')) u=craft Y' Z' u 1 by unfold craft zom; rw [one_smul]]; exact p
end YM.CF.BPress.Spin
#print axioms YM.CF.BPress.Spin.reading_point
