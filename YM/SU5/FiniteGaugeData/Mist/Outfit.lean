import YM.SU5.FiniteGaugeData.Mist.Kodiak
import YM.SU5.FiniteGaugeData.KernelP.Price
/-!
# Spacetime motion on actual retained Pc
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra
open Py Py.Rate LocalLimit Preparation Journey Fiber Vale VolumeCape FullBill
set_option quotPrecheck false
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(h:Real.exp 1≤ Λ.x)
local notation "Kₜ"=> tent Y h
local notation "N₁" i:max s:max=> side Y i s
local notation "Wₐ" i:max s:max => (Y.voyage i).CapeT s
local notation "D₀"=> aliasLaw Λ
local notation "D₁"=> distanceLaw l
local notation "L₁"=> Λ.R.L
local notation "C₀"=> (VolumeCape.Dream.plot l).C
local notation "Xᵣ" i:max k:max=> (Y.voyage i).X (Y.uv k)
local notation "Tᵣ" i:max k:max s:max=> ((Y.voyage i).X (Y.uv k)).gram s
variable (S T: Finset Cover)(s i k:ℕ)
open Nacre Heat Charm Chrono SalonG Journey Hills Playlist Show
namespace Mist
open KernelP
variable {u v:ℕ→ℕ}{I:ℕ→Family (tent Y h)→ℕ→ℂ}{E:ℕ→ Family (tent Y h)→ℂ}{P:Call Λ l}{J:Wicket Λ l}
variable (W':Universal Y h u v I E)(R:Rolled Y h u v J P)(A:∀ a:Axis,Repertory Y h W' R a)
variable {Φ:ℕ→ Charm.W (tent Y h)→ₗ[ℂ]ℂ}(S':Sphere Y h W' R A Φ)
variable (a:Axis)(z:ℤ)(d n:ℕ)
local notation "D"=> Decko Y h a
variable (H:Harbor Y h W' R Φ a)(x y:Decko Y h a)
local notation "Λ₀"=> (A a)
open scoped ENNReal NNReal
variable (X:Engine Y h W' R a H)(b:Axis)(B:List Axis)
abbrev TipH := CoreH (Anteroom X.val)
local notation "Q"=> Anteroom X.val
local notation "T'"=> Terrace.scheduleL
local notation "M"=> TipH Y h W' R a H X
local notation "G"=> regular Y h W' R a H X
protected lemma liveL (A:Preparation) : 1<A.R.L.val:=by have u:=A.R.coarse; omega
#check Mist.liveL
section
include X
lemma home_base (w:ℝ≥0): Commute (regular Y h W' R a H X w) (planeP (GroupR X.val B)):= by
 apply comm_Group; intro i; apply Willow.commute_pay (ScrollQ X.val i); intro v; change Commute _ (ramble X.val i v); unfold ramble; split; exact Commute.one_right _; rename_i e; obtain ⟨j,z,rfl⟩:=(frequentT L₁ v).exists; rw [Driver_eq]; exact regular_coin ..
include S'
variable (m:ℝ≥0)
def coneT (w:ℝ≥0) : (TipH Y h W' R a H X).Op:=social Q ((G) w)
def whimsy (j:Axis) := WindR X.val Terrace.scheduleL (Mist.liveL Λ) (Terrace.scheduleV j)
def combT:=Kodiak.combT (whimsy Y h W' R a H X)
local notation "F₀" i:max=> (coneT Y h W' R a H X i)
local notation "F₁" i:max => (combT Y h W' R a H X i)
local notation "ℙ" i:max x:max => mistU X.val Terrace.scheduleL (Mist.liveL Λ) x i (Terrace.scheduleV i)
omit S'
lemma unit_flow (t:ℝ): mistU X.val Terrace.scheduleL (Mist.liveL Λ) t a (Terrace.scheduleV a)=1:= Kodiak.stream_self T' X.val _ (Terrace.scheduleV a) _
private lemma lock (t:ℝ)(f:H.space.Op)(p:∀ t:VistaQ Λ.R.L, Commute (ramble X.val b t) f) : Commute (ℙ b t) (social Q f):=unitInter _ _ _ t (Terrace.scheduleV _) p
lemma coneComm (t:ℝ) : Commute (mistU X.val Terrace.scheduleL (Mist.liveL Λ) t b (Terrace.scheduleV b)) (coneT Y h W' R a H X m):=by apply lock; intro i; unfold ramble; split; exact Commute.one_left _; rename_i e; obtain ⟨j,z,rfl⟩:=(frequentT _ i).exists; rw [Driver_eq]; exact (regular_coin ..).symm
lemma comb_zero : combT Y h W' R a H X 0 B=1:= Kodiak.comb_zero (whimsy Y h W' R a H X) B
lemma comb_comp (u v:E4): combT Y h W' R a H X (u+v) B=(F₁ u) B * (F₁ v) B:= Kodiak.comb_comp _ B (fun i j t s=> unitAcross X.val j T' _ t (Terrace.scheduleV i) (Terrace.scheduleV j) s) u v
lemma comb_price (x:E4)(v:M):‖combT Y h W' R a H X x B v‖= ‖v‖:= Kodiak.comb_price ..
lemma comb_strong(v:M):Continuous (fun x=>combT Y h W' R a H X x B v):= Kodiak.comb_strong (whimsy Y h W' R a H X) B (fun i=>unitC X.val _ (Mist.liveL Λ) (Terrace.scheduleV i)) v
lemma confluence (x:E4): Commute (combT Y h W' R a H X x B) (coneT Y h W' R a H X m):=Kodiak.confluence (whimsy Y h W' R a H X) _ x _ (fun i=> coneComm Y h W' R a H X i m)
include S'
def casin : OS.Semigroup (TipH Y h W' R a H X) a where
 E:=coneT Y h W' R a H X
 U v:=combT Y h W' R a H X v.val Terrace.scheduleL
 eZero:=by unfold coneT; rw [regular_zero Y h W' R A S' a H X]; exact social_id
 time t s:=by unfold coneT; rw [regular_time Y h W' R A S' a H X]; exact Cot.citizen (home_base Y h W' R a H X Terrace.scheduleL t)
 sym t:=by have hp:= (time_aux Y h W' R A S' a H X).sym t; exact (social_star (U:=Q) ((G) t)).symm.trans (congrArg (fun x:H.space.Op=>social Q x) hp)
 shrinks t:= le_trans (social_bound _) (regular_bounds Y h W' R A S' a H X t)
 uZero:= comb_zero Y h W' R a H X _
 space x y:= comb_comp Y h W' R a H X _ x.val y.val
 unitary y x:= comb_price ..
 independent t y:=(confluence Y h W' R a H X _ t y.val).eq.symm
 continuousU v:=(comb_strong Y h W' R a H X _ v).comp continuous_subtype_val
 continuousE v:=(dip Q).continuous.comp (regular_all Y h W' R A S' a H X (cpo Q v))
-- identification.U core.
omit S' in
lemma core_tick (h₀:b≠a): (ℙ b (spinT L₁ s z))=social Q (X.val.stepT s b z (fun e=>(h₀ e).elim)):=by
 exact Kodiak.streamU _ X.val _ _ _ b (Terrace.scheduleV b) h₀
#print axioms casin
#print axioms core_tick
end
end Mist
end YM.CF.Buffered.Afterglow.Hierarchy
