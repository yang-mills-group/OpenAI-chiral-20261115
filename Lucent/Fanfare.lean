import YM.SU5.Diva.SPF
/-! Adaptation of Fluxion,Audition,Duet. Testing ALL clans, same enrollment.
 Two tolerance orders: take R large first. The internal evaluation estimate
 is on the true spin/color/momentum form, invoked on auxiliarily-chosen sequences
 (does not need a continuum limit for these volumes). -/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.Buffered.Ballad
open Function Filter Metric Fock Finset Fir Jill Lat Lattice Laurent Next.Free Bloch Cube Sods Tulip Scroll Spire Pastry RP Branch Wilson Phase SU Rush Mir Reflect Lifted Bilinear Window Skye Emu Onyx Kea Flare Dial
open Cache Glaze
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Topology
attribute [local instance] opCStarAlgebra
variable {R:ℕ}{B N:Side}{j:ℕ}
open Py.Rate.LocalLimit.Papal (Weaver)
open YM.CF.Lamour YM.CF.Velvet
open YM.CF.Lamour.Bridge.Celeste
namespace Twah
open Lead (Clan)
open YM.Stationary (Gaia)
open Lamour.Bridge
variable {I:Type*} (Z:I→Clan)(Y:ℕ→ I→Twah)(L:List I)(s:ℕ→ℕ) {Q:ℕ→Side}{N:Side}

variable (P:Cellz I→Gaia) (D:I→DirSpin) (x:List (Stamp I))
variable (Yp:riseUp Y s P)(Yu:plateau Y P)
include Yp Yu
-- Product at any history T Pres shadow. Supply arrangement spine not needed for kernel cost, this part exact.
variable (Yh:Yard Q (fun i=> (s i:ℝ))) (Yt: ∀ i, bodyF (Y i)=D) (j) (h:1≤j)
include Yh Yt h
lemma fanfare (M:ℕ→Jill.Male)(Ht:∀ i,Kea.Pad j (Q i))(t:∀ i,Wave (Single (Q i)))(p:∀ i, Sea (spar j (M i) (1:Pane (Q i))) (t i)) : Tendsto (fun i:ℕ=> alleyR (mateK (Q i)) (t i) (rollC (ton ∘ pulse (Y i) (Q i) (s i)) x)) atTop (𝓝 (runes (germRho P D) x)):=by
 let P': Plot (Stamp I) (fun i:ℕ=> (s i:ℝ)):= ⟨fun i p=> crumbs Y i (colbase p),pilotS D,P ∘ colbase,fun x=> Yp _,fun x y=> Yu _ _⟩
 obtain ⟨u,v,g⟩:= lake_formal h
 let A(i):= (lake (Q i) j (M i)); have hx(i): A i = Dofu (Q i) (lakeP (Q i) j (M i)):=rfl
 have he(i:ℕ)(u:Stamp I): P'.tag (m:=i) 0 (Kea.tax emptyC) 1 u=pulse (Y i) (Q i) (s i) u:=by
    change nac _ _ _ _ _=nac _ _ _ _ _; rw [clear_canvas, show P'.seat u=pilotS (bodyF (Y i)) u from congrArg (fun A=>pilotS A u) (Yt i).symm]; rfl
 refine (P'.sun (r:=u) (C:=1) (d:=fun _=>emptyC) (fun i=>too _) M (fun i:ℕ=>lakeP _ j (M i)) (fun _=>0) Yh v (by norm_num) (fun x:Slot=> Eventually.of_forall (fun i=> g _ (Ht i).1 (M i) x)) h (fun _=>1) x).congr fun i=> ?_
 simp_rw [show ∀ (w:Stamp I), P'.tag (m:=i) _ _ _ w=pulse (Y i) _ _ _ from he i]
 have hp:=bank_chant (R:=s i) (Y i) (fun _=>⟨0,false⟩) [] h (Ht i) (M i) _ (p i) x
 have hf:plait (Y i) (fun _=>⟨0,false⟩) [] (s i) (Q i) (1,1)=1:=rfl
 rw [hf,mul_one] at hp; exact hp.symm
#check fanfare
