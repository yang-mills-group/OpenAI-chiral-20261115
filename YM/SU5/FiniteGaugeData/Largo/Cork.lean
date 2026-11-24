import YM.SU5.FiniteGaugeData.Largo.Track
import YM.SU5.FiniteGaugeData.Brique.Ravine
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 380000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Quest
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra
open Heat Brique Window.Brique Journey Py Py.Rate LocalLimit Preparation FullBill Steam Vale
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(h:Real.exp 1 ≤ Λ.x)
variable (s i k:ℕ) {u v:ℕ→ℕ}
set_option quotPrecheck false
local notation "Y₁"=> (Y.voyage i).X (Y.uv k)
local notation "A"=> ((Y.voyage i).X (Y.uv k)).gram
local notation "Ρ"=> ((Y.voyage i).X (Y.uv k)).pilot
-- on that cutoff choose all large Male. 
lemma diameter_b (p:s≤Y.uv k) : Y.uv k - s < (((Y.voyage i).X (Y.uv k)).gram s).J.M.val.val:=by
 let X:= Y₁
 let U: Py.Period.Session Λ.V 1 2 6 Λ.N0 Λ.J Chi.canonical Λ.h Λ.R0 Λ.δ Λ.x (Y.ir i) (Y.uv k):= ⟨Y.meter,(Y.voyage i).funds,X.pilot,X.gram,(Y.voyage i).CapeT,X.wave,X.fee,Y.history i k⟩
 let k':= Y.uv k; have ht(j:ℕ)(t:j≤k'): (U.E j).J.M=( (Λ.W.arm (U.val.large.trans U.tip) (Y.uv k)).Q j).M:= ((U.scale.note.owns j t).taste) ▸ rfl
 let K:= Λ.W.arm (m:=Y.ir i) (U.val.large.trans U.tip) (Y.uv k)
 change _<(U.E s).J.M.val.val; rw [ht _ p]; suffices e:∀ i j,i+j=k'→ j < (K.Q i).M.val.val from e s (k'-s) (by unfold k'; omega)
 intro i j; induction j generalizing i with
 | zero=> intro z; exact (K.Q _).M.val.pos
 | succ j ih=> intro z; have b:= ih (i+1) (by omega); rw [(K.pass i (by change i<k'; omega)).grown]; change _ < Λ.R.L.val * (K.Q (i+1)).M.val.val; have e:=Λ.R.coarse; nlinarith
lemma heightZoom(d:ℕ)(p:StrictMono v) : ∀ᶠ k:ℕ in atTop, ∀ i:ℕ, d ≤ (((Y.voyage i).X (Y.uv (v k))).gram s).J.M.val.val:=by
 filter_upwards [(Y.uv_grows.comp p).tendsto_atTop.eventually_ge_atTop (s+d)] with i x k; change s+d≤Y.uv (v i) at x; have e:= diameter_b Y s k (v i) (by omega); omega
end YM.CF.Buffered.Afterglow.Hierarchy.Quest
