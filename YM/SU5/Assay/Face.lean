import YM.SU5.Assay.Walled
import YM.SU5.Assay.Rebate
import YM.SU5.Assay.Jaw
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4900
set_option maxHeartbeats 420000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
open Aria Set OS.Semigroup
variable (P:Spine)(j:Axis)(x:P.Spectrum0 j)
local notation "K"=> P.calibration
local notation "H"=> P.ColorHil j x
local notation "B"=> P.ManyF j x
local notation "X"=> (P.ColorHil j x).Op
local notation "Y"=> (P.ManyF j x).Op
local notation "Lag"=>ℝ→ℝ→(P.ManyF j x).Op
local notation "S"=> P.seasons j x
local notation "U"=> P.physicalEnergy j x
local notation "ω"=> (P.seasons j x).wax
local notation "W"=> P.cartage j x
local notation "θ"=> P.tableau j x
local notation "E"=> P.enter j x
local notation "R"=> P.wealth j x
local notation "Vac"=> P.colorZero j x
local notation "Ω"=> P.heaven j x
/-! Buying frames for every component, on each separate side and pairs. Rounding isn't
  necessary for actual measurements where `Grips` applies, but ensures tick clearance for
  any separate loose probe consultations on the advertised budgets, even union slots. -/
local notation "δ" =>P.macroStep
local notation "τ"=>P.tock
structure FrameFace (t:ℕ)(M:Set Vantage)(a b:ℝ)(k:ℤ)(w:ℕ):Prop where
  width:0<w
  left:a≤ τ t k
  right:τ t (k+w)≤b
  buys:∀y∈M,τ t k≤ y j∧y j≤ τ t (k+w)
variable {P j x}{M N D:Set Vantage}{k l:ℤ}{w v t:ℕ}{a b c:ℝ}
lemma FrameFace.covers (h:P.FrameFace j t M a b k w)(p:D⊆M):P.FrameFace j t D a b k w:={h with buys:= fun y q=>h.buys y (p q)}
lemma FrameFace.connect (h:P.FrameFace j t M a b k w)(r:P.FrameFace j t N b c l v):
 ∃d, P.FrameFace j t (M∪N) a c k d ∧ k+w ≤ l∧ k+(d:ℤ)=l+v:=by
 have hl:k+w≤l:=(P.tock_le ..).mp (h.right.trans r.left)
 have :0<w∧0<v:=⟨h.width,r.width⟩
 have u:k≤l:=by omega
 have f:P.tock t (k+w) ≤ τ t (l+v):= (P.tock_le ..).mpr (by omega)
 have eq:k+↑(l+v-k).toNat=l+v:=by omega
 refine ⟨_,⟨?_,h.left,Eq.symm eq ▸ r.right,?_⟩,hl,eq⟩
 · omega
 intro y z;rw [eq];rcases z with i|i
 · exact ⟨(h.buys y i).1,((h.buys y i).2.trans f)⟩
 exact ⟨le_trans ((P.tock_le ..).mpr u) (r.buys y i).1,(r.buys y i).2⟩

private lemma frame_ceil (y:ℝ):y≤τ t ⌈y/δ t⌉ ∧ τ t ⌈y/δ t⌉< y+δ t:=by
 have p:= P.macroStep_pos t
 rw [P.tock_price]
 exact ⟨(div_le_iff₀ p).mp (Int.le_ceil _), calc
   _< _ := mul_lt_mul_of_pos_right (Int.ceil_lt_add_one _) p
   _= _ := by rw [add_mul,div_mul_cancel₀ _ p.ne',one_mul]⟩
lemma FrameFace.checkout (h:∀y∈M,a+c≤y j∧y j≤b-c)(p:a+c≤ b-c)(d:δ t<c):
  ∃k w,P.FrameFace j t M a b k w:=by
 let k:= ⌈a/δ t⌉
 let r:= -⌈(-b)/δ t⌉
 have h₁:a ≤ τ t k ∧ τ t k < a+c:=⟨(frame_ceil _).1, ((frame_ceil _).2).trans (by linarith)⟩
 have h₂:b-c < τ t r ∧ τ t r ≤ b:=by
   obtain ⟨u,v⟩:=frame_ceil (P:=P) (t:=t) (-b)
   unfold r
   rw [P.tock_price] at u v ⊢
   push_cast
   constructor <;> linarith
 have u:k<r:=lt_of_not_ge (fun w=>not_le.mpr (lt_of_lt_of_le h₁.2 (p.trans h₂.1.le)) ((P.tock_le ..).mpr w))
 have e:k+↑(r-k).toNat=r:=by omega
 refine ⟨k,(r-k).toNat,by omega,h₁.1,by rw [e];exact h₂.2,?_⟩
 intro y w;rw [e]; exact ⟨h₁.2.le.trans (h y w).1,(h y w).2.trans h₂.1.le⟩

lemma Fades.face {F:SampleDose}{Q:ℕ→P.Apron} (h:P.Fades Q)(q:Walled j F a b 0)(p:a<b):
   ∀ᶠ s in atTop,∀ t≥s, ∃k w,P.FrameFace j t (P.spacePrice (Q s) F) a b k w:=by
 obtain ⟨d,u,v⟩:=q.more
 let z:=min (d/2) ((b-a)/2)
 have z₁:0<z:=lt_min (by linarith) (by linarith)
 have k:=P.macroStep_zero.eventually (gt_mem_nhds z₁)
 obtain ⟨T,t₀⟩:=eventually_atTop.1 k
 filter_upwards [h.one z₁ j,eventually_ge_atTop T] with s i g -- typo
 intro t e
 refine FrameFace.checkout ?_ ?_ (t₀ t (g.trans e))
 · intro y l;obtain ⟨r,w,n⟩:= Set.mem_iUnion₂.mp l; have k:= v r w;have u:=abs_le.mp (n j)
   have r:z≤d/2:=min_le_left ..;constructor <;> linarith
 have r:z≤(b-a)/2:=min_le_right ..;linarith
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
