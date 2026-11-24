import YM.SU5.Reconstruction.Hygrometry.Constellation
import YM.SU5.May.FloeProof
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 32000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.Screened.FloeRoom
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open SlabMark MeshClock Tilted WindRose
open Fock Lat Laurent Wilson Cube Finset Branch Scree RG Spire Vale Pastry Peaks Dial Phase Lifted Skye Tapestry.Exhibition Tapestry.Altitude Tenant Rush Tulip
open PolarArchives Brazier
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
variable {Λ:Preparation}{l:ℕ} (Y:Course Λ (VolumeCape.Dream.Nimbus l)) (H:Real.exp 1 ≤ Λ.x)
variable {i k : ℕ→ℕ} {I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ} (V:Universal Y H i k I E)
  (G : GroundExtension (i:=i) (k:=k) (E:=E) Y H)
local notation "v₁" n:max => i (G.rows n)
local notation "v₂" n:max => k (G.columns n)
local notation "T" n:max => Therapies.paceFloor Y H G n
open LocalLimit.Intermediate Harbour
open Hygrometry Hygrometry.MeterFunding
open May.Floe
abbrev periodTube (Y:Course Λ (VolumeCape.Dream.Nimbus l))(m t:ℕ):Side:= mesh (Y.ir m) Λ.R.L t -- m param index
abbrev poseTube(n:ℕ):=periodTube Y (v₁ n) (T n)
abbrev basePose (n:ℕ):Side:=Journey.side Y (v₁ n) (T n)
abbrev waveM (r:ℕ):= (Therapies.freshBook Y (v₁ r) (v₂ r) (T r)).M
local notation "μ₀" r:max => poseTube Y H G r
local notation "C" r:max => basePose Y H G r
local notation "M" r:max=> waveM Y H G r
abbrev earnLook (n:ℕ):=(poseTube Y H G n)*(waveM Y H G n).val
abbrev growthSpace(n:ℕ):=(M n).val.val
noncomputable def earnRatio(a:ℕ) : Ratio (basePose Y H G a) (CSide (earnLook Y H G a) Λ.block):= ⟨(M a).val,by unfold CSide More earnLook; change (((μ₀ a).val * (M a).val.val)*2)*Λ.block.val=((μ₀ a).val*2)*Λ.block.val*(M a).val.val; ring⟩
lemma ratio_M (a:ℕ): Odd ((earnRatio Y H G a).count).val:= (M a).property
-- to use with Stamp.TH.
include V
lemma grows_material : Tendsto (growthSpace Y H G) atTop atTop:=by
 have hw:Tendsto (Y.ivory ∘ k ∘ G.columns) atTop atTop:= (Y.UV.comp (V.pick.grow_k.comp G.history.growsB)).tendsto_atTop
 have hg:1<Λ.R.L.val:=by have ht:=Λ.R.coarse; omega
 have he(r:ℕ)(j:ℕ)(t:j+T r≤ Y.uv (v₂ r)) : Λ.R.L.val^j ≤ growthSpace Y H G r:=by
    let A:ℕ→Male:= fun j=> (Therapies.freshBook Y (v₁ r) (v₂ r) j).M
    let L:=Λ.R.L.val; have hh (v:ℕ)(v':v<Y.uv (v₂ r)): A v=upMale Λ.R.L Λ.R.odd_side (A (v+1)) := ((projectA Y (v₁ r) (v₂ r)).last.pass v v').grown
    change Λ.R.L.val^j ≤ (A (T r)).val.val
    -- generalize induction on dilation.M horizons
    suffices ∀ a b:ℕ, b+a ≤ Y.uv (v₂ r) → Λ.R.L.val^b ≤ (A a).val.val from this _ _ t
    intro a b; induction b generalizing a with
    | zero=>intros; exact (A a).val.property
    | succ b ih => intro t; rw [hh a (by omega),pow_succ']; exact Nat.mul_le_mul_left Λ.R.L.val (ih (a+1) (by omega)) -- mistake nat left factor
 refine tendsto_atTop.mpr fun n=>?_ ; filter_upwards [(show Tendsto (fun i=> Λ.R.L.val^(Y.ivory (k (G.columns i)))) atTop atTop from (tendsto_pow_atTop_atTop_of_one_lt hg).comp hw).eventually_ge_atTop n] with i u; refine u.trans (he i (Y.ivory (k (G.columns i))) ?_); unfold Therapies.paceFloor Course.uv; unfold Py.buoy Py.Rate.trunk; omega
lemma steady_board : May.Floe.Twilight Λ.K.j (earnRatio Y H G) := by
 let f:= earnLook Y H G; let Bm(i):= basePose Y H G i -- name clash
 let Θ:=Therapies.paceFloor Y H G; have he:Onyx.Yard (basePose Y H G) (precisionAt Λ ∘ Θ):= Therapies.budget_grant Y H V G Θ (Therapies.level_mon Y H V G Θ (Therapies.eligibility_horizon Y H V G).1)
 let s (i):= CSide (f i) Λ.block; let r(i:ℕ):ℝ:=(growthSpace Y H G i)
 have hp:Tendsto (fun i=> (basePose Y H G i).val) atTop atTop:= tendsto_atTop.mpr (fun k=> Hygrometry.Overlook.boundsFrom (poseTube Y H G) he k)
 have hr: Tendsto (fun i=> (↑(Bm i).val:ℝ)) atTop atTop:= tendsto_natCast_atTop_atTop.comp hp
 have hK:Onyx.Yard s r:= by
    refine ⟨fun i=> Lat.nPos (M i).val,tendsto_natCast_atTop_atTop.comp (grows_material Y H V G),?_,fun i=>?_⟩; swap; · rw [show (s i).val=_ from RP.suff ..]; exact even_two.mul_right _
    apply Tendsto.congr _ (show Tendsto (fun i=> Real.pi/(↑(Bm i).val:ℝ)) atTop (𝓝 0) from tendsto_const_nhds.div_atTop hr); intro i; unfold Ember.pinch; rw [show (s i).val=(Bm i).val*(M i).val.val from (earnRatio Y H G i).exact_size]; unfold r growthSpace; change _= ((↑(M i).val.val):ℝ)*_; rw [Nat.cast_mul]; field_simp
 let H₀:∀ i, Wave (Single (CSide (f i) Λ.block)):= fun r=> changeM (m:=f r) Λ.U 1 white
 exact ⟨he.even,ratio_M Y H G,hp,hK,H₀,(Hygrometry.Overlook.resolutionM Λ.U Λ.dpos.le (Therapies.solvable (Λ:=Λ)) f hK (fun _=>white)).mono (fun i v=>v.2.2)⟩
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.Screened.FloeRoom
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.Screened.FloeRoom.steady_board
