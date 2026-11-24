import YM.SU5.May.FloeRoad
import YM.SU5.May.FloeCore
import YM.SU5.May.FloeCourse
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
open Push.SectorMeasure
open Advance.Depths
variable (κ:ℕ){U : Finset Cover}
private lemma gauge_anchor (n : Side)(x:Cover)(i:SpinIdx)(b:SU.Slot)(p:nodeC x∈ U): withinM (modesIn n (U.image (wrap (More n)))) (basisC n x i b) := by
 have he : Lifted.index n x i b ∈ modesIn n (U.image (wrap (More n))) := by rw [modes_at]; change node (wrap n x) ∈_; rw [node_of]; exact mem_image_of_mem _ p
 unfold withinM basisC; rw [map_smul,within_basis _ _ he]
variable {J':Calibration}
lemma gauge_laps {k r:Bool}{F:Family J'} (p: InTest J' r U k F): ∃ κ:ℕ,∀ m:Side,Keeps (J'.c m) κ (Satin.region U (J'.c m)) k (F m):=by
 induction p with
 | @seed f p=>exact ⟨0,fun m x=>Submodule.smul_mem _ _ capOne⟩
 | @creator x i b p v=>
    refine ⟨1,fun m y=> capCreates _ ?_ (gauge_anchor (J'.c m) x i b v)⟩; unfold withinM basisC; rw [map_smul,within_basis _ (Lifted.index (J'.c m) x i b) ((mem_Tset ..).mpr p)]
 | @remover x i b p v=>
    refine ⟨1,fun m y=> capRemoves _ ?_ (gauge_anchor (J'.c m) x i b v)⟩; unfold withinM basisC; rw [map_smul, within_basis (Tset (J'.c m))ᶜ (Lifted.index (J'.c m) x i b) (Finset.mem_compl.mpr fun h=> p ((mem_Tset ..).mp h))] -- Finset comp
 | one=>exact ⟨0,fun m y=> capOne⟩
 | zero=>exact ⟨0,fun m y=> Submodule.zero_mem _⟩
 | add _ _ ih il=> obtain ⟨v,h⟩:= ih; obtain ⟨t,l⟩:=il; exact ⟨v+t,fun m z=> Submodule.add_mem _ (Depths.monotone (Finset.Subset.refl _) (by omega) (h m z)) (Depths.monotone (Finset.Subset.refl _) (by omega) (l m z))⟩
 | mul _ _ ih il=> obtain ⟨v,h⟩:=ih; obtain ⟨t,l⟩:=il; exact ⟨v+t,fun m y=> longerF (h m y) (l m y)⟩
 | smul a _ ih=> obtain ⟨v,h⟩:=ih; exact ⟨v,fun m y=> Submodule.smul_mem _ _ (h m y)⟩
-- exhibition and funded climb.
private lemma capTransport {κ:ℕ}{m n:Side}(p:m=n){f:Mark m}{b:Bool} (h:Keeps m κ (Satin.region U m) b f): Keeps n κ (Satin.region U n) b (arrange m n p f):= by subst n; exact h
local notation "𝗠" i:max j:max=> Journey.side Y i j
variable (s m t:ℕ) {U V': Finset Cover}
lemma startingLaps {g:Family (tent Y H)}{b:Bool} (h:InTest (tent Y H) true U b g): ∃ κ:ℕ,∀ (s m:ℕ), Keeps (Journey.side Y m s) κ (Satin.region U (Journey.side Y m s)) b (exhibit Y H s m g):= by
 obtain ⟨k,g⟩:=gauge_laps h
 exact ⟨k, fun s i=> capTransport (terrain Y H (Y.ir i) s) (g (momentm Y i s))⟩
variable (L:ℕ) (F:Intermediate.Room L→ Corr (Λ.Ctor (Y.ir m) L))(z:Intermediate.Room L)
local notation "PR" => (screen Y m t L F z)
local notation "wb" i:max=> Harbour.earns Y m t L F z i
lemma steps_kept {b:Bool}{f:Mark (Journey.side Y m s)} (u:Keeps (Journey.side Y m s) κ (Satin.region U (𝗠 m s)) b f): Keeps (𝗠 m (s+1)) κ (Satin.region (wingspan Λ l U) (𝗠 m (s+1))) b (assembleNext Y m t s L F z f):= by
 let A:= steps Λ.V (Y.ir m) Λ.block (Y.uv t) s ; let D:= Vale.apt (Y.ir m) Λ.block Λ.R.L s
 -- higher gap does not need launched budget; width calendar fixed.P.Radius.Scope
 refine increaseScope ?_ (capPush D A Λ.K.j (wb s).val ((Harbour.screen Y m t L F z (s+1)).J.M) Λ.R.odd_side Chi.canonical Λ.J.d (Harbour.screen Y m t L F z (s+1)).beta ((Y.voyage m).CapeT s) (Journey.legal Λ) _ u)
 have he: padded D (Satin.region U (𝗠 m s)) (Stencil.clothRadius Λ.R.L (aliasLaw Λ)) ⊆ padded D (Satin.region U (𝗠 m s)) (Λ.R.L.val*gross (aliasLaw Λ) (distanceLaw l) Λ.R.J):= le_trans ((halo_subset _ _).trans (before_zone D (Satin.region U (𝗠 m s)) (aliasLaw Λ))) (Corona.halo_mono (Nat.mul_le_mul_left Λ.R.L.val (by unfold gross; omega)) (Finset.Subset.refl _)) -- aliasPad notation.K
 exact he.trans (next_contains U _ _ _)
lemma pyramid {b:Bool}{f:Mark (Journey.side Y m s)}(p:Keeps (𝗠 m s) κ (Satin.region U (𝗠 m s)) b f) (n:ℕ): Keeps (𝗠 m (s+n)) κ (Satin.region (volumeAround Λ l n U) (𝗠 m (s+n))) b (climb Y m t s L F z f n):= by
 induction n with
 | zero=> exact p
 | succ n ih=> exact steps_kept Y κ (s+n) m t L F z ih
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.Screened.FloeRoom
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.Screened.FloeRoom.startingLaps
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.Screened.FloeRoom.pyramid
