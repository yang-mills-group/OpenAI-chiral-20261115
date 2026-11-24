import YM.SU5.Reconstruction.Quartz.Moire
import YM.SU5.Reconstruction.Vermont.Along
/-! # New multi-clock Rank proof: occupancy at all large wall costs on this Compass -/
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 32000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open SlabMark MeshClock ConePrice SelectionAnalysis Germ Chambers
open Anvil
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
local notation "D" => Domain Y H G false
local notation "Ds" => Domain Y H G true
local notation "Gt" => marks (timeMesh Λ)
variable (C : ∀ j, Arena Y H G.history.circuit j 0 false)
variable (a:Axis)
variable (χ : displayAlgebra Y H V G.history G.clipped a false (C a) →⋆ₐ[ℂ] ℂ)
local notation "w" i:max=> displacement Y H V G.history G.clipped a false (C a) χ i (C i)
local notation "J₀" i:max=> indoor Y H V G.history G.clipped i false (C i) (w i)
local notation "C₀" i:max=> saunters Y H V G.history G.clipped i false (C i) (w i)
local notation "G₀" i:max=> fort Y H V G.history G.clipped i false (C i) (w i)
local notation "Ω₀" i:max=> vocation Y H V G.history G.clipped i false (C i) (w i)
local notation "S₀" i:max=> peninsula Y H V G.history G.clipped i false (C i) (w i)
local notation "ℜ" p:max=> Real.toNNReal (p:ℝ)
local notation "Pr" i:max=> bridgeEstate Y H V G i (C i) (w i)
local notation "Vo" i:max=> coreOs Y H V G i (C i) (w i)
local notation "Os" i:max=> compassKet Y H V G i (C i) (w i)
local notation "D'" i:max=> Domain Y H G false (flank i 0)
local notation "Tx" => timeMesh Λ
local notation "Q" i:max=>Follows Y H V G i (C i) (w i)
local notation "X" i:max=> OSvector Y H V G i (C i) (w i)
local notation "θ" i:max=> flipMark i (tent Y H)
local notation "m₁" => FirstWindows.move (tent Y H)
local notation "ℓ_"=>osValue Y H V G a (C a) χ
open BridgeClub Reflector
namespace Crease
variable (F: BoostBacking Y H V G C a χ)
variable (j z:Axis) (b:j≠z)
open CrossedFrame
local notation "U"=>flank j 0∩flank z 0
local notation "Λ₁" i:max=>onceLens Y H V G C a χ i
local notation "Π" i:max=> opCarries Y H V G i (C i) (w i)
variable {D₀:Hilbert} (Z : Clasp D₀ (fort Y H V G.history G.clipped j false (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j))) (fort Y H V G.history G.clipped z false (C z) (displacement Y H V G.history G.clipped a false (C a) χ z (C z))))
variable (p:Quarter Y H V G C a χ j z b.symm Z)
local notation "Tm" i:max=> Picket.trans (S₀ i)
local notation "Ω" i:max=> Ω₀ i
local notation "Sq" => (S₀ j)
namespace Boots
local notation "lu" x:max=> (Tm j) ((x:ℝ) • basis z)
local notation "BC" => parcelUp Sq
-- not assumed closed! uses full port and wall in native mesh
noncomputable def reserves (x:Gt) : Submodule ℂ (G₀ j):= LinearMap.range (((lu x).comp Z.l).toLinearMap)
local notation "N" => reserves Y H V G C a χ j z Z
lemma doorway (x:Gt)(y:G₀ j) : y∈ N x ↔ ∃ t:D₀,(Tm j) ((x:ℝ) • basis z) (Z.l t) = y:= LinearMap.mem_range
include b F p
lemma byWall (x y:Gt)(s:x≤y): N y ≤ N x:= by
 intro v h; obtain ⟨u,d⟩:= (doorway Y H V G C a χ j z Z y v).1 h; subst v
 apply (doorway Y H V G C a χ j z Z ..).2
 let r:= y-x; have he:0≤ (r:ℝ):= by change (0:Gt)≤ r; exact sub_nonneg.mpr s
 have ht:=stepB Y H V G C a χ j z b.symm Z (F.present j) (F.present z) p.port (eject z r) (by simp [b]) (by simpa using he)
 rw [castSpace Y H V G C a χ j b.symm] at ht
 obtain ⟨t,q,e⟩:= ht u; refine ⟨t,?_⟩; rw[q, ←mul_apply_eq_comp,←Picket.trans_sum,←add_smul, show (x:ℝ)+(r:ℝ)=(y:ℝ) from ?_]; change (x:ℝ)+ ((y:ℝ)-(x:ℝ))= y; abel
lemma wallHeat (x t:Gt)(v:0≤ (t:ℝ))(wq:G₀ j)(h:wq∈ N x) : (Sq).E (ℜ t) wq∈ N x:= by
 obtain ⟨u,d⟩:= (doorway Y H V G C a χ j z Z x wq).1 h; subst wq
 apply (doorway Y H V G C a χ j z Z x _).2
 have ht:=stepB Y H V G C a χ j z b.symm Z (F.present j) (F.present z) p.port (eject j t) (by simpa using v) (by simp [b.symm])
 rw [bridge_time] at ht; obtain ⟨r,e,h'⟩:=ht u
 refine ⟨r,?_⟩; rw [e,Picket.trans_space (h:=b.symm)]; exact (DFunLike.congr_fun ((Sq).independent _ _) _).symm
lemma boardVac (x:Gt): Ω j∈N x:= by
 have he: Z.Latch (Ω j) (Ω z):= by rw [← comesHome Y H V G C a χ j, ← comesHome Y H V G C a χ z]; exact p.port.sees (⟨1,domain_one ..⟩:Ds U)
 obtain ⟨t,b,h⟩:=he; apply (doorway Y H V G C a χ j z Z x _).2; exact ⟨t,b.symm ▸ (compass_origin Y H V ..)⟩ -- tune

lemma accost (x:Gt)(u v:Axis→Gt)(b':x<u z)(B:(G₀ j).Op)(eB:Sight Y H V G C a χ j u v B): MapsTo B (N (u z+v z)) (N x):= by
 intro y h; obtain ⟨t,h0⟩:=(doorway Y H V G C a χ j z Z _ y).1 h; subst y
 apply (doorway Y H V G C a χ j z Z ..).2
 let w₀:Gt:= u z+v z; let off:=-((x:ℝ) • basis z)
 let B₀:=BC off B; let u':= u+ eject z (-x)
 have hu:u' z+v z=w₀-x:= by unfold w₀ u'; rw [Pi.add_apply,eject_at]; abel
 have hv:Sight Y H V G C a χ j u' v B₀:= by unfold B₀ off; rw [← neg_smul]; exact aheadSight Y H V G C a χ F j z b u v (-x) B eB
 obtain ⟨Y',E₀⟩:= awardEcho Y H V G C a χ F j z b Z p u' v B₀ (show _ from (by rw [show u' z=u z-x from (by simp [u',sub_eq_add_neg])]; exact (show (0:Gt) < _ from sub_pos.mpr b'))) hv
 have hx:=bookedEcho Y H V G C a χ F j z b Z p u' v B₀ Y' E₀
 rw [hu] at hx; obtain ⟨r,d,h'⟩:= hx t
 refine ⟨r,?_⟩; let U':= lu x; let V':=(Tm j) off; change U' _ = B ((lu w₀) (Z.l t)); rw [d]
 have he: U' *B₀ * (lu (w₀-x:Gt)) = B * (lu w₀) := by
    have ht:U'* V'=1:= mail ..; have hp: U'*(lu (w₀-x:Gt))=lu w₀:=by unfold U'; rw[←Picket.trans_sum,←add_smul,show (x:ℝ)+ (↑(w₀-x:Gt):ℝ)=(w₀:ℝ) from (by rw[AddSubgroup.coe_sub]; ring)]
    rw [show B₀=V'*B*U' from (by unfold U' V' B₀ off parcelUp; rw [neg_neg]),← mul_assoc,← mul_assoc,ht,one_mul,mul_assoc,hp]
 simp_rw [mul_apply_eq_comp]; simpa only [mul_apply_eq_comp] using DFunLike.congr_fun he (Z.l t)
end Boots
end Crease
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget
