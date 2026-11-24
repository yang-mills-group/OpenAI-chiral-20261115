import YM.SU5.Relativistic.Passage
import YM.SU5.Relativistic.Nickel
import YM.SU5.Relativistic.Grades
set_option autoImplicit false
set_option synthInstance.maxSize 26000
set_option maxHeartbeats 400000
set_option maxRecDepth 5000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Fock
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical InnerProductSpace
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat PhaseChoice SlabMark Vacancy Tapestry Tapestry.Altitude Tapestry.Exhibition Tower.Selected
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
variable {a b:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}{L:Rack Λ l}{B:Clay Λ l}
    (D : Exhibition Y H a b I E L B)
local notation "V"=>D.univ_
variable (G:SatinVerification.GroundExtension (i:=a) (k:=b) (E:=E) Y H)
variable (u:ℕ→ℕ) {T:ℕ→Bool→Family (tent Y H)→Family (tent Y H)}(t:GradesAll (i:=a) (a:=G.rows) (k:=b) (b:=G.columns) Y H u T)
variable (d j:Axis) (c:∀ j:Axis,Arena Y H G.history.circuit j 0 false)
variable (x:displayAlgebra Y H D.univ_ G.history G.clipped d false (c d)→⋆ₐ[ℂ] ℂ)
local notation "χ" i:max=> displacement Y H D.univ_ G.history G.clipped d false (c d) x i (c i)
local notation "ψ"=>evaluate Y H D.univ_ G d c (SameCharacter.resident Y H D.univ_ G d false (c d) x)
local notation "D₀"=> Dome (tent Y H)
local notation "Ξ"=> Cloud (Dome (tent Y H))
local notation "φ" n:max => response Y H V n G.history G.clipped j false (c j) (χ j)
local notation "P" s:max F:max=>stream Y H (fun s=>T s true) s F
local notation "Q"=> G.history
variable (s:ℕ)
local notation "α" => walkV Y H j
local notation "F₀"=> Cabin (tent Y H) j
local notation "κ" u:max=>mirror K j u
local notation "Λ₀"=> Λ.R.L.val
local notation "B₁" s:max=> creed Y H D G d j c x s

open HostLegal MeshClock
local notation "R₁"=> timeMesh Λ
local notation "U"=>flier Y H D G u t d j c x
local notation "W₀" s:max=> Tower.Field Y H s j 0 false
local notation "Ωe"=> doorstep Y H V Q G.clipped j false (c j) (χ j)
local notation "Φ" s:max=> arriving Y H V s Q G.clipped j false (c j) (χ j)
local notation "Υ" s:max=> (U).entry s
local notation "E₁"=> indoor Y H V Q G.clipped j false (c j) (χ j)
local notation "E₂"=> (U).booth
local notation "Δ₀"=> relocate (tent Y H)
local notation "B₀"=> ruler Λ.block
open CF.Pannier.Chancel.ScreeV
local notation "Lst"=>Slab (timeMesh Λ)
local notation "N" k:max z:max=> notch (timeMesh Λ) k z
lemma slipBetween (a b:ℝ)(h:a<b):∃ A:Stamp (timeMesh Λ), a<A.val ∧ A.val<b:= by
 obtain ⟨x,h,t⟩:= (daylight (timeMesh Λ)).exists_mem_open isOpen_Ioo (Set.nonempty_Ioo.mpr h); exact ⟨⟨x,h⟩,t⟩
lemma knack (S:Finset Cover)(u:S.Nonempty): (footprint Λ l s S).Nonempty:=by
 obtain ⟨i,u⟩:=u; exact ⟨_, Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr ⟨u, Set.left_mem_Icc.mpr (collar_bound (Λ:=Λ) (l:=l) s i)⟩⟩⟩ -- implicit u; no Y
local notation "Sphere"=>Finset Cover
def hulls (S:Finset Cover)(W:Slab (timeMesh Λ)):= ∀ u∈ footprint Λ l s S,(W.lower:ℝ)≤u j∧ u j≤ (W.upper:ℝ)
def slottedHere (A B:Finset Cover):Prop:= ∀ i∈ footprint Λ l s A,∀ w∈ footprint Λ l s B,i j < w j
local notation "T₂"=> slottedHere (Λ:=Λ) (l:=l) j s
lemma slotTill {A B:Sphere}{u:ℕ}{z:ℤ}(h:Till K u j z A B)(p:0<u): T₂ A B :=by
 intro a b i e; refine lt_of_lt_of_le ?_ (regionGap Y H j s z u h a i b e); have ht:=gaugeMesh_pos Λ s; nlinarith only [show 0<(2:ℝ)* ↑u * gaugeMesh Λ s by positivity]
lemma slotFence {A B:Sphere}(u:A.Nonempty)(v:B.Nonempty)(h:T₂ A B): ∃ (z : Stamp (timeMesh Λ)), (∀ a∈ footprint Λ l s A, a j<z.val) ∧ ∀ b∈ footprint Λ l s B,z.val < b j:= by
 obtain ⟨a,p,z⟩:= (footprint_compact Λ l s A).exists_isMaxOn (knack s _ u) (continuous_apply j).continuousOn
 obtain ⟨b,t,e⟩:= (footprint_compact Λ l s B).exists_isMinOn (knack s _ v) (continuous_apply j).continuousOn
 obtain ⟨n,u,v⟩:= slipBetween _ _ (h a p b t) (Λ:=Λ)
 exact ⟨n,fun _ p=>lt_of_le_of_lt (z p) u,fun _ w=>lt_of_lt_of_le v (e w)⟩
lemma slotLow{S:Sphere}(v:S.Nonempty): ∃ z:Stamp (timeMesh Λ), ∀b∈ footprint Λ l s S,z.val<b j:=by
 obtain ⟨a,p,h⟩:=(footprint_compact Λ l s S).exists_isMinOn (knack s _ v) (continuous_apply j).continuousOn
 obtain ⟨z,u,q⟩:= slipBetween (a j-1) (a j) (Λ:=Λ) (by linarith)
 exact ⟨z,fun x w=> lt_of_lt_of_le q (h w)⟩
lemma slotTall{S:Sphere}(v:S.Nonempty): ∃ z:Stamp (timeMesh Λ), ∀b∈ footprint Λ l s S,b j<z.val:=by
 obtain ⟨a,p,h⟩:=(footprint_compact Λ l s S).exists_isMaxOn (knack s _ v) (continuous_apply j).continuousOn
 obtain ⟨z,u,q⟩:= slipBetween (a j) (a j+1) (Λ:=Λ) (by linarith)
 exact ⟨z,fun x w=> lt_of_le_of_lt (h w) u⟩
local notation "plowM"=>hulls (Λ:=Λ) (l:=l) j s
lemma slotMake{S:Sphere}(s₀:S.Nonempty)(a b:Stamp (timeMesh Λ))(v:∀p∈ footprint Λ l s S,a.val<p j)(w:∀p∈ footprint Λ l s S,p j<b.val):∃ z:Slab (timeMesh Λ),plowM S z ∧ a < z.lower ∧ z.upper<b:=by
 obtain ⟨u,p,h⟩:=(footprint_compact Λ l s S).exists_isMinOn (knack s _ s₀) (continuous_apply j).continuousOn
 obtain ⟨i,t,d⟩:=(footprint_compact Λ l s S).exists_isMaxOn (knack s _ s₀) (continuous_apply j).continuousOn
 obtain ⟨c,e,q⟩:=slipBetween _ _ (v u p) (Λ:=Λ)
 obtain ⟨x,n,r⟩:=slipBetween _ _ (w i t) (Λ:=Λ)
 exact ⟨⟨c,x,(lt_of_lt_of_le q (h t)).trans n⟩,fun i t=> ⟨q.le.trans (h t),(d t).trans n.le⟩,e,r⟩
lemma fleetHull{S:Sphere}{W:Lst}(s₀:plowM S W): ∀ᶠ m:ℕ in atTop, s≤ m∧ ∃ (r:ℤ)(w:ℕ), 0<w∧ notch R₁ m r=W.lower∧notch R₁ m (r+w)=W.upper∧ Between K j (B₀*r) (B₀*(r+w)) (volumeAround Λ l (m-s) S):=by
 filter_upwards [W.grids,eventually_ge_atTop s] with i q h; obtain ⟨⟨a,r⟩,b,p⟩:=q
 have hp:a<b:=(stamp_lt R₁ i _ _).1 (by rw [r,p]; exact W.thick)
 let d:=(b-a).toNat; have hd:0<d:=by omega
 have hg:a+(d:ℤ)=b:=by omega
 let U':= footprint Λ l s S; let X':=i-s
 have hZ: SupportedPhysically Λ l i (volumeAround Λ l X' S) U':= (show s+(i-s)=i by omega) ▸ (has_footprint Λ l s S).persists (i-s) -- careful rewrites rhs too
 refine ⟨h,a,d,hd,r,hg.symm ▸ p,lists_between Y H j W (fun u p=>s₀ u p) hZ r (hg.symm ▸ p)⟩
end YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab.fleetHull
