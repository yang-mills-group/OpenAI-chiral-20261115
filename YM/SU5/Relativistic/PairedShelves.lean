import YM.SU5.Relativistic.Consist
/-!
# Geometry registration of local physical polynomials.
-/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 350000
set_option synthInstance.maxSize 30000
set_option maxRecDepth 5500
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction
open Function Set Filter MeasureTheory Metric
open Lattice Wilson RG SU Lat Mir RP Reflect Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Py Py.Rate LocalLimit PhaseChoice Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy MeshClock Selected
open Tapestry Tapestry.Altitude Tapestry.Exhibition
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
variable {a b:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}
    {L:Rack Λ l}{B:Clay Λ l}(D : Exhibition Y H a b I E L B)(G:SatinVerification.GroundExtension (i:=a) (k:=b) (E:=E) Y H)
variable (j:Axis) (J: Arena Y H G.history.circuit j 0 false)
local notation "M"=> timeMesh Λ
local notation "N" i:max z:max=> notch M i z
local notation "D₀"=> Dome (tent Y H)
local notation "Τ"=> Cloud (Dome (tent Y H))
local notation "P₀" n:max=> vistaFinish Y H n D
local notation "d★" => vistaDressing Y H D
local notation "B₀" => driveAlgebra Y H D.univ_ G.history G.clipped j false J
local notation "Rg" t:max => Docked Y H D.univ_ t G.history G.clipped j J

local notation "ρ"=> D.univ_
local notation "reach" n:max f:max => reachMark (tent Y H) ((P₀ n) f)
section billing
variable (d:Axis)(c:∀ j:Axis,Arena Y H G.history.circuit j 0 false)(χ : displayAlgebra Y H D.univ_ G.history G.clipped d false (c d) →⋆ₐ[ℂ] ℂ)
local notation "χ̂" j:max=> displacement Y H D.univ_ G.history G.clipped d false (c d) χ j (c j)
local notation "Χ"=> SameCharacter.resident Y H D.univ_ G d false (c d) χ
local notation "Ψ"=> onDrawing Y H D.univ_ G D d c Χ
local notation "Θ"=> procession Y H D.univ_ G.history G.clipped j false (c j) (χ̂ j)
local notation "Ρ"=>indoor Y H D.univ_ G.history G.clipped j false (c j) (χ̂ j)
local notation "V"=>fort Y H D.univ_ G.history G.clipped j false (c j) (χ̂ j)
local notation "p★"=>saunters Y H D.univ_ G.history G.clipped j false (c j) (χ̂ j)
local notation "ω"=> vocation Y H D.univ_ G.history G.clipped j false (c j) (χ̂ j)
local notation "Ω"=> doorstep Y H D.univ_ G.history G.clipped j false (c j) (χ̂ j)
local notation "A"=>ride Y H D.univ_ G.history G.clipped j false (c j) (χ̂ j)
local notation "Ξ"=> peninsula Y H D.univ_ G.history G.clipped j false (c j) (χ̂ j)
local notation "E□"=> encase Y H D.univ_ G.history G.clipped j (c j) (χ̂ j)
local notation "P□"=> mainsea Y H D.univ_ G.history G.clipped j false (c j) (χ̂ j)
local notation "e□"=> follows_road Y H D.univ_ G.history G.clipped j false (c j) (χ̂ j)
local notation "B□"=> docket Y H D G j (c j)
local notation "Φ"=> driveAlgebra Y H D.univ_ G.history G.clipped j false (c j)
local notation "dock" n:max => Docked Y H D.univ_ n G.history G.clipped j (c j)
local notation "Zg" t:max => (Axis→Fin ((timeMesh Λ).L^t))

section stable
lemma packDense {z y:ℝ}(M':MeshClock.Mesh)(p:z< y): ∃ a:Stamp M', z< (a:ℝ) ∧ (a:ℝ)< y:=by
 obtain ⟨x,h,e⟩:= (MeshClock.daylight M').exists_mem_open isOpen_Ioo (Set.nonempty_Ioo.mpr p); exact ⟨⟨x,h⟩,e⟩
variable {U W:Set RSpace}
lemma leased_geometry (M':Mesh)(h:IsCompact U)(v:IsCompact W)(p:∀ x∈U,∀ y∈ W,x j< y j):
    ∃ (g f T T':Slab M'),
       U⊆ {z:RSpace| (g.lower:ℝ) ≤ z j ∧ z j ≤ g.upper.val} ∧ W⊆{z:RSpace| (f.lower:ℝ) ≤ z j ∧ z j ≤ f.upper.val} ∧
       T.lower<g.lower ∧ g.upper<T.upper ∧ T'.lower<f.lower ∧ f.upper<T'.upper ∧ T.upper<T'.lower := by
 have h':∃ a b c d:ℝ,a<b ∧ b<c ∧ c<d∧ U⊆ {z:RSpace|a ≤ z j ∧ z j ≤ b} ∧ W⊆ {z:RSpace| c ≤ z j ∧ z j ≤ d}:=by
    have ht(s:Set RSpace)(t:IsCompact s): ∃ a b:ℝ,a<b∧ s ⊆ {z:RSpace| a≤ z j ∧ z j ≤ b}:=by
       obtain ⟨b,g⟩:= (t.image (continuous_apply j)).bddAbove
       obtain ⟨a,h⟩:= (t.image (continuous_apply j)).bddBelow
       refine ⟨a,max b a+1, by linarith [le_max_right b a],fun x k=>?_⟩ -- tune
       exact ⟨h (Set.mem_image_of_mem _ k), (g (Set.mem_image_of_mem _ k)).trans (by linarith [le_max_left b a])⟩
    rcases Set.eq_empty_or_nonempty U with u|u
    · obtain ⟨a,b,c,e⟩:= ht W v; refine ⟨a-2,a-1,a,b,by linarith,by linarith,c,?_, e⟩; simp [u]
    rcases Set.eq_empty_or_nonempty W with w|w
    · obtain ⟨a,b,c,e⟩:= ht U h; refine ⟨a,b,b+1,b+2,c,by linarith,by linarith,e,?_⟩; simp [w]
    obtain ⟨a,x,ha⟩:= h.exists_isMaxOn u (continuous_apply j|>.continuousOn)
    obtain ⟨b,y,hb⟩:= v.exists_isMinOn w (continuous_apply j|>.continuousOn)
    obtain ⟨c,c',hc⟩:= h.exists_isMinOn u (continuous_apply j|>.continuousOn)
    obtain ⟨d,d',hd⟩:= v.exists_isMaxOn w (continuous_apply j|>.continuousOn)
    refine ⟨c j-1,a j,b j,d j+1,by have hx:c j≤ a j:= hc x; linarith, p _ x _ y,by have hx:b j ≤ d j:= hd y; linarith,fun i v=>?_,fun i v=>?_⟩
    · exact ⟨(sub_le_self _ (by norm_num)).trans (hc v), ha v⟩
    exact ⟨hb v,(hd v).trans (le_add_of_nonneg_right zero_le_one)⟩
 obtain ⟨a,b,c,d,h₁,h₂,h₃,hA,hB⟩:=h'
 obtain ⟨x,hx,hx'⟩:= packDense M' (show a-1<a by linarith)
 obtain ⟨t,hx0,hx₁⟩:= packDense M' hx
 obtain ⟨a₀,q,q₁⟩:= packDense M' h₂
 obtain ⟨y,_,hy⟩:= packDense M' q
 have hxy: b<y.val:=by assumption
 obtain ⟨p,hp,hp'⟩:=packDense M' q₁; obtain ⟨q,hq,hq'⟩:=packDense M' hp'
 obtain ⟨r,w,h⟩:=packDense M' (show d<d+1 by linarith); obtain ⟨s,i,k⟩:= packDense M' h
 refine ⟨⟨x,y,hx'.trans (h₁.trans hxy)⟩,⟨q,r,hq'.trans (h₃.trans w)⟩,⟨t,a₀,hx₁.trans ((hx'.trans h₁).trans ?_)⟩,⟨p,s,hp'.trans (h₃.trans (w.trans i))⟩,fun j x=> ⟨hx'.le.trans (hA x).1,(hA x).2.trans hxy.le⟩, fun j x=>⟨hq'.le.trans (hB x).1,(hB x).2.trans w.le⟩,hx₁,hy,hq,i,hp⟩
 exact hxy.trans hy
local notation "f★" x:max y:max=> (fun i:Bool=> if i then y else x)
lemma pairShelf {X Z: Cloud (Dome (tent Y H))}{s t:ℕ} (hX:X∈ poet Y H s U) (hZ: Z∈ poet Y H t W) (h:IsCompact U)(v:IsCompact W)(p:∀ x∈U,∀ y∈ W,x j < y j) :
    ∃ (n:ℕ)(S T : Bool → Slab (timeMesh Λ)), Corridor Y H j (f★ X Z) (fun _=> n) S T [false,true] (T false).lower 0 ∧
       (T false).upper < (T true).lower := by
  obtain ⟨g,f,R,J,u,x,ha,hb,hc,hd,he⟩:= leased_geometry j M h v p
  obtain ⟨n,hN,gv,GG,HH⟩:= ((eventually_ge_atTop s).and ((eventually_ge_atTop t).and (g.grids.and f.grids))).exists
  let S:= f★ g f
  let T:= f★ R J
  refine ⟨n,S,T,⟨ show _ from ⟨le_rfl,he.le,trivial⟩,fun i _=> ?_, fun i _=>?_⟩,he⟩
  · cases i
    · change Carries Y H n X j g; exact ⟨⟨U,h,circum_widens Y H Subset.rfl (Set.Iic_subset_Iic.mpr hN) hX,u⟩,GG⟩
    change Carries Y H n Z j f; exact ⟨⟨W,v,circum_widens Y H Subset.rfl (Set.Iic_subset_Iic.mpr gv) hZ,x⟩,HH⟩
  cases i
  · change R.lower.val< g.lower.val+0 ∧ g.upper.val+0<R.upper.val; rw [add_zero,add_zero]; exact ⟨ha,hb⟩
  change J.lower.val<f.lower.val+0 ∧ f.upper.val+0 <J.upper.val; rw [add_zero,add_zero]; exact ⟨hc,hd⟩
end stable
end billing
end YM.CF.Buffered.Afterglow.Tower.Reconstruction
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.pairShelf
