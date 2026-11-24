import YM.SU5.Relativistic.Signer
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
-- Cad lemmas including transverse geometric reorder. Plane act. 
local notation "Ms" n:max z:max=> notch (timeMesh Λ) n z
lemma posedC {Z:Calibration}{S:Finset Cover}{w: Bool}{F:Family Z}(p:List Axis)(j:Axis)(h:InTest Z true S w F)(i:Cover)(r:ℤ): cad Z p i (relocate Z j r F)= relocate Z j r (cad Z p i F):=by induction p with| nil=> rfl| cons k p ih=> rw [cad_step,cad_step,ih,unions Z k j (tour_test i p h)]
lemma cad_rank {Z:Calibration}{S:Finset Cover}{w:Bool}{F:Family Z}{l l':List Axis}(v:l.Perm l')(h:InTest Z true S w F)(i:Cover): cad Z l i F=cad Z l' i F:=by
 induction v with|nil=>rfl|cons k _ ih=>rw [cad_step,cad_step,ih]|swap k a lt=>exact unions Z _ _ (tour_test i lt h) (i a) (i k)|trans _ _ p q=>exact p.trans q
lemma transitX {Z:Calibration}{S:Finset Cover}{w:Bool}{F:Family Z}(h:InTest Z true S w F)(j:Axis)(i:Cover)(z:ℤ)(e:i j=0): Vacancy.chart Z (Function.update i j z) F= relocate Z j z (Vacancy.chart Z i F):=by
 unfold Vacancy.chart; rw [cad_rank (normal j) h,cad_rank (normal j) h,cad_step,cad_step,e,Function.update_self,edge_void j (tour_test i _ h)]
 refine congrArg (relocate Z j z) ?_
 let d(k:Trans j):= i k.val
 rw [transverse_eq Z j _ _ d (fun k=> Function.update_of_ne k.property ..),← transverse_eq Z j _ i d (fun _=> rfl)]
open Germ SelectionAnalysis
-- physical Players uniqueness notch ext
variable (k:Trans j)
local notation "W" s:max k:max=> perroll Y H D G u t d j c x s k
noncomputable def carrU (k:Trans j)(v:Stamp R₁):(U).booth.Op:=by
 let n:=(notch_exists (timeMesh Λ) v).choose
 let z:=(notch_exists (timeMesh Λ) v).choose_spec.choose
 exact sendU Y H D G u t d j c x n k z
local notation "Zx"=>carrU Y H D G u t d j c x
lemma carr_site (r:ℤ): Zx k (Ms s r)= sendU Y H D G u t d j c x s k r:=by
 let Y':= notch_exists R₁ (Ms s r)
 let n:= Y'.choose; let z:= Y'.choose_spec.choose
 have ht: Ms n z=Ms s r:=Y'.choose_spec.choose_spec
 let m:=max s n; have hs:s≤ m:=le_max_left ..; have hv:n≤ m:=le_max_right ..
 change sendU Y H D G u t d j c x n k z=_; rw [grove Y H D G u t d j c x n k hv, grove Y H D G u t d j c x s k hs]
 exact congrArg _ ((notch_tight R₁ m) ((notch_up R₁ n m hv z).trans (ht.trans (notch_up R₁ s m hs r).symm))) -- syntax partial
noncomputable def roadCrew: Alliance (Trans j) (marks R₁) E₂ where
 crew k:={ play:=Zx k
           pulls i v:=by
              obtain ⟨n,z,rfl⟩:= notch_exists R₁ i; rw [carr_site]; let P₁:= W n k
              exact (P₁.wind z|>.le_opNorm v).trans (mul_le_of_le_one_left (norm_nonneg _) (P₁.small _)) -- P₁ pulls def exact
           play_zero:=by rw [←notch_zero R₁ 0,carr_site]; exact Rolls.nil (W 0 k)
           piles a b:=by
              obtain ⟨n,y,z⟩:= ((MeshRead a).and (MeshRead b)).exists; obtain ⟨u',rfl⟩:=y; obtain ⟨b,rfl⟩:=z
              rw [←notch_add,carr_site,carr_site,carr_site]; exact Rolls.along (W n k) .. }
 cCom a b i j':=by
    obtain ⟨n,x',rfl⟩:= notch_exists R₁ i; obtain ⟨m,t',rfl⟩:= notch_exists R₁ j'
    change (Zx a (Ms n x')).comp (Zx b (Ms m t')) = (Zx b (Ms m t')).comp (Zx a (Ms n x')); rw [carr_site,carr_site]; exact alongD ..
local notation "P₁"=> roadCrew Y H D G u t d j c x
local notation "Up₁"=> upCycle Y H D G u t d j c x
lemma togetherP (k:Trans j)(i:Stamp R₁)(v:ℝ≥0): (((P₁).crew k).play i).comp ((Up₁).E v)=((Up₁).E v).comp (((P₁).crew k).play i):=by
 obtain ⟨s,x',rfl⟩:= notch_exists R₁ i
 change (Zx k _).comp _= _; -- occurrences hidden in RHS; change
 change (Zx k _).comp _= ((Up₁).E _).comp (Zx k _); rw [carr_site]; exact acrossE ..
noncomputable def trueSun : Sunbelt j (marks R₁) E₂ where
 track:= P₁
 list:=look j
 traverses:=look_all _
 unique_list:=look_one _
 heat:=(Up₁).E
 smooth:=(Up₁).continuousE
 diffusion z:=by simp_rw [(Up₁).sym]; exact (Up₁).continuousE _
local notation "Ξ₁"=> trueSun Y H D G u t d j c x
noncomputable def convoy := glass (Ξ₁) (daylight R₁) (Up₁) (togetherP Y H D G u t d j c x) -- constructor C
end YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab.convoy
