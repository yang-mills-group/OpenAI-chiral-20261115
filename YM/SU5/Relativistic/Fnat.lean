import YM.SU5.Relativistic.Wreaths
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
variable {w:ℕ}(F : Slice (tent Y H) j w)
local notation "F₁" p:max=> uphill Y H D G u t j s F p
local notation "F₂"=> wreath Y H j s F
local notation "Bc"=> procession Y H V Q G.clipped j false (c j) (χ j)
local notation "By" p:max=> Bc (entrance Y H V s Q G.clipped j false (c j) (F₂) p)
def Season (s:ℕ):=Σ (n:{k:ℕ//s≤k}), Tower.Field Y H n.val j 0 false
variable {s}
def folks (i:Season Y H j s):indoor Y H V Q G.clipped j false (c j) (χ j):= (Φ i.fst.val) i.2
variable (s)
local notation "Ψ₀" k:max=> folks Y H D G d j c x (s:=k)
lemma folks_dense : DenseRange (folks Y H D G d j c x (s:=s)):=by
 refine (stroll_dense Y H V Q G.clipped j false (c j) (χ j)).mono ?_
 intro v t'; obtain ⟨r,q⟩:= Set.mem_iUnion.mp t'; obtain ⟨u,rfl⟩:=q
 let m:=max s r; let h:s≤ m:=le_max_left ..; let hp:r≤ m:=le_max_right ..
 exact ⟨⟨⟨m,h⟩,Raise Y H G.history.circuit j 0 false r m hp u⟩,(flourishes Y H V _ Q G.clipped j false (c j) (χ j) _ hp u)⟩
local notation "Ba" k:max p:max=> sprout Y H j k (F₁ p)
include t
lemma terminal (bb:0<w) : ∃ L:(indoor Y H D.univ_ G.history G.clipped j false (c j) (χ j))→L[ℂ] E₂,∀ k,∀z:s≤ k,∀x':W₀ k, L ((Φ k) x')=(Υ k) ((Ba k z) x'):=by
 let U₀:= Season Y H j s
 let R:= Ψ₀ s
 let Z(i:U₀):E₂ := let k:=i.fst.val; let v:= i.fst.property; (Υ k) ((Ba k v) i.2)
 let M₀:=By (show 0 < w+w from by omega); let d':= Real.sqrt ‖M₀‖
 have h(k)(p:s≤ k)(x':W₀ k): ‖(Υ k) ((Ba k p) x')‖≤d'* ‖(Φ k) x'‖:=by
    let y:=(Φ k) x'; have hp:d' ^ 2= ‖M₀‖:=Real.sq_sqrt (norm_nonneg _)
    apply (sq_le_sq₀ (norm_nonneg _) (by unfold d'; positivity)).1
    have hz: inner ℂ ((Υ k) ((Ba k p) x')) ((Υ k) ((Ba k p) x'))= inner ℂ y (M₀ y):= plait Y H D G u t d j c x s F p bb x'
    rw [mul_pow,hp]
    calc _ = ‖inner ℂ y (M₀ y)‖ := by rw [←hz,inner_self_eq_norm_sq_to_K,norm_pow]; simp
     _ ≤ ‖y‖ * ‖M₀ y‖:= norm_inner_le_norm ..
     _ ≤ ‖y‖*(‖M₀‖*‖y‖):=mul_le_mul_of_nonneg_left (M₀.le_opNorm y) (norm_nonneg _)
     _ = _ := by unfold y; ring
 let a: _root_.YM.Kernel.Gram (fun x y:U₀=> inner ℂ (R x) (R y)):= ⟨E₁,R,(folks_dense Y H D G d j c x s).mono Submodule.subset_span,fun i j=> rfl⟩
 have he(f:U₀ →₀ ℂ): ‖Finsupp.linearCombination ℂ Z f‖≤ d'* ‖a.stems f‖:=by
    let m:=max s (f.support.sup fun i=> i.fst.val); have h₀:s≤ m:=le_max_left ..
    have hv(i:U₀)(p:i∈f.support): i.fst.val≤ m:=(Finset.le_sup (f:=fun i=> i.fst.val) p).trans (le_max_right ..)
    let x'(i:U₀):W₀ m:= if h:i.fst.val≤ m then Raise Y H G.history.circuit j 0 false i.fst.val m h i.2 else 0
    have hz(i:U₀)(p:i∈f.support): (Υ m) ((Ba m h₀) (x' i))= Z i:=by
       unfold x'; rw [dif_pos (hv i p),←first_glass Y H D G u t d j c x s F i.fst.property (hv i p), Tier.increase _ (hv i p)]
    let Y₁:= f.sum fun i p=> p • x' i
    have hX: Finsupp.linearCombination ℂ Z f=(Υ m) ((Ba m h₀) Y₁):=by
       unfold Y₁; simp only [map_finsuppSum,map_smul,Finsupp.linearCombination_apply]; unfold Finsupp.sum; exact Finset.sum_congr rfl fun i p=> congrArg (f i • ·) (hz i p).symm
    have hY:a.stems f=(Φ m) Y₁:=by
       unfold Y₁; simp only [map_finsuppSum,map_smul,_root_.YM.Kernel.Gram.stems,Finsupp.linearCombination_apply]; unfold Finsupp.sum; refine Finset.sum_congr rfl fun i p=>?_ ; dsimp only; unfold x'; rw [dif_pos (hv i p)]; exact congrArg (fun z:E₁=> f i • z) (flourishes Y H V _ Q G.clipped j false (c j) (χ j) _ (hv i p) _).symm
    rw [hX,hY]; exact h m h₀ _
 obtain ⟨L,_,t'⟩:= a.by_bound Z d' (Real.sqrt_nonneg _) he
 exact ⟨L,fun k z x' => t' ⟨⟨k,z⟩,x'⟩⟩
noncomputable def blossoms (b:0<w) : (indoor Y H V Q G.clipped j false (c j) (χ j))→L[ℂ] E₂:= (terminal Y H D G u t d j c x s F b).choose
local notation "Bc₀" s:max F:max b:max=> blossoms Y H D G u t d j c x s F b
lemma blossoms_later (b:0<w) {k:ℕ}(v:s≤k)(z:W₀ k): (Bc₀ s F b) ((Φ k) z)= (Υ k) ((Ba k v) z):= (terminal Y H D G u t d j c x s F b).choose_spec k v z
end YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab.blossoms_later
