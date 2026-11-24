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
-- Glair compound
local notation "Ms" n:max z:max=> notch (timeMesh Λ) n z
variable {F Z:ℕ→ℤ→Family (tent Y H)} {A B' C D':ℝ→ℝ}
variable (Q₁: Set ℝ)
structure Clears (F:ℕ→ℤ→Family (tent Y H))(A C:ℝ→ℝ):Prop where
 norms : ∃ O:ℝ→ (E₁).Op, (∀ z:ℝ→ E₁, Continuous z → Continuous (fun t=>O t (z t)))∧∀{n:ℕ},s≤n→∀p:ℤ, let m:=(Ms n p).val; m∈Q₁→∃ a b:ℤ, TestFamily K true (F n p) ∧ A m=(Ms n a).val∧ C m=(Ms n b).val∧ Glair Y H D G d j c x (s:=n) (F n p) a b (O m)
local notation "Tg"=> Clears Y H D G d j c x s Q₁
local notation "Up₀"=> ride Y H V Q G.clipped j false (c j) (χ j)
local notation "Up₁"=> upCycle Y H D G u t d j c x
variable (h:Continuous B')(p:Continuous C)(e:Set.EqOn B' C Q₁)
local notation "η"=> fun x:ℝ=>affer (B' x) (C x)
lemma clears_one (f:(E₁).Op)(q:TimedEve Y H D G d j c x s F A B' f): Tg F A B':= by
 refine ⟨fun _=> f,fun z h=> f.continuous.comp h,?_⟩
 intro n p v a _; exact q.learns p v
include h p
lemma eta_cont:Continuous (fun x'=> affer (B' x') (C x')):=continuous_real_toNNReal.comp (p.sub h)
lemma clears_post (v:Tg F A B')(w:Tg Z C D')(q:∀ m∈ Q₁,B' m ≤ C m): Tg (F*Z) A D':=by
 obtain ⟨O,g,s₀⟩:= v.norms; obtain ⟨B,z,t'⟩:=w.norms
 refine ⟨fun i=> (O i).comp (((Up₀).E ((η) i)).comp (B i)), fun y v=>g _ (positiveCont (Up₀) _ _ (z _ v) (eta_cont h p)),?_⟩
 intro n v r y yr; obtain ⟨a,b,S,l,u,h⟩:=s₀ v r yr; obtain ⟨i,j₁,T,w,t,p⟩:=t' v r yr
 refine ⟨a,j₁,S.mul T,l,t,?_⟩
 change B' y= _ at u; change C y= _ at w
 change Glair Y H D G d j c x (s:=n) (F n r*Z n r) a j₁ ((O y).comp (((Up₀).E (affer (B' y) (C y))).comp _))
 rw [u,w]; exact melted Y H D G d j c x n T (u ▸ w ▸ q y yr) h p
include t
lemma clears_groom (v:∃ X W,TimedOdd Y H D G u t d j c x s F A B' X W)(w:∃ X W,TimedOdd Y H D G u t d j c x s Z C D' X W)(q:∀m∈ Q₁,B' m≤ C m): Tg (F*Z) A D':=by
 obtain ⟨X,W,f⟩:=v; obtain ⟨X',W',f'⟩:=w
 refine ⟨fun i=> W.comp (((Up₁).E ((η) i)).comp X'), fun y z=> W.continuous.comp (positiveCont (Up₁) _ _ (X'.continuous.comp z) (eta_cont h p)),?_⟩
 intro n v r y yr
 obtain ⟨a,b,S,tS,lS,rS,_,h₁⟩:=f.learns v r
 obtain ⟨i,j',T₂,tF,lF,rF,h₂,_⟩:=f'.learns v r
 refine ⟨a,j',aux_test ((tS.mono (subset_union_left (s₂:=T₂))).mul (tF.mono subset_union_right)),lS,rF,?_⟩
 change B' y=_ at rS; change C y=_ at lF
 change Glair Y H D G d j c x (s:=n) _ a j' (W.comp (((Up₁).E (affer (B' y) (C y))).comp X'))
 rw [rS,lF]; exact clasp Y H D G u t d j c x n tF (rS ▸ lF ▸ q y yr) h₁ h₂
omit t h p
def Zest (F:ℕ→ℤ→Family (tent Y H)): Prop := ∃ S:ℝ→ℂ,Continuous S∧∀{n:ℕ},s≤n→∀ p:ℤ,(Ms n p).val ∈ Q₁→ S (Ms n p).val=ψ n (F n p)
lemma zest_p (h:Tg F A B'): Zest Y H D G d c x s Q₁ F:=by
 obtain ⟨O,z,t⟩:=h.norms; refine ⟨fun t=>inner ℂ Ωe (O t Ωe),continuous_const.inner (z _ continuous_const),?_⟩
 intro n h p g; obtain ⟨a,b,u,_,_,k⟩:= t h p g
 exact singed Y H D G d j c x n u k
end YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab.clears_groom
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab.clears_post
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab.zest_p
