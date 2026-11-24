import YM.SU5.Relativistic.Cupka
import YM.SU5.Relativistic.CaperV
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
open Germ SelectionAnalysis CF.Pannier.Chancel.ScreeV
local notation "uX" k:max m:max A:max q:max b:max z:max=> plated Y H (T:=T) k s q m z b A
local notation "Γ"=> marks (timeMesh Λ)
local notation "Ms" n:max z:max=> notch (timeMesh Λ) n z
local notation "δ"=> daylight (timeMesh Λ)
variable {S T':Finset Cover}{v:Bool}{F H':Family (tent Y H)}
variable {W:Hilbert}{X:Sunbelt j (marks (timeMesh Λ)) W}{Z W':W}
include t
lemma guaging (e:InTest K true S v F)(p:InTest K true T' v H')(h:Faze Y H D G (T:=T) d j c x s v F H' X Z W') (k:Trans j)(q:Soft Y H D G (T:=T) d k.val c x s v F H'):
   ∃ O:Set ℝ, IsOpen O ∧ (0:ℝ)∈O ∧ ∀ a:Axis→ ↥(marks (timeMesh Λ)), 0≤ (a j).val→ (a k.val).val ∈ O→ ContinuousAt (fun z:Γ=> X.playback Z W' (Function.update a k.val z) []) (a k.val):=by
 obtain ⟨V₁,r,t₁⟩:=q.moon
 obtain ⟨O,O',g,f⟩:= _root_.mem_nhds_iff.mp r
 refine ⟨O,g,f,?_⟩; intro a e₁ c₁
 let B:= Function.update a k.val 0
 obtain ⟨m,ψ',z,w⟩:= (t₁.and ((eventually_ge_atTop s).and (eventually_all.mpr fun i:Axis=> MeshRead (B i)))).exists
 choose d₀ hX using w; have hp: d₀ k.val=0:= notch_tight R₁ m (by rw [notch_zero,hX]; exact update_self ..)
 obtain ⟨z',P'₁,P₂⟩:= ψ' _ hp
 apply (P'₁.comp continuous_subtype_val).continuousAt.congr
 filter_upwards [(continuous_subtype_val.tendsto (a k.val)).eventually (g.mem_nhds c₁)] with b b'
 -- direction
 obtain ⟨n,p₀,r,t₀⟩:= ((eventually_ge_atTop m).and (MeshRead b)).exists
 let T'₁:Cover:= fun i=>castor R₁ m n (d₀ i); let T'₂:= Function.update T'₁ k.val r; let L:=Function.update a k.val b
 have hτ: T'₁ k.val=0:=by unfold T'₁; rw [hp, castor,mul_zero]
 have hx: L=(fun i=>Ms n (T'₂ i)):=by
    funext i; unfold L T'₂; by_cases e:i=k.val; · subst i; simpa only [Function.update_self] using t₀.symm
    rw [update_of_ne e,update_of_ne e]; unfold T'₁; rw [notch_up _ _ _ p₀, hX]; exact (update_of_ne e ..).symm
 have hg: 0≤ T'₂ j:= (stamp_le R₁ n _ _).1 ?_
 swap
 · rw [← show L j= _ from congrFun hx j, notch_zero]; unfold L; rw [Function.update_of_ne (Ne.symm k.property)]; exact e₁
 have hK:= P₂ p₀ r (show (Ms n r).val∈V₁ from by rw [t₀]; exact O' b')
 change z' b.val= X.playback Z W' L []
 rw [hx,h.usher (z.trans p₀) _ hg,←t₀,hK]
 simp only [Pi.mul_apply, plate_zero Y H D G u t k.val s m d₀ e z p₀ r, plate_more Y H D G u t k.val s m d₀ p z p₀ r]; unfold T'₂; rw [transitX (t.allSupport Y H V Q u s _ p) k.val T'₁ r hτ]
-- forecast projection
structure InnerRoad (P₁:Sunbelt j Γ W)(Z W':W): Prop where
 full: ∃ T:Trans j→Set ℝ, (∀ i,IsOpen (T i)) ∧ (∀ i,(0:ℝ)∈T i)∧ ∀i:Axis→ Γ,Passport T i→ P₁.playback Z W' i []= P₁.curtain (daylight R₁) Z W' (fun v=> (i v).val)
lemma full_r (e:InTest K true S v F)(p:InTest K true T' v H')(h:Faze Y H D G (T:=T) d j c x s v F H' X Z W')(q:∀k:Trans j,Soft Y H D G (T:=T) d k.val c x s v F H') : InnerRoad (Λ:=Λ) j X Z W':=by
 choose O w m s using (fun k=>guaging Y H D G u t d j c x s e p h k (q k))
 refine ⟨O,w,m,?_⟩; intro i g
 rw [← X.curtain_eq δ, ← album_r X Z W' O w i g X.list]; intro v x k p; exact s k v x.1 (x.2 k)
omit t
lemma Indoor_peak (q:InnerRoad (Λ:=Λ) j X Z W') : X.playback Z W' 0 []= X.curtain (daylight R₁) Z W' 0:=by
 obtain ⟨O,p,o,h⟩:=q.full; exact h 0 ⟨le_refl _,o⟩
lemma lastFaze (t':Faze Y H D G (T:=T) d j c x s v F H' X Z W') (e:InTest K true T' v H') : X.playback Z W' 0 []= ψ s (F*H'):=by
 have ht:0 ≤ (0:Cover) j:= le_rfl
 have hx:=t'.usher (le_refl _) 0 ht
 rw [show (fun i=>Ms s ((0:Cover) i))=(0:Axis→Γ) from funext (fun i=> notch_zero _ s),Nat.sub_self] at hx
 refine hx.trans ?_; change ψ s (_ * cad K ordinate 0 H')=_; generalize eV:ordinate=L
 suffices h:∀L:List Axis,cad K L 0 H'=H' by rw [h]; rfl
 intro L; induction L with| nil=>rfl|cons i l ih=>rw [cad_step,ih,Pi.zero_apply,edge_void i e]
end YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab.full_r
