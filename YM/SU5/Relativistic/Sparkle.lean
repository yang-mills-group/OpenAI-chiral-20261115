import YM.SU5.Relativistic.Pagoda
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
variable {S T':Finset Cover}{b₀:Bool}{F H': Family (tent Y H)}(m:ℕ)
local notation "uX" m:max A:max q:max b:max z:max=> plated Y H (T:=T) j s q m z b A
local notation "ZT" n:max=> Zest Y H D G d c x n
structure Soft (b₀:Bool) (F H':Family (tent Y H)):Prop where
 moon : ∃ Q₁∈nhds (0:ℝ),∀ᶠ m:ℕ in atTop,∀ z:Cover,z j=0→ (ZT m) Q₁ ((uX m F false b₀ z)*(uX m H' true b₀ z))
local notation "Hg" m:max=> hulls (Λ:=Λ) (l:=l) j m
lemma shift_notice {W V':Slab R₁}(h:(W.upper)<V'.lower)(q p:Bool):
    ∀ᶠ a:ℝ in nhds 0, shifted q W.upper.val a< shifted p V'.lower.val a:=by
 have he(q:Bool)(r:ℝ): shifted q r 0=r:=by cases q <;> simp [shifted]
 exact (shifty q _).continuousAt.tendsto.eventually_lt (shifty p _).continuousAt.tendsto (by rw [he,he]; exact h) -- tune
include t
lemma soft_pay (h:InTest K true S b₀ F)(v: InTest K true T' b₀ H')(e:S.Nonempty)(r:T'.Nonempty)(w:slottedHere (Λ:=Λ) (l:=l) j s S T') (q p:Bool): ∃ Q₁∈nhds (0:ℝ),∀ᶠ m:ℕ in atTop,∀z:Cover,z j =0→(ZT m) Q₁ ((uX m F q b₀ z)*(uX m H' p b₀ z)):=by
 obtain ⟨a,f,g⟩:= slotFence j s e r w; obtain ⟨b,u'⟩:= slotLow j s e (Λ:=Λ) (l:=l); obtain ⟨k,u''⟩:=slotTall j s r (Λ:=Λ) (l:=l)
 obtain ⟨C,hC,_,y⟩:= slotMake j s e b a u' f
 obtain ⟨W,hW,xv,rW⟩:=slotMake j s r a k g u''
 let L:=shifted q C.upper.val; let R:=shifted p W.lower.val
 have ht:=shift_notice (W:=C) (V':=W) (y.trans xv) q p
 let Q₁: Set ℝ:={a| L a< R a}
 refine ⟨Q₁,ht,?_⟩
 filter_upwards [winFlight Y H D G u t d j c x s q h C hC,winFlight Y H D G u t d j c x s p v W hW] with n T₁ T₂ z Hz
 have hx:= T₁ z Hz; have hw:= T₂ z Hz
 have zP(a:ℝ)(h:a∈ Q₁): L a≤ R a:= (show L a< R a from h).le
 cases b₀
 · obtain ⟨V',t₀⟩:=hx; obtain ⟨W',w'⟩:=hw
   exact zest_p Y H D G d j c x n Q₁ (clears_post Y H D G d j c x n Q₁ (shifty q _) (shifty p _) (clears_one Y H D G d j c x n Q₁ V' t₀) (clears_one Y H D G d j c x n Q₁ W' w') zP)
 exact zest_p Y H D G d j c x n Q₁ (clears_groom Y H D G u t d j c x n Q₁ (shifty q _) (shifty p _) hx hw zP)
lemma soft_two (h:InTest K true S b₀ F)(v: InTest K true T' b₀ H')(e:S.Nonempty)(r:T'.Nonempty)(w:slottedHere (Λ:=Λ) (l:=l) j s S T' ∨ slottedHere (Λ:=Λ) (l:=l) j s T' S) : Soft Y H D G (T:=T) d j c x s b₀ F H':=by
 rcases w with w|w; exact ⟨soft_pay Y H D G u t d j c x s h v e r w false true⟩
 obtain ⟨Q₁,z,t'⟩:= soft_pay Y H D G u t d j c x s v h r e w true false
 refine ⟨Q₁,z,?_⟩
 filter_upwards [t',eventually_ge_atTop s] with m t' p y g
 obtain ⟨P₀,f,q⟩:= t' y g
 let a:=Sector.grainB b₀ b₀
 refine ⟨fun v=>a* P₀ v,continuous_const.mul f,?_⟩; intro n g l' z'
 have ht:=never_paid Y H D G u t j s false m y h p g l'; have hv:= never_paid Y H D G u t j s true m y v p g l'; let B₁':=(uX m F false b₀ y) n l'; let Dd:=(uX m H' true b₀ y) n l'
 have hΓ:TestFamily K true (Dd*B₁'):=by
    obtain ⟨S,r⟩:=ht; obtain ⟨V₁,u⟩:=hv
    have hp:= (u.mono (Finset.subset_union_left (s₂:=S))).mul (r.mono subset_union_right); rw [Bool.xor_self] at hp; exact aux_test hp
 change a* P₀ _= ψ n (B₁'*Dd)
 rw [q g l' z',signMark K ht.choose_spec hv.choose_spec] -- rw unifies let
 exact ((audition Y H V G _ c _ n).map_smul a (show Dome K from ⟨_,hΓ⟩)).symm
end YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab.soft_two
