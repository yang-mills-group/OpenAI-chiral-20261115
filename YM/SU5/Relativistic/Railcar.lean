import YM.SU5.Relativistic.Waygo
import YM.SU5.Relativistic.Envelopes
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
local notation "N" n:max z:max=> notch (timeMesh Λ) n z
structure Sheaf {s:ℕ}(F:Family (tent Y H))(a b:ℤ)(B:E₁→L[ℂ] E₂) : Prop where
 earns (x':W₀ s) : ∃ z:Cabin (tent Y H) j, B ((Φ s) x')=(Υ s) z∧ z.val=Δ₀ j (-a) F* Δ₀ j (b-a) x'.val
structure Shale {s:ℕ}(F:Family (tent Y H))(a b:ℤ)(B:E₂ →L[ℂ] E₁) : Prop where
 earns (z:Cabin (tent Y H) j): ∃ x':W₀ s, B ((Υ s) z)=(Φ s) x'∧ x'.val=Δ₀ j (-a) F* Δ₀ j (b-a) z.val
structure Glair {s:ℕ} (F:Family (tent Y H))(a b:ℤ)(B:E₁ →L[ℂ] E₁): Prop where
 earns (x':W₀ s): ∃ z:W₀ s, B ((Φ s) x')= (Φ s) z∧ z.val=Δ₀ j (-a) F* Δ₀ j (b-a) x'.val
local notation "Bc₀" s:max F:max b:max=> blossoms Y H D G u t d j c x s F b
local notation "Bo" s:max F:max b:max=> otters Y H D G u t d j c x s F b
local notation "Pe" s:max F:max b:max=> procession Y H V Q G.clipped j false (c j) (χ j) (entrance Y H V s Q G.clipped j false (c j) F b)
variable {w:ℕ}(p:0<w){r r':ℤ} {H':Family (tent Y H)}
include t
lemma sheaf_h (F:Slice K j w) (h:r'=r+w)(v:F.f=Δ₀ j (-r) H'): Sheaf Y H D G u t d j c x (s:=s) H' r r' (Bc₀ s F p) :=by
 refine ⟨fun x'=> ⟨_,sprout_exact Y H D G u t d j c x s F p x',?_⟩⟩; change F.f* Δ₀ j w x'.val= _; rw [v,h,add_sub_cancel_left]
lemma shale_h (F:Slice K j w)(h:r'=r+w)(v:F.f=Δ₀ j (-r) H') : Shale Y H D G u t d j c x (s:=s) H' r r' (Bo s F p):=by
 refine ⟨fun z=> ⟨_,reeds_on Y H D G u t d j c x s F p z,?_⟩⟩; change F.f* Δ₀ j w z.val= _; rw [v,h,add_sub_cancel_left]
omit t
lemma glair_h (F:Entry Y H s j false w)(h:r'=r+w)(v:F.val.val=Δ₀ j (-r) H'):
    Glair Y H D G d j c x (s:=s) H' r r' (Pe s F p) :=by
 refine ⟨fun x'=>⟨_,slotted Y H V _ Q G.clipped j false (c j) (χ j) F p x',?_⟩⟩; rw [slab_eq,v,h,add_sub_cancel_left]
local notation "Ge" s:max=> Glair Y H D G d j c x (s:=s)
local notation "Up₀"=> ride Y H V Q G.clipped j false (c j) (χ j)
local notation "Up₁"=> upCycle Y H D G u t d j c x
noncomputable def affer (r w:ℝ):ℝ≥0:= (w-r).toNNReal
lemma affer_p (M₁:MeshClock.Mesh){a b:ℤ}{w:ℕ}(p:a+w=b)(n:ℕ): affer (notch M₁ n a).val (notch M₁ n b).val= whenly M₁ n w:=heatGap_stamp p n
lemma MovesJ {M₁:MeshClock.Mesh}{a b:ℤ}(h:(notch M₁ s a).val≤ (notch M₁ s b).val): ∃ n:ℕ,a+n=b∧affer (notch M₁ s a).val (notch M₁ s b).val=whenly M₁ s n:=by
 have he: a≤ b:= (stamp_le M₁ s _ _).1 h; let v:=(b-a).toNat; have p:a+v=b:=by unfold v; omega
 exact ⟨v,p,affer_p M₁ p s⟩
variable {A B₃ C Dd:ℤ}{F Z:Family (tent Y H)}
include t
lemma clasp {T':Finset Cover} {X:E₁→L[ℂ] E₂}{W:E₂→L[ℂ] E₁}(z:InTest K true T' true Z) (hz: (N s B₃).val≤ (N s C).val)(g:Shale Y H D G u t d j c x (s:=s) F A B₃ W)(p:Sheaf Y H D G u t d j c x (s:=s) Z C Dd X) : (Ge s) (F*Z) A Dd (W.comp (((Up₁).E (affer (N s B₃).val (N s C).val)).comp X)):=by
 constructor; intro x'; obtain ⟨n,h,hg⟩:=MovesJ s hz
 obtain ⟨U',t',hU⟩:=p.earns x'; obtain ⟨i,uw,hX⟩:=g.earns (walkV Y H j n U'); refine ⟨i,?_,?_⟩
 · simp only [ContinuousLinearMap.comp_apply,t',hg]; rw [visits Y H D G u t d j c x s n _ (le_refl _),Nat.sub_self,pow_zero,one_mul]; exact uw
 rw [hX]; change _ * Δ₀ j _ (Δ₀ j _ U'.val)= _; rw [edge_roll j _ _ (hutSpec j K U').choose_spec.1,hU,relocate_mul,relocate_mul,edge_roll j _ _ z,edge_roll j _ _ (eve_test Y H j s x').choose_spec.1,show _+ -C= -A by omega,show B₃-A+(n:ℤ)+(Dd-C)=Dd-A by omega,mul_assoc]
omit t
lemma melted {Xe W:(E₁).Op} (z:TestFamily K true Z) (hz:(N s B₃).val ≤ (N s C).val)(g:(Ge s) F A B₃ W)(e:(Ge s) Z C Dd Xe) : (Ge s) (F*Z) A Dd (W.comp (((Up₀).E (affer (N s B₃).val (N s C).val)).comp Xe)):=by
 constructor; intro x'; obtain ⟨n,h,hg⟩:=MovesJ s hz
 obtain ⟨U',t',hU⟩:=e.earns x'; obtain ⟨i,u,hX⟩:=g.earns (tick Y H s j 0 false (2*n) U'); refine ⟨i,?_,?_⟩
 · simp only [ContinuousLinearMap.comp_apply,t',hg]; simp only [arriving_eq]; rw [ride_ticks]; exact u
 rw [hX,timed_apply,edge_roll j _ _ (eve_test Y H j s U').choose_spec.1,hU,relocate_mul,relocate_mul,edge_roll j _ _ z.paid.choose_spec,edge_roll j _ _ (eve_test Y H j s x').choose_spec.1,show _+ -C= -A by omega,show B₃-A+(n:ℤ)+(Dd-C)=Dd-A by omega, mul_assoc] -- z of type TestFamily paid def ok
lemma singed {Bz:(indoor Y H V G.history G.clipped j false (c j) (χ j)).Op} (h:TestFamily K true F)(p:(Ge s) F A Dd Bz): inner ℂ Ωe (Bz Ωe)= ψ s F :=by
 let I':=unity Y H j 0 false s
 have hX: ∃ z:W₀ s, Bz Ωe=(Φ s) z ∧ z.val=Δ₀ j (-A) F:=by
    have ht:=Glair.earns p I'
    rcases ht with ⟨z,g,q⟩
    have hy:Δ₀ j (Dd-A) I'.val=1:=by change chime K j _ 1=1; rw [chime_unit]
    rw [show (Φ s) I'= Ωe from root Y H V s Q G.clipped j false (c j) (χ j)] at g
    rw [hy,mul_one] at q
    exact ⟨z,g,q⟩
 obtain ⟨v,z,hv⟩:=hX; rw [z]
 change inner ℂ Ωe (bud _ _ _ _ _ _ _ _ _ _ _) = _; rw [call,selected_here Y H D G d j c x s, future_val,hv]; exact elect_slide Y H V G j d c _ h (2*(-A)) s
end YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab.clasp
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab.singed
