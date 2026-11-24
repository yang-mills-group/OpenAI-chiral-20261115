import YM.SU5.Relativistic.Northeast
import YM.SU5.Relativistic.BoothProj
import YM.SU5.Relativistic.Quintile
import YM.SU5.Relativistic.StreetSign
import YM.SU5.Relativistic.FirGreen
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
local notation "M" n:max=> cargoV Y H D G u t j s n
local notation "B₁" s:max=> creed Y H D G d j c x s

open HostLegal MeshClock
local notation "R₁"=> timeMesh Λ
local notation "U"=>flier Y H D G u t d j c x
variable (k:Axis)(σ:k≠j)
-- parity-ind in pose computations
variable {Z:Calibration}{S:Finset Cover}{v b₀:Bool}{F:Family Z}
open Signs
local notation "μ"=> mirror K j 0
local notation "P₁"=>perroll Y H D G u t d j c x s ⟨k,σ⟩
local notation "Π"=>upCycle Y H D G u t d j c x
local notation "ξ"=> (U).entry s

variable {S V':Finset Cover}{f g:Family (tent Y H)}(p:InTest (tent Y H) true S true f)(q:InTest (tent Y H) true V' true g)
local notation "Δ₀" => relocate (tent Y H)
local notation "Kv" J:max k:max F:max T:max=>stringUp Y H D G d J c x s k F T
include D G t σ
local notation "Yp"=>Signs.finalProject (Π) (P₁)
lemma behaves(X Y':Cabin (tent Y H) j): Tendsto (fun w:ℕ×ℕ=> (Kv j k (mirror K j 0 X.val) Y'.val) w.1 w.2) atTop (𝓝 (inner ℂ (Yp (ξ X)) (Yp (ξ Y')))):=by
 rw [← Signs.paid (Π) (P₁) (fun v a=>acrossE Y H D G u t d j c x s ⟨k,σ⟩ a v)]
 obtain ⟨S,h,z⟩:=hutSpec j K X; obtain ⟨W,h',v⟩:=hutSpec j K Y'
 exact northeast Y H D G u t d j c x s k σ (axial K j 0 h) h' _ _ (stockZero Y H D G u t d j c x s k σ X Y')
include p q
-- shifted sunrise (both later) of odd footprint. true for any. connect shifted kernel reflected readings with deep costs.
lemma inTorsion {n:ℕ}(m l:ℤ) :
    (Kv j k (relocate K j (- (n:ℤ)) f) (relocate K j (n:ℤ) g)) m l = (Kv j k f g) (m+n+n) l:=by
 let F':= Δ₀ j (m+(n:ℤ)+n) (Δ₀ k l g); have hx:=froll j (froll k q l) (m+n+n)
 have hu: TestFamily K true (Complex.I • (f*F')):=by
    apply TestFamily.scale; exact aux_test ((p.mono (Finset.subset_union_left (s₂:=plow K j _ (plow K k _ _)))).mul (hx.mono subset_union_right))
 have ht: Δ₀ j (-(n:ℤ)) (Complex.I • (f*F'))=Complex.I • (Δ₀ j (-(n:ℤ)) f * Δ₀ j m (Δ₀ k l (Δ₀ j n g))):=by
    have h(j:Axis)(p:ℤ)(F:Family K)(c:ℂ): Δ₀ j p (c • F)=c • Δ₀ j p F:=chime_scale K j _ c
    rw [h,relocate_mul]; unfold F'
    rw [unions K k j q, edge_roll j _ _ (froll k q _), edge_roll j _ _ (froll k q _), show - (n:ℤ)+(m+n+n)=m+n by omega]
 unfold stringUp; rw [←ht]; exact elect_slide _ _ _ _ _ _ _ _ hu (2* - (n:ℤ)) s
omit q
lemma mail {n:ℕ}(x': F₀) (P':μ f=f) (h:x'.val=relocate K j (n:ℤ) f):Yp (ξ x')=0:=by
 apply (inner_self_eq_zero (𝕜:=ℂ)).mp
 have hv:= behaves Y H D G u t d j c x s k σ x' x'; have h0:=vanishing_ff Y H D G u t d j c x s k σ p
 refine tendsto_nhds_unique hv ?_
 have ht:Tendsto (fun (r:ℕ×ℕ)=> (r.1+n+n,r.2)) atTop atTop:=by
    rw [Filter.tendsto_atTop]; intro (a,b); filter_upwards [eventually_ge_atTop (a,b)] with t e; exact ⟨Nat.le_trans (show a ≤ t.1 from e.1) (by omega),e.2⟩
 refine (h0.comp ht).congr fun i=>?_ ; dsimp only [Function.comp_apply]
 push_cast; rw [h,backsV j p,P',inTorsion Y H D G u t d j c x s k σ p p]
omit p
lemma projection_sees (y:(U).booth)(v:ℝ≥0): Yp ((Π).E v y)=Yp y:=by
 let C':= Yp; let Y':=(Π); let D':=P₁
 have hc(i z): D'.wind i * Y'.E z=Y'.E z * D'.wind i :=acrossE Y H D G u t d j c x s ⟨k,σ⟩ z i
 change C' (Y'.E v y)=C' y
 apply ext_inner_right ℂ; intro w
 have hw(i : (U).booth):inner ℂ (C' i) w=inner ℂ i (C' w):= Signs.final_self Y' D' hc i w
 rw [hw,hw,Y'.swing]; have hv:C' w∈ Y'.ground:=Submodule.starProjection_apply_mem ..; rw [(Y'.fixed _).mp hv v]
lemma mean_absent (z:F₀): Yp (ξ z)=0 :=by
 obtain ⟨T',e,h⟩:=hutSpec j K z
 let X:= reflectedBox j 0 T'; let a:= μ z.val; let C := z.val + a; let c' := Complex.I • z.val + star Complex.I • a
 have hX: InTest K true X true a:= axial K j 0 e
 have hv:InTest K true (T'∪X) true C:= (e.mono subset_union_left).add (hX.mono subset_union_right)
 have ht:InTest K true (T'∪X) true c':= (.smul _ (e.mono subset_union_left) : InTest K true (T'∪X) true _).add (.smul _ (hX.mono subset_union_right))
 have hp:μ C=C:=by unfold C a; rw [mirror_plus,reversal K j 0 e,add_comm]
 have hg:μ c'=c':=by unfold c' a; rw [mirror_plus,mirror_scale,mirror_scale,star_star, reversal K j 0 e,add_comm]
 obtain ⟨n,h⟩:= (onstrip Y H j hv).exists
 let f:F₀:=⟨Δ₀ j n C,_,froll j hv n,h⟩
 let g:F₀:=⟨Δ₀ j n c',_,froll j ht n,h⟩
 have hh:=mail Y H D G u t d j c x s k σ hv f hp rfl; have he:=mail Y H D G u t d j c x s k σ ht g hg rfl
 have h2:f + (-Complex.I) • g=(2:ℂ) • α n z:=by
    apply Subtype.ext; change Δ₀ j n C + -Complex.I • Δ₀ j n c'=(2:ℂ) • Δ₀ j n z.val
    have hp(j:Axis)(v:ℤ)(f g:Family K): Δ₀ j v (f+g)=Δ₀ j v f+Δ₀ j v g:=chime_plus _ _ _
    have hz(v:ℂ)(j:Axis)(p:ℤ)(F:Family K): Δ₀ j p (v • F)=v • Δ₀ j p F:=chime_scale K j _ v
    unfold C c'; rw [hp,hp,hz,hz, smul_add,smul_smul,smul_smul,show -Complex.I*Complex.I=1 by simp, show -Complex.I*star Complex.I= -1 by simp,one_smul,neg_one_smul,two_smul]; abel
 have hu:Yp (ξ (α n z))=0:=by
    have hx:Yp (ξ ((2:ℂ) • α n z))=0:=by rw [←h2,map_add,map_smul,map_add,map_smul,hh,he]; simp
    simpa only [map_smul,smul_eq_zero,OfNat.ofNat_ne_zero, false_or] using hx -- lemma
 have he:(Π).E (whenly (timeMesh Λ) s n) (ξ z)= ξ (α n z):=by rw [visits Y H D G u t d j c x s n s (le_refl _),Nat.sub_self,pow_zero,one_mul]
 rw [← he,projection_sees] at hu; exact hu
end YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab.mean_absent
