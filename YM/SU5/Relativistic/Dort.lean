import YM.SU5.Relativistic.Aries
import YM.SU5.Relativistic.Desert
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
lemma stereotypical(X:F₀): Tendsto (fun n:ℕ=>inner ℂ ((Π).orth (ξ X)) ((P₁).wind n (ξ X))) atTop (𝓝 0):=by
 have ht:= stockZero Y H D G u t d j c x s k σ X X
 have hz:= behaves Y H D G u t d j c x s k σ X X
 rw [mean_absent Y H D G u t d j c x s k σ X,inner_zero_right] at hz; exact Signs.evaporates (P₁) ((Π).orth (ξ X)) (ξ X) ht hz
lemma planetary (y:(U).booth): Tendsto (fun n:ℕ=> inner ℂ ((Π).orth y) ((P₁).wind n y)) atTop (𝓝 0) :=by
 refine Signs.sterile (P₁) ((Π).orth) _ ((U).front) ?_ y
 intro X h; obtain ⟨q,f⟩:= Set.mem_iUnion.mp h; obtain ⟨f,rfl⟩:= f
 let v:=max q s; have hq:q≤v:=le_max_left ..; have hb:s≤ v:=le_max_right ..; let γ:= α 0 f
 let q':=(U).cl q v f; have hi: (U).entry v q'=(U).entry q f:=(U).increase hq f
 rw [←hi]; let M':=Λ.R.L.val^(v-s); have h0:0<M':=pow_pos Λ.R.L.property _
 have he:Tendsto (fun n:ℕ=> M'*n) atTop atTop:= tendsto_atTop_mono (show (fun n:ℕ=>n) ≤ fun n:ℕ=> M'*n from fun n=>by simpa using Nat.mul_le_mul_right n h0) tendsto_id
 refine ((stereotypical Y H D G u t d j c x v k σ q').comp he).congr ?_; intro i
 dsimp only [Function.comp_apply]; change inner ℂ _ (sendU Y H D G u t d j c x v ⟨k,σ⟩ _ (_))= inner ℂ ((Π).orth _) (sendU Y H D G u t d j c x s ⟨k,σ⟩ _ _)
 rw [grove Y H D G u t d j c x s ⟨k,σ⟩ hb]; unfold M' castor; push_cast; rfl
lemma phantom (z:(U).cabin.H)(p: z∈(Π).ground)(c':ℂ)(q:sendU Y H D G u t d j c x s ⟨k,σ⟩ 1 z=c' • z): z=0 :=by
 apply Signs.dies (P₁) z _ c' q
 have hz:= planetary Y H D G u t d j c x s k σ z; rwa [show (Π).orth z=z from Submodule.starProjection_eq_self_iff.mpr p] at hz

-- zero for all marks, not only on huts. positive quadrant and negative etc
include p q
lemma whole_qturn: Tendsto (fun t:ℕ×ℕ=> (Kv j k f g) t.1 t.2) atTop (𝓝 0) :=by
 obtain ⟨n,h,v⟩ := ((onstrip Y H j (axial K j 0 p)).and (onstrip Y H j q)).exists
 let X:F₀:=⟨Δ₀ j n (mirror K j 0 f),_, froll j (axial K j 0 p) _,h⟩; let Y': F₀:=⟨Δ₀ j n g,_, froll j q _,v⟩
 have hp:= behaves Y H D G u t d j c x s k σ X Y'
 rw [mean_absent Y H D G u t d j c x s k σ X, inner_zero_left] at hp
 have ht:Tendsto (fun t:ℕ×ℕ=> (t.1-(n+n),t.2)) atTop atTop:=by
    rw [Filter.tendsto_atTop]; intro (a,b); filter_upwards [eventually_ge_atTop (a+(n+n),b)] with t h; exact ⟨by have hv:a+(n+n)≤t.1:=h.1; omega,h.2⟩
 refine (hp.comp ht).congr' ?_; filter_upwards [eventually_ge_atTop (n+n,0)] with i t'
 have he:mirror K j 0 X.val= Δ₀ j (- (n:ℤ)) f:=by change mirror K j 0 (Δ₀ j n (mirror K j 0 f))=_; rw [backsV j (axial K j 0 p),reversal K j 0 p]
 change ((Kv j k _ _) _) _=_; rw [he,show Y'.val=Δ₀ j ↑n g from rfl,inTorsion Y H D G u t d j c x s k σ p q]; congr 2; have h:i.1≥n+n:= t'.1; dsimp; omega -- tune dsimp
lemma east_morn: Tendsto (fun n:ℕ×ℕ=> ψ s (f*(Δ₀ j (n.1:ℤ) (Δ₀ k (n.2:ℤ) g)))) atTop (𝓝 0):=by
 have hp:= whole_qturn Y H D G u t d j c x s k σ p q; rw [tendsto_zero_iff_norm_tendsto_zero]; refine (tendsto_zero_iff_norm_tendsto_zero.mp hp).congr ?_; intro i
 unfold stringUp; have ht:=froll j (froll k q i.2) i.1
 let z:= f* Δ₀ j i.1 (Δ₀ k i.2 g); let Z:Dome K:=⟨z, aux_test ((p.mono (subset_union_left (s₂:=plow K j _ (plow K k _ _)))).mul (ht.mono subset_union_right))⟩
 change ‖ψ s (Complex.I • z)‖=‖ψ s z‖; rw [show ψ s (Complex.I • z)= Complex.I*ψ s z from (audition Y H V G d c _ s).map_smul Complex.I Z, norm_mul,Complex.norm_I,one_mul]
end YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab.phantom
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab.east_morn
