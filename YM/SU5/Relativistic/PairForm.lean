import YM.SU5.Relativistic.FrontSign
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

local notation "P₀"=>indoor Y H V Q G.clipped j false (c j) (χ j)
local notation "Πe"=> ride Y H V Q G.clipped j false (c j) (χ j)
local notation "Ω"=>doorstep Y H V Q G.clipped j false (c j) (χ j)
local notation "Eb"=> bud Y H V s Q G.clipped j false (c j) (χ j)
local notation "Σ" r:max => shiftStamp Y H V Q G.clipped j false (c j) (⟨k,σ⟩:Trans j) (notch (timeMesh Λ) s r)
local notation "ρ"=> procession Y H V Q G.clipped j false (c j) (χ j)
noncomputable def eveRoll : Rolls (indoor Y H V G.history G.clipped j false (c j) (χ j)) where
 wind i:= procession Y H V Q G.clipped j false (c j) (χ j) (shiftStamp Y H V Q G.clipped j false (c j) (⟨k,σ⟩:Trans j) (notch (timeMesh Λ) s i))
 small i:= (NonUnitalStarAlgHom.norm_apply_le _ _).trans (transverse_price Y H V Q G.clipped ..)
 along a b:=by
    change (ρ (Σ a)) * (ρ (Σ b))=ρ _; rw [←map_mul,transverse_mul,notch_add]
 nil:=by rw [notch_zero,transverse_z,map_one]; rfl
local notation "RΞ"=> eveRoll Y H D G d j c x s k σ
local notation "Yp"=> Signs.finalProject (Πe) (RΞ)

local notation "TE"=> Tower.Field Y H s j 0 false
lemma pricing(X Y':TE):inner ℂ (Eb X) (Eb Y')= ψ s (μ X.val*Y'.val):= (earns Y H V s Q G.clipped j false (c j) (χ j) X Y').trans (selected_here Y H D G d j c x s _)
-- selected_here not new orientation
lemma pricing_(X:TE):inner ℂ Ω (Eb X)=ψ s X.val:=by
 rw [← Selected.root Y H V s Q G.clipped j false (c j) (χ j),pricing Y H D]
 rw [show (unity Y H j 0 false s).val=1 from rfl,mirror_unit,one_mul]

local notation "Δ₀" => relocate (tent Y H)
-- budget on any even, standalone. axis weights not claiming eigen
noncomputable def panelsE (f g:Family (tent Y H))(n m:ℤ):= ψ s (f*(relocate K j n (relocate K k m g)))
local notation "Ke" J:max k:max F:max T:max=>panelsE Y H D G d J c x s k F T

lemma announced(j:Axis){S:Finset Cover} {f:Family K}(p:InTest K true S false f)(h:Tower.region j 0 (K).ℓ S) : ∃ x: Tower.Field Y H s j 0 false, x.val=f:=by
 let x:Tower.Field Y H s j 0 false:=⟨f, (purpose_ok ..).2 ⟨⟨S,p, by rw [area0]; exact h⟩,nofun⟩⟩; exact ⟨x,rfl⟩
include D G σ
lemma lease (X Y': TE): Signs.Stock (Ke j k (μ X.val) Y'.val) (RΞ) ((Πe).orth (Eb X)) (Eb Y'):= by
 refine Signs.full_stock (Πe) (Eb X) _ (fun t:ℕ=>whenly R₁ s t) ?_ (RΞ) (Eventually.of_forall fun n v=>?_)
 · unfold whenly; simpa using rovers (mill_pos R₁ s) 0
 change _=inner ℂ (Eb X) ((Πe).E (whenly R₁ s n) (ρ (Σ v) (Eb Y')))
 rw [turns_across, ride_ticks,pricing Y H D, timed_apply];
 have hg:(sail Y H s j 0 false k σ (2*v) Y').val=relocate K k v Y'.val:= rfl; rw [hg]; rfl
variable {S W:Finset Cover}{f g:Family (tent Y H)}(p:InTest (tent Y H) true S false f)(q:InTest (tent Y H) true W false g)
include σ
lemma admissions (p:InTest (tent Y H) true S false f)(q:InTest (tent Y H) true W false g): ∃ A B, Signs.Stock (Ke j k f g) (RΞ) A B:=by
 obtain ⟨n,h,v⟩ := ((onstrip Y H j (axial K j 0 p)).and (onstrip Y H j q)).exists
 let Xc:= relocate K j n (mirror K j 0 f); let Yc:=relocate K j n g
 obtain ⟨A,hA⟩ := announced Y H s j (froll j (axial K j 0 p) _) h
 obtain ⟨B,hB⟩ := announced Y H s j (froll j q _) v
 refine ⟨(Πe).orth (Eb A),Eb B, Signs.full_stock (Πe) (Eb A) (Eb B) (fun t:ℕ=>whenly R₁ s (t-(n+n))) (rovers (mill_pos R₁ s) (n+n)) (RΞ) ?_⟩
 filter_upwards [eventually_ge_atTop (n+n)] with i x' z
 change _=inner ℂ (Eb A) ((Πe).E (whenly R₁ s (i-(n+n))) (ρ (Σ z) (Eb B)))
 rw [turns_across,ride_ticks,pricing Y H D,timed_apply,show (sail Y H s j 0 false k σ (2*z) B).val=Δ₀ k z B.val from rfl]
 rw [hA,hB,backsV j (axial K j 0 p),reversal K j 0 p,unions K k j q z n,edge_roll j _ _ (froll k q z)]
 let T':= Δ₀ k z g
 have ht : Δ₀ j (-(n:ℤ)) (f*(Δ₀ j i T'))= Δ₀ j (-(n:ℤ)) f * (Δ₀ j ((i-(n+n):ℕ)+(n:ℤ)) T'):=by rw [relocate_mul, edge_roll j _ _ (show InTest K true _ false T' from froll k q z),show -(n:ℤ)+i=(i-(n+n):ℕ)+(n:ℤ) by omega]
 change ψ s (f*(Δ₀ j i T')) = ψ s (Δ₀ j _ f* (Δ₀ j _ T'))
 rw [←ht]
 have hQ:= froll j (froll k q z) (i:ℤ)
 exact (elect_slide Y H V G j d c _ ((aux_test p).mul (aux_test hQ)) (2* - (n:ℤ)) s).symm

lemma billboard (X Y':TE): Tendsto (fun w:ℕ×ℕ=> (Ke j k (μ X.val) Y'.val) w.1 w.2) atTop (𝓝 (inner ℂ (Yp (Eb X)) (Yp (Eb Y')))):=by
 let Z:=Πe; let L':=RΞ; let Q':= (μ X.val); let f':= Ke j k (μ X.val) Y'.val
 have u(t m): L'.wind t*Z.E m=Z.E m* L'.wind t:=(rides_trans Y H V Q G.clipped j false (c j) (χ j) («α»:=⟨k,σ⟩) (notch (timeMesh Λ) s t) m).eq.symm
 obtain ⟨S,g⟩:= (field_test Y H s j 0 false X).paid; obtain ⟨T,h⟩:=(field_test Y H s j 0 false Y').paid
 let Z':=eveRoll Y H D G d k c x s j σ.symm
 rw [← Signs.paid Z L' u];
 obtain ⟨A,B,v⟩:=admissions Y H D G d k c x s j (Ne.symm σ) (axial K j 0 g) h
 refine Signs.quadrant L' Z' ((Πe).orth (Eb X)) (Eb Y') A B (lease Y H D G d j c x s k σ X Y') ?_
 intro ε e; apply (v ε e).mono; intro i p m; dsimp only; unfold panelsE; rw [unions K j k h]; exact p m

lemma tallyTrue(X: TE) (e:ψ s X.val≠0): Yp (Eb X) ≠ 0 :=by
 let Z:= Πe; let L':= RΞ
 have u(t m): L'.wind t*Z.E m=Z.E m* L'.wind t:=(rides_trans Y H V Q G.clipped j false (c j) (χ j) («α»:=⟨k,σ⟩) (notch (timeMesh Λ) s t) m).eq.symm
 have ht:Yp Ω=Ω:= (Signs.final_fix _ _ u Ω).mpr ⟨fun t=> ride_affordable Y H V Q G.clipped j false (c j) (χ j) (fun s n=>hinges _ _ _ s _ _ _ _ _ _ n) t,fun m=> jamb Y H V Q G.clipped j false (c j) (χ j) ⟨k,σ⟩ (notch R₁ s m)⟩ -- mStamp
 intro x'; have hp:= pricing_ Y H D G d j c x s X
 rw [←ht, Signs.final_self Z L' u,x',inner_zero_right] at hp; exact e hp.symm
end YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab.tallyTrue
