import YM.SU5.Relativistic.Paves
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

lemma edge_roll (a b:ℤ)(f:InTest Z v S b₀ F): relocate Z j a (relocate Z j b F)= relocate Z j (a+b) F:=by
 unfold relocate; rw [hoops Z j _ f]; unfold gaugeT Heat.gaugeShift; congr 1; ring
lemma edge_void (f:InTest Z v S b₀ F):relocate Z j 0 F=F:=by
 unfold relocate gaugeT Heat.gaugeShift; rw [mul_zero,mul_zero]; exact reversal Z j 0 f
lemma backsV (f:InTest Z v S b₀ F)(t:ℤ): mirror Z j 0 (relocate Z j t F)=relocate Z j (-t) (mirror Z j 0 F):=by
 unfold relocate; rw [counterSlide Z j _ _ f]; unfold gaugeT Heat.gaugeShift; congr 2; ring
lemma froll (p:InTest Z v S b₀ F)(a:ℤ): InTest Z v (plow Z j a S) b₀ (relocate Z j a F):=flow_port Z j _ p
lemma rovers {v:ℝ≥0}(p:0<v)(c:ℕ):Tendsto (fun r:ℕ=> ((r-c:ℕ):ℝ≥0)*v) atTop atTop :=by
 rw [Filter.tendsto_atTop]; intro s
 obtain ⟨i,ht⟩:= exists_nat_gt (s/v)
 filter_upwards [eventually_ge_atTop (i+c)] with r hr
 exact (div_le_iff₀ p).mp (ht.le.trans (Nat.cast_le.mpr (by omega))) -- arg implicit Y? likely no
-- aperture alone at fixed rung; any coarse k offset multiples m; permits.
variable {S V':Finset Cover}{f g:Family (tent Y H)}
local notation "Δ₀" => relocate (tent Y H)
def stringUp (f g:Family (tent Y H))(m n:ℤ):ℂ:= ψ s (Complex.I • (f * (Δ₀ j m (Δ₀ k n g))))
local notation "Kv" F:max T:max=>stringUp Y H D G d j c x s k F T
-- geometry for any pose, offset big even tick with later p fixed
lemma onstrip {w:Bool}(h:InTest K true S w f) : ∀ᶠ t:ℕ in atTop, Tower.region j 0 (K).ℓ (plow K j t S):=by
 let p:= ruler Λ.block; have ht : 0 < p := ruler_gene _
 have hx(y:Cover):∀ᶠ t:ℕ in atTop, (0:ℤ)+(K).ℓ ≤ y j + p*t := by
    let a:=((K).ℓ:ℤ); have hv:Tendsto (fun t:ℕ=> p*(t:ℤ)) atTop atTop:= tendsto_natCast_atTop_atTop.const_mul_atTop' ht
    filter_upwards [hv.eventually_ge_atTop (a-y j)] with i v; omega
 filter_upwards [(eventually_all_finset S).mpr (fun y _=>hx y)] with u m i t
 obtain ⟨y,h,g⟩:=plow_stays K j _ S t; rw [g,moves,if_pos rfl]; exact m y h
include t σ
lemma stageWalk (X:Cabin (tent Y H) j)(n:ℤ): (P₁).wind n (ξ X)= ξ (dwell Y H j ⟨k,σ⟩ n X):=by
 change sendU Y H D G u t d j c x s ⟨k,σ⟩ n (ξ X)=_
 rw [sendsL Y H D G u t d j c x s ⟨k,σ⟩ n (le_refl _),castor,Nat.sub_self,pow_zero,one_mul]
lemma stockZero (X Y':Cabin (tent Y H) j): Stock (Kv (mirror K j 0 X.val) Y'.val) (P₁) ((Π).orth (ξ X)) (ξ Y'):=by
 refine Signs.full_stock (Π) (ξ X) _ (fun t:ℕ=>whenly R₁ s t) ?_ (P₁) (Eventually.of_forall fun n u'=>?_)
 · unfold whenly; simpa using rovers (mill_pos R₁ s) 0
 rw [stageWalk Y H D G u t d j c x s k σ,visits Y H D G u t d j c x s n s (le_refl _),Nat.sub_self,pow_zero,one_mul,Tier.arrived]
 rfl
lemma stocks (p: InTest K true S true f)(q: InTest K true V' true g): ∃ A B, Stock (Kv f g) (P₁) A B:=by
 -- move f negatively by same C, meanwhile move g positively by C+-n. combine paid heft.C- may =C+ in coords
 obtain ⟨n,h,v⟩ := ((onstrip Y H j (axial K j 0 p)).and (onstrip Y H j q)).exists
 let Xc:= relocate K j n (mirror K j 0 f); let Yc:=relocate K j n g
 let A: F₀:= ⟨Xc,_, froll j (axial K j 0 p) _,h⟩
 let B: F₀:= ⟨Yc,_,froll j q _,v⟩
 have he:mirror K j 0 Xc= relocate K j (-(n:ℤ)) f:=by unfold Xc; rw [backsV j (axial K j 0 p),reversal K j 0 p]
 refine ⟨(Π).orth (ξ A),ξ B, Signs.full_stock (Π) (ξ A) (ξ B) (fun t:ℕ=>whenly R₁ s (t-(n+n))) (rovers (mill_pos R₁ s) (n+n)) (P₁) ?_⟩
 filter_upwards [eventually_ge_atTop (n+n)] with i x' z
 rw [stageWalk Y H D G u t d j c x s k σ,visits Y H D G u t d j c x s _ s (le_refl _),Nat.sub_self,pow_zero,one_mul,Tier.arrived]
 unfold stringUp
 let T':= Δ₀ k z g
 change _= ψ s (Complex.I • (mirror K j 0 Xc * (Δ₀ j _ (Δ₀ k z Yc))))
 unfold Yc; rw [he,unions K k j q z n,edge_roll j _ _ (froll k q z)]
 have ht : Δ₀ j (-(n:ℤ)) (Complex.I • (f*(Δ₀ j i T')))= Complex.I • (Δ₀ j (-(n:ℤ)) f * (Δ₀ j ((i-(n+n):ℕ)+(n:ℤ)) T')):=by
    rw [show ∀ (f:Family (tent Y H)), Δ₀ j (-(n:ℤ)) (Complex.I • f)=Complex.I • Δ₀ j (-(n:ℤ)) f from fun f=>chime_scale _ _ _ _, relocate_mul, edge_roll j _ _ (show InTest K true _ true T' from froll k q z),show -(n:ℤ)+i=(i-(n+n):ℕ)+(n:ℤ) by omega]
 change ψ s (Complex.I • (f*(Δ₀ j i T'))) = ψ s (Complex.I • (Δ₀ j _ f* (Δ₀ j _ T')))
 rw [←ht]
 have hQ:= froll j (froll k q z) (i:ℤ)
 have hK :TestFamily K true (f* Δ₀ j i T'):=aux_test ((p.mono (Finset.subset_union_left (s₂:=plow K j _ (plow K k _ _)))).mul (hQ.mono subset_union_right))
 exact (elect_slide Y H V G j d c _ (hK.scale Complex.I) (2* - (n:ℤ)) s).symm
end YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab.stocks
