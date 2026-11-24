import YM.SU5.Relativistic.Waltz
import YM.SU5.Relativistic.PairForm
import YM.SU5.Relativistic.Trucks
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
local notation "UfOld"=>flier Y H D G u t d j c x
variable (k:Axis)(σ:k≠j)
-- parity-ind in pose computations
variable {Z:Calibration}{S:Finset Cover}{v b₀:Bool}{F:Family Z}
open Signs
local notation "μ"=> mirror K j 0
local notation "P₁"=>perroll Y H D G u t d j c x s ⟨k,σ⟩
local notation "Π"=>upCycle Y H D G u t d j c x
local notation "ξ"=> (UfOld).entry s

open CF.Pannier.Chancel.ScreeV
include D G t
variable (c':Axis)(e0:c'≠j)(hK:c'≠k)
variable {F W:Finset Cover}{f g:Family (tent Y H)}
local notation "Ωe" J:max=> doorstep Y H V Q G.clipped J false (c J) (χ J)
local notation "Bi" J:max=> bud Y H V s Q G.clipped J false (c J) (χ J)
local notation "E₁"=> ride Y H V G.history G.clipped k false (c k) (χ k)
local notation "R₂"=> eveRoll Y H D G d k c x s c' hK
local notation "Δ₀" => relocate (tent Y H)
local notation "p₂"=> Signs.finalProject (E₁) (R₂)

include e0 σ t hK
lemma fuses (r:ℕ)(p:0<r)(z:ℤ)(v:FundX Y H D G d j c x s (T:=T) F W f g true z r): ∃ n:ℕ, let f':=relocate (tent Y H) k n f; let g':=relocate (tent Y H) k n g; let S:= plow (tent Y H) k n F; let X:=plow (tent Y H) k n W;
    ∀ᶠ i :ℕ×ℕ in atTop, let A:=mirror (tent Y H) k 0 f' * (Δ₀ k i.1 (Δ₀ c' i.2 f')); let B:=mirror (tent Y H) k 0 g'* (Δ₀ k i.1 (Δ₀ c' i.2 g')); FundX Y H D G d j c x s (T:=T) (reflectedBox k 0 S∪plow K k i.1 (plow K c' i.2 S)) (reflectedBox k 0 X∪plow K k i.1 (plow K c' i.2 X)) A B false z r :=by
 obtain ⟨ρ,e,h⟩:= v.nonfactorCoordinate
 have hz:ψ s (f*g) ≠ 0:=by
    intro e'; specialize h 0
    have he:Lariat.discount ψ true s f=0:=rfl; have ht:Lariat.discount ψ true s g=0:=rfl
    change ρ ≤ ‖ψ s (f*g)-Lariat.discount ψ true s f*Lariat.discount ψ true s g‖ at h; rw [he,ht,e'] at h; simp at h; linarith
 let hp:= v.input; let ht:= v.certified
 obtain ⟨n,hN,hB⟩:= ((onstrip Y H k hp.widen).and (onstrip Y H k ht.widen)).exists
 let f':= Δ₀ k n f; let g':=Δ₀ k n g; have hf:= froll k hp n; have hg:= froll k ht n; let S:= plow K k n F; let T':= plow K k n W
 have hΓ:InTest K true (S∪T') false (f'*g'):= (hf.widen.mono subset_union_left).mul (hg.widen.mono subset_union_right)
 obtain ⟨X,eX⟩:= announced Y H s k hΓ (show Tower.region k 0 (tent Y H).ℓ (S∪T') from fun i t=> (mem_union.mp t).elim (hN i) (hB i))
 have uX:ψ s X.val ≠ 0:=by
    rw [eX]; unfold f' g'; rw [← relocate_mul]
    rw [show ψ s (Δ₀ k n (f*g)) = ψ s (f*g) from elect_slide _ _ _ _ _ _ _ _ (aux_test ((hp.widen.mono (subset_union_left (s₂:=W))).mul (ht.widen.mono subset_union_right))) (2*(n:ℤ)) s]; exact hz
 let Z:= p₂ ((Bi k) X); let H':= inner ℂ Z Z; have h': H' ≠ 0:= fun e=> tallyTrue Y H D G d k c x s c' hK X uX (inner_self_eq_zero (𝕜:=ℂ)|>.mp e)
 have hE:= billboard Y H D G d k c x s c' hK X X
 let A(m:ℕ×ℕ):=mirror K k 0 f'*(Δ₀ k m.1 (Δ₀ c' m.2 f')); let B'(m:ℕ×ℕ):= mirror K k 0 g'*(Δ₀ k m.1 (Δ₀ c' m.2 g'))
 let Xs(m:ℕ×ℕ):=reflectedBox k 0 S∪plow K k m.1 (plow K c' m.2 S); let Ys(m:ℕ×ℕ):=reflectedBox k 0 T'∪plow K k m.1 (plow K c' m.2 T')
 have hxF(m:ℕ×ℕ):InTest K false (Xs m) false (A m):= ((axial K k 0 hf).mono subset_union_left).mul ((froll k (froll c' hf m.2) m.1).mono subset_union_right)
 have hxB(m:ℕ×ℕ):InTest K false (Ys m) false (B' m):= ((axial K k 0 hg).mono subset_union_left).mul ((froll k (froll c' hg m.2) m.1).mono subset_union_right)
 have hD:Tendsto (fun m=> ψ s (A m * B' m)) atTop (𝓝 (-H')) := by
    refine hE.neg.congr fun m=> ?_
    let Uf:= Δ₀ k m.1 (Δ₀ c' m.2 f'); let Vg:=Δ₀ k m.1 (Δ₀ c' m.2 g')
    have h: A m * B' m= - (mirror K k 0 X.val * (Δ₀ k m.1 (Δ₀ c' m.2 X.val))):=by
       have hG:InTest K false (plow K k m.1 (plow K c' m.2 S)) true Uf:= froll k (froll c' hf m.2) m.1
       have hS:InTest K false (reflectedBox k 0 T') true (mirror K k 0 g'):= axial K k 0 hg
       have hi: Uf* mirror K k 0 g' = - (mirror K k 0 g'*Uf):= by rw [signMark K hG hS]; simp [Sector.grainB]
       unfold A B'; rw [eX,mirror_times,relocate_mul,relocate_mul]
       change (_*Uf)*(mirror K k 0 g' * Vg)=_ -- tune
       simp only [mul_assoc]; rw [←mul_assoc Uf,hi,neg_mul,mul_neg,mul_assoc]
    rw [h]
    let V':= field_test Y H s k 0 false X; let R:Dome K:= ⟨_,(aux_test (axial K k 0 V'.paid.choose_spec)).mul (aux_test (froll k (froll c' V'.paid.choose_spec m.2) m.1))⟩
    exact ((audition Y H V G d c _ s).map_neg R).symm
 have h₁:Tendsto (fun m=> ψ s (A m)* ψ s (B' m)) atTop (𝓝 0):=by
    have hF:=east_morn Y H D G u t d k c x s c' hK (axial K k 0 hf.widen) hf.widen
    have hA:=east_morn Y H D G u t d k c x s c' hK (axial K k 0 hg.widen) hg.widen
    simpa only [mul_zero] using (hF.mul hA)
 have h2:Tendsto (fun m=> ‖ψ s (A m* B' m)-ψ s (A m)*ψ s (B' m)‖) atTop (𝓝 ‖H'‖):= by simpa only [sub_zero,norm_neg] using (hD.sub h₁).norm
 refine ⟨n,?_⟩; dsimp only
 filter_upwards [h2.eventually (lt_mem_nhds (norm_pos_iff.mpr h'))] with m h
 have hk:=walksGap j k σ K (n:ℤ) v.gap
 have ha:Till K r j z (Xs m) (Ys m) := bothGap j K (turnedGap j k σ K (0:ℤ) hk) (walksGap j k σ K (m.1:ℤ) (walksGap j c' e0 K (m.2:ℤ) hk))
 let p':=slideMove K k (n:ℤ) hp v.gauge.1; let q':= slideMove K k (n:ℤ) ht v.gauge.2
 exact even_persists Y H D G u t d j c x s p ha (hxF m) (hxB m) (slideMul K (slideHon K k 0 hf p') (slideMove K k _ (froll c' hf _) (slideMove K c' _ hf p'))) (slideMul K (slideHon K k 0 hg q') (slideMove K k _ (froll c' hg _) (slideMove K c' _ hg q'))) (sub_ne_zero.mp (norm_pos_iff.mp h))
end YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab.fuses
