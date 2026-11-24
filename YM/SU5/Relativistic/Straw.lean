import YM.SU5.Relativistic.RawEase
import YM.SU5.Relativistic.Confining
/-!
# Geometry registration of local physical polynomials.
-/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 350000
set_option synthInstance.maxSize 30000
set_option maxRecDepth 5500
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction
open Function Set Filter MeasureTheory Metric
open Lattice Wilson RG SU Lat Mir RP Reflect Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Py Py.Rate LocalLimit PhaseChoice Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy MeshClock Selected
open Tapestry Tapestry.Altitude Tapestry.Exhibition
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
variable {a b:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}
    {L:Rack Λ l}{B:Clay Λ l}(D : Exhibition Y H a b I E L B)(G:SatinVerification.GroundExtension (i:=a) (k:=b) (E:=E) Y H)
variable (j:Axis) (J: Arena Y H G.history.circuit j 0 false)
local notation "M"=> timeMesh Λ
local notation "N" i:max z:max=> notch M i z
local notation "D₀"=> Dome (tent Y H)
local notation "Τ"=> Cloud (Dome (tent Y H))
local notation "P₀" n:max=> vistaFinish Y H n D
local notation "d★" => vistaDressing Y H D
local notation "B₀" => driveAlgebra Y H D.univ_ G.history G.clipped j false J
local notation "Rg" t:max => Docked Y H D.univ_ t G.history G.clipped j J

local notation "ρ"=> D.univ_
local notation "reach" n:max f:max => reachMark (tent Y H) ((P₀ n) f)
section billing
variable (d:Axis)(c:∀ j:Axis,Arena Y H G.history.circuit j 0 false)(χ : displayAlgebra Y H D.univ_ G.history G.clipped d false (c d) →⋆ₐ[ℂ] ℂ)
local notation "χ̂" j:max=> displacement Y H D.univ_ G.history G.clipped d false (c d) χ j (c j)
local notation "Χ"=> SameCharacter.resident Y H D.univ_ G d false (c d) χ
local notation "Ψ"=> onDrawing Y H D.univ_ G D d c Χ
local notation "Θ"=> procession Y H D.univ_ G.history G.clipped j false (c j) (χ̂ j)
local notation "Ρ"=>indoor Y H D.univ_ G.history G.clipped j false (c j) (χ̂ j)
local notation "V"=>fort Y H D.univ_ G.history G.clipped j false (c j) (χ̂ j)
local notation "p★"=>saunters Y H D.univ_ G.history G.clipped j false (c j) (χ̂ j)
local notation "ω"=> vocation Y H D.univ_ G.history G.clipped j false (c j) (χ̂ j)
local notation "Ω"=> doorstep Y H D.univ_ G.history G.clipped j false (c j) (χ̂ j)
local notation "A"=>ride Y H D.univ_ G.history G.clipped j false (c j) (χ̂ j)
local notation "Ξ"=> peninsula Y H D.univ_ G.history G.clipped j false (c j) (χ̂ j)
local notation "E□"=> encase Y H D.univ_ G.history G.clipped j (c j) (χ̂ j)
local notation "P□"=> mainsea Y H D.univ_ G.history G.clipped j false (c j) (χ̂ j)
local notation "e□"=> follows_road Y H D.univ_ G.history G.clipped j false (c j) (χ̂ j)
local notation "B□"=> docket Y H D G j (c j)
local notation "Φ"=> driveAlgebra Y H D.univ_ G.history G.clipped j false (c j)
local notation "dock" n:max => Docked Y H D.univ_ n G.history G.clipped j (c j)
local notation "Zg" t:max => (Axis→Fin ((timeMesh Λ).L^t))

variable {I':Type*}(f:I'→ Cloud (Dome (tent Y H)))
variable (t:I'→ℕ)(S T:I'→ Slab (timeMesh Λ)) (l':List I')(b₁: Stamp (timeMesh Λ))
local notation "EE" i:max z:max => envelope (P□) (A) (e□) (Θ (B□ (t i) (f i) (S i))) (S i) (T i) z
local notation "Q₀" g:max=> packetEnvelope Y H D G j d c χ f t S T g l' b₁
local notation "ϕ" v:max=> integerRead v
local notation "GΛ"=> Axis → Stamp (timeMesh Λ)
local notation "R★" q:max=> rawRoom Y H D G j d c χ f l' b₁ T t S q
variable (u:I'→Axis→ℝ)
local notation "cm" t:max S:max T:max l:max b:max u:max=> Corridor Y H j f t S T l b u
section payments
variable (v:I'→ Axis→ Stamp (timeMesh Λ))[Fintype I']
local notation "N₀" i:max n:max=> nub (timeMesh Λ) (v i) n
local notation "Δ" k:max=> (fun i=> N₀ i k)
local notation "β" n:max k:max i:max=> packetPoly Y H D (N₀ i k) (f i) n
local notation "T₀"=> rawRoom Y H D G j d c χ f l' b₁ T t S
local notation "K★" k:max=> (Axis→ Fin ((timeMesh Λ).L^k))
-- expansions on SAME χ. Equality at every purchasing mesh.
lemma packet_trend (k:ℕ) (p:∀i∈ l',Served Y H j (t i) (f i) (S i) (T i) (N₀ i k))
    (h:inRow T b₁ l') (e:l'.Nodup):
     ∀ᶠ n in atTop, Ψ ((l'.map (fun i=> β n k i)).prod) = apk v T₀ k (n-k):= by
   have ht: ∀ᶠ n in atTop, ∀ i∈ l', PricedPacket Λ (N₀ i k) n ∧ t i ≤ n ∧ (T i).lines n := by simp_rw [←List.mem_toFinset]; exact (eventually_all_finset _).mpr fun i _=> (readyPacket (N₀ i k)).and ((eventually_ge_atTop _).and (T i).grids)
   filter_upwards [ht, ReadPrecise b₁] with n hz g
   let V' (i:I')(y:K★ (n-k)):= navigateC Λ (N₀ i k) n y
   haveI:= _root_.YM.SelectionAnalysis.avg_lives M (n-k)
   let G'(i:I')(v:K★ (n-k)):=signOver Y H D n (V' i v) (f i)
   have hy(i:I'): packetPoly Y H D (N₀ i k) (f i) n=algMean (G' i):=by
      rw [packet_sample]; unfold Packet.score; simp only [nub,Pi.one_apply,one_smul]; -- might unfold f etc
      -- Fintype proof diamond again
      rfl
   have hx(x:I'→ (K★ (n-k))): Ψ ((l'.map (fun i=> G' i (x i))).prod)= T₀ (waveSpot v k (n-k) x):=by
      let u':=fun i=> V' i (x i)
      have hc(i:I')(y:i∈l'):(fun j:Axis=> notch M n (u' i j))=waveSpot v k (n-k) x i:= funext (exactPacket (N₀ i k) n (hz i y).1 (x i))
      rw [priceEncase Y H D G j d c χ f l' b₁ T t S u' (fun i v=> (p i v).visibleHere) h n g ?_]
      · unfold rawRoom; rw [brace_match (A).E T (fun i=> E□ (S i) (T i) (B□ (t i) (f i) (S i)) (fun j:Axis=> notch M n (u' i j))) (fun i=> E□ _ _ (B□ (t i) (f i) (S i)) (waveSpot v k (n-k) x i)) l' b₁ (fun i p=> ?_)]
        rw [hc i p]
      intro i y; refine ⟨(hz i y).2.1,(hz i y).2.2,?_⟩; rw [hc i y]; exact position_cert Y H j _ _ _ _ _ (p i y) _ (x i)
   -- Fintype I'→K axis instance
   simp_rw [hy]; rw [← algProduct G' l' e]; unfold algMean apk; rw [map_smul,map_sum]; simp_rw [hx]; rfl

theorem material (p:cm t S T l' b₁ (ϕ v))(e: l'.Nodup)(g:∀ k:Axis,∃ (w:List I')(b':Stamp (timeMesh Λ))(t':I'→ℕ)(X X': I'→ Slab (timeMesh Λ)), Corridor Y H k f t' X X' w b' (integerRead v) ∧ l'.Perm w) :
   rawRoom Y H D G j d c χ f l' b₁ T t S v= windowPrice Y H D G j d c χ f t S T l' b₁ (integerRead v):=by
  let Γ(n:ℕ):= packetEnvelope Y H D G j d c χ f t S T (Δ n) l' b₁
  apply tendsto_nhds_unique (f:=Γ) (materializes v T₀ (handholds Y H D G j d c χ f t S T l' b₁ v p g) Γ ?_) (window_limit Y H D G j d c χ f t S T l' b₁ (integerRead v) (fun i k=> N₀ i k) (fun i _=> adjusts_mesh _))
  filter_upwards [p.eventuallyServed Y H j f t S T l' b₁ (integerRead v) (fun i k=> N₀ i k) (fun i _=> adjusts_mesh _)] with i u
  exact (envelop_consumes Y H D G j d c χ f t S T (Δ i) l' b₁ p.vault u).congr' (packet_trend Y H D G j d c χ f t S T l' b₁ v i u p.vault e)
end payments
end billing
end YM.CF.Buffered.Afterglow.Tower.Reconstruction
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.material
