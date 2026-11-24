import YM.SU5.Relativistic.Consist
import YM.SU5.Relativistic.NeedlePacket
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
abbrev integerRead {M':MeshClock.Mesh} (u:I'→Axis→Stamp M') : I'→Axis→ℝ:=fun i j=> (u i j).val
local notation "ϕ" v:max=> integerRead v
local notation "GΛ"=> Axis → Stamp (timeMesh Λ)
local notation "R★" q:max=> rawRoom Y H D G j d c χ f l' b₁ T t S q
variable (u:I'→Axis→ℝ)
local notation "cm" t:max S:max T:max l:max b:max u:max=> Corridor Y H j f t S T l b u
lemma Corridor.openAt (p:cm t S T l' b₁ u): ∀ᶠ v:I'→Axis→ℝ in 𝓝 u, Corridor Y H j f t S T l' b₁ v:=by
  have ht(i:I')(x:i∈ l') : ∀ᶠ v:I'→Axis→ℝ in 𝓝 u, safely j (S i) (T i) (v i):= (continuous_apply i).continuousAt.tendsto.eventually ((safe_open j (S i) (T i)).mem_nhds (p.assured _ x))
  filter_upwards [(eventually_all_finset l'.toFinset).2 fun i x => ht i (List.mem_toFinset.mp x)] with i h -- tune
  exact ⟨p.vault,p.issued,fun b v=>h b (List.mem_toFinset.mpr v)⟩

theorem Corridor.buyExact (q:I'→Axis→ Stamp (timeMesh Λ))(k:cm t S T l' b₁ (ϕ q)) :
    ∀ᶠ n:ℕ in atTop, Ψ ((l'.map (fun i=> signOver Y H D n (fun j=> tags n (q i j)) (f i))).prod) = rawRoom Y H D G j d c χ f l' b₁ T t S q:=by
   have he : ∀ᶠ n:ℕ in atTop, ∀ i∈ l', t i ≤ n ∧ (T i).lines n ∧ ∀ j:Axis, Precise n (q i j):=by
      simp_rw [←List.mem_toFinset]; apply (eventually_all_finset _).mpr
      intro i _; exact (eventually_ge_atTop _).and ((T i).grids.and (eventually_all.mpr (fun i' => ReadPrecise _)))
   filter_upwards [he, ReadPrecise b₁] with n h a
   let v(i:I'):Cover:=fun j:Axis=> tags n (q i j)
   have hh(i:I')(g:i∈l'): (fun j:Axis=> notch M n (v i j))=q i:=funext fun j=>tags_on _ ((h i g).2.2 j) -- tune args
   rw [priceEncase Y H D G j d c χ f l' b₁ T t S v k.issued k.vault n a ?_]
   · unfold rawRoom; rw [brace_match (A).E T (fun i=>E□ (S i) (T i) (B□ (t i) (f i) (S i)) (fun j:Axis=> notch M n (v i j))) (fun i=> E□ (S i) (T i) (B□ (t i) (f i) (S i)) (q i)) l' b₁ ?_]
     intro i g; rw [hh i g]
   intro i x; refine ⟨(h i x).1,(h i x).2.1,?_⟩; rw [hh i x]; exact ⟨(k.assured i x).1.le,(k.assured i x).2.le⟩

theorem Corridor.raw_cmp (q:I'→Axis→ Stamp (timeMesh Λ))(p:cm t S T l' b₁ (ϕ q))(a:Axis)(w:List I')(b':Stamp (timeMesh Λ))(t':I'→ℕ)(S' T':I'→Slab (timeMesh Λ))(v:Corridor Y H a f t' S' T' w b' (integerRead q)) (e:l'.Perm w):
    rawRoom Y H D G j d c χ f l' b₁ T t S q=rawRoom Y H D G a d c χ f w b' T' t' S' q:=by
 obtain ⟨n,x,y⟩:= ((p.buyExact Y H D G j d c χ f t S T l' b₁ q).and (v.buyExact Y H D G a d c χ f t' S' T' w b' q)).exists
 rw [←x,←y]; exact congrArg Ψ (List.Perm.prod_eq (e.map _))
end billing
end YM.CF.Buffered.Afterglow.Tower.Reconstruction
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.Corridor.buyExact
