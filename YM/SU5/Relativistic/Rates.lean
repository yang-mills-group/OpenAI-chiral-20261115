import YM.SU5.Relativistic.ZonalPacket
import YM.SU5.Relativistic.BraceLimits
import YM.SU5.Relativistic.DockLinear
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

section budget
variable (t:ℕ) (F : Cloud (Dome (tent Y H))) (S T : Slab (timeMesh Λ)) (Q:Packet (timeMesh Λ))
local notation "Z★" => Q.size
local notation "Δ" n:max x:max => Q.near (n-Z★) x
local notation "K★" n:max=> Zg (n-Q.size)
local notation "X★" n:max=> packetMark Y H D Q F n
local notation "Pm" n:max=> collecting (P□) (A) (Θ (B□ t F S)) S T Q (n-Q.size)
local notation "ord" n:max x:max=> navigateC Λ Q n x
local notation "μ" t:max z:max x:max=>migrate Y H D t z x
local notation "ρ'" t:max => response Y H D.univ_ t G.history G.clipped j false (c j) (χ̂ j)

abbrev fitsAt {M₁:MeshClock.Mesh} (j:Axis) (S T:Slab M₁) (u:Axis→ℝ) : Prop:= (T.lower:ℝ)≤ (S.lower:ℝ)+u j ∧ (S.upper:ℝ)+u j ≤ (T.upper:ℝ) -- rename macro
structure Served : Prop where
 visibleHere : Carries Y H t F j S
 padding : ∀ u∈UBox Axis, fitsAt j S T (Q.region u)

lemma position_cert (p:Served Y H j t F S T Q)(n:ℕ) (x: Zg n): fitsMesh j S T (Q.near n x):=by
 have hx:= p.padding _ (Packet.lives («M»:=timeMesh Λ) n x); rw [←funext (Q.points_near n x)] at hx; exact hx

lemma collecting_used (p:Served Y H j t F S T Q)(n:ℕ)(h:t≤n)(g:PricedPacket Λ Q n)(b:T.lines n) :
    ∃ B:Φ, (dock n) T (packetMark Y H D Q F n) B ∧ Θ B= collecting (P□) (A) (Θ (B□ t F S)) S T Q (n-Q.size):=by
  have hx(i: Axis→ Fin ((M).L^(n-Q.size))): ∃ Z : Φ, (dock n) T (μ n (ord n i) F) Z ∧ Θ Z=encase Y H D.univ_ G.history G.clipped j (c j) (χ̂ j) S T (B□ t F S) (Δ n i) := by
    have ht:(fun j:Axis=> N n ((ord n i) j))=(Δ n i):=funext (exactPacket Q n g i)
    rw [←ht]; exact Docked.pokes Y H D.univ_ n G.history G.clipped j (c j) (χ̂ j) S T _ _ (docket_above Y H D G j (c j) t F S p.visibleHere n h) (navigateC Λ Q n i) b (by rw [ht]; exact position_cert Y H j t F S T Q p (n-Q.size) i)
  choose Z hz t' using hx; let V' (i:K★ n) : Φ := Q.score (n-Q.size) i • Z i
  have hh : Average.center (fun i:K★ n=> Θ (V' i))= Θ (Average.center V'):=by unfold Average.center; rw [map_smul,map_sum]
  refine ⟨Average.center V', ?_,?_⟩
  · unfold Average.center packetMark
    apply Docked.scaledX; exact Docked.combineX Y H D.univ_ n G.history G.clipped j (c j) Finset.univ b fun i _=> Docked.scaledX Y H D.univ_ n G.history G.clipped j (c j) (hz i) _
  rw [← hh]; unfold collecting
  -- beware Fintype classical inst
  apply avg_any
  intro i; unfold V'; rw [map_smul,t']
  rfl

noncomputable def earned : (fort Y H D.univ_ G.history G.clipped j false (c j) (χ̂ j)).Op:= envelop (P□) (A) (e□) (Θ (B□ t F S)) S T Q
end budget
section product
variable {I':Type*}(f:I'→Cloud (Dome (tent Y H))) (t:I'→ℕ)(S T:I'→ Slab (timeMesh Λ))(Q:I'→ Packet (timeMesh Λ)) (l₁:List I') (b':Stamp (timeMesh Λ))
local notation "Qp" n:max i:max=> packetMark Y H D (Q i) (f i) n
local notation "Pm" n:max i:max=> collecting (P□) (A) (Θ (B□ (t i) (f i) (S i))) (S i) (T i) (Q i) (n-(Q i).size)
local notation "Bη" i:max=> earned Y H D G j d c χ (t i) (f i) (S i) (T i) (Q i)
local notation "Vv" b:max x:max => bracing (Ξ).E T (fun i=> Bη i) b l₁ x
lemma matchesHere (p:inRow T b' l₁) (g:∀i∈ l₁, Served Y H j (t i) (f i) (S i) (T i) (Q i)) :
    ∀ᶠ n:ℕ in atTop,
       inner ℂ Ω ((bracing (A).E T (fun i=> Pm n i) b' l₁) Ω)= Ψ ((l₁.map (fun i=> packetPoly Y H D (Q i) (f i) n)).prod):=by
   have hh : ∀ᶠ n:ℕ in atTop,∀ i∈ l₁,PricedPacket Λ (Q i) n ∧ t i ≤ n ∧ (T i).lines n:= by
     -- finite membership
     simp_rw [← List.mem_toFinset]; exact (eventually_all_finset _).mpr fun i _=> (readyPacket _).and ((eventually_ge_atTop _).and ((T i).grids))
   filter_upwards [hh, ReadPrecise b'] with n hh x
   choose! C hC using fun i (v:i∈l₁)=> collecting_used Y H D G j d c χ _ _ _ _ _ (g i v) n (hh i v).2.1 (hh i v).1 (hh i v).2.2
   let X(i:I'):=Qp n i
   have ht := calendarPrice Y H D.univ_ n G.history G.clipped j (c j) (χ̂ j) T X C l₁ (fun i v=> (hC i v).1) b' x p
   rw [brace_match (A).E T (fun i=>Θ (C i)) (fun i=> Pm n i) l₁ b' (fun i u=> (hC i u).2)] at ht
   rw [ht,← costs_basis Y H D G d j c χ n (l₁.map X|>.prod) (packMark K (l₁.map X|>.prod)) rfl]; apply congrArg Ψ; rw [map_list_prod,map_list_prod]; simp only [X,List.map_map]; rfl

noncomputable def packetEnvelope : ℂ:= inner ℂ ω (Vv b' ω)
lemma receiving (x : V): Tendsto (fun n:ℕ=> bracing (A).E T (fun i=> Pm n i) b' l₁ (x.val:Ρ)) atTop (𝓝 (((Vv b' x:p★).val):Ρ)):= charged_limits (P□) (A) (e□) b' l₁ S T Q (fun i=>Θ (B□ (t i) (f i) (S i))) x
lemma envelop_consumes (p:inRow T b' l₁) (g:∀i∈ l₁, Served Y H j (t i) (f i) (S i) (T i) (Q i)) :
    Tendsto (fun n=> Ψ ((l₁.map (fun i=> packetPoly Y H D (Q i) (f i) n)).prod)) atTop (𝓝 (packetEnvelope Y H D G j d c χ f t S T Q l₁ b')):= by
  have hv:= matchesHere Y H D G j d c χ f t S T Q l₁ b' p g
  refine Tendsto.congr' hv ?_
  have he := (tendsto_const_nhds (x:= ((ω).val:Ρ))).inner (𝕜:=ℂ) (receiving Y H D G j d c χ f t S T Q l₁ b' (ω))
  refine (Tendsto.congr' ?_ he)
  exact Eventually.of_forall fun i=> by rw [vocate]
end product
end billing
end YM.CF.Buffered.Afterglow.Tower.Reconstruction
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.envelop_consumes
