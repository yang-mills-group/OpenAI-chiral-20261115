import YM.SU5.Relativistic.Rates
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
noncomputable def windowPrice (u:I'→Axis→ℝ):ℂ := inner ℂ ω (bracing (Ξ).E T (fun i=> EE i (u i)) b₁ l' ω : V)
local notation "VV" u:max=> windowPrice Y H D G j d c χ f t S T l' b₁ u
variable (u:I'→Axis→ℝ)
lemma window_limit (Q:I'→ℕ→ Packet (timeMesh Λ))(p:∀ i∈ l', Settler (Q i) (u i)) :
    Tendsto (fun n:ℕ=> Q₀ (fun i=>Q i n)) atTop (𝓝 (windowPrice Y H D G j d c χ f t S T l' b₁ u)) := by
 let Y₀(Q : I'→ Packet (timeMesh Λ))(i:I'):=earned Y H D G j d c χ (t i) (f i) (S i) (T i) (Q i)
 have he:Tendsto (fun n:ℕ=> bracing (Ξ).E T (Y₀ (fun i=>Q i n)) b₁ l' ω) atTop (𝓝 (bracing (Ξ).E T (fun i=>EE i (u i)) b₁ l' ω)):=by
     induction l' generalizing b₁ with
     | nil=> exact tendsto_const_nhds
     | cons i l ih=>
       have hz:=p i List.mem_cons_self; have ht(G₁:ℕ): ‖Y₀ (fun i=>Q i G₁) i‖≤‖(Θ (B□ (t i) (f i) (S i)))‖:= not_far j (S i) (T i) (Q i) (u i) (P□) (A) (e□) (Θ (B□ (t i) (f i) (S i))) hz G₁ -- param order
       have hv:= ih ((T i).upper) fun u v=>p u (List.Mem.tail _ v)
       simp only [bracing]; change Tendsto (fun i'=> (Ξ).E (heatGap b₁ _) (Y₀ (fun a=>Q a i') i (_))) atTop (𝓝 ((Ξ).E (heatGap b₁ _) ((EE i (u i)) _)))
       refine ((Ξ).E _).continuous.continuousAt.tendsto.comp ?_
       refine moves_still (H:= (V)) (fun n=> Y₀ (fun a=>Q a n) i) ⟨_,ht⟩ _ hv ?_; exact collecting_point j (S i) (T i) (Q i) (u i) P□ A e□ _ hz _
 exact tendsto_const_nhds.inner he
-- local stability of permitting charts. no matter when any dimensions are equal coordinates; need each authorizing tile to have room for the smeared requests around this offset. supports elsewhere explicitly cared separately.
structure Corridor (u:I'→Axis→ℝ) : Prop where
  vault : inRow T b₁ l'
  issued : ∀ i∈ l', Carries Y H (t i) (f i) j (S i)
  assured : ∀ i∈ l', safely j (S i) (T i) (u i)

local notation "cm" t:max S:max T:max l:max b:max u:max=> Corridor Y H j f t S T l b u
lemma Corridor.eventuallyServed (p:cm t S T l' b₁ u)(Q:I'→ℕ→Packet (timeMesh Λ))(z:∀i∈l',Settler (Q i) (u i)) : ∀ᶠ n in atTop,∀ i∈ l', Served Y H j (t i) (f i) (S i) (T i) (Q i n):=by
 simp_rw [← List.mem_toFinset]; apply (eventually_all_finset _).mpr; intro i hi; have g:=List.mem_toFinset.mp hi
 filter_upwards [safe_with j (S i) (T i) (Q i) (u i) (p.assured i g) (z i g)] with k hk
 exact ⟨p.issued i g,fun v hv=> ⟨(hk v hv).1.le,(hk v hv).2.le⟩⟩
lemma Corridor.pulse (h:cm t S T l' b₁ u)(Q:I'→ℕ→Packet (timeMesh Λ))(z:∀i∈l',Settler (Q i) (u i)) :
    (∀ᶠ v in atTop, Tendsto (fun n=> Ψ ((l'.map (fun i=> packetPoly Y H D (Q i v) (f i) n)).prod)) atTop (𝓝 (Q₀ (fun i=>Q i v)))) ∧
    Tendsto (fun n:ℕ=> Q₀ (fun i=>Q i n)) atTop (𝓝 (windowPrice Y H D G j d c χ f t S T l' b₁ u)):=by
 refine ⟨?_,window_limit Y H D G j d c χ f t S T l' b₁ u Q z⟩
 exact (eventuallyServed Y H j f t S T l' b₁ u h Q z).mono fun i k=> envelop_consumes Y H D G j d c χ f t S T (fun a=>Q a i) l' b₁ h.vault k
/-- Real overlap: different axes (incl different permutation vendor), and ANY registrations and lifts. NOT identifying two orthogonal time generators; charts, not Wightman. -/
theorem Corridor.interchange (h:cm t S T l' b₁ u)(a:Axis)(w:List I')(b':Stamp (timeMesh Λ))(T': I'→ℕ)(X X': I'→ Slab (timeMesh Λ))(q:Corridor Y H a f T' X X' w b' u)(e:l'.Perm w):
    windowPrice Y H D G j d c χ f t S T l' b₁ u= windowPrice Y H D G a d c χ f T' X X' w b' u := by
   choose Q p using fun i:I'=> Settler.advances (timeMesh Λ) (u i)
   obtain ⟨x,x'⟩:= h.pulse Y H D G j d c χ f t S T l' b₁ u Q (fun i _=>p i)
   obtain ⟨v,v'⟩:= q.pulse Y H D G a d c χ f T' X X' w b' u Q (fun i _=>p i)
   -- here subtle `p.pulse ... a` includes binder same etc 
   apply tendsto_nhds_unique_of_eventuallyEq x' v'
   filter_upwards [x,v] with i g u
   apply tendsto_nhds_unique_of_eventuallyEq g u
   exact Eventually.of_forall fun n=> congrArg Ψ (List.Perm.prod_eq (e.map (fun z=> packetPoly Y H D (Q z i) (f z) n))) -- check
end billing
end YM.CF.Buffered.Afterglow.Tower.Reconstruction
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.Corridor.interchange
