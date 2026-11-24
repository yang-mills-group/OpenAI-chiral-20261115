import YM.SU5.Selected.Upstage
import YM.SU5.Selected.WeldedVac
/-!
# Spacetime Euclidean region pair law on step compatibility

This is key for future reconstruction with this same x, even off-shift Pf.
Every polynomials with a disjoint footprint evaluate together by simply
separate advancement to common level and multiplication, preserving at all
higher resolutions. Thus on genuinely separate regions the contact
distinction disappears. Single-token reading, Euclidean product vs one
mono-level mark on union after advancing either. Includes sharp finite-
torus interpretation with the SAME cross-resolution limit in mix. Still does
not say a single step globally homomorphic, or spacelike operator commutation
in Minkowski. Combine with morphisms between coordinate grids.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 600000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.PhaseChoice
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}
  (V:Universal Y H i k I E)
  (G:GroundExtension (i:=i) (k:=k) (E:=E) Y H)
variable (j : Axis) (strict : Bool) (C : Arena Y H G.history.circuit j 0 strict)
local notation "A"=>Ark.Ht Y H G.history.circuit j 0 strict C
local notation "Fₛ" i:max=>Tower.Field Y H i j 0 strict
local notation "κ" s:max=>actor Y H s G.history.circuit j 0 strict C
local notation "ω"=>floorV Y H G.history.circuit j 0 strict C
local notation "Γ"=>Aurora Y H V G.history j strict C
local notation "Ω"=>seat0 Y H V G.history j strict C
local notation "ι₀"=> (Γ).subtypeL
local notation "π"=> (Γ).orthogonalProjectionOnto
open Set Theory MeshClock Tapestry Tapestry.Altitude Tapestry.Exhibition
variable {L:Rack Λ l}{B:Clay Λ l}(D:Exhibition Y H i k I E L B)
local notation "χ"=>Dome (tent Y H)
local notation "Cₚ"=>Cloud (Dome (tent Y H))
local notation "F₀"=>vistaDressing Y H D
local notation "P₀" n:max=>vistaFinish Y H n D
local notation "D₀" n:max=> Exhibition.liftD Y H n D
variable (d:Axis)(T:∀ j:Axis,Arena Y H G.history.circuit j 0 false)
local notation "R"=>catalog Y H V G d false (T d)

variable (x:Resident (catalog Y H V G d false (T d)))
local notation "Mx"=>evaluate Y H V G d T x
local notation "Θ"=> onDrawing Y H V G D d T x
-- here license, on full extension too
lemma separatedPhys {Λ:Preparation}{l s:ℕ}{S T:Finset Cover}{U V:Set RSpace}
    (p:printedHere Λ l s S U)(q:printedHere Λ l s T V)(h:Disjoint U V): Detached Λ l S T:=by
  let r:ℤ:=reserve Λ l
  intro a u b v hv
  let ζ(i:Axis):ℝ:= precisionAt Λ s
  let f(i:Axis):=(markZ Λ s (a i)+markZ Λ s (b i))/2
  have he(i): 0 < ζ i:=positiveScale Λ s
  have hw(i): (a i:ℝ) - b i ≤ 2*(reserve Λ l) ∧ (b i:ℝ)-a i ≤2*(reserve Λ l):=by
    have hg: a i-b i ≤ ((2*reserve Λ l-1:ℕ):ℤ):= (Lattice.box_test.mp hv).2 i
    have hp: -((2*reserve Λ l-1:ℕ):ℤ) ≤ a i-b i:= (Lattice.box_test.mp hv).1 i
    have ht:= margin_good Λ l; exact ⟨by exact_mod_cast (show a i-b i ≤ 2*(reserve Λ l:ℤ) by omega),by exact_mod_cast (show b i-a i ≤ 2*(reserve Λ l:ℤ) by omega)⟩
  have hp(i): (precisionAt Λ s)*f i=((a i:ℝ)+ b i)/2:=by
     unfold f markZ; have h:=positiveScale Λ s; field_simp
  exact Set.disjoint_left.mp h (p a u (show f∈ Tapestry.shield Λ l s a from fun i=> by rw [hp,abs_le]; obtain ⟨x,y⟩:=hw i; constructor <;> linarith)) (q b v (show f∈ Tapestry.shield Λ l s b from fun i => by rw [hp,abs_le]; obtain ⟨x,y⟩:=hw i; constructor <;> linarith))

include V G
lemma lift_paired (s:ℕ){f g:χ}{U W:Set RSpace}(p:f∈keep Λ l s K true U) (q:g∈ keep Λ l s K true W)(h:Disjoint U W) :
  (D₀ s) (f*g)=(D₀ s) f*(D₀ s) g:=by
    obtain ⟨S,u,w⟩:=p; obtain ⟨T,v,k⟩:=q; apply Subtype.ext
    change _=((D₀ s) f).val * ((D₀ s) g).val; rw [lifts_here Y H V G,lifts_here Y H V G,lifts_here Y H V G]
    exact G.history.circuit.separates s u v ((separatedPhys w k h).act Λ l) -- defeq mul
local notation "V₁" U:max t:max n:max=> jetty Λ l K true U (t∩ Set.Iic n)
lemma depart_pair {s:ℕ}{f g:Cₚ}{U W:Set RSpace}{a b:Set ℕ}(p:f∈V₁ U a s)(q:g∈ V₁ W b s)(h:Disjoint U W) :
  (P₀ s) (f*g)=(P₀ s) f*(P₀ s) g:=by
  let M:=a∩ Set.Iic s; let E:=b∩ Set.Iic s
  apply boarded (P:={f| Officer M (fun i=>keep Λ l i K true U) f}) (M:=fun f=>(P₀ s) (f*g)=(P₀ s) f*(P₀ s) g) ?_ ?_ ?_ ?_ p
  · intro x (g₀ : Officer M _ x)
    apply boarded (P:={f|Officer E (fun i=>keep Λ l i K true W) f}) (M:=fun g => (P₀ s) ((pureShot K x)*g)=(P₀ s) (pureShot K x)*(P₀ s) g) ?_ ?_ ?_ ?_ q
    · intro y (p : Officer E _ y)
      have hp : Altitude.Enough s x:= g₀.visible M _ Set.inter_subset_right; have hg:Altitude.Enough s y:=p.visible E _ Set.inter_subset_right
      unfold pureShot vistaFinish; rw [PiTensorProduct.tprod_mul_tprod, Decking.reckon_paid _ _ _ hp,Decking.reckon_paid _ _ _ hg, Decking.reckon_paid _ _ _ (hp.together hg)]
      exact trail h x y g₀.observes p.observes s -- V arg
    · simp
    · intro p q _ _ u v; rw [mul_add,map_add,map_add,mul_add,u,v]
    intro d t _ v; rw [Algebra.mul_smul_comm, map_smul, map_smul, Algebra.mul_smul_comm,v]
  · simp
  · intro p q _ _ u v; rw [add_mul,map_add,map_add,add_mul,u,v]
  intro a b _ v; rw [Algebra.smul_mul_assoc,map_smul,map_smul,Algebra.smul_mul_assoc,v]
where
 trail (h:Disjoint U W)(x y:sequenceOf (tent Y H))(p:∀ i,x i∈keep Λ l i K true U)(q:∀ i,y i∈keep Λ l i K true W)(n:ℕ):
   Decking.finish (F₀) n (x*y) = Decking.finish (F₀) n x * Decking.finish (F₀) n y := by
   induction n with
   | zero => rfl
   | succ n ih =>
     simp only [Decking.finish,Pi.mul_apply,map_mul]; rw [ih]
     have he:(D₀ n) (Decking.finish (F₀) n x * Decking.finish (F₀) n y)=(D₀ n) (Decking.finish (F₀) n x)*(D₀ n) (Decking.finish (F₀) n y):= lift_paired Y H V G D n (finishShelter Λ l n (F₀) (fun i z=>rfl) U (fun i f z=> roofline Λ l i true U D z) x p) (finishShelter Λ l n (F₀) (fun i z=> rfl) W (fun i f z=> roofline Λ l i true W D z) y q) h
     change (D₀ n) _ * _= (D₀ n) _ * _ * ((D₀ n) _ * _); rw [he]; ac_rfl
lemma order_window {s:ℕ}{f g:Cₚ}{U W:Set RSpace}{a b:Set ℕ}(p:f∈ V₁ U a s)(q:g∈ V₁ W b s)(h:Disjoint U W) :
   Θ (f*g)= Mx s (((P₀ s) f).val *((P₀ s) g).val):=by
 rw [drawAt Y H V G D d T x ((shorter χ s).mul_mem (jettyBan Λ l K true U a s p) (jettyBan Λ l K true W b s q)),depart_pair Y H V G D p q h]; rfl
lemma endorse_window {s:ℕ}{f g:Cₚ}{U W:Set RSpace}{a b:Set ℕ}{u v:Bool}(p:f∈ circum Λ l K u U (a∩ Set.Iic s))(q:g∈circum Λ l K v W (b∩ Set.Iic s))(h:Disjoint U W) :
   Θ (f*g)= Mx s (((P₀ s) f).val *((P₀ s) g).val):=
 order_window Y H V G D d T x ((well_spec ..).mp (wellWider Λ K l u (handstamp U) _ p)).1 ((well_spec ..).mp (wellWider Λ K l v (handstamp W) _ q)).1 (Disjoint.preimage _ h)
end YM.CF.Buffered.Afterglow.Tower.PhaseChoice
#print axioms YM.CF.Buffered.Afterglow.Tower.PhaseChoice.endorse_window
