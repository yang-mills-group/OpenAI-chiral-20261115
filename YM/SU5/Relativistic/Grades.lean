import YM.SU5.Relativistic.Docket
import YM.SU5.Relativistic.Joint
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

-- both workers see same permitted core. inverse of erase when strict=false.
def reachMark (Z:Calibration) : Dome Z →ₐ[ℂ] Marks Z false where
  toFun i:=⟨i.val,(marque ..).1 i.property,nofun⟩
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_one' := rfl
  commutes' _ := rfl

def packMark (Z:Calibration): Marks Z false →ₐ[ℂ] Dome Z where
  toFun i:= ⟨i.val, (marksSpec false i).1⟩
  map_one' := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl
local notation "φ" n:max f:max => reachMark K (vistaFinish Y H n D f)

lemma priceClimb (n:ℕ) {x:Τ} (h:x∈shorter D₀ n) (t:ℕ)(k:n≤t):
    reachMark K ((P₀ t) x)=upGrade Y H n G.history false (φ n x) t:=by
  induction t,k using Nat.le_induction with
  | base=>apply Subtype.ext; change _= stream Y H G.refine _ _ _; rw [Nat.sub_self]; rfl
  | succ t k ih=>
    have he:= Decking.joins d★ t x (auxiliaryPad K) (Altitude.climbs _ k h)
    apply Subtype.ext -- tune
    change ((P₀ (t+1)) x).val=stream Y H G.refine n ((t+1)-n) ((P₀ n) x).val
    change (P₀ (t+1)) x=(D.liftD Y H t) ((P₀ t) x) at he
    have ht: ((P₀ t) x).val= stream Y H G.refine n (t-n) ((P₀ n) x).val:=congrArg Subtype.val ih
    rw [he,lifts_here Y H D.univ_ G,show t+1-n=t-n+1 by omega,ht]; change G.refine _ _= G.refine (n+(t-n)) (stream _ _ _ _ _ _)
    rw [show n+(t-n)=t by omega]
variable {s:ℕ} {v:Set ℕ} (f : Cloud (Dome (tent Y H))) (U:Set RSpace) (W:Slab (timeMesh Λ))
local notation "ZZ"=>ruler Λ.block
abbrev poet (s:ℕ)(X:Set RSpace):= circum Λ l K true X (Set.Iic s)
lemma precise_meters (n:ℕ) (z:ℤ): (N n z).val= ((ruler Λ.block:ℤ):ℝ)*z*gaugeMesh Λ n:=by
  have ht:= double_clock_calibration Λ n 1; rw [whenly,Nat.cast_one,one_mul,Nat.cast_one,mul_one] at ht
  unfold notch bell; change (z:ℝ)*(mill M n:ℝ)=_
  rw [ht]; ring
lemma collar_inside {n:ℕ}{U:Set RSpace}{S:Finset Cover}(h:SupportedPhysically Λ l n S U) : footprint Λ l n S⊆U:=by
  rintro v p; obtain ⟨i,w⟩:= mem_iUnion.mp p; obtain ⟨w,hv⟩:=mem_iUnion.mp w
  let u:RSpace:=fun i=>2*v i; have he:(fun i:Axis=> u i/2)=v:=by ext; unfold u; ring
  have hz :=h i w (show u∈ Tapestry.shield Λ l n i from (shield_collar ..).symm ▸ (show (fun i:Axis=> u i/2)∈ collar Λ l n i from he.symm ▸ hv)); change (fun i:Axis=> u i/2) ∈ U at hz; rwa [he] at hz
variable {U}
lemma collar_bound (n:ℕ) (x:Cover) : collarLower Λ l n x ≤ collarUpper Λ l n x:=by
  intro i; unfold collarLower collarUpper; nlinarith only [mul_nonneg (show 0≤ (Journey.reserve Λ l:ℝ) by positivity) (gaugeMesh_pos Λ n).le]
lemma lists_between {S:Finset Cover} (c:U ⊆ {x : RSpace| (W.lower:ℝ) ≤ x j ∧ x j≤ (W.upper:ℝ)}) (g:SupportedPhysically Λ l s S U) {d:ℤ} {w:ℕ}(p:notch (timeMesh Λ) s d=W.lower)(t:notch (timeMesh Λ) s (d+w)=W.upper) :
    Between K j (ZZ*d) (ZZ*(d+w)) S:=by
  intro x hx
  have he:collar Λ l s x⊆ footprint Λ l s S:=subset_iUnion_of_subset x (subset_iUnion (fun (_: x∈(S:Set Cover))=> collar Λ l s x) (show x∈(S:Set Cover) from hx))
  have hh:collar Λ l s x⊆ U:= he.trans (collar_inside g)
  obtain ⟨h₁,_⟩:=c (hh (show _ from left_mem_Icc.mpr (collar_bound (Λ:=Λ) (l:=l) s x)))
  obtain ⟨_,h₂⟩:= c (hh (right_mem_Icc.mpr (collar_bound (Λ:=Λ) (l:=l) s x)))
  change (W.lower:ℝ) ≤ collarLower Λ l s x j at h₁; change collarUpper Λ l s x j ≤ (W.upper:ℝ) at h₂
  rw [lower_gauge,←p,precise_meters (Λ:=Λ)] at h₁
  rw [upper_gauge,←t,precise_meters (Λ:=Λ)] at h₂
  unfold gaugePosition at h₁ h₂
  rw [←_root_.sub_mul,mul_le_mul_iff_left₀ (gaugeMesh_pos ..),le_sub_iff_add_le] at h₁
  rw [← _root_.add_mul,mul_le_mul_iff_left₀ (gaugeMesh_pos ..)] at h₂
  refine ⟨show ZZ*d+(reserve Λ l:ℤ) ≤ x j by exact_mod_cast h₁, show x j+(reserve Λ l:ℤ) ≤ ZZ*(d+w) by exact_mod_cast h₂⟩
lemma precise_tile (v : f∈ poet Y H s U) (p:U ⊆ {x : RSpace | (W.lower:ℝ) ≤ x j ∧ x j≤ (W.upper:ℝ)}) (t:W.lines s) : ∃ A : driveAlgebra Y H D.univ_ G.history G.clipped j false J,
    Docked Y H D.univ_ s G.history G.clipped j J W (reachMark (tent Y H) ((P₀ s) f)) A:=by
  have he:f∈ circum Λ l K true U (Set.Iic s ∩ Set.Iic s):=by rw [Set.inter_self]; exact v
  have aK:= gateIssued Λ (tent Y H) l true (handstamp U) (Set.Iic s) s he
  have a₁: ((P₀ s) f)∈keep Λ l s K true (handstamp U):=crownShelter Λ l s d★ (auxiliaryPad K) (fun i x=>rfl) (handstamp U) (fun i g h=>roofline Λ l i true (handstamp U) D h) ((well_spec Λ K l true _ _).1 he).1
  obtain ⟨S,u,hg⟩:=a₁
  have hS:InTest K true S false ((P₀ s) f).val := (Tapestry.locates ..).1 u
  obtain ⟨⟨c,hc⟩,b,hb⟩:=t
  have hc': c<b:= (stamp_lt M s _ _).mp (by rw [hc,hb]; exact W.thick)
  obtain ⟨w,(h₀:0<w),(v:c+(w:ℤ)=b)⟩:∃ w:ℕ,0<w∧ c+(w:ℤ)=b:=⟨(b-c).toNat,by omega,by omega⟩
  subst b; have h := (lists_between Y H j W p (S:=S) (s:=s) hg hc hb).relocate K j (-c)
  have h' : Between K j 0 (ZZ*w) (plow K j (-c) S):=by
    change Between K j (ZZ*_+_) (ZZ*_+_) _ at h
    rw [show ZZ*(-c)+ZZ*c=0 by ring,show ZZ*(-c)+ZZ*(c+(w:ℤ))=ZZ*w by ring] at h; exact h
  let X:=relocate K j (-c) ((P₀ s) f).val; have hX:= flow_port K j (gaugeT K (-c)) hS
  let x: Tower.Field Y H s j 0 false:= ⟨X,(purpose_ok ..).2 ⟨⟨plow K j (-c) S,hX,by intro i hi; rw [area0]; exact (h' i hi).1⟩,nofun⟩⟩
  let e : Entry Y H s j false w:= ⟨x,plow K j (-c) S,hX,h'⟩
  exact ⟨entrance Y H D.univ_ s G.history G.clipped j false J e h₀, c,w,hc,hb,h₀,e,rfl,rfl⟩
end YM.CF.Buffered.Afterglow.Tower.Reconstruction
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.priceClimb
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.precise_tile
