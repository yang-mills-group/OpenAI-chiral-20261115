import YM.SU5.FiniteGaugeData.Tapestry.Keeps
import YM.SU5.FiniteGaugeData.Tapestry.Colonnade
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tapestry
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
open Satin
attribute [local instance] opCStarAlgebra
open Py Py.Rate LocalLimit Preparation Journey Vale FullBill
open Nacre Mir Phase RP
open Altitude Heat
open PiTensorProduct (tprod)

/-!
# Support (in physical cover regions), coherent time plane and antilinear reflection

Allowed levels can be restricted in any of these polynomials. For positivity use
only levels where the plane is aligned---e.g. it might be fractional in units of
the very coarsest gauge spacing even though it's an integer at slightly finer
levels. Use any axis. Keep the tower vocabulary independent of the plane.

All local observables make up the union over bounded regions, still at fixed
stencil widths per named resolution in building each. `jetty .. Set.univ` gives
this algebra; keep takes s and Region. Use first-link only or all supported. These
ignore color qualification; others may intersect with it.
-/
set_option quotPrecheck false
variable (Λ:Preparation)(l:ℕ)
section
variable (K:Calibration)(wide:Bool)(V W:Set RSpace) (a b:Set ℕ)
def jetty : Subalgebra ℂ (Cloud (Dome K)) := colonnade a fun i=>keep Λ l i K wide V
lemma jetty_span : (jetty Λ l K wide V a).toSubmodule= Altitude.heights {f| Officer a (fun i=> keep Λ l i K wide V) f}:= rfl
lemma generating : jetty Λ l K wide V a= Algebra.adjoin ℂ (⋃ i∈a, (pinhole (Dome K) i) '' (keep Λ l i K wide V:Set (Dome K))) := col_generation ..
lemma jettyBan (k:ℕ): jetty Λ l K wide V (a∩ Set.Iic k)≤ shorter (Dome K) k:= col_short ..
lemma jets : jetty Λ l K wide V a≤ FiniteGaugeDataPoly K:= col_poly ..
lemma jetty_awork : jetty Λ l K true Set.univ Set.univ=FiniteGaugeDataPoly K:= by simp_rw [jetty,fullKeep,vestibuleFull]; exact col_unbound
-- isotony in whole regions/level windows etc
lemma admits (h:a⊆ b)(p:V ⊆ W): jetty Λ l K wide V a≤jetty Λ l K wide W b:= makesWay _ _ _ _ h fun i _=> rooms Λ l i K wide V p
lemma exposes : jetty Λ l K wide V a≤jetty Λ l K true V a:=makesWay _ _ _ _ Set.Subset.rfl fun i _=> access Λ l i K wide V
lemma entrusted {x:Cloud (Dome K)}(p:x∈jetty Λ l K wide V a): ∃ n:ℕ,x∈ jetty Λ l K wide V (a∩ Set.Iic n):= (col_front ..).mp p

-- `jetty` really all local polynomials, recover in bounded portions, not a von Neumann claim.
lemma cabin_event (s:ℕ){x:Dome K}(p:x∈keep Λ l s K wide V): ∀ᶠ N:ℕ in atTop,x∈ keep Λ l s K wide (V ∩ cabin N):=by
 obtain ⟨S,h,t⟩:=p; exact (fundCabin Λ l s S).mono fun n p=> ⟨S,h,fun x hx=>Set.subset_inter (t x hx) (p x hx)⟩
lemma cabined (x:Cloud (Dome K))(p:x∈ jetty Λ l K wide V a): ∀ᶠ n:ℕ in atTop, x∈ jetty Λ l K wide (V∩ cabin n) a:=by
 let U(n:ℕ):= jetty Λ l K wide (V∩cabin n) a
 apply boarded (P:={f|Officer a (fun i=>keep Λ l i K wide V) f}) (M:=fun x=>∀ᶠ n:ℕ in atTop,x∈ U n) ?_
    (Eventually.of_forall fun n=> (U n).zero_mem) (fun x y _ _ u v=> (u.and v).mono fun i h=> (U i).add_mem h.1 h.2) (fun z x _ u=> u.mono fun i h=> (U i).smul_mem h z) p
 intro f h; have t:Officer a _ f := h; obtain ⟨n,x⟩:= t.toll
 filter_upwards [(eventually_all_finset (Iic n)).mpr fun i _=> cabin_event Λ l K wide V i (t.observes i)] with j q
 refine officer_stone a (fun i=> keep Λ l i K wide (V∩cabin j)) ?_; refine ⟨t.toll,fun i=>?_,t.forbids⟩
 by_cases h:i≤n; exact q i (mem_Iic.mpr h); rw [x _ (Nat.gt_of_not_le h)]; exact Subalgebra.one_mem _ -- may name lt
end

/- Planes are certified in integer gauge coords of each usable mesh. For the
   PSD claim require not just common x but the GaugeShift of block (multiple
   4Λ.block). Convention for signs (see Buffered/Reflection). -/
abbrev flank (α:Axis)(z:ℝ): Set RSpace := {x| z ≤ x α}
def mirrorE (α:Axis)(z:ℝ)(x:RSpace) : RSpace:= fun i=> if i=α then 2*z-x i else x i
lemma mirrorTwice (α:Axis) (z:ℝ): Involutive (mirrorE α z) := fun x=> by ext a; unfold mirrorE; by_cases p:a=α<;>simp [p]
lemma mirroredShield {s α z}(x:Cover){y:RSpace}(p:y∈ shield Λ l s ((plane α z).motion x)): mirrorE α (markZ Λ s z) y ∈ shield Λ l s x :=by
 intro i; have h : |precisionAt Λ s*y i- ((plane α z).motion x i:ℤ)| ≤ (reserve Λ l:ℝ):= p i -- cast
 rw [fling_move] at h; by_cases e:i=α; swap
 · unfold mirrorE; rw [if_neg e]; rwa [if_neg (Ne.symm e)] at h
 rw [if_pos e.symm] at h; unfold mirrorE; rw [if_pos e]
 obtain ⟨a,b⟩:= abs_le.mp h; have hl:markZ Λ s z*precisionAt Λ s=z:=div_mul_cancel₀ _ (positiveScale Λ s).ne'; push_cast at a b ⊢; rw [abs_le]; constructor<;> linarith
lemma reversed {S:Finset Cover}{s α z V}(p:printedHere Λ l s S V): printedHere Λ l s (negativeSide S z α) ((mirrorE α (markZ Λ s z)) '' V):=by
  intro x h; obtain ⟨u,c,rfl⟩:=mem_image.mp h; intro y v
  exact ⟨_,p u c (mirroredShield Λ l u v), mirrorTwice α (markZ Λ s z) y⟩ -- .. weird
lemma facingBay {s α z V}(K:Calibration)(wide:Bool){x:Dome K}(p:x∈keep Λ l s K wide V): aureole K α z x∈keep Λ l s K wide (mirrorE α (markZ Λ s z) '' V):=by obtain ⟨S,h,q⟩:=p; exact ⟨_, aureoleBay K S _ α z x h, reversed Λ l q⟩

structure Sunlight where
 start : ℕ
 marks : ℕ → ℤ
 -- gauge lattice coords. phase before start irrelevant
 aligned (i) : start ≤ i → Scaled Λ (marks i) = marks (i+1)
 shifted (i) : start ≤ i → ∃ z:ℤ, marks i= Heat.gaugeShift Λ.block z

-- immersions at fixed points (mate/spin unit 2), can construct any start/gaugeShift integer. Supply x=0 on unused coarser.
def glare (s: ℕ)(z:ℤ): Sunlight Λ where
 start:=s
 marks i:= if s≤ i then Heat.gaugeShift Λ.block ((Λ.R.L.val:ℤ)^(i-s)*z) else 0
 aligned i p:=by rw [if_pos p,if_pos (show s ≤ i+1 by omega), show i+1-s=i-s+1 by omega, pow_succ]; unfold Scaled Heat.gaugeShift; ring
 shifted i p:=⟨_,if_pos p⟩
lemma glareFound (s:ℕ)(z:ℤ): (glare Λ s z).marks s= Heat.gaugeShift Λ.block z:=by simp [glare]

namespace Sunlight
variable (a:Axis)(z:Sunlight Λ)(n:ℕ)(K:Calibration)
abbrev hinge:= markZ Λ z.start (z.marks z.start)
lemma home (p:z.start≤n): markZ Λ n (z.marks n)= z.hinge Λ:=by
 induction n,p using Nat.le_induction with |base=> rfl |succ n k ih=> rw [←z.aligned n k, markUp, ih]
lemma fires {V:Set RSpace}{x:Dome K}{wide:Bool}(h:x∈ keep Λ l n K wide V)(p:z.start ≤ n): aureole K a (z.marks n) x∈ keep Λ l n K wide ((mirrorE a (z.hinge Λ)) '' V):=by rw [← z.home Λ n p]; exact facingBay Λ l K wide h
lemma rents {S:Finset Cover}(p:z.start ≤ n) : printedHere Λ l n S (flank a (z.hinge Λ)) ↔ Ledge Λ l S a (z.marks n) := by rw [←z.home Λ n p]; exact ⟨returns Λ l n a (z.marks n) S,brought Λ l n a (z.marks n) S⟩ -- wide omit

def oppose : Cloud (Dome K) →ₗ⋆[ℂ] Cloud (Dome K):= plume (fun i=> aureole K a (z.marks i))
def opponent (f:sequenceOf K):sequenceOf K := plumeTail (fun i=> aureole K a (z.marks i)) f
@[simp] lemma opposes (f:sequenceOf K): oppose Λ a z K (pureShot K f)=pureShot K (z.opponent Λ a K f):= pluage ..
lemma turns : Function.Involutive (oppose Λ a z K) := Altitude.flare _ (fun i=> aureoleTwice K a _) -- binder syntax tune
lemma opposeOne: z.oppose Λ a K 1=1:= plumeUnit _ fun i=> aureoleUnit ..
lemma opposeMany (x y: Cloud (Dome K)): oppose Λ a z K (x*y)= oppose Λ a z K x* oppose Λ a z K y:= plumeTimes (fun i=> aureole K a (z.marks i)) (fun i=> aureoleProduct K a _) _ _
lemma opponentEnough {f:sequenceOf K} (p:Enough n f) : Enough n (opponent Λ a z K f):= plumeEnough _ (fun i=>aureoleUnit ..) p
lemma onOfficer {S:Set ℕ} (u:S⊆ Set.Ici z.start)(V:Set RSpace)(wide:Bool)(f:sequenceOf K)(p:Officer S (fun i=>keep Λ l i K wide V) f): Officer S (fun i=>keep Λ l i K wide (mirrorE a (z.hinge Λ) '' V)) (z.opponent Λ a K f):=by
 have he(i:ℕ)(h:i∉S) : opponent Λ a z K f i=1:=by unfold opponent plumeTail; rw [p.forbids i h,aureoleUnit]
 refine ⟨⟨p.toll.choose, z.opponentEnough Λ a p.toll.choose K p.toll.choose_spec⟩,fun i=> ?_,he⟩; by_cases h:i∈ S; exact z.fires Λ l a i K (p.observes i) (u h); rw [he i h]; exact Subalgebra.one_mem _
lemma opposition {S:Set ℕ}(u:S⊆Set.Ici z.start)(V:Set RSpace)(wide:Bool){x:Cloud (Dome K)}(p:x∈jetty Λ l K wide V S): oppose Λ a z K x∈jetty Λ l K wide (mirrorE a (z.hinge Λ) '' V) S:=
 plumeExtend _ (P:={f|Officer S (fun i=>keep Λ l i K wide V) f}) (Q:={f|Officer S (fun i=>keep Λ l i K wide (mirrorE a (z.hinge Λ) '' V)) f}) (fun f H=> onOfficer Λ l a z K u V wide f H) p
end Sunlight
end YM.CF.Buffered.Afterglow.Tapestry
#print axioms YM.CF.Buffered.Afterglow.Tapestry.Sunlight.turns
#print axioms YM.CF.Buffered.Afterglow.Tapestry.Sunlight.opposition
#print axioms YM.CF.Buffered.Afterglow.Tapestry.Sunlight.onOfficer
#print axioms YM.CF.Buffered.Afterglow.Tapestry.cabined
#print axioms YM.CF.Buffered.Afterglow.Tapestry.generating
