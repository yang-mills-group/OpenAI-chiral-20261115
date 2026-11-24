import YM.SU5.FiniteGaugeData.Tapestry.SkyRoom
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 450000
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
# Multilevel positive-correlation computation

Opposition with respect to a *single* physical plane, with the buffer & room
convention used for these local observables. Includes the union over all usable
levels ≥ start level; we don't restrict to single-scale positives. `Θ` doesn't
require kernels be positive, only an exact separated product & reflection.
Here split the algebra calculation from the analytic proofs; everything used is
proved on the actual election in the Tapestry modules.
-/
set_option quotPrecheck false
namespace Sunlight
variable (Λ:Preparation)(l:ℕ)(a:Axis)(z: Sunlight Λ)(K:Calibration)
def arena := Set.Ici z.start
abbrev sanctum := jetty Λ l K true (flank a (z.hinge Λ)) (z.arena Λ)
abbrev cloister (n:ℕ) := jetty Λ l K true (flank a (z.hinge Λ)) ((z.arena Λ) ∩ Set.Iic n)
lemma limitsArena {x: Cloud (Dome K)}(p:x∈ sanctum Λ l a z K): ∃ n:ℕ, z.start≤ n∧ x∈cloister Λ l a z K n:=by
 obtain ⟨n,v⟩:= entrusted Λ l K true (flank a (z.hinge Λ)) (z.arena Λ) p
 refine ⟨max z.start n, le_max_left .., ?_⟩; apply admits Λ l K true (flank a (z.hinge Λ)) (flank a (z.hinge Λ)) ((z.arena Λ)∩ Set.Iic n) ((z.arena Λ)∩ Set.Iic (max z.start n)) ?_ Set.Subset.rfl v; exact fun i p=> ⟨p.1, le_trans (show i ≤ n from p.2) (le_max_right z.start n)⟩
lemma respectsCut {x:Cloud (Dome K)}{n:ℕ}(p:x∈ cloister Λ l a z K n): oppose Λ a z K x∈ shorter (Dome K) n := jettyBan Λ l K true _ (z.arena Λ) n (opposition Λ l a z K (V:=flank a (z.hinge Λ)) Set.inter_subset_left _ p) -- n implicit variable add later
end Sunlight

section generic
variable (Λ:Preparation)(l:ℕ)(α:Axis)(z:Sunlight Λ)(n:ℕ)
variable {K : Calibration}
variable (D:Decking (Dome K) (fun _=> Dome K))(v:Pad (Dome K))

-- local-only version. Supply `finishShelter` also for nonaligned V from B.
variable (both : ∀ i:ℕ,∀ x:Dome K, D.perceive i x=x)
variable (V : Set RSpace) (H : ∀ (i:ℕ) (x:Dome K), x∈keep Λ l i K true V→D.surge i x∈keep Λ l (i+1) K true V)
include H both
lemma finishShelter(f:ℕ→Dome K)(q:∀ i,f i∈ keep Λ l i K true V) : Decking.finish D n f∈keep Λ l n K true V:=by
 induction n with
 | zero=> rw [Decking.finish,both]; exact q 0
 | succ n ih=> rw [Decking.finish,both]; exact Subalgebra.mul_mem (keep Λ l (n+1) K true V) (H n _ ih) (q (n+1))
lemma crownShelter{a: Set ℕ}{x:Cloud (Dome K)}(p:x∈jetty Λ l K true V (a∩ Set.Iic n)): D.crown v n x∈keep Λ l n K true V:=by
 apply boarded (P:={f|Officer (a∩Set.Iic n) (fun i=>keep Λ l i K true V) f}) (M:=fun x=>_) ?_ ?_ ?_ ?_ p
 · intro f (g : Officer _ _ f); rw [Decking.reckon_paid _ _ _ (g.visible _ _ Set.inter_subset_right)]; exact finishShelter Λ l n D both V H f g.observes
 · rw [map_zero]; exact Subalgebra.zero_mem _
 · intro x y t e u w; rw [map_add]; exact Subalgebra.add_mem _ u w
 intro a y t e; rw [map_smul]; exact Subalgebra.smul_mem _ e a
omit H
local notation "Θ" i:max=> aureole K α (z.marks i)
local notation "F" => Sunlight.opponent Λ α z K
-- combine step hypotheses into sun eligibility
structure GlassRule (K:Calibration)(D:Decking (Dome K) (fun _=>Dome K)):Prop where
 lantern(i:ℕ)(x:Dome K):D.perceive i x=x
 onward(i:ℕ)(x:Dome K): x∈ keep Λ l i K true (flank α (Sunlight.hinge Λ z)) → D.surge i x∈keep Λ l (i+1) K true (flank α (Sunlight.hinge Λ z)) -- useful early
 opposeMany(i:ℕ)(u:z.start≤ i)(x y:Dome K)(p:x∈keep Λ l i K true (flank α (Sunlight.hinge Λ z)))(g:y∈keep Λ l i K true (flank α (Sunlight.hinge Λ z))) :
    D.surge i (aureole K α (z.marks i) x * y)=aureole K α (z.marks (i+1)) (D.surge i x) * D.surge i y
omit both
variable (G:GlassRule Λ l α z K D)
include G
local notation "Φ"=>fun i : ℕ=>keep Λ l i K true (flank α (Sunlight.hinge Λ z))
lemma outlook {S:Set ℕ}(w:S⊆ z.arena Λ) (t:z.start≤n)
   {f g:ℕ→ Dome K}(p : Officer S (fun i=>keep Λ l i K true (flank α (Sunlight.hinge Λ z))) f)(q: Officer S (fun i=>keep Λ l i K true (flank α (Sunlight.hinge Λ z))) g) :
 D.finish n (Sunlight.opponent Λ α z K f * g) = aureole K α (z.marks n) (D.finish n f) * D.finish n g := by
  induction n,t using Nat.le_induction with
  | base=>
    have h(i)(p:i<z.start): i∉ S := fun q=> p.not_ge (w q)
    rw [Decking.finish_alone D z.start (F f*g) ?_, Decking.finish_alone D z.start f (fun n g=> p.forbids _ (h n g)), Decking.finish_alone D z.start g (fun n g=> q.forbids _ (h n g)), G.lantern,G.lantern,G.lantern]
    · rfl
    intro i v; rw [Pi.mul_apply,Sunlight.opponent,plumeTail,p.forbids i (h i v),q.forbids i (h i v),aureoleUnit,mul_one]
  | succ n v ih=>
    rw [Decking.finish,Decking.finish,Decking.finish,ih,G.lantern,G.lantern,G.lantern,G.opposeMany _ v _ _ (finishShelter Λ l n D G.lantern (flank α (z.hinge Λ)) G.onward f p.observes) (finishShelter Λ l n D G.lantern (flank α (z.hinge Λ)) G.onward g q.observes)]
    rw [aureoleProduct,Pi.mul_apply]
    rw [show (Sunlight.opponent Λ α z K f (n+1))=(Θ (n+1)) (f (n+1)) from rfl]; ac_rfl

local notation "V'"=> Sunlight.cloister Λ l α z K n
local notation "ϑ"=> Sunlight.oppose Λ α z K
local notation "F'" => D.crown v n
set_option maxRecDepth 3000 in
lemma reflectionHat {x y: Cloud (Dome K)}(t : z.start≤ n)(p:x∈Sunlight.cloister Λ l α z K n)(q : y∈Sunlight.cloister Λ l α z K n):
    D.crown v n (z.oppose Λ α K x * y)= aureole K α (z.marks n) (D.crown v n x)*D.crown v n y:=by
  let S:=z.arena Λ∩ Set.Iic n; let V:= {f| Officer (z.arena Λ∩Set.Iic n) (Φ) f}
  apply boarded (M:=fun x=> F' (ϑ x*y)=(Θ n) (F' x)*F' y) (P:=V) ?_ ?_ ?_ ?_ p
  · intro x (x' : Officer S _ x); have he:= x'.visible S _ Set.inter_subset_right -- tuning inferred n
    apply boarded (M:=fun y=> F' (ϑ (pureShot K x)*y)=(Θ n) (F' (pureShot K x))*F' y) (P:=V) ?_ ?_ ?_ ?_ q
    · intro y (g:Officer S _ y); have hg:Enough n y:=g.visible S _ Set.inter_subset_right
      rw [Sunlight.opposes]; unfold pureShot; rw [PiTensorProduct.tprod_mul_tprod,Decking.reckon_paid _ _ _ ((z.opponentEnough Λ α n K he).together hg), Decking.reckon_paid _ _ _ he, Decking.reckon_paid _ _ _ hg]; exact outlook Λ l α z n D G Set.inter_subset_left t x' g -- w not defeq maybe
    · rw [mul_zero,map_zero,mul_zero]
    · intro a b h t g u; rw [mul_add,map_add,map_add,mul_add,g,u]
    intro y z c g; rw [Algebra.mul_smul_comm,map_smul,map_smul,Algebra.mul_smul_comm,g]
  · simp
  · intro x g h u t v; rw [map_add,add_mul,map_add,t,v,map_add,map_add,add_mul]
  intro w u t k; rw [LinearMap.map_smulₛₗ,Algebra.smul_mul_assoc,map_smul,k,map_smul, LinearMap.map_smulₛₗ,Algebra.smul_mul_assoc]
end generic
end YM.CF.Buffered.Afterglow.Tapestry
#print axioms YM.CF.Buffered.Afterglow.Tapestry.reflectionHat
#print axioms YM.CF.Buffered.Afterglow.Tapestry.crownShelter
