import YM.SU5.Selected.Time.Diary
import YM.SU5.Selected.Euro.Palate
import YM.SU5.Selected.Time.Prom
/-! Observables CP6. Select & reconstruct continuous **physical time**, no spectator semantics. Includes concurrence test of spatial mesh motions. Test spacings as Vanguard. ( `monoAxis U` has dummy spatial even though real mesh is present; `stay` keeps only relevant time facts expressed with spectralP pushed to ℝ of THAT operator system). -/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 320000
set_option quotPrecheck false
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.Selection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory
open RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
open scoped InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark OS.Semigroup MeshClock
open Vacancy

variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  {D : ℕ → Family (tent Y H) → Family (tent Y H)} {a b : ℕ → ℕ}
  (Q : Coherent (i := i) (k := k) (E := E) Y H D a b)
  (Qc : Clipped Y H (i ∘ a) (k ∘ b))
  (j : Axis) (r : Bool) (C : Arena Y H Q.circuit j 0 r)
local notation "R" => Aurora Y H V Q j r C
local notation "A" => Ark.Ht Y H Q.circuit j 0 r C
local notation "W" => floorV Y H Q.circuit j 0 r C
local notation "F₊" n:max => Tower.Field Y H n j 0 r
local notation "φ" n:max => actor Y H n Q.circuit j 0 r C
local notation "Ω" => seat0 Y H V Q j r C
local notation "π₀" => (R).orthogonalProjectionOnto
local notation "N" n:max => cap Y H V n Q Qc j r C
local notation "Test" => Vacancy.observable (tent Y H) r
local notation "Lab" => Beacon (tent Y H) r

local notation "B" => groundAlgebra Y H V Q Qc j r C
local notation "Β" => pruner Y H V Q Qc j r C
local notation "M" s:max => liftCap Y H V Q Qc j r C s
local notation "uℋ" => basisRoom Y H V Q j r C
local notation "U₀" s:max => timePruner Y H V Q Qc j r C s
local notation "p₀" s:max => spacePruner Y H V Q Qc j r C s
local notation "τ" s:max => tick Y H s j 0 r
local notation "ρ" s:max => ripple Y H V s Q.circuit j 0 r C
local notation "P₀" s:max => stretches Y H V Q Qc j r C s
variable {χ : CapCharacter Y H V Q Qc j r C} (U : Birthplace Y H V Q Qc j r C χ)
local notation "λ₀" => vacuum Y H V Q Qc j r C U
local notation "η" s:max => markedActor Y H V Q Qc j r C U s
local notation "η₀" => leave Y H V Q Qc j r C U
open Companies
namespace Actress
-- no default quotient identification of window widths, even for unit letters. Heat envelope. (May later strip envelopes under provenance costs.) Urban labels can group across time with physical shift as in Tapestry/Block.
open Tapestry
local notation "C₀" V:max s:max w:max f:max h:max=> boxOp Y H V s Q Qc j r C w f h
local notation "J"=> Diary.jetTime Y H V Q Qc j r C U
variable (s:ℕ)
section city
variable (w:ℕ)(f:Entry Y H s j r w)(p:0<w)
abbrev incubate := (η₀) ((P₀ s) w f p)
local notation "Vγ"=> (C₀ V s w f p)
local notation "B₁" => incubate Y H V Q Qc j r C U
local notation "W₁" s:max=> SlabMark.boxOp Y H V s Q Qc j r C
include V Q Qc C U p
lemma thrills (x : F₊ s) : B₁ s w f p ((η s) x)= (η s) (slabT Y H s j r w f x):= acts_on _ _ _ _ _ _ _ _ s U _ _ _ _ (prepare_box Y H V Q Qc j r C s w f p x) -- inspect args
lemma service_u : B₁ s w f p λ₀=(η s) f.val:= by
 let i:=B₁ s w f p; have h:slabT Y H s j r w f (unity Y H j 0 r s)=f.val:= by apply Subtype.ext; rw [slab_eq]; change _*relocate K j w 1=f.val.val; rw [relocate_unit,mul_one];
 exact (congrArg i (normal_base Y H V Q Qc j r C U s)).trans ((thrills Y H V Q Qc j r C U s w f p _).trans (congrArg (η s) h))
lemma metrics {v:ℕ}(g:Entry Y H s j r v)(q:0<v): (B₁ s w f p)*(B₁ s v g q) = B₁ s _ (SlabMark.edit Y H s j r w v f g) (by omega):=(map_mul (η₀) _ _).symm.trans (congrArg (η₀) (Subtype.ext (SlabMark.edit_comp Y H V s Q Qc j r C w v f g p q)))
lemma reverses : star (B₁ s w f p)=B₁ s w (inverse Y H s j r w f) p:= (map_star ..).symm.trans (congrArg (η₀) (show star ((P₀ s) w f p)= _ from Subtype.ext (SlabMark.respects Y H V s Q Qc j r C w f p)))
lemma sets (t:ℕ)(h:s≤t): B₁ s w f p=B₁ t _ (furnished Y H s Q j r w f t h) (Nat.mul_pos (pow_pos Λ.R.L.property _) p):=
 congrArg (η₀) (Subtype.ext (SlabMark.refined_box Y H V s Q Qc j r C w f p t h))
local notation "HT" n:max=> (J).E (whenly (timeMesh Λ) s n)
private lemma plank (n:ℕ): HT n=walking Y H V Q Qc j r C U s (2*n):=(journey Y H V Q Qc j r C U).track_even s n
private lemma supplyTime (n:ℕ): advance Y H V Q.circuit j 0 r C (whenly (timeMesh Λ) s n)=((U₀ s) (2*n)).val:= Tower.advance_at Y H V s Q.circuit j 0 r C n -- order
lemma roof_id: B₁ s w (SlabMark.identity Y H s j r w) p=HT w:=by
 have he : (P₀ s) w (SlabMark.identity Y H s j r w) p = (U₀ s) (2*w):= Subtype.ext ((SlabMark.ticket_birth Y H V s Q Qc j r C w p).trans (supplyTime Y H V Q Qc j r C U s w p w))
 exact (congrArg (η₀) he).trans (plank Y H V Q Qc j r C U s w p w).symm
-- padding time doesn't keep same *operator*. Only AFTER ground projection can ignore in those senses.
lemma flexR(n:ℕ)(X:Entry Y H s j r (w+n))(v:X.val.val=f.val.val): B₁ s _ X (by omega)=(B₁ s w f p)*(HT n):=by
 let P:= (U₀ s) (2*n); rw [plank Y H V Q Qc j r C U s w p]; have ht: (P₀ s) (w+n) X (by omega)= ((P₀ s) w f p)*P:= by apply Subtype.ext; rw [show ((P₀ s) _ X (by omega)).val= _ from (show ((P₀ s) _ X (by omega)).val = _ from SlabMark.shape_right Y H V s Q Qc j r C w w f p n X v)]; rw [supplyTime Y H V Q Qc j r C U s w p]; rfl
 exact (congrArg η₀ ht).trans (map_mul ..)
lemma flexL(n:ℕ)(X:Entry Y H s j r (n+w))(v:X.val.val=relocate K j n f.val.val): B₁ s _ X (by omega)=(HT n)*(B₁ s w f p):=by
 let P:= (U₀ s) (2*n); rw [plank Y H V Q Qc j r C U s w p]; have ht: (P₀ s) (n+w) X (by omega)=P*((P₀ s) w f p):= by apply Subtype.ext; rw [show ((P₀ s) _ X (by omega)).val= _ from (show ((P₀ s) _ X (by omega)).val = _ from SlabMark.shape_left Y H V s Q Qc j r C w w f p n X v)]; rw [supplyTime Y H V Q Qc j r C U s w p]; rfl
 exact (congrArg η₀ ht).trans (map_mul ..)
local notation "Ψ" v:max=> travel_χ Y H V Q Qc j r C U s v
lemma sideways_commit (i:Trans j)(d:ℤ) : (Ψ i) d * B₁ s w f p= B₁ s w (blown Y H j r s i.val i.property d w f) p * (Ψ i) d :=by
 let u:= spacePruner Y H V Q Qc j r C s i d; let g:= (P₀ s) w (blown Y H j r s i.val i.property d w f) p; have hr:u*((P₀ s) w f p)=g*u:=Subtype.ext (sail_width Y H V Q Qc j r C s i.val i.property d w f p)
 exact (map_mul η₀ u ((P₀ s) w f p)).symm.trans ((congrArg (η₀) hr).trans (map_mul η₀ g u))
end city
section label
structure Label where -- local mark (real stencil separately can certify narrow & support)
 count : ℕ
 span : ℕ
 paid : 0 < span
 appraise : Entry Y H count j r span
 ward : CovCover (tent Y H) appraise.val.val -- literal neutral on gauge. ward persists
variable (F:Label Y H j r)
abbrev Label.original:= F.appraise.val
abbrev Label.time := whenly (timeMesh Λ) F.count F.span -- ℝ≥0
abbrev Label.money:= incubate Y H V Q Qc j r C U F.count F.span F.appraise F.paid
local notation "Z₁"=> Label.money Y H V Q Qc j r C U
local notation "YY"=> Label.time Y H j r
local notation "Kx"=> Label.original Y H j r
section furnish
variable (p:F.count ≤ s)
def Label.finery : Entry Y H s j r (Λ.R.L.val^(s-F.count)*F.span):= furnished Y H F.count Q j r F.span F.appraise s p
local notation "f₀" s:max=> furnished Y H F.count Q j r F.span F.appraise s p
include F V Q Qc C U p
lemma Label.upSize : (YY F)=whenly (timeMesh Λ) s (Λ.R.L.val^(s-F.count)*F.span):= (MeshClock.matchR (timeMesh Λ) F.count s F.span p).symm
lemma Label.up_neutral: CovCover (K) ((f₀ s).val.val):= by
 obtain ⟨T,x⟩:=((SlabMark.test_entry Y H F.count j r F.appraise).paid); let f:=stream Y H D F.count (s-F.count) (Kx F).val; exact (obs_in _ _ _ _).mp (Tower.chroma Y H Q.circuit F.count (s-F.count) ((obs_in ..).2 ⟨x,F.ward⟩)) |>.2 -- no univ.
lemma Label.compatible: Z₁ F= incubate Y H V Q Qc j r C U s _ (Label.finery Y H Q j r s F p) (Nat.mul_pos (pow_pos Λ.R.L.property _) F.paid):= sets Y H V Q Qc j r C U F.count F.span F.appraise F.paid _ p
end furnish
end label
end Actress
end YM.CF.Buffered.Afterglow.Tower.Selection
open YM.CF.Buffered.Afterglow.Tower.Selection.Actress
#print axioms service_u
#print axioms thrills
#print axioms metrics
#print axioms sets
#print axioms Label.up_neutral
#print axioms Label.compatible
#print axioms Label.upSize
#print axioms roof_id
#print axioms reverses
#print axioms flexR
#print axioms flexL
#print axioms sideways_commit
