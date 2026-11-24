import YM.SU5.Reconstruction.Based.Magnitude
import YM.SU5.Reconstruction.Based.Pegs
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 5000
set_option maxHeartbeats 950000
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra

variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
set_option quotPrecheck false
open CF.Pannier.Chancel CF.Pannier.Chancel.Cliplet Py.Rate.Pannier
open SlabMark Finset Fock Lat Laurent Cube Spire Vale Pastry Peaks Dial Phase Lifted Skye Tenant Rush Tulip Girt Scree RG
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
namespace LineCharge
open Rooted Orbitals
open _root_.YM.CF.Signal.Ovation.Transit
variable (z:SU.Slot){k₀:ℕ}(a:Fin k₀→ Cover)(S:Finset Cover)
variable (s:ℕ) (j:Axis)(C:∀ j, Arena Y H G.history.circuit j 0 false)(χ:displayAlgebra Y H V G.history G.clipped j false (C j) →⋆ₐ[ℂ]ℂ)(p q:Cover)
local notation "R"=>rect S
local notation "F"=>oneAt Y H V G j (C j) χ s
local notation "ϕ" =>sameRead Y H V G j (C j) χ s
local notation "L₊" x:max=> FirstWindows.leg j p x
local notation "R₊" x:max=> reposition (tent Y H) q x

variable {μ ν: Multiset Cover}{x y:Dome (tent Y H)}
local notation "ν₀" p:max=> (star (zeta p))
noncomputable def earlierCoord (v:Cover):= Rooted.Orbitals.spun j 0 (Rooted.Orbitals.carried (tent Y H) p (nodeC v) ordinate)
noncomputable def laterCoord(v:Cover):= Rooted.Orbitals.carried (tent Y H) q (nodeC v) ordinate
lemma witnessesEarlier {x}(h:nodeC x∈ S): earlierCoord Y H j p x∈ reflectedBox j 0 (streetBox (tent Y H) p S):= Finset.mem_image_of_mem _ (Orbitals.carried_in (tent Y H) h ordinate p) -- spin fn?
lemma witnessesLate {x}(h:nodeC x∈ S): laterCoord Y H q x∈ streetBox (tent Y H) q S:= Orbitals.carried_in (tent Y H) h _ q
local notation "Ms" n:max=> momentm Y n s
local notation "S₀" m:max=> Journey.side Y m s
local notation "L" n:max => (Y.voyage n).CapeT s
local notation "Z" n:max k:max=> ((Y.voyage n).X (Y.uv k)).gram s
variable (n:ℕ)
local notation "Lt" k:max=> earlierCoord Y H j p (a k)
local notation "Rt" k:max => laterCoord Y H q (a k)
local notation "pos" x:max=> posted Y H s n (L₊ x)
local notation "neg" x:max=> posted Y H s n (R₊ x)
-- Arm knows actually-purchased Fields. choose one for this cell at each late inspection; nontrivial
-- gauge dependence there too.
noncomputable def snrAt {m:Side}(f : Mark m)(x:Fields m)(v:Cover):Prop:= f (gauge (atGauge m v) x.1,x.2)≠ f x
lemma ne_color {m:Side}(f: Mark m)(x:Fields m)(k:Cover)(ε:ℂ)(h:ε≠1)(p: Communicates m k ε f)(t:f x≠0): snrAt f x k:=by
 obtain ⟨x,v⟩:=x; intro e; change f (gauge _ x,v)=f (x,v) at e; exact h ((smul_left_injective ℂ t) ((p x v).symm.trans (e.trans (one_smul ..).symm)))
noncomputable def armTruth (μ ν:Multiset Cover)(x y:Dome (tent Y H))(n t:ℕ)(ζ:Cover):Prop:= ∃ e:Orbit (Journey.side Y n s), countEnergy Y H s n t (matchWith Y H j ζ ((L₊ x)*(R₊ y))*((L₊ x)*(R₊ y))) e≠0 ∧ denZ (Z n t) Λ.U (L n) e≠0 ∧
    posted Y H s n (L₊ x) (drawn (L n) e)≠0 ∧ posted Y H s n (R₊ y) (drawn (L n) e)≠0 ∧ (∀ k,a k∈ μ→ snrAt (posted Y H s n (L₊ x)) (drawn (L n) e) (Lt k)) ∧ (∀ k,a k∈ ν→snrAt (posted Y H s n (R₊ y)) (drawn (L n) e) (Rt k))
lemma started_now {d:ℕ}{w: Cover}(e: Injective a) (b:Addressable Y H s j w (L₊ x) (R₊ y) n d)(sx:Digest z a S μ x)(sy: Digest z a S ν y)(g:Hosp S (Journey.side Y n s)): armTruth Y H a s j p q μ ν x y n d w:=by
 obtain ⟨u,y1,y2,p0,kz⟩:= b.witnessed
 have ht : Hosp S ((tent Y H).c (Ms n)):= (show (tent Y H).c (Ms n)=S₀ n from terrain Y H (Y.ir n) s).symm ▸ g
 refine ⟨u,y1,y2,p0,kz,fun i h=> ?_, fun i h=>?_⟩
 · let X:= any_anchor (tent Y H) a z sx.raw_origin sx.paid.2 i h e (sx.support _ h) ht
   let v:= posting_real Y H s n _ _ _ (shifted_detects (tent Y H) (Ms n) _ _ x X j p q).1
   exact ne_color (LineCharge.posted Y H s n _) _ (Lt i) (star (star (zeta z))) (fun t=> charge_one z (star_injective (t.trans (star_one _).symm))) v p0 -- simp danger star_star
 let X:= any_anchor (tent Y H) a z sy.raw_origin sy.paid.2 i h e (sy.support _ h) ht
 let v:= posting_real Y H s n _ _ _ (shifted_detects (tent Y H) (Ms n) _ _ y X j p q).2
 exact ne_color _ _ _ _ (charge_one z) v kz
lemma exposure (e:Injective a)(u:ϕ ((L₊ x) * (R₊ y)) ≠0)(hx: Digest z a S μ x)(hy: Digest z a S ν y): ∃ ζ:Cover,∀ᶠ t in atTop, let n:= i (G.rows t); let d:= k (G.columns t); Addressable Y H s j ζ (L₊ x) (R₊ y) n d ∧ armTruth Y H a s j p q μ ν x y n d ζ:=by
 obtain ⟨ζ,t⟩:=true_receptor Y H V G s C j χ _ _ u; refine ⟨ζ,?_⟩
 filter_upwards [t, G.history.growsA.tendsto_atTop.eventually (hosp_later Y H V s S)] with t v q'; let n:= i (G.rows t); exact ⟨v, started_now Y H z a S s j p q n e v hx hy ((show (tent Y H).c (Ms n)=S₀ n from terrain Y H (Y.ir n) s) ▸ (show Hosp S ((tent Y H).c (Ms n)) from q')) ⟩

end LineCharge
end YM.CF.Buffered.Afterglow.Tower.FirstWindows
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.LineCharge.exposure
