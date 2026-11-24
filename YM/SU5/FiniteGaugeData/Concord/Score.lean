import YM.SU5.FiniteGaugeData.Concord.Exhibit
/-!
# On the actual course

Cast control here and common scores. Don't embed a word over a step geometrically; `observe`
uses the observing resolution's own gauge/chiral grid (`momentm` there). `sharply`->`Journey.sharp`
for the actual finite regulator. Track all estimates on it.
-/
set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 22000
noncomputable section
namespace YM.CF.Buffered.Concord
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker
  Topology ComplexOrder Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent
  Next.Free Bloch Drapes Spire Lifted Skye Precision Tree Push.SectorMeasure Next.SectorChange Fock
open Afterglow Afterglow.Common Afterglow.Sound Afterglow.Satin Afterglow.Journey
attribute [local instance] opCStarAlgebra
open Py Py.Rate LocalLimit Preparation Journey Vale
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1 ≤ Λ.x)

namespace Copies
variable {x y:Side}
def transport (h:x=y) : Mark x ≃ₐ[ℂ] Mark y := by subst y; exact AlgEquiv.refl

lemma transports (h:x=y)(f:Mark x) : transport h f = (h ▸ f) := by subst x; rfl
lemma certified (h:x=y) {F:Mark x}{b:Bool}{S:Finset Cover} : AtSupport b (region S y) (transport h F) ↔ AtSupport b (region S x) F := by subst x; rfl
lemma certificate (h:x=y) {F:Mark y}{b:Bool}{S:Finset Cover} : AtSupport b (region S x) ((transport h).symm F) ↔ AtSupport b (region S y) F := by subst x; rfl
lemma constantCost (h:x=y) {v:Mark x}{c:ℝ} : (∀ i, ‖transport h v i‖ ≤ c) ↔ ∀ i,‖v i‖≤c := by subst y; rfl
lemma constantPost (h:x=y) {v:Mark x} {S:Finset Cover} (z:PairsC) : ‖transport h v (replant S y z)‖= ‖v (replant S x z)‖:=by subst y; rfl
lemma constantDist (h:x=y){v:Mark x} {S:Finset Cover} (z w:PairsC) : dist (transport h v (replant S y z)) (transport h v (replant S y w)) = dist (v (replant S x z)) (v (replant S x w)) := by subst y; rfl
lemma knot (h:x=y) (f:PairsC→ℂ)(u:Chorus) : transport h (Satin.knot x u f)= Satin.knot y u f:=by subst y; rfl
end Copies

variable (i s k:ℕ)

local notation "K"=> tent Y H
local notation "Λc"=> side Y i s
local notation "Λi"=> momentm Y i s

def observe : Buffered.Family (tent Y H) → Mark (side Y i s) := fun f=> Journey.send Y H i s (f (momentm Y i s))

lemma observe_formula (f : Family (tent Y H)): observe Y H i s f= Copies.transport (terrain Y H (Y.ir i) s) (f Λi):=(Copies.transports ..).symm

-- point-label coe gets lengthy, avoid `AlgHom` unless needed later
lemma observe_add (f g : Family (tent Y H)): observe Y H i s (f+g)=observe Y H i s f+observe Y H i s g:=by simp_rw [observe_formula,Pi.add_apply,map_add]
lemma observe_mul (f g : Family (tent Y H)): observe Y H i s (f*g)=observe Y H i s f * observe Y H i s g:=by simp_rw [observe_formula,Pi.mul_apply,map_mul]
lemma observe_scale (c:ℂ)(f : Family (tent Y H)): observe Y H i s (c • f)=c • observe Y H i s f:=by simp_rw [observe_formula,Pi.smul_apply,map_smul]
lemma observe_one : observe Y H i s 1=1 := by rw [observe_formula,Pi.one_apply,map_one]
lemma observe_nota (F:PairsC→ℂ)(u:Chorus) : observe Y H i s (note K F u)= Satin.knot (side Y i s) u F:= by rw [observe_formula,kiosk]; exact Copies.knot ..
lemma observe_support {F:Family (tent Y H)}{S: Finset Cover}{b:Bool} (p:InTest K true S b F): AtSupport b (region S (side Y i s)) (observe Y H i s F):=by rw [observe_formula, Copies.certified]; exact p.support _
lemma observe_ext {F G:Family (tent Y H)}{S: Finset Cover}(p:InTest K true S false F)(t:InTest K true S false G)(h:Hosp S (side Y i s)) (v:observe Y H i s F= observe Y H i s G):F=G:=by
  simp_rw [observe_formula] at v; exact native_ext S K ((terrain Y H (Y.ir i) s).symm ▸ h) p t ((Copies.transport _).injective v)

variable (S:Finset Cover)

def nativeHere : Palette S→ₗ[ℂ] Mark (side Y i s) :=
  (Copies.transport (terrain Y H (Y.ir i) s)).toLinearMap.comp (native S K Λi)
lemma nativeHere_eq (f: Palette S): nativeHere Y H i s S f= observe Y H i s (pigment S K f):=(observe_formula ..).symm
lemma native_cost (f:Palette S)(x:Fields (side Y i s)) : ‖nativeHere Y H i s S f x‖ ≤ count S * ‖f‖:=
  (Copies.constantCost (x:=(tent Y H).c (momentm Y i s)) (y:=side Y i s) (terrain Y H (Y.ir i) s) (v:=native S K Λi f)).mpr (native_bound S K f Λi) _
lemma cost_palette (f:Palette S){v:ℝ}(h:Hosp S (side Y i s))(p:∀ x, ‖nativeHere Y H i s S f x‖ ≤ v): ‖f‖ ≤ v:=
  palette_norm S K ((terrain Y H (Y.ir i) s).symm ▸ h) ((Copies.constantCost (terrain Y H (Y.ir i) s)).mp p)
lemma nativeHere_support (f:Palette S): AtSupport false (region S (side Y i s)) (nativeHere Y H i s S f):= by rw [nativeHere_eq]; exact observe_support Y H i s (pigment_test S K f)

-- the finite signed formula for these Palettes at observing resolution; see Journey.transformed/etc.
def sharply : Palette S→ ℂ:=fun f=> Journey.compass Y i k s (nativeHere Y H i s S f)
lemma sharply_s (f:Palette S): sharply Y H i s k S f= Journey.sharp Y H s i k (pigment S K f) := by unfold sharply; rw [nativeHere_eq]; rfl

variable {i s k} (p : (Y.voyage i).kick ≤ k)(v : s≤ Y.uv k)
local notation "R" => (Y.voyage i).CapeT s
local notation "X" => ((Y.voyage i).X (Y.uv k)).gram s

include p v
lemma voice_add {f g:Mark (side Y i s)} (a:Envelope f)(b:Envelope g): Journey.compass Y i k s (f+g)= Journey.compass Y i k s f+ Journey.compass Y i k s g := by
  unfold Journey.compass; rw [mark_add ((Y.voyage i).ownership s).paid.bill a b (Marks.can_read _ _ X R (Y.each_level i k s p v)), add_div]
omit p v in
lemma voice_smul (c:ℂ)(f:Mark (side Y i s)): Journey.compass Y i k s (c • f)= c*Journey.compass Y i k s f:=by unfold Journey.compass; rw [mark_smul,mul_div_assoc]
lemma voice_one : Journey.compass Y i k s 1=1:=by unfold Journey.compass; rw [markvac]; exact div_self (Y.each_level i k s p v).valid
lemma sharply_add (f g: Palette S): sharply Y H i s k S (f+g)= sharply Y H i s k S f + sharply Y H i s k S g := by unfold sharply; rw [map_add, voice_add Y p v (nativeHere_support ..).env (nativeHere_support ..).env]
omit p v
lemma sharply_scale (c:ℂ)(f:Palette S): sharply Y H i s k S (c•f)=c*sharply Y H i s k S f := by unfold sharply; rw [map_smul,voice_smul]

variable (s)
include H
lemma local_cost : ∃ D:ℝ,0 ≤ D ∧ ∀ᶠ k in atTop, ∀ i:ℕ,(Y.voyage i).kick ≤ k → s≤ Y.uv k ∧ ∀ f:Palette S, ‖sharply Y H i s k S f‖ ≤ D*‖f‖:=by
  obtain ⟨D,d,u⟩:= library Y H S s; refine ⟨D*count S,mul_nonneg d.le (count_nonneg _),?_⟩
  filter_upwards [u, Y.uv_grows.tendsto_atTop.eventually_ge_atTop s] with k t l i p
  refine ⟨l, fun f=>?_⟩; rw [mul_assoc]; exact t i p _ (nativeHere_support ..) (count S*‖f‖) (fun _=> native_cost ..)
end YM.CF.Buffered.Concord
#print axioms YM.CF.Buffered.Concord.sharply_s
#print axioms YM.CF.Buffered.Concord.local_cost
