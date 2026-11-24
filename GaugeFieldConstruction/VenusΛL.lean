import GaugeFieldConstruction.AeneidΛL
import Mathlib.GroupTheory.Perm.Fin
/-!
 # Unit consistency. Analytic deletion in all words; reconstruction gives unital identity explicitly.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 15000
set_option maxHeartbeats 300000
noncomputable section
-- full ζ deletion slot k, axial inert
namespace YM.NSF.Boundary
open YM.Boundary Mink Function Set Filter MeasureTheory Complex Finset
open scoped Topology BigOperators ContDiff InnerProductSpace
open NSF.Work.C20
variable {n:ℕ}
abbrev remΛ {X:Sort*}(k:Fin (n+1))(f:Fin (n+1)→X): Fin n→X := f∘ k.succAbove
def waneΛL (k:Fin (n+1)): Full (n+1)→L[ℂ] Full n:=LinearMap.toContinuousLinearMap {
 toFun x:= WithLp.toLp 2 fun i=> x (k.succAbove i.1,i.2)
 map_add' f g:=by ext i; rfl
 map_smul' s f:=by ext i; rfl }
def pithΛL (k:Fin (n+1))(x:Points (n+1)):Points n:= points (remΛ k x.ofLp)
lemma pithPatchΛL (k:Fin (n+1))(x: Points (n+1))(p:x∈ ordered (n+1)): pithΛL k x ∈ ordered n:= by
 change StrictMono (remΛ k (readings x)); exact StrictMono.comp p k.strictMono_succAbove
lemma pithGlowΛL (k:Fin (n+1))(x: Points (n+1)): waneΛL k (wickSlice (n+1) x)= wickSlice n (pithΛL k x):=rfl
lemma PlushFieldsΛL {u:Points n}(e:u∈ fields n) (k j:Fin n)(p:k<j):u j-u k∈inside:=by
 let D(ℓ:ℕ):= ∀ i:Fin n, k < i → i.val ≤ ℓ → u i-u k∈inside
 suffices H:∀ ℓ:ℕ,D ℓ from H j.val j p le_rfl
 intro ℓ; induction ℓ with
 | zero=>intro i hi p; change i.val≤0 at p; omega
 | succ l ih =>
    intro i hi p; by_cases x:k.val+1=i.val
    · exact mem_iInter.mp (mem_iInter.mp (mem_iInter.mp e k) i) x
    let j':Fin n:=⟨i.val-1,by omega⟩; have hx:j'.val=i.val-1:=rfl
    have hy:u j'-u k∈inside:= ih j' (show k.val< j'.val by omega) (by omega)
    have hu:u i-u j'∈inside:= mem_iInter.mp (mem_iInter.mp (mem_iInter.mp e j') i) (show _+1=_ by omega)
    rw [show u i-u k=(u i-u j')+(u j'-u k) from (sub_add_sub_cancel ..).symm]
    change ‖_‖ < _; rw [rest_add,clock_add]; exact (norm_add_le _ _).trans_lt (add_lt_add hu hy)
lemma PithFeelΛL (k:Fin (n+1)) : MapsTo (waneΛL k) (tube (n+1)) (tube n):= by
 intro z u; change Boundary.shade _ ∈ fields n; simp only [fields,mem_iInter]; intro i j v
 let v := Boundary.shade z; change (v (k.succAbove j)) - (v (k.succAbove i))∈inside; exact PlushFieldsΛL (show v∈ fields (n+1) from u) (k.succAbove i) (k.succAbove j) (k.strictMono_succAbove (show i<j by omega))
#print axioms PithFeelΛL
end YM.NSF.Boundary
namespace YM.GaugeFieldConstruction.Ember.Volumetric
open Calibration Raw Cauchy Phys Apit Stage Fathom Function Set Filter Module Empire Hulse Salam Palace
open Floor Carat Dawn Sailing Angles Points Bulb Analysis MeasureTheory Complex Finset
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexConjugate ContDiff Kronecker InnerProductSpace
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
variable {S:City}{P:Axis→Across}{L:Sheds S P}{C:Supplies L}{u:ℕ→Carat}
namespace FirstPackMars
open Loft Cell NSF.Boundary NSF.Work.C20
attribute [local instance] floatA floatY
attribute [local instance 30000] topx topg
variable {A Z:CloudsL}(H:SurfCheckL A)(G:SurfCheckL Z)
variable {Y:NSF.Boundary.Surface (SurfRimL A)}{D:∀ i, Blanket i}{F:NSF.Boundary.Waves (SurfRimL A)}{N:Y.Aurora D}
variable (hz:F.Region (SurfRimL Z))(hu:F.NonTangentialFree Y)(hv:N.FullBody F)
variable {n:ℕ}(V:Fin (n+1)→ΧiMars)
local notation "M_ν" => H.TinCanL
local notation "τΨ"=> Empire.one four
abbrev ΥoneΛL: (SurfRimL A).Union:= M_ν τΨ
variable (k:Fin (n+1))(e:V k= Empire.one four)
include G e
lemma CoilΛL {x:Points (n+1)}(h:x∈conf (n+1)):Z (n+1) x V= Z n (pithΛL k x) (remΛ k V):=by
 let p:= k.cycleRange.symm; let y:=NSF.Points.rearrange p x
 rw[← G.symmetry p V x h,show V ∘ p=Fin.cons (τΨ) (remΛ k V) from ?_]
 · change Z _ y _= _; rw [show Z _ y _ = Z _ (Points.tail y) (remΛ k V) from G.coin _ _ (NSF.Points.rearrange_in p h)]; rw [show Points.tail y=pithΛL k x from ?_]; apply PiLp.ext; intro i; change x (p i.succ)= x _ ; rw [show p i.succ=k.succAbove i from k.cycleRange_symm_succ i] -- maybe qualified
 ext1 j; refine Fin.cases ?_ (fun i=>?_) j
 · simp [p,e]
 simp [p,remΛ]
include H hz hv
lemma ΡCoinΛL (z:Full (n+1))(q:z∈tube (n+1)): N.emit (M_ν ∘ V) z= N.emit (M_ν ∘ remΛ k V) (waneΛL k z):= by
 apply sub_eq_zero.mp
 let u:Full (n+1)→ℂ:= ΑΛL H (N:=N) V; let s:Full n→ℂ:= ΑΛL H (N:=N) (remΛ k V)
 apply ΛLaneL (X:=fun i=> u i - s (waneΛL k i)) _ _ q
 · intro i ht; exact ((hv.hol (n+1) _) i ht).sub (((hv.hol n _) (waneΛL k i) (PithFeelΛL k ht)).comp ((waneΛL k).analyticAt _)) -- inference
 intro i ht; dsimp only [u,s]; rw [ΥLiveΛL H G hz hv V ht, pithGlowΛL, ΥLiveΛL H G hz hv _ (pithPatchΛL k i ht), CoilΛL G V k e (ΜConfΛL ht),sub_self]
#print axioms ΡCoinΛL
end FirstPackMars
end YM.GaugeFieldConstruction.Ember.Volumetric
end
