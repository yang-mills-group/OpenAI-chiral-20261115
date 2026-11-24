import YM.SU5.Selected.Cor.Coterie
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 650000
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
  (C : ∀ j : Axis, Arena Y H Q.circuit j 0 false)
local notation "Test" => Vacancy.observable (tent Y H) false
local notation "Lab" => Beacon (tent Y H) false
local notation "m" χ:max => marked Y H V Q Qc (3:Axis) false (C 3) χ
open CF.Pannier.Chancel Tapestry Papal SatinVerification
open CF.Pannier.Chancel.Lantern CF.Pannier.Chancel.Lantern.Bulb CF.Pannier.Chancel.Lantern.Bulb.Mezz
open Crest.Airy (Coast Wq)
open Mileage
attribute [local instance] opCStarAlgebra
namespace Fern
open Sermon
namespace Guild
variable {j:Axis}{ξ δ:ℝ}
local notation "P" u:max => plow (K) (3:Axis) u
local notation "mT"=> (3:Axis)
local notation "θ" f:max=> Tower.mirror K mT 0 f
local notation "R"=> ruler (K).B
variable (s:ℕ)
local notation "S" => Tower.Field Y H s mT 0 false
local notation "T"=> whenly (timeMesh Λ) s 1
variable {X₀:Mezz}(χ : CapCharacter Y H V Q Qc 3 false (C 3))(e:X₀.Legate)
local notation "ω" v:max=> escort Y H V Q Qc mT false (C 3) v (C v) χ
local notation "Φ" v:max=> phaseRead Y H V Q Qc v (C v)
local notation "W"=> X₀.Broad
local notation "O"=> Birthplace Y H V Q Qc mT false (C 3) (ω mT) -- escort double = sample same
-- surfaces. Must demand coherent horizon in following consumer. Lanes E and χ. use same mark family $Eχ xreading$. 
variable {F:Window.Family} (Z:Sermon X₀ (tent Y H) F)
local notation "H₀"=> solitude X₀ K e Z
local notation "N" t:max=> embrace X₀ K e Z t
local notation "Λ₁" V:max t:max=> Liturgy X₀ K e Z V t
local notation "U" V:max i:max => stagU X₀ K e Z V i
local notation "D₀" V:max i:max=> stagD X₀ K e Z V i
local notation "d" i:max=> declination X₀ K i
local notation "c₀" t:max=> toyL X₀ K t
local notation "c₁" t:max=> toyR X₀ K t
local notation "p₀" t:max=> X₀.coast_b t
local notation "ℳ" T':max a:max b:max c:max=> Rubric.Marble K F X₀.Zumba (X₀.coast_b true) (X₀.coast_b false) T' a b c
local notation "U₀" v:max f:max g:max=> Alight Y H V Q Qc v (C v) s ξ (grate Λ l s) f g
local notation "Σ"=> X₀.Lot -- maybe conflict binder
local notation "β"=> honey X₀
variable (h:addgap (tent Y H) ≤ X₀.ℓ.val)
variable (hc:printedHere Λ l s X₀.Broad (cabin ξ))
attribute [local instance] opCStarAlgebra
include V Q Qc C e
-- nonvacuum sector payoff. exact phase cones & ζT. preserve as Heated. h+ semi may not prove energy>0, but `$joint` annihil. Nonzero convolution amplitude at actual marked time. give lower and basis independence.
local notation "N'"=> Birthplace Y H V Q Qc 3 false (C 3) (ω mT)
local notation "Φ₀" u:max => bottom Y H V Q Qc 3 false (C 3) u
local notation "arc" u:max=> journey Y H V Q Qc 3 false (C 3) u
local notation "η" u:max => markedActor Y H V Q Qc mT false (C 3) u s
local notation "λ₁" u:max => Selection.vacuum Y H V Q Qc mT false (C 3) u
local notation "φ"=> (Φ mT) (ω mT)
omit V Q Qc C e
-- Type univers helper. prevents β reduction through plank.
private lemma forbid_l (B:Hilbert) (L:B.Op)(p: L.adjoint=L)(τ:B)(t: ‖τ‖=1)(h:L τ=τ)
  (x y:B) (u:inner ℂ τ x=0)(v: inner ℂ τ y=0)(hp:inner ℂ x (L y)≠0) (S':Submodule ℂ B)(s': S'=Submodule.span ℂ {τ}) :
    x∉ S' ∧ y∉S' ∧ L x∉ S' ∧ L y∉ S':=by
 have he(u':B)(hu:inner ℂ τ u'=0)(a:u'∈S') : u'=0:= by
    rw [s',Submodule.mem_span_singleton] at a; obtain ⟨a,rfl⟩:= a; rw [inner_smul_right,inner_self_eq_norm_sq_to_K,t] at hu; simp at hu; rw [hu,zero_smul]
 have ho(i:B):inner ℂ τ (L i)= inner ℂ τ i:= by
    rw [←L.adjoint_inner_left,p,h]

 refine ⟨fun h=>hp (by rw [he x u h, inner_zero_left]), fun h=>hp (by rw [he y v h,map_zero,inner_zero_right]),fun h=>?_ ,fun h=> hp (by rw [he (L y) ((ho y).trans v) h,inner_zero_right])⟩
 apply hp; rw [←L.adjoint_inner_left,p,he (L x) ((ho x).trans u) h,inner_zero_left]
include V Q Qc C e χ
variable {X: Birthplace Y H V Q Qc 3 false (C 3) (escort Y H V Q Qc 3 false (C 3) 3 (C 3) χ)}
variable (wX : LoneVac Y H V Q Qc 3 false (C 3) X)
local notation "ΛT"=> (arc X).track T
namespace Radiant
set_option maxHeartbeats 780000
include wX in
lemma flyAway(s':Finset X₀.Lot)(p:Radiant Y H V Q Qc C s χ e Z s' ξ)(x y:S)(t:inner ℂ (λ₁ X) ((η X) x)=0)(v:inner ℂ (λ₁ X) ((η X) y)=0)(z: honey X₀<‖inner ℂ ((η X) x) ((ΛT) ((η X) y))‖): (η X) x∉ Φ₀ X∧ (η X) y∉ Φ₀ X ∧ (ΛT) ((η X) x)∉ Φ₀ X∧ (ΛT) ((η X) y)∉ Φ₀ X:=by
 -- p used only for Universe; tune later
 let Z' := ((η X) x); let L:= (arc X).track T; let U':=((η X) y);
 have he1 := (arc X).track_adjoint T; have h₂:= (vacuum_norm Y H V Q Qc 3 false (C 3) X); have h₃:= time_floor Y H V Q Qc 3 false (C 3) X T
 have hp₀:inner ℂ Z' (L U')≠ 0:= norm_pos_iff.mp ((Sermon.honey_fee X₀).trans z)
 have e₀:Φ₀ X= Submodule.span ℂ {λ₁ X}:= wX
 have h₀:= forbid_l X.H L he1 _ h₂ h₃ Z' U' t v hp₀ (Φ₀ X) e₀
 exact h₀
#print axioms flyAway
include wX in
/-- Every retinue pair supplied by Radiant.crosses in LoneVac has both legs outside joint-vacuum
subspace, and **remains** outside after one registered true heat step at this scale. Standard
CStar op adjoint etc. Not claiming nonzero strictly positive time energy eigenspaces. -/
lemma brisk (s':Finset X₀.Lot) (p:Radiant Y H V Q Qc C s χ e Z s' ξ) (x y:S)(h:inner ℂ (λ₁ X) ((η X) x)=0)(t:inner ℂ (λ₁ X) ((η X) y)=0)(v:inner ℂ ((η X) x) ((ΛT) ((η X) y))=φ s (N s').val) :
       honey X₀ < ‖inner ℂ ((η X) x) ((ΛT) ((η X) y))‖ ∧ (η X) x∉ Φ₀ X∧ (η X) y∉ Φ₀ X ∧ (ΛT) ((η X) x)∉ Φ₀ X∧ (ΛT) ((η X) y)∉ Φ₀ X:=by
 have hp:=(p.flash 3).trans_eq (congrArg norm v).symm; exact ⟨hp,p.flyAway Y H V Q Qc C s χ e Z wX s' x y h t hp⟩
#print axioms brisk
lemma product_priced (s':Finset X₀.Lot)(p:Radiant Y H V Q Qc C s χ e Z s' ξ) (v:Axis) (n:ℕ) :
    ∃ u w:Vacancy.observable K false,u.val= (Liturgy X₀ K e Z s' true).val ∧ w.val=(Liturgy X₀ K e Z s' false).val ∧ let x:= upward Y H Q false u s n; let y:=upward Y H Q false w s n; cap Y H V (s+n) Q Qc v false (C v) (composed false x y) ≠ cap Y H V (s+n) Q Qc v false (C v) x * cap Y H V (s+n) Q Qc v false (C v) y := by
 let h:Alight Y H V Q Qc v (C v) s ξ _ _ _ _ _:=p.yaw.inspired v; let i:=gentle Y H h.inspires.1.widen; let j:=gentle Y H h.blazes.1.widen; refine ⟨i,j,rfl,rfl,h.rigorousNE Y H V Q Qc v (C v) s n (ω v) (Or.inr ?_) _ _ rfl rfl⟩; intro z; exact norm_pos_iff.mp ((Sermon.honey_fee X₀).trans (p.flash v)) ((congrArg ((Φ v) (ω v) s) p.yaw.valley).trans z)
end Radiant
end Guild
end Fern
end YM.CF.Buffered.Afterglow.Tower.Selection
open YM.CF.Buffered.Afterglow.Tower.Selection.Fern.Guild.Radiant
#print axioms brisk
#print axioms product_priced
