import YM.SatinExist.Nugget
import YM.SatinExist.CelesteB
import YM.SatinExist.CeladonA
import YM.SatinExist.Lack
import YM.SatinExist.Amy
import YM.SatinExist.Patina
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4100
set_option maxHeartbeats 430000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
namespace Spine
open OS.Semigroup (F)
open OS.Semigroup.Balloon
-- introduce double tail filter.P
variable (P:Spine)(x:P.Spectrum0 3) (n s m:ℕ)
open Aria Casting Six
local notation "∇" => ruler P.calibration.B
local notation "ℓ"=> P.calibration.ℓ
open Chalice
structure Calderon (Sx Fx:Finset Cover)(F G: Stone→P.Test):Prop where
    leftUp : EarshotAlpha P x s Sx F
    rightWall : EarshotAlpha P x s Fx G
    gapL : Punctus (P:=P) false Finset.univ (ruler P.calibration.B) Sx
    gapR : Punctus (P:=P) true Finset.univ (ruler P.calibration.B) Fx
    win : Prized (P.ticketGold x s F G)
-- report.Kernel before/after
section
variable (S V:Finset Cover)(F G:Stone→P.Test)(h:P.Calderon x s S V F G)(j:Axis)
lemma loomrP : 0 ≤ ruler P.calibration.B :=by have h:=ruler_gene P.calibration.B; omega
include h
lemma calf (i i':Stone):
 let p:=h.leftUp.past_as j ∇ P.loomrP h.gapL i
 let q:=h.rightWall.view_as j ∇ P.loomrP h.gapR i'
 let ξ:=P.advocate 3 x j
 (P.ticketGold x s F G) i i'=inner ℂ (P.wealth j ξ (P.viewF j ξ s p)) (P.wealth j ξ (P.viewF j ξ s q)):=by exact P.open_wall x s j le_rfl P.loomrP h.gapL h.gapR h.leftUp h.rightWall i i'
omit h
end
local notation "τ" j:max=> (P.otherSpectrum 3 j x)
local notation "T" p:max=> ({nodeC (P.myroof n p)}: Finset Cover)
local notation "Φ" p:max=> (fun i:Stone=>P.WallRuby x i n s p)
structure Older :Prop where
 card : Calderon P x s ({nodeC (P.myroof n false)}) ({nodeC (P.myroof n true)}) (fun i => P.WallRuby x i n s false) (fun i=>P.WallRuby x i n s true)
 long (k:ℝ): ∃ (D D':List (Axis×ℤ)), let A:=P.zoneCost (T false) D; let A':= P.zoneCost (T true) D';
                          P.Calderon x s A A' (P.amplot (fun i=> P.WallRuby x i n s false) (T false) D) (P.amplot (fun i=>P.WallRuby x i n s true) (T true) D') ∧ P.pinFoot s A ⊆ {x|∀i:Axis,x i< -k} ∧ P.pinFoot s A' ⊆ {x|∀ i:Axis,k < x i}
open CF.Velvet
variable (B:ℝ)(A:ℝ)(G: Supplier)(R:P.Register)(u:uniform P R G B A)(d:P.NightCop)
private lemma gapD {p q:ℤ}(e:p≤q)(U:Finset Axis)(S:Finset Cover)(b:Bool)(h:Punctus (P:=P) b U q S): Punctus (P:=P) b U p S:=by intro i t j; specialize h i t j; by_cases h': j∈ U<;>cases b<;>simp only [h',ite_true,ite_false,Bool.false_eq_true] at * <;> omega
private lemma stateGold (s n:ℕ)(h:Prized (P.ticketGold x s (fun i=>P.WallRuby x i n s false) (fun i=>P.WallRuby x i n s true))):Older P x n s:=by
 let F:Stone→P.Test:= fun i=>P.WallRuby x i n s false; let G:Stone→P.Test:=fun i=>P.WallRuby x i n s true
 let h₀:=P.westP n; let h₁:=P.eastP n
 refine ⟨⟨P.rentWall x s n false,P.rentWall x s n true,h₀,h₁,h⟩,fun k=>?_⟩; let v:=Selected.gaugeMesh P.par s
 have ht:0<v:= Selected.gaugeMesh_pos ..
 obtain ⟨y,g⟩:= exists_nat_gt (k/v); let m:ℤ:= y+∇; let f:= P.rentWall x s n false; let f':=P.rentWall x s n true
 have hz:∇≤ m:=by unfold m; omega
 have hx:k < (m:ℝ)*v:= lt_of_lt_of_le ((div_lt_iff₀ ht).mp g) (mul_le_mul_of_nonneg_right (by have he:= P.loomrP; exact_mod_cast (show (y:ℤ) ≤ m from (by unfold m; omega))) ht.le)
 have he' (J:Finset Cover)(b:Bool)(t:Punctus (P:=P) b Finset.univ ∇ J): Punctus (P:=P) b ∅ m J:=by
    have h:=P.loomrP; intro p H i; specialize t p H i; cases b <;> simp only [Finset.mem_univ,Finset.notMem_empty, ite_false,ite_true,Bool.false_eq_true] at * <;> omega
 obtain ⟨D,D',s',t',u⟩:= P.blazeC x s m (P.loomrP.trans hz) f f' (he' _ false h₀) (he' _ true h₁) h
 exact ⟨D,D',⟨P.amplop x s _ D F f, P.amplop x s _ D' G f',P.gapD hz _ _ _ s',P.gapD hz _ _ _ t',u⟩,P.neg_funds s k _ _ hx s',P.length_funds s k _ _ hx t'⟩
include u d
lemma wholly_acquired : ∀ᶠ n:ℕ in atTop,∀ᶠ s:ℕ in atTop,∀ x:P.Spectrum0 3, P.Older x n s:=by
 filter_upwards [P.roster_bank B A G R u d] with r t
 filter_upwards [t] with s w x; exact P.stateGold x s r (w x)
omit u d
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
