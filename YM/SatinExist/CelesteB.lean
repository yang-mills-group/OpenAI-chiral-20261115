import YM.SatinExist.Amy
import YM.SatinExist.Patina
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
set_option maxHeartbeats 280000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia) -- tune
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
namespace Spine
open OS.Semigroup (F)
open OS.Semigroup.Balloon
open Set
variable (P:Spine)(x:P.Spectrum0 3)(Z:Lead.Clan)(k:Street)(s:ℕ)(c r:ℕ→ℕ)
local notation "β" => P.otherSpectrum 3 3 x
local notation "S₀" => P.physicalEnergy 3 (β)
local notation "Vu" => P.ColorHil 3 (β)
local notation "Ψ" => P.voyageF 3 (β)
local notation "yb@" i:max=> P.shard x Z (c (i:ℕ)) (r (i:ℕ))
local notation "ρ" i:max=> P.dew (c (i:ℕ)) (r (i:ℕ))
local notation "Γ" => marks (timeMesh P.par)
local notation "Nt" => notch (timeMesh P.par)
open Aria Casting Six
local notation "Hp"=> P.ColorHil 3 (β)
local notation "B"=> P.par.block
local notation "l₀"=> P.width
local notation "Λ"=> P.par
local notation "K"=> P.calibration
local notation "q@" n:max => P.asked_at n
local notation "ρₛ" t:max=> Selected.gaugeMesh Λ t
local notation "θ" t:max => Selected.gaugePosition Λ t
local notation "ℓ"=> P.calibration.ℓ
-- horizontal/integer growth from ANY mixed roster, keeping every stencil at SAME height. useful later for pure/pure.
variable (j:Axis)
local notation "ϕ"=> P.singleState 3 s x
local notation "ξ"=> P.advocate 3 x j
local notation "ω"=> P.ColorHil j ξ
local notation "e₀"=> P.physicalEnergy j ξ

variable {I:Type}[Fintype I][DecidableEq I]
local notation "Ω"=> P.wealth j ξ
variable {F G:I→ P.Test}{U V:Finset Cover}
-- actual Pc buys ALL cross Wights between these curtains; σ on ANY such basis including origin stations.
lemma open_wall {p:ℤ}(q:ruler P.calibration.B≤p)(p0:0 ≤ p)(L:Punctus (P:=P) false Finset.univ p U)(S:Punctus (P:=P) true Finset.univ p V)(f:P.EarshotAlpha x s U F)(g:P.EarshotAlpha x s V G)(i i':I):
 let u :P.ColorHil j (P.advocate 3 x j) := P.viewF j (P.advocate 3 x j) s (f.past_as j p p0 L i)
 let v := P.viewF j (P.advocate 3 x j) s (g.view_as j p p0 S i'); P.ticketGold x s F G i i'=inner ℂ (P.wealth j (P.advocate 3 x j) u) (P.wealth j (P.advocate 3 x j) v):=by
 intro u v; have he:inner ℂ (Ω u) (Ω v)=inner ℂ u v:=by
    apply P.livingH; intro k; let z:=k.val; let C:=plow (K) z (-1) V
    let Gx:= fun i=> P.shifts z (-1) (G i); have h:=g.plus z (-1)
    have hp:Punctus (P:=P) true Finset.univ 0 C:=by
       intro i t j'; obtain ⟨x,hx,rfl⟩:=plow_stays _ z (-1) _ t; specialize S x hx j'; simp only [Finset.mem_univ,ite_true] at S ⊢; rw [SlabMark.moves]; split_ifs <;> simp only [mul_neg,mul_one,add_zero] <;> omega -- second else no mul
    have hG:P.shifts z 1 (Gx i')=G i':= (P.shifts_sum ..).trans (P.shifts_zero ..) -- definitional 1+(-1) reduces
    let t:= (h.view_as j 0 le_rfl hp i'); let y:= P.viewF j ξ s t; let T:= P.voyageF j ξ
    have hx:(T.crew k).play (Nt s 1) y=v:=(P.registered j ξ s k t 1).trans (P.identical_F _ _ _ _ _ hG)
    constructor
    refine ⟨0,?_⟩
    have hu(a:ω): (((T.crew k).play 0) a)=a := by rw [(T.crew k).play_zero]; rfl
    change P.Eats j ξ k ((T.crew k).play 0 u) ((T.crew k).play 0 v); rw [hu,hu,←hx]
    refine Spine.Eats.chooseF s (f.past_as j p p0 L i) t ?_ (h.view_as z 0 le_rfl hp i') (Nt s 1) ?_
    · rw [show (P.reflectTest j (P.reflectTest j (F i)))=F i from (aureoleTwice ..)] ; exact f.past_as z p p0 L i
    exact ((show ((notch (timeMesh P.par) s 1):ℝ)= ↑(whenly (timeMesh P.par) s 1) from natural_time (timeMesh P.par) s 1).symm ▸ (show 0<(↑(whenly (timeMesh P.par) s 1):ℝ) from when_pos (timeMesh P.par) s 1 (by norm_num))) -- goals
 rw [he]; change ϕ _=inner ℂ (P.viewF j _ _ _) (P.viewF j _ _ _)
 rw [P.released_gram,show P.reflectTest j (P.reflectTest j (F i))=F i from aureoleTwice ..]; exact (P.single_agrees 3 j x s _).symm
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
