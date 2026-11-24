import GaugeFieldConstruction.AcrossPrices
import YM.CF.Reed.Play
-- footprint and multiplicity vary independently; no comparison claim at fixed beta
-- between different m in these lemmas. Keep the actual chiral amplitude. Cf. Reconstruct.Bare,
-- Chiral for the version at the one-tape arguments. No division by a modulus or absolute mass.
set_option autoImplicit false
noncomputable section
set_option synthInstance.maxSize 18000
set_option maxRecDepth 2800
set_option maxHeartbeats 500000
namespace YM.CF
open Function Filter Metric NormedSpace Graph Lattice Laurent Wilson Analysis Pressure Tulip Lat Cube SU Emu Rush Scree Graph RG Scroll Peaks Drapes Cascade Vault Sods Spire Paige Nova Girt Skye Kea Ember MeasureTheory Vale Hom Grace Push.SectorMeasure Next.SectorChange Precision Fock
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator ContDiff BigOperators InnerProductSpace ComplexOrder NNReal ENNReal Classical Kronecker
attribute [local instance] opCStarAlgebra
open Mint Dial Phase Reed
namespace AcrossLands
attribute [local instance] measurePrice
local instance bPrice (I : Type)[Fintype I][DecidableEq I]: BorelSpace (Op I):=⟨rfl⟩
open VolumeRate
variable {K:Teller group}{P:Patch}{R:ChartRatio group} {W:Grace K P R}
   {M m B:Side}{e b:ℝ}{U:Grasp W.U B e}{G:GivenX W U}
   {L:Robes M W G}{p:BudgetPoint}
variable (m U)(p:BudgetPoint)(b:ℝ)
noncomputable def volumeInk
    (A: Pane (mid m B) → FC (Single (mid m B))) (y:Pane (mid m B)):ℂ:=
 inner ℂ (mateK (mid m B)) (acts (A y) (capP (K:=K) U b p y))

variable {m U p b}
local notation "Nm"=> mid m B
local notation "bₚ" A:max=> volumeInk m U p b A
private lemma priorWritten (A: Pane (mid m B) → FC (Single (mid m B))) (h:Envelope A) (g:Envelope (sharpHat m U p b)) :
    Integrable (volumeInk m U p b A) (prior SU.group (More (mid m B))) ∧
     (∫ x:Orbit Nm, volumeInk m U p b A x.1 ∂city Nm) = ∫ y:Pane Nm, volumeInk m U p b A y ∂prior SU.group (More Nm) := by
 have he : Integrable (fun x :Orbit (mid m B) => volumeInk m U p b A x.1) ((prior SU.group (More (mid m B))).prod (depot (mid m B))) := ink_T m U p b A h g
 refine ⟨?_,?_⟩
 · simpa only [integral_const,probReal_univ,one_smul] using he.integral_prod_left
 change (∫ x:Orbit Nm, volumeInk m U p b A x.1 ∂Measure.prod (prior SU.group (More Nm)) (depot Nm))= _; rw [integral_prod _ he]; simp

structure VolumeInk (K:Teller group){P:Patch}{R:ChartRatio group} {W:Grace K P R} {B:Side}{e:ℝ} (U:Grasp W.U B e) (p:BudgetPoint) (b:ℝ) (m:Side) :Prop where
  origin : ∃ T:Scree.Loom (mid m B),
            Envelope (sharpHat m U p b) ∧
            denZ (launch W.L b p (mid m B)) U T=sharpHat m U p b ∧
            partitionZ (launch W.L b p (mid m B)) U T= sharpWeight m U p b ∧
            sharpWeight m U p b≠ 0
  actual : ∀ A:Pane (mid m B)→ FC (Single (mid m B)), Envelope A →
               let ν:= prior SU.group (More (mid m B))
               Integrable (inkMark (m:=m) p b U A) (city (mid m B)) ∧
               Integrable (volumeInk m U p b A) ν ∧ Integrable (volumeInk m U p b 1) ν ∧
               (∫ y, volumeInk m U p b 1 y∂ν) = sharpWeight m U p b ∧
               position m U p b A=(∫ y, volumeInk m U p b A y∂ν)/(∫ y, volumeInk m U p b 1 y∂ν)
  aptitude : ∀ y:Pane (mid m B), flags p.threshold y=∅ →
               let V:= Lat.frame SU.matter (Cube.links y) (anticut (mid m B))
               let D:= spar K.j Vale.babyM y
               Safe V.H ∧ D=portW (Tulip.helix _).symm (projector V.H) ∧
               Sea D (changeM (m:=m) U y Vale.babyM) ∧
               portW (Tulip.helix _).symm V.overlap*D=cutM (Tset _) * D

variable (d:K.top.clip.direct≤1) {c:Side} (g:L.h≤c.val) (a:p.threshold≤L.k) (u: sharpWeight (c*M) U p b≠0)
include L d g a u
local notation "S" => mid (c*M) B
lemma at_volume : VolumeInk K U p b (c*M):=by
 let T:=L.rack c g
 obtain ⟨H,Z,h⟩:=L.soaring p a c g b d
 have he': Envelope (sharpHat (c*M) U p b):=soars L g a d b
 refine ⟨⟨T, he', funext Z,true_top L g a d b,u⟩,?_,?_⟩
 · intro A w μ
   obtain ⟨bc,b1⟩:= priorWritten A w he'
   obtain ⟨h₀,h1⟩:= priorWritten 1 (by exact ⟨measurable_const,1,fun x=> by rw [Pi.one_apply,norm_one]⟩) he'
   have hp: (∫ y:Pane S, volumeInk (c*M) U p b 1 y ∂μ)=sharpWeight (c*M) U p b := by
      change (∫ y:Pane S, volumeInk (c*M) U p b 1 y ∂prior SU.group (More S))=_; rw [←h1]; unfold sharpWeight volumeInk; simp only [Pi.one_apply,act_one]
   refine ⟨ink_T (c*M) U p b A w he',bc,h₀,hp,?_⟩; rw [hp]; apply congrArg (· / sharpWeight (c*M) U p b) b1
 intro y p'
 obtain ⟨v,t⟩:=h y p'; intro V D
 let z:Orbit S:=(y,Classical.arbitrary _)
 let R':=L.berth c g
 let ex:T z=y:=Robes.solar z T R' p a p'
 have hv:Guard y e:= ex ▸ R'.paid z
 have hs: Safe V.H:=Phase.wiel_ok _ U.baseY hv; let f:=love S; change _= _ at v
 refine ⟨hs,v,t,?_⟩; rw [←touchP]; change portW _ V.overlap * spar K.j babyM y=tickA S* spar K.j babyM y; rw [v]; have H:V.overlap * projector V.H=cutM (upperP S)* projector V.H:=by rw [← Reed.plus_joint (Cube.links y) (anticut S)]; exact WilsonFrame.overlap_action _ hs
 change f _ * f _= f _ * f _; rw [←map_mul,←map_mul]; exact congrArg f H
#print axioms at_volume
end AcrossLands
end YM.CF
