import YM.SU5.SatinWard.Resolution.Dovetail
import YM.SU5.SatinWard.Resolution.LordWeek
import YM.SU5.Six.PressSmear
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 430000
set_option maxRecDepth 8000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase
open MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound
open Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker
open scoped ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy
open Tapestry Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open CF.Velvet CF.Pannier.Chancel
open Spine Pitching.Focus QuadClock Ione Vow Swell
open _root_.Zephyr.Chern
universe uΩ


open Papal CF.Papyrus.Franc.SatinForce CF.Pannier.Chancel Checkers

open CF.Papyrus.Franc.Loaves
-- CP3 package. PUBLIC, no topology/order changes
open Moon
open Horizons FoliageP BareProgram Moonlit Moonlit.SwitchC
open _root_.YM.Regis.Head.Brecht _root_.YM.Regis.Circuit _root_.YM.Regis.Circuit.SpringDay
open SlabMark VelourBoard Papal.SkyTax Cygnet VelourWiggle
open YM.Stationary (Gaia)
open SwitchC.Garland SwitchC.Garland.Terrace SwitchC.Garland.Terrace.Juniper
open Abacus CheckerFlag SlopeCharge Maxwell
open scoped RealInnerProductSpace ContDiff
namespace Fame
open BProof Pressure
namespace Regulator

open _root_.YM.Gleam.Luster.Almanac Grade
open Papal.SkyTax
open _root_.YM.Regis.Head
open _root_.YM.Gleam.Luster.Almanac Grade
open _root_.YM.CF.Py.Rate.LocalLimit.Preparation _root_.YM.CF.Py.Rate.LocalLimit.Preparation.Tabletop Shrine Ione.Clock Moto
variable (P:Spine)
local notation "W★"=>P.calibration
local notation "Ω★"=>P.run.meter
open Preparation.Yoke Spine.Gingham Spine.Gingham.Diary
open ShapeLab ResolutionFrame Shrine 
namespace Internal
open Preparation.Tabletop ShapeLab SignSlot Emu
open CasaF.Signboard LitCurrent LitCurrent.AuroraX
open Worth Pays BProof Aria Casting MacroGrid Selected Reconstruction.Atlas
open SoulField Verdance Mezzo SatinWard.Installment
open OS.Semigroup OS.Semigroup.Marble PSE MarbleFace
open MezzoBill
namespace Dovetail
-- explicit Cost helper.Native book on the ℓ∞ μ-room. `UnitStencil.First-Small` uses physical address & still valid LinkIndependent.
namespace RibbonDoc
local notation "Du" => P.Test
local notation "T"=> P.calibration
local notation "ν"=> P.sidesPerTick
variable {v:ℕ}(q:Cover)(M:P.par.R.L.val%16=1)(z:Soul)(mu:Axis)(B:P.Apron)(S:Set Vantage)
lemma corner (p:B.s=v) : P.issuing v B q=P.chartAll q B.F:=by unfold issuing Apron.full; rw [p,Nat.sub_self]; rfl
variable {b:ℕ}(U V:P.Test)
lemma asking_sum {S:Set Vantage}(x y:P.Test)(p:P.asked_at v x S)(g:P.asked_at v y S) : P.asked_at v (x+y) S:=by
 obtain ⟨k,h,t⟩:=p; obtain ⟨m,z,w⟩:=g; refine ⟨k∪m,?_,by rw [P.pin_union]; exact Set.union_subset t w⟩; exact Subalgebra.add_mem _ (tallerBay _ _ true Finset.subset_union_left h) (tallerBay _ _ true Finset.subset_union_right z) -- need monotone names
lemma asking_zero : P.asked_at v 0 S:=by refine ⟨∅, Subalgebra.zero_mem _,?_⟩; simp [pinFoot]
lemma asking_scale(a:ℂ)(h:P.asked_at v U S): P.asked_at v (a • U) S:=by obtain ⟨x,p,t⟩:=h; exact ⟨x,Subalgebra.smul_mem _ p a,t⟩ -- order
lemma inside (p:B.s=v)(t:P.Aperture B (P.meshPose v q)⊆ S) : P.asked_at v (P.chartAll q B.F) S∧ P.chartAll q B.F∈enclave P.calibration:=by rw [←corner P q B p]; exact ⟨⟨P.plotSet v B q,P.issuing_support ..,(P.inside_now v q B p.le).trans t⟩,P.issuing_color v q B⟩
open Six
lemma spinBill : Six.PureMatter P.calibration (RunH P M z v q mu):= by rw [literals]; exact matterHome mu P.par _ _ _ -- order?
private lemma plusCoeff {u v': PairsC→ℂ}{S:Finset Cover}(p:Coeff true S u)(q:Coeff true S v'): Coeff true S (u+v'):=by
 refine ⟨nofun,Girt.kitE u v' (fun x y=> x+y) (continuous_fst.add continuous_snd) p.env q.env,fun x y h w=>?_⟩; exact congrArg₂ (·+·) (p.locus _ _ h w) (q.locus _ _ h w)
private lemma timesCoeff {a:PairsC→ℂ}{S:Finset Cover}(p:Coeff true S a)(c:ℂ):Coeff true S (c • a) :=by
 refine ⟨nofun,Girt.pole_w _ (c • ·) (Continuous.const_smul continuous_id c) p.env,fun x y h w=>?_⟩; exact congrArg (c • ·) (p.locus _ _ h w)
structure SpiritGlow (J:P.Test): Prop where
 pure : Six.PureGauge P.calibration J
 core (n:Side)(v w:Fields (P.calibration.c n)): v.1=w.1→J.val n v=J.val n w
lemma psyche(t:SpiritGlow P U) (u:SpiritGlow P V): SpiritGlow P (U+V):=by
 obtain ⟨x,f,p,hF⟩:=t.pure; obtain ⟨y,g,w,hg⟩:=u.pure; refine ⟨⟨x∪y,f+g,plusCoeff (p.mono (Finset.subset_union_left)) (w.mono (Finset.subset_union_right)),?_⟩,fun _ _ _ h=> congrArg₂ (·+·) (t.core _ _ _ h) (u.core _ _ _ h)⟩
 change U.val+V.val=_; rw [hF,hg]; funext i z; exact (add_smul ..).symm
lemma physH(t:SpiritGlow P U) (c:ℂ): SpiritGlow P (c • U):=by
 obtain ⟨S,f,p,h⟩:=t.pure; refine ⟨⟨S,c • f,timesCoeff p c,?_⟩,fun i v w h=> congrArg (c • ·) (t.core i v w h)⟩; change c • U.val=_; rw [h]; funext i z; exact smul_smul c (f (onC ((T).c i) z.1,onC ((T).c i) z.2)) (1:FC (Single ((T).c i))) -- Fock.FC
lemma colour_zero : SpiritGlow P 0:= (zero_smul ℂ (1:P.Test)) ▸ (physH P 1 ⟨(Six.pure_unit ..).1,fun _ _ _ _=>rfl⟩ 0) -- maybe inf `[SMulComm...]`
lemma lensColor (q₂:payable P v 2): SpiritGlow P (RunK P q q₂):=by
 let f(t:ℕ):ℝ:=1; let c:=tollηw P f v; let O:= homeTag P rayPost+ ν • q; have he := (aptSingularity (P:=P) 1 1 q₂ O f).2.2; let F:=aptLabel P f 1 1 v O q₂; have h:RunK P q q₂=(↑c:ℂ) • F:=by
    rw [show RunK P q q₂=τEnd P v O pseV q₂ from temple_sweep ..]; apply Subtype.ext; change bumper P v O (keynote _)=_; unfold keynote; rw [mpse]; exact bump_scaled _ _ _ _ _ _ f zero_lt_one
 rw [h]; exact physH P F ⟨he.1,he.2⟩ _
#print axioms asking_sum
#print axioms lensColor
end RibbonDoc
end Dovetail
end Internal
end Regulator
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
