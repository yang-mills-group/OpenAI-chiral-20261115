import YM.SU5.Velvet.Acclaim
import YM.SU5.Lamour.Meringue
import YM.SU5.Gleam.Receipts
import YM.SU5.Velvet.Hemline
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry

open TopologicalSpace
open Tapestry.Exhibition Tapestry.Altitude Set

open CF.Pannier.Chancel FixedProbe
open Velvet
theorem satin_comes_Wick (d₀:ℕ)(C₀ W₀:ℝ)(Q:0≤C₀)(hl:0<W₀)(β:ℕ→ℕ→ℝ→ℝ→ℝ)(iβ:∀ a b x y,0<x→0<y→0<β a b x y)(X:Supplier)(ε η v:ℝ)(p:0<η)(w:0<v)(o:Cover)(j : Axis):
    ∃ P : Spine, P.par.nominated (VolumeCape.Dream.Nimbus P.width) ∧ ε<P.par.x ∧ P.par.d ≤ η ∧
      ∃ R : P.Register, SeasonCert P.run P.large R.exhibition ∧
      ∃ (q d w : ℕ) (Z C : ℝ), Papal.Cornet P.run P.large q d w C Z ∧ Geometry P.par ∧ decorate X P.par P.width Z ≤ P.par.h ∧
      (∀ (ε:ℝ), ε>0 → ∀ᶠ s in atTop,∀ i k:ℕ,(P.run.voyage i).kick≤k → s ≤ P.run.uv k → VLine P.run s i k ε) ∧
      (∀ κ:ℝ, ∀ ε:ℝ, ε>0 → ∀ᶠ s in atTop,∀ i k:ℕ,s ≤ P.run.uv k →
                        Papal.landedCost P.run s i k κ ε) ∧
      (∃ a,Velvet.Procurement P.par.K.j a P.par.d) ∧
      (∃ u:ℝ, 0<u ∧ u≤1 ∧ Papal.SizeCloud P.par.K.j (v/8) u ∧ flowCost u≤P.par.h) ∧
      (∀ᶠ s in atTop,∀ᶠ i in atTop, ∀ r:ℕ,(P.run.voyage i).kick≤r → s≤ P.run.uv r → Papal.BrokenMark P.run s i r 1 ≤ Real.exp (v*sites (Papal.count P.run s i))) ∧
      (∃ n k y e θ ψ z, Lamour.Bridge.Optic P.par.K.j n k d₀ y e θ ψ C₀ W₀ ∧
        Lamour.Bridge.Closen P.par.K.j z e ∧ 0<z ∧ z≤1 ∧ Papal.SizeCloud P.par.K.j (β n k y e/8) z ∧
        Papal.Hfuel z y≤ P.par.h ∧ ∀ (r:ℕ)(ξ:ℝ), 0<ξ → Papal.Meringue.{0} P.run k r d₀ e ξ C₀ W₀ (β n k y e)) ∧
      ∀ z : SU.Slot, ∀ᶠ s : ℕ in atTop, let W := Sen o (payout d q w); let b:=booty o d q;
                                     ∃ (F : FixedProbe.KernelTest P.run P.large) (f:P.Test) (N:ℕ), f.val=F.val ∧
      FixedProbe.AnchorGap (Λ:=P.par) s b W ∧ Carries P.run P.large P.law s P.projection F W N ∧
      f.val∈Filigree P.calibration (Window.family z) b W ∧ (∃ i y, nodeC y∈ W ∧ (∀ t, y≠ b t) ∧
        0<dist (addressG P.par s (nodeC y)) (addressG P.par s (nodeC (b i)))) ∧
      pinhole P.Test s f∈ well P.par P.calibration P.width false (cabin N) Set.univ ∧
      1/4≤ ‖P.E s f.val‖ ∧
      ∃ u:P.Spectrum0 j, P.Sanctuary R j u ∧ 1/8<‖P.spirits R j u (pinhole P.Test s f)‖ ∧ ∀ k:Axis, P.Retained k s (P.otherSpectrum j k u) b W z f:= by
 obtain ⟨n,k,y,f,r,Lm,Hm⟩:= Lamour.Bridge.choose_optic (j:=4) (by decide) d₀ Q hl
 let x:=β n k y f; have hx:0<x:=iβ n k y f Hm.genuine Hm.zephyr
 obtain ⟨z,cz,z1,Kz,X'⟩:= Papal.choose_floor 4 (by decide) hx Hm.zephyr
 let fuel:Supplier:= fun K p V H B d S W M J l Z=> max (X K p V H B d S W M J l Z) (Papal.Hfuel z y)
 obtain ⟨P,t,E,pL,Y,A,q',d',w',Z,C',hQ,kP,vZ,t',R',a',u',vp,T⟩:= satin_bench_variation fuel ε η v p w o j
 have hy:Lamour.Bridge.Optic P.par.K.j n k d₀ y f r Lm C₀ W₀:=P.par.kJ.symm ▸ Hm -- tune Lean rewrite
 have hvY:Papal.Hfuel z y ≤ P.par.h:=(le_max_right ..).trans vZ
 obtain ⟨a,u⟩:= a'
 have hx' (ξ:ℝ)(p:0<ξ)(d:ℕ):= Papal.quartermaster.{0} P.run hy cz z1 u (P.par.kJ.symm ▸ Kz) (P.par.kJ.symm ▸ X') hx kP hvY p Q hl d
 exact ⟨P,t,E,pL,Y,A,q',d',w',Z,C',hQ,kP,(le_max_left ..).trans vZ,t',R',⟨a,u⟩,u',vp,⟨n,k,y,f,r,Lm,z,hy,(by rw [P.par.kJ]; exact Kz),cz,z1,(by rw [P.par.kJ]; exact X'),hvY, fun i j e=> hx' j e i⟩,T⟩ -- binder needs type annotation hx' partial implicit
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#check @YM.CF.Buffered.Afterglow.Tower.VacuumSelection.satin_comes_Wick
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.satin_comes_Wick
