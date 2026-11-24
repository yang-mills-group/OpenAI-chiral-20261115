import VerifiedSatinSelectedSectors
import YM.SU5.Reconstruction.BareRead
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6500
set_option maxHeartbeats 440000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory
  RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
  InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification
open Selected PhaseChoice PhaseChoice.SameCharacter PhaseChoice.Theory
open Tapestry Tapestry.Altitude Tapestry.Exhibition

/-!
# Explicit overlap/oscillator dictionary for the actual selected history cutoffs.
Adapt `Emu.touchS/artQ` (there with Psalm etc on OTHER periods; not assuming those prices).
Keep one choice of PS and phase for all the physical reads. Pair-linked/pivot
coupling semantics here at **same** gauge.
-/
open Dial Thera Scree Paige Reed
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l)) (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable (i k : ℕ) (A : Pane (Journey.side Y i (Y.uv k)))
local notation "m₀" => Y.uv k
local notation "N₀" => Journey.side Y i (Y.uv k)
local notation "R₀" => Y.voyage i
local notation "ρ" => (R₀).CapeT m₀
local notation "G" => ((R₀).X m₀).gram m₀
local notation "p" => (Y.meter.a m₀).threshold
local notation "w₀" => changeM («m»:= Vale.mesh (Y.ir i) Λ.R.L m₀) Λ.U A babyM
local notation "o" => Dial.mateK N₀
local notation "PS" => spar Λ.K.j babyM A
noncomputable def bareMatrix (A : Pane (Journey.side Y i (Y.uv k))) :=
  love N₀ (Lat.frame SU.matter (Cube.links A) (anticut N₀)).overlap
local notation "M" => bareMatrix Y i k A

local notation "s" => Tset (Journey.side Y i m₀)

lemma conventional (t : flags p A=∅) (u:UNI (Single (Journey.side Y i m₀))) (S:Finset (Single (Journey.side Y i m₀)))
    (z : spar Λ.K.j babyM A=twist u (cutM S)) :
    (M*PS= cutM (Tset (Journey.side Y i m₀))*PS) ∧
    Reed.chemical (M*u.val) (Tset (Journey.side Y i m₀)) S=Reed.chemical u.val (Tset (Journey.side Y i m₀)) S ∧
    ∃ c:ℂ, ‖c‖=1 ∧ ∀ x:FC (Single (Journey.side Y i m₀)), Reed.Plain x →
      c*Reed.spell (Reed.syms (Tset (Journey.side Y i m₀))) u.val (Tset (Journey.side Y i m₀)) S x =
        inner ℂ o (acts ((Reed.think s).eval x) w₀) := by
  let L:= love N₀; let I:= Single (Journey.side Y i m₀); let A₀:= Lat.frame SU.matter (Cube.links A) (anticut N₀)
  let K' : Skye.Orbit N₀:= ⟨A,Classical.arbitrary _⟩
  have hm:= (top_system Y i k K' t).2; -- ∧ PS and Safe
  have hv : PS=L (projector A₀.H) := hm.2.1
  have he : cutM s=L (cutM (Lat.upperP N₀)):= (Spire.touchP _).symm
  have ht : M * PS= cutM s * PS := by
    rw [he,hv]; exact ((map_mul L _ _).symm.trans ((congrArg L hm.2.2.2.2.1).trans (map_mul L _ _))) -- index ? hm Safe ∧ PS ∧ Sea ∧ ...
  have hf: M * u.val * cutM S= cutM s * u.val * cutM S:= by
    have t: PS*u.val=u.val*cutM S:= by rw [z]; exact twist_product ..
    rw [mul_assoc,mul_assoc,←t,←mul_assoc,ht,mul_assoc]
  refine ⟨ht, ?_, ?_⟩
  · have ha (x y : Single N₀) (a : x∈s) (b : y∈ S): (M*u.val) x y=u.val x y := by
      have h:= Matrix.ext_iff.mpr hf x y
      simp only [cutM,Matrix.mul_diagonal,b,if_true,mul_one, Matrix.diagonal_mul,a,one_mul] at h; exact h
    unfold Reed.chemical; congr 1; apply sum_congr rfl; intro i h; congr 1; unfold Reed.tote
    apply sum_congr rfl; intro j t; rw [ha i j h t]
  let y:= w₀; let T:= Fock.wedge u.val S; let c:= inner ℂ T y
  let v:= o; let α:= basisKet s; let d:= inner ℂ α v
  have hy : Sea PS y:=hm.2.2.1
  have hz : Sea (cutM s) v:= Spire.touchP N₀ ▸ Dial.tickB N₀
  have hd : v=d • α:=by nth_rw 1 [← hz.1]; rw [cutLine, cut_oneAct]; unfold d α; rw [basis_inner]
  have hE : y=c • T:=by nth_rw 1 [← hy.1]; rw [z]; exact act_twistLine ..
  have l : ‖c‖=1:= by have t:=hy.2; rw [hE,norm_smul,show ‖T‖=1 from wedge_norm ..,mul_one] at t; exact t
  have h : ‖d‖=1:= by have t:=hz.2; rw [hd,norm_smul,show ‖α‖=1 from (by simp [α,basisKet]),mul_one] at t; exact t
  refine ⟨star d*c,by rw [norm_mul,norm_star,h,l,one_mul],fun x hx=>?_⟩
  rw [Reed.moment _ _ _ _ hx]; change _=inner ℂ v (acts _ y); rw [hd,hE,map_smul,inner_smul_right,inner_smul_left]; change _=c*(star d* _); ring

lemma paid_basis (t : flags p A=∅) :
    ∃ (u : UNI (Single (Journey.side Y i m₀))) (S : Finset (Single (Journey.side Y i m₀))),
      spar Λ.K.j babyM A=twist u (cutM S) := by
  let v : Skye.Orbit N₀:= ⟨A,Classical.arbitrary _⟩
  have hm:= (top_system Y i k v t).2
  apply spot_projection
  rw [show PS=(love _) (projector (Lat.frame SU.matter (Cube.links A) (anticut N₀)).H) from hm.2.1]
  exact (Safe.projection hm.1).map (love N₀) -- lemma

lemma top_insertion (t : (Y.voyage i).kick≤ k) (S : BillOfWork) (x : Cloud (Dome (tent Y H)))
    (u : x∈ fountainHeads K S m₀) :
    ∃ a:FC (Single (Journey.side Y i m₀)), Reed.Absorb (modesIn _ (Satin.region (frameBudget S Λ l m₀) N₀)) a ∧
      observableTop Y H i k x A=(Reed.think s).eval a ∧ Reed.Plain a := by
  obtain ⟨a,h,e⟩:= Reed.Fine.writer ((bare_support Y H i k x S t u).allV (A,A)) -- args
  exact ⟨a,h,e, Reed.Absorb.packs h (Finset.subset_univ _)⟩

/-- Bare-symbol terminology in this dictionary. Not a conclusion about the chirality of limits. -/
lemma empty_symbol :
    let f := Lat.frame SU.matter (Cube.links (1:Pane N₀)) (anticut N₀)
    projector f.H=fourImage SU.Slot (Journey.side Y i (Y.uv k)) (fun k=>projector (latticeAtoms _ k).H) ∧
    f.H=fourImage SU.Slot N₀ (fun k=>(latticeAtoms _ k).H) ∧
    (∀ x : BZ.Mom, BZ.Zone x → x≠0 → let W:=BZ.atom x; let P:=projector W.H; let T:= W.overlap*P;
      ∃ X: Op SpinIdx, T*X=W.plus ∧ X*T=P) ∧
    (projector (BZ.atom 0).H=1-(BZ.atom 0).plus ∧ (BZ.atom 0).overlap * projector (BZ.atom 0).H=0) ∧
    ∀ t : BZ.Mom, HasDerivAt (fun v:ℝ=> let W:= BZ.atom (v • t); W.overlap * projector W.H*(1-BZ.gPos))
      ((1/2:ℝ) • (BZ.symbolD t*(1-BZ.gPos))) 0 := by
  intro f
  have h:f=emptyFrame SU.matter N₀:= by unfold f emptyFrame; rw [show links (1:Pane N₀)=1 from ?_]; funext x; simp [Cube.links]
  rw [h]; exact ⟨project_four SU.matter N₀,H_four SU.matter N₀,fun t v q=>⟨_,BZ.inverseMode t v q⟩,BZ.origin,BZ.linear_kinetic⟩
end YM.CF.Buffered.Afterglow.Tower.Reconstruction
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.conventional
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.empty_symbol
