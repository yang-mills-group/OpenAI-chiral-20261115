import SatinThinStationary

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
namespace Spine
open Lamour.Bridge.Celeste
open Lamour.Bridge.Celeste.Morn
open Py.Rate.LocalLimit.Papal (Weaver household)
open TopologicalSpace Tapestry.Exhibition
variable (P:Spine)(R : P.Register)(j:Axis)
local notation "φ"=> P.groundZero j
local notation "μ"=> P.pillars j
local notation "W"=> P.calibration
local notation "Q"=> P.par.block
local notation "ℓ"=> P.calibration.ℓ
open Papal Regis.Head Gleam
/-! # Price of ensemble-of-trips. Exactly composed on printed test level before estimation. -/
open Clock Clock.Hookah Clock.Hookah.Blaze
open Preparation.Yoke Yoke.Travel Regis.Head.Garland
open QuadClock Again Pressure
variable {s t f r v i k:ℕ}
local notation "Λ"=> P.par
local notation "L"=> P.par.R.L
local notation "H"=>P.large
local notation "N" s:max i:max => Journey.side P.run i s
/-! # Buy height and travel together. Keep both actual calibration and rank resolution schedule. -/
open CF.Pannier.Chancel CF.Py.Rate.LocalLimit.Preparation.Yoke
open Worth Pays CF.BProof
open Real (log)
open Aria Casting MacroGrid
local notation "z'" => witnessZ
open Regis.Head.Etch Push.Local AnalyticBridge.VerifiedReset
local notation "Δ" t:max x:max => P.tariffQ z' t x
variable (x : P.Spectrum0 3)
local notation "ξ"=> P.advocate 3 x 3
local notation "M"=> P.ColorHil 3 (ξ)
local notation "G"=> P.ManyF 3 (ξ)
local notation "E" r:max=> P.singleState 3 r x
local notation "Ω"=> P.colorZero 3 ξ
/-! # CP11: same footprint congruence at all calendar poses, every axis. -/
noncomputable def Apron.pivot (P:Spine)(A:P.Apron) (l:List Axis):P.Apron:= match l with
 | []=>A
 | z::t=>(A.pivot P t).kiss P z
@[simp] lemma Apron.pivot_nil(P:Spine)(A:P.Apron) : A.pivot P []=A:=rfl
lemma Apron.pivot_cons(P:Spine)(A:P.Apron)(v:Axis)(l:List Axis) : A.pivot P (v::l)=(A.pivot P l).kiss P v:= by rw [Apron.pivot]
lemma Apron.pivot_s (P:Spine)(A:P.Apron)(l:List Axis) : (A.pivot P l).s=A.s:=by
 induction l with|nil=>rfl|cons v t ih=> rw [Apron.pivot_cons]; exact ih
lemma Apron.pivot_w(P:Spine) (A:P.Apron) (l:List Axis) : (A.pivot P l).realWidth P j=A.realWidth P j:=by
 induction l with|nil=>rfl|cons v t ih=> rw [Apron.pivot_cons]; exact ih
include x in
lemma reflect_any (X:Cover): P.reflectTest j (P.centeredQ x s X)= P.centeredQ x s (opposeQ j X):= by
 have hv:= P.single_agrees 3 j x s (P.visitOne s X); have he:= P.single_agrees 3 j x s (P.reflectTest j (P.visitOne s X)); rw [P.single_state,P.single_state, ← P.reading_star,map_star] at he -- rw state at he hv? 
 rw [P.single_state,P.single_state] at hv; rw [hv] at he; rw [←P.single_state,← P.single_state] at he
 rw [P.reflect_visit] at he; unfold centeredQ dewy; rw [map_sub,P.reflect_visit,P.scale_mirror (1:P.Test), show P.reflectTest j 1=1 from aureoleUnit ..]; exact congrArg (fun w:ℂ=> P.visitOne s (opposeQ j X) - w • (1:P.Test)) he
-- underscore rw maybe problems
-- Recover coordinates simultaneous orientation
noncomputable def pivotQ (C:Cover) (l:List Axis): Cover:= match l with
 | []=> C
 | z::l=> opposeQ z (pivotQ C l)
lemma pivot_alone (C:Cover)(l:List Axis)(j:Axis): pivotQ C l j=C j ∨ pivotQ C l j= - C j:=by
 induction l with
 | nil=> left; rfl
 | cons v l ih=>
   rw [pivotQ]; by_cases h:j=v
   · rw [opposeQ,mirrorΩ, if_pos h,←h]; exact ih.elim (fun r=> Or.inr (by rw [r])) (fun r=> Or.inl (by rw [r,neg_neg]))
   rw [opposeQ,mirrorΩ,if_neg h]; exact ih
lemma baseP_F (l:List Axis)(f r:ℕ) : ((P.basePlay x f r).pivot P l).F=P.centeredQ x r (pivotQ (P.granule (P.megaK f r)) l):=by
 induction l with
 | nil=>rfl
 | cons v l ih=> rw [Apron.pivot_cons,pivotQ]; exact Eq.trans (congrArg (P.reflectTest v) ih) (P.reflect_any v x _)
local notation "g" k:max L₁:max=> pivotQ (P.granule k) L₁
local notation "K" f:max t:max=> P.megaK f t
local notation "Ω₀"=> P.sidesPerTick
local notation "Mℤ"=> (P.sidesPerTick:ℤ)
local notation "Z" f:max t:max L₁:max => pivotQ (fun _=> (P.megaK f t:ℤ)) L₁
local notation "κ"=>P.sidesPerTick
noncomputable abbrev lunar(f s:ℕ)(l:List Axis):Cover:=fun i=> ((pivotQ (fun _=> (P.megaK f s:ℤ)) l i)-1)/2
noncomputable abbrev barely (y:Cover)(f:ℕ): Cover:= P.plateau f+ fun i:Axis=> (y i-(P.plateau f i))%Mℤ
noncomputable abbrev rootSpace (f s:ℕ)(l:List Axis):=P.barely (P.lunar f s l) s
local notation "xZ" f:max s:max=> P.rootSpace f s
lemma lunar_resident (s f:ℕ)(l:List Axis)(p: Odd P.par.R.L.val) : nodeC (P.lunar f s l)=pivotQ (fun _=> (P.megaK f s:ℤ)) l:=by
 funext i; have he:= Odd.mul (a:=(L).val^(s-f)) (p.pow) (b:= P.baseK f) ⟨P.axleQ 3 (P.thresholdF f),rfl⟩; change Odd (K f s) at he; obtain ⟨w,h⟩:=he; simp only [lunar,nodeC,Pi.add_apply,two_smul,Pi.one_apply]; obtain hq|hq:=pivot_alone (fun _=> (P.megaK f s:ℤ)) l i <;> omega
private lemma pivots_sum (x y z:Cover)(l:List Axis)(k:ℕ)(h:x= y+k • z): pivotQ x l=pivotQ y l+k • pivotQ z l:=by
 induction l with
 | nil=> exact h
 | cons v l ih=> rw [pivotQ,pivotQ,pivotQ,ih]; ext i; by_cases e:i=v <;> simp [opposeQ,mirrorΩ,e]; ring
private lemma pivots_cost (x:Cover)(l:List Axis)(k:ℕ) : pivotQ (k • x) l=k • pivotQ x l:=by
 induction l with
 | nil=> rfl
 | cons v l ih=> rw [pivotQ,pivotQ,ih]; ext i; by_cases e:i=v <;> simp [opposeQ,mirrorΩ,e]
lemma barely_A(s:ℕ)(x:Cover) : ∃ t:Cover, nodeC (P.barely x s)=nodeC x+ P.sidesPerTick • t:=by
 let z(i:Axis):= - ((x i-P.plateau s i)/Mℤ); have he(i:Axis): κ • z i=P.barely x s i-x i:=by
   unfold barely z; let b:= x i-P.plateau s i; have he:= Int.emod_add_mul_ediv b Mℤ; simp only [Pi.add_apply,nsmul_eq_mul]; unfold b at he; linarith only [he] -- nsmul wrong parsing Λ
 refine ⟨2 • z,?_⟩; ext i; simp only [nodeC, Pi.add_apply, Pi.smul_apply,Pi.one_apply]; simp only [nsmul_eq_mul,Nat.cast_ofNat] at he ⊢; unfold barely at he; simp only [Pi.add_apply] at he; linarith only [he i] 
lemma mega_suit (hf:f ≤ s)(hu:s ≤ v)(l:List Axis): Z f v l = P.par.R.L.val^(v-s) • Z f s l:=by
 rw [← pivots_cost]; have he:v-f=(v-s)+(s-f):=by omega
 apply congrArg (fun t:Cover=> pivotQ t l); ext i; unfold megaK; rw [he,pow_add]; simp only [Pi.smul_apply]; simp only [nsmul_eq_mul]; push_cast only [Nat.cast_mul,Nat.cast_pow]; ring
lemma charge_race (f s v:ℕ)(hf:f ≤ s)(hu:s ≤ v)(l:List Axis)(p: Odd P.par.R.L.val) :
    ∃ t: Cover, P.clockPlate s v (P.rootSpace f s l)=g (P.megaK f v) l+P.sidesPerTick • t:=by
 let y0:= P.megaK f v; obtain ⟨d,h⟩:= P.barely_A s (P.lunar f s l); rw [P.lunar_resident s f l p] at h -- occurrence right
 let m:= (L).val^(v-s); let R(i:Axis):= P.persistD y0; let zz:Cover:= pivotQ R l; have ht: Z f v l= g y0 l+ P.sidesPerTick • zz:=pivots_sum (fun _=>(y0:ℤ)) (P.granule y0) R l (P.sidesPerTick) (by funext i; exact Eq.symm ( (by simp only [Pi.add_apply,Pi.smul_apply]; simp only [granule,nsmul_eq_mul,R]; linarith only [(P.lodge y0).2.2]))) -- try
 refine ⟨zz+  m • d,?_⟩; change m • nodeC (P.barely _ s)=_; rw [h,smul_add, ←P.mega_suit hf hu l, ht, smul_add]; rw [show _ • (P.sidesPerTick • d)=P.sidesPerTick • (m • d) from smul_comm m P.sidesPerTick d]; abel
lemma broadly(s f:ℕ)(l:List Axis): P.plateau s j ≤ P.rootSpace f s l j ∧ P.rootSpace f s l j ≤ P.plateau s j+ Mℤ:= by
 unfold rootSpace barely; simp only [Pi.add_apply]; have hx:=P.stepPos; have ht:=Int.emod_lt_of_pos ((P.lunar f s l j)-P.plateau s j) hx; have h0:= Int.emod_nonneg (P.lunar f s l j-P.plateau s j) hx.ne'; constructor <;> omega
lemma rent_honors(f s:ℕ)(l:List Axis): Plans j (P.rootSpace f s l) s P:= P.seat_plan j _ (P.broadly j s f l).1
lemma point_bought (s f:ℕ)(l:List Axis): 0 < nodeC (P.rootSpace f s l) j:= by
 have ht: 0 ≤ P.rootSpace f s l j:= le_trans (Int.natCast_nonneg (P.axleQ j (P.thresholdF s))) (P.broadly j s f l).1; simp only [nodeC,Pi.add_apply,two_smul,Pi.one_apply]; unfold rootSpace barely at ht; simp only [Pi.add_apply] at ht; omega
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.charge_race
