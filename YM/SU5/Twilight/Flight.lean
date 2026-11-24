import YM.SU5.Selected.Moment
/-!
# Select the canonical continuous part of **the tested selected color character**
Use TOWER *even* mesh `notch(M)`; recall units here are **fermion lattice units at
level zero**. Since `shifts` are translations by `2* gaugeT` many gauge steps in the
observing lattice (per integer unit), and one cell in fermion lattice stands for two
gauge steps of same rung, then both `notch` and `mill` factors here in E4 and ℂ are
what relate to actual supported marks. Don't confuse with `RSpace` of `Altitude` which
uses gauge steps, compare by factor 2 if reading there.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 220000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
variable (P: Spine) (j:Axis) (x:P.Spectrum0 j)
local notation "T"=> P.par
local notation "X"=>P.ColorHil j x
local notation "X₀"=>P.colorSpace j x
local notation "Y"=> P.physicalEnergy j x
local notation "C"=> P.walksColor j
local notation "π"=> P.pinJoint j
local notation "ω"=> P.colorZero j x
local notation "M"=> timeMesh P.par
local notation "Γ"=> marks M
local notation "N"=> notch M
local notation "ν"=> daylight M
open WeakDual
lemma phase_unitary (s:Grid j): P.walksColor j s ∈ unitary (P.Physical j):= ⟨Subtype.ext (P.falls_toUnit j s |>.1), Subtype.ext (P.falls_toUnit j s|>.2)⟩
def flutter (k:Trans j): Lunation M (P.ColorHil j x) where
 nav s i:= X₀ (C (s,i,k))
 zero s:=by rw [show C (s,0,k)=1 from Subtype.ext (Subtype.ext (P.shift_zero j s k)), map_one]; rfl
 sums s i a:=by
   have h : C (s,i,k)*C (s,a,k)=C (s,i+a,k):=Subtype.ext (Subtype.ext (P.shift_plus j s i a k)); exact (map_mul X₀ (C (s,i,k)) (C (s,a,k))).symm.trans (congrArg (fun w=>X₀ w) h)
 changeover s t v a:=by
   apply congrArg; apply Subtype.ext; apply Subtype.ext; change (P.crew j k).play (N s a)=(P.crew j k).play (N t _); rw [← notch_up M s t v]
 limited s i:= by
   apply (NonUnitalStarAlgHom.norm_apply_le X₀ (C (s,i,k))).trans; exact P.grow j (s,i,k) -- name
local notation "Yb" i:max=> P.flutter j x i
lemma flyers_cComm (a b : Trans j) (y z:Γ) : ((Yb a).plays.play y).comp ((Yb b).plays.play z) = ((Yb b).plays.play z).comp ((Yb a).plays.play y):= by
 obtain ⟨s,i,rfl⟩:=notch_exists M y; obtain ⟨t,k,rfl⟩:=notch_exists M z
 change ((Yb a).ship _) * ((Yb b).ship _) = ((Yb b).ship _) * ((Yb a).ship _); rw [Lunation.navZ,Lunation.navZ]
 have he : C (s,i,a)*C (t,k,b)=C (t,k,b)*C (s,i,a):= Subtype.ext (Subtype.ext ((ladder P.run P.large P.law P.history.circuit j 0 false (P.room j)).cCom a b (N s i) (N t k)))
 exact (map_mul X₀ _ _).symm.trans ((congrArg (fun z=> X₀ z) he).trans (map_mul X₀ _ _))
def voyageF : Alliance (Trans j) (marks (timeMesh P.par)) X:= ⟨fun i=> (Yb i).plays, P.flyers_cComm j x⟩
local notation "κ"=> P.voyageF j x
local notation "V" i:max=> ((κ).crew i).play
local notation "F"=> look j
local notation "E₀"=> (κ).Realm (look j)
lemma meets (i:Trans j)(s:ℕ)(p:ℤ): ((P.voyageF j x).crew i).play (N s p)= X₀ (C (s,p,i)):=Lunation.navZ (P.flutter j x i) s p
lemma colorMoveE (i:Trans j)(y:Γ)(t:ℝ≥0): ((V i) y).comp ((Y).E t)= ((Y).E t).comp ((V i) y):=by
 obtain ⟨s,p,rfl⟩:= notch_exists M y; rw [P.meets]; let c:= C (s,p,i); let d:=P.risesColor j t; have hv:c*d=d*c:=Subtype.ext ((P.grid_member j t _).symm); exact (map_mul X₀ c d).symm.trans ((congrArg (fun z=> X₀ z) hv).trans (map_mul X₀ d c))
lemma colorFresh (i:Trans j)(b:Γ): (V i) b ω= ω:=by
 obtain ⟨s,p,rfl⟩:= notch_exists M b; rw [P.meets]; apply P.stasis
-- reuse stage/nav/scoped tools *without* invoking ANY specific history's ladder other than P, see `Sight.lean`
abbrev Viewers:= (P.voyageF j x).aviator F
instance campBase : CompleteSpace (P.Viewers j x):=Alliance.buried ..
abbrev visitors:= (P.voyageF j x).stackS F
abbrev ManyF : Hilbert:= (P.voyageF j x).Realm F
local notation "v"=> P.visitors j x
local notation "A"=> P.Viewers j x
lemma leader : P.colorZero j x∈ P.Viewers j x := by
 rw [Alliance.assembled]; intro i _; change ContinuousAt (fun a=> (V i) a ω) 0; simp_rw [P.colorFresh]; exact continuousAt_const
abbrev heaven : P.ManyF j x:= (⟨P.colorZero j x,P.leader j x⟩: A)
noncomputable def sunRise (t:ℝ≥0) :(P.ManyF j x).Op:= (κ).lame F ((Y).E t) (fun i _ a=>P.colorMoveE j x i a t)
lemma risen(t:ℝ≥0)(b:P.ManyF j x): ((P.sunRise j x t) b:A).val=(Y).E t b.val:=rfl
local notation "π₁"=>P.sunRise j x
abbrev enter : P.ManyF j x →ₗᵢ[ℂ] P.ColorHil j x:= (P.Viewers j x).subtypeₗᵢ
noncomputable def seasons : OS.Semigroup (P.ManyF j x) j:= by
 let S:=inheritS («B»:=P.ManyF j x) («A»:=P.ColorHil j x) π₁ (Y) (P.enter j x) (fun t x=> rfl)
 exact { S with
   U := fun y=> aviation (κ) (ν) (F) (fun a => y.val a.val)
   uZero:= Alliance.aviation_zero ..
   space a b:= (aviation_group ..).symm
   unitary y t:= aviation_unit ..
   independent:= fun t y=> by
    ext1 i; apply Subtype.ext
    let L:=(κ).flight (ν) (F) (fun a=>y.val a.val)
    change (Y).E t (L i.val) = L ((Y).E t i.val)
    rw [←ContinuousLinearMap.comp_apply L]; exact (congrArg (fun u:(P.ColorHil j x).Op=>u i.val) ((κ).fluid (ν) (F) ((Y).E t) (fun i _ a=>P.colorMoveE j x i a t) (fun a=>y.val a.val)).symm)
   continuousU z := Alliance.aviation_cont _ _ _ _ (fun (i:Trans j) _=>show Continuous (fun y:OS.Cross j => (y.val:E4) i.val) by fun_prop) z }
local notation "S"=>P.seasons j x
abbrev bank (b:P.ColorHil j x): P.ManyF j x:= ⟨P.visitors j x b,(κ).planted (F) b⟩
lemma bankHeat(t:ℝ≥0)(b:P.ColorHil j x): P.bank j x ((Y).E t b)=(S).E t (P.bank j x b):=by
 apply Subtype.ext
 change v ((Y).E t b)=(Y).E t (v b)
 exact DFunLike.congr_fun ((κ).ground (F) ((Y).E t) (fun i _ a=>P.colorMoveE j x i a t)).symm b
lemma soleHeat(t:ℝ≥0)(b:P.ManyF j x): P.enter j x ((P.seasons j x).E t b)=(P.physicalEnergy j x).E t (P.enter j x b):= rfl
lemma soleEdge(t:ℝ)(b:P.ManyF j x): P.enter j x ((P.seasons j x).edge t b)=(P.physicalEnergy j x).edge t (P.enter j x b):=
 DFunLike.congr_fun (within_energy (S) (Y) (P.enter j x).toContinuousLinearMap (fun t=> ContinuousLinearMap.ext (fun z=>rfl)) t) b -- name
-- rename projections for clarity. visitors = starproj
lemma visitors_op : P.visitors j x = (P.Viewers j x).starProjection:=by
  ext1 y; symm; apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero ((κ).planted F y); intro z p
  rw [inner_sub_left,sub_eq_zero, ← (κ).symmetricstack]; rw [ContinuousLinearMap.adjoint_inner_left,(κ).grounded F p]
lemma bank_linear : ∃ L: P.ColorHil j x→L[ℂ] P.ManyF j x, ∀ b, L b=P.bank j x b:= ⟨(P.visitors j x).codRestrict _ (fun _=> (κ).planted F _),fun _=>rfl⟩
def wealth : P.ColorHil j x →L[ℂ] P.ManyF j x:= (P.visitors j x).codRestrict _ ((κ).planted F)
lemma banked(z:X): P.wealth j x z=P.bank j x z:=rfl
lemma rewarded(z:A): P.bank j x (P.enter j x z)=z:= Subtype.ext ((κ).grounded F z.property)
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
