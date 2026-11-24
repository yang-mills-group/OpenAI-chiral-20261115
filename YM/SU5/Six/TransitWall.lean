import YM.SU5.Six.Photos
import YM.SU5.Six.OrdinaryMist
import YM.SU5.Aria.Grotto
import YM.SU5.Six.KeepCharge
import YM.SU5.Six.MirrorCharge
set_option maxHeartbeats 200000
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
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
open Aria Set
open Cheer (Narrow)
/-!
# Wall formulae for the actual samples

Use `ColorHil`; no change to the Hilbert
space already given here. Time is set by the width-paid Mesh. Wall formulae
allow integration across every strict-order frame (for these pairs, the only
frames used in `t:trans6`).
-/
open MacroGrid
variable (P:Spine)(t:ℕ)
def macroStep := (mill (timeMesh P.par) t:ℝ)
lemma macroStep_pos : 0<P.macroStep t:= mill_pos _ _
lemma macroStep_zero : Tendsto P.macroStep atTop (𝓝 0):= NNReal.tendsto_coe.mpr (MeshClock.vanishes ..)
lemma tile_pose (p:Cover): P.meshPose t p= atTick (P.macroStep t) p:=rfl
lemma tile_add (p q:Cover): P.vtile t (p+q)= P.vtile t p+P.vtile t q:=funext fun i=> Subtype.ext (show bell (timeMesh P.par) t (p i+q i)=bell (timeMesh P.par) t (p i)+bell (timeMesh P.par) t (q i) from bell_add ..)
open Casting
abbrev opposeR(j:Axis):Vantage→Vantage:=mirrorΩ j
abbrev opposeQ(j:Axis):Cover→ Cover:=mirrorΩ j
lemma tile_reflect (p:Cover)(j:Axis): P.meshPose t (opposeQ j p)= opposeR j (P.meshPose t p) := by
 funext i; change bell _ t (mirrorΩ j p i)= _; by_cases u:i=j
 · subst i; simp only [mirrorΩ, if_pos rfl,opposeR]; simp [meshPose,laysM,vtile,notch,bell]
 rw [mirrorΩ,if_neg u]; exact (if_neg u).symm
lemma reflectPose_twice (j:Axis)(p:Vantage): opposeR j (opposeR j p)=p:=by funext i; by_cases h:i=j <;> simp [opposeR,mirrorΩ,h]
lemma reflectInt_twice (j:Axis)(p:Cover): opposeQ j (opposeQ j p)=p:=by funext i; by_cases h:i=j <;> simp [opposeQ,mirrorΩ,h]
lemma issue_reflect (A:P.Apron)(p:Cover)(j:Axis): P.issuing t (A.kiss P j) (opposeQ j p)= P.reflectTest j (P.issuing t A p):= by
 unfold issuing; rw [A.full_exchange]
 let Φ:= P.reflectTest j
 have ht(i:Axis)(F:P.Test) : P.shifts i (opposeQ j p i) (Φ F)= Φ (P.shifts i (p i) F):= by
    by_cases h:i=j
    · subst i; rw [opposeQ,mirrorΩ,if_pos rfl]; exact (P.meetOwn ..).symm
    rw [opposeQ,mirrorΩ,if_neg h]; exact P.meetrefl i j _ _ h
 let f:= A.full P t
 suffices H:∀ L, P.cruise L (opposeQ j p) (Φ f)= Φ (P.cruise L p f) from H Vacancy.ordinate
 intro L; induction L with | nil=> rfl| cons i l h=> rw [P.cruise_step, P.cruise_step,AlgHom.comp_apply, AlgHom.comp_apply,h]; exact ht _ _
section projection
variable (a:P.Spectrum0 3)(j:Axis)(J:P.Ellis 3 a)
local notation "V"=> P.advocate 3 a j
local notation "F"=> P.truck j V
local notation "ε"=> P.wealth j V
local notation "Π'"=> P.enter j V
local notation "H"=> P.ColorHil j V
include J
lemma macroRiemann (f:Vantage→P.ColorHil j (P.advocate 3 a j))(u:HasCompactSupport f)(h:Continuous f):
    Tendsto (fun i=> MacroGrid.poseApprox H f (F ∘ P.vtile i) (P.macroStep i)) atTop
      (𝓝 (Π' (∫ x:Vantage, P.cartage j V x (ε (f x))))) := by
  refine pays_projection H (P.ManyF j V) ((Π').toContinuousLinearMap) ε P.laysM F _ P.vtile
      P.macroStep P.macroStep_pos P.macroStep_zero P.tile_pose P.tile_add ?_ (P.truck_paves j V) (P.truck_norm j V) (P.cart_and j V) ?_ J.mistT ?_ (J.shaky j) f u h
  · intro g; filter_upwards [Filter.eventually_all.mpr fun i:Axis=>P.vwhere (g:=g) 0 i] with n t
    choose k v using t; exact ⟨k,funext v⟩
  · exact P.caravan j V Prod.fst Prod.snd continuous_fst continuous_snd
  exact fun X e=> P.gentle_room J.owned e
end projection
section axis
variable (j:Axis)(x:P.Spectrum0 j)
local notation "Ψ" => P.physicalEnergy j x
local notation "Ε"=> (Ψ).E
local notation "Ω"=> P.colorZero j x
local notation "Γ"=>P.truck j x
lemma sixWard_truck_heat (p:P.VMark)(a:ℝ≥0)(y:P.ColorHil j x): Γ p (Ε a y)= Ε a (Γ p y):=by
 unfold truck; generalize look j=L; induction L with
 | nil=>rfl
 | cons i l h=>
   rw [raw_step]; simp only [ContinuousLinearMap.comp_apply,h]; exact DFunLike.congr_fun (P.colorMoveE ..) _
lemma truck_star (p:P.VMark): (P.truck j x p).adjoint= P.truck j x (-p):=by
 ext1 z; apply ext_inner_left ℂ; intro y; rw [ContinuousLinearMap.adjoint_inner_right,P.truck_inner]
lemma charter_opposed(p:P.VMark)(D:P.Apron): (P.charter j x p ((D.kiss P j).engine P j x)).adjoint=P.charter j x p (D.engine P j x):= by
  have hv: star (D.engine P j x)=(D.kiss P j).engine P j x:=D.peer P j x
  let A:= D.engine P j x
  have hp: ((D.kiss P j).engine P j x)= ContinuousLinearMap.adjoint A:=hv.symm; rw [hp]; unfold charter
  simp only [ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_adjoint,P.truck_star,neg_neg]; rfl
lemma raw_aperture (p:P.VMark)(A:P.Apron): P.charter j x p (A.engine P j x) Ω= Γ p (A.engine P j x Ω):= by
 unfold charter; rw [ContinuousLinearMap.comp_apply,ContinuousLinearMap.comp_apply,P.truck_empty]
end axis
variable (x:P.Spectrum0 3)(J:P.Ellis 3 x) (Z W:Lead.Clan)(s n:ℕ)
local notation "D"=> P.gridStory s n Z W
local notation "A"=> P.experimentBody Z s n
local notation "B"=> P.experimentBody W s n
local notation "A'"=> (A).kiss P 3
local notation "H"=> P.ColorHil 3 (P.otherSpectrum 3 3 x)
local notation "Ζ"=> P.ManyF 3 (P.otherSpectrum 3 3 x)
local notation "ψ"=> P.physicalEnergy 3 (P.otherSpectrum 3 3 x)
local notation "Ψ" => P.seasons 3 (P.otherSpectrum 3 3 x)
local notation "ξ"=> P.advocate 3 x 3
local notation "Γ"=> P.truck 3 ξ
local notation "π'"=> P.wealth 3 ξ
local notation "Φ₀"=> P.filterVector x s n
local notation "Φ"=> P.sixWard_macroVector x s n
local notation "Ε"=> (ψ).E
local notation "Ω"=> P.colorZero 3 ξ
local notation "S"=> P.probeWidth s n 3
local notation "T"=> P.vtile t
local notation "u"=>P.meshPose t
open OS.Semigroup
private lemma gains (L:Hilbert)(p:OS.Semigroup L (3:Axis))(x:L)(a b:ℝ)(f:0≤a)(v:a ≤ b): p.E ((b-a).toNNReal) (p.E a.toNNReal x)= p.E b.toNNReal x:= by
  have he: b.toNNReal=(b-a).toNNReal+a.toNNReal:= by ext; simp [f,show 0≤ b from f.trans v, sub_nonneg.mpr v]
  rw [he,p.time]; rfl
def hotRead (c:ℝ)(p:Cover): H:= P.truck 3 ξ (T p) (Ε ((u p 3-c).toNNReal) (Φ₀ Z))
def coldRead (c:ℝ)(p:Cover): H:= P.truck 3 ξ (T p) (Ε ((c-u p 3).toNNReal) (Φ₀ Z))
#check @hotRead
#check @coldRead
lemma charterShift (p:Cover)(z:ℝ)(h:S≤z):
    Ε ((z-S).toNNReal) (P.charter 3 ξ (T p) ((A).engine P 3 ξ) Ω)= Γ (T p) (Ε (z.toNNReal) (Φ₀ Z)):= by
  have ht:= P.raw_aperture 3 ξ (T p) A
  let U:= P.truck 3 ξ (T p); let y:= (A).engine P 3 ξ Ω; let L:=P.filterVector x s n Z
  exact (congrArg (fun y:H=> Ε ((z-S).toNNReal) y) ht).trans (((P.sixWard_truck_heat 3 ξ (T p) _ y).symm).trans (congrArg (fun y:H=> U y) ((congrArg (fun y:H=> Ε ((z-S).toNNReal) y) (P.rawEntry x s n Z)).trans (gains H ψ L _ _ (P.width_here _ _ _).le h))))
-- Pin Ward supports and sample expression separated by FIXED real wall.
private lemma sidle (X:Hilbert)(T₀:OS.Semigroup X (3:Axis))(x:X)(Q:X.Op)(Y:X)(d:ℝ)(f g:ℝ≥0)(ht:d.toNNReal=f+g)(l m:X)(hp:T₀.E f (Q.adjoint x)=l)(hq:T₀.E g Y=m): inner ℂ x (Q (T₀.E d.toNNReal Y))=inner ℂ l m:=by rw [ht,←ContinuousLinearMap.adjoint_inner_left,T₀.time,ContinuousLinearMap.comp_apply,← OS.Semigroup.swing,hp,hq]
private lemma noVac (X:Hilbert)(p:OS.Semigroup X (3:Axis))(x y:X)(a:ℝ≥0)(h:∀ a:ℝ≥0,p.E a x=x):inner ℂ x (p.E a y)= inner ℂ x y:=by rw [← p.swing, h]
set_option maxHeartbeats 300000 in
lemma raw_wall (c:ℝ) (k l:Cover)(a:u k 3+S<c)(b:c+S<u l 3)(p:s≤t):
    P.singleState 3 t x (P.issuing t A' k * P.issuing t B l) =
      inner ℂ (P.coldRead t x Z s n c k) (P.hotRead t x W s n c l):= by
  let r:=usher k l; let L:List Bool:=[false,true]; let R:= (T) ∘ r
  have e: P.issuing t A' k * P.issuing t B l=P.fullScroll t D r L:=by
     change _=_*(_*(1:P.Test)); rw [mul_one]; rfl
  have hv: P.Turnstile 3 D L (P.laysM ∘ R):= List.pairwise_pair.mpr (by change u k 3+S < u l 3-S; linarith)
  have he:∀ i∈L,(D i).s≤t:=fun i _=>by cases i <;> exact p
  rw [e]; refine (P.single_agrees 3 3 x t _).symm.trans ((P.turn_purchase 3 ξ D r t L hv he).symm.trans ?_)
  let Q:=P.charter 3 ξ (T k) ((A').engine P 3 ξ)
  let C:=P.charter 3 ξ (T l) ((B).engine P 3 ξ)
  let m:=u l 3-c; let a':=c-u k 3
  let d:=u l 3-S-(u k 3+S); let f:=(a'-S).toNNReal; let g:=(m-S).toNNReal
  have had: S < a':=by unfold a'; linarith
  have hb: S < m:=by unfold m; linarith
  have ht: d.toNNReal=f+g:= by ext; rw [Real.coe_toNNReal,NNReal.coe_add]; simp only [f,g,Real.coe_toNNReal _ (sub_nonneg.mpr had.le), Real.coe_toNNReal _ (sub_nonneg.mpr hb.le)]; unfold d a' m; ring; exact sub_nonneg.mpr (by linarith only [a,b])
  have hh:P.preview 3 ξ D L R=inner ℂ Ω (Q (Ε d.toNNReal (C Ω))):= by
    unfold preview; refine (rector_view ψ Ω _ _ _ (P.sector_hot 3 ξ) 0 L).symm.trans ?_
    change inner ℂ Ω (Ε _ (Q (Ε d.toNNReal (C Ω))))= _
    exact noVac H ψ Ω _ _ (P.sector_hot 3 ξ)
  have heQ: Ε f (Q.adjoint Ω)=P.coldRead t x Z s n c k:= ((congrArg (fun X:(P.ColorHil 3 ξ).Op=> Ε f (X Ω)) (P.charter_opposed 3 ξ (T k) A)).trans (P.charterShift t x Z s n k _ had.le))
  exact hh.trans (sidle H ψ Ω Q (C Ω) d f g ht _ _ heQ (P.charterShift t x W s n l _ hb.le))
def forwardRay (c:ℝ)(p:Vantage): Ζ:= P.cartage 3 ξ p ((Ψ).E ((p 3-c).toNNReal) (Φ Z))
def backwardRay (c:ℝ)(p:Vantage): Ζ:= P.cartage 3 ξ p ((Ψ).E ((c-p 3).toNNReal) (Φ Z))
private lemma film (X:Hilbert) (U:OS.Semigroup X (3:Axis))(x y:X)(Y Z W:X.Op)(a b:ℝ)(p:0≤a)(h:0≤b)
   (e: Y.adjoint.comp Z=W)(w:∀ z:X, U.E a.toNNReal (W z)=W (U.E a.toNNReal z)):
   inner ℂ (Y (U.E a.toNNReal x)) (Z (U.E b.toNNReal y))= inner ℂ x (W (U.E (a+b).toNNReal y)):= by
 rw [← ContinuousLinearMap.adjoint_inner_right]; rw [←ContinuousLinearMap.comp_apply Y.adjoint,e,U.swing,w,Real.toNNReal_add p h,U.time]; rfl
include J
lemma ordered_wall (c:ℝ) (p q:Vantage)(a:p 3+S<c)(b:c+S<q 3):
    P.transmission x s n Z W (q-p)= inner ℂ (P.backwardRay x Z s n c p) (P.forwardRay x W s n c q):= by
 have he:= P.width_here s n 3
 let z:Vantage:=q-p; let k:= P.cartage 3 ξ
 have hv: (k p).adjoint.comp (k q)=k (q-p):= by unfold k; rw [P.cart_reverses,← P.cart_paves, sub_eq_add_neg, add_comm]
 have hs:z 3=(c-p 3)+(q 3-c):=by change q 3-p 3=_; ring
 refine (P.positive_time_charge x s n Z W _ J ?_).trans (Eq.trans ?_ (film Ζ Ψ (Φ Z) (Φ W) (k p) (k q) (k z) (c-p 3) (q 3-c) (by linarith only [a,he]) (by linarith only [b,he]) hv (P.warm_drive 3 ξ z _)).symm)
 · change _<q 3-p 3; linarith only [a,b]
 exact congrArg (fun t:ℝ=> inner ℂ (Φ Z) (k z ((Ψ).E t.toNNReal (Φ W)))) hs
omit J
lemma mirrored_ray (p:Vantage) : P.backwardRay x Z s n 0 (opposeR 3 p)=P.forwardRay x Z s n 0 p:= by
 have ht:P.cartage 3 ξ (opposeR 3 p)= P.cartage 3 ξ p:= cart_mirror ..
 have he:0- (opposeR 3 p) 3=p 3-0:=by rw [show opposeR 3 p 3= -p 3 from if_pos rfl]; ring
 exact congrArg₂ (fun (L:(P.ManyF 3 ξ).Op)(t:ℝ)=>L ((Ψ).E t.toNNReal (Φ Z))) ht he
-- The ray formula is also the upward actual VIEW. (Gram is enough but explicit.)
lemma manifestRead(k:Cover)(b:S<u k 3)(p:s≤t): ∃ h:P.birthF 3 t (P.issuing t A k),P.viewF 3 ξ t h=P.hotRead t x Z s n 0 k:= by
  let i:Fin 1:=0; let L:=[i]; let Q:= fun _:Fin 1=>A; let r:=fun _:Fin 1=>k; let V:= (T) ∘ r
  have he : ∀ i∈L,(Q i).s≤t:= fun i _=>p
  have ht:P.onBoard 3 t Q r L 0:= by
    refine ⟨(bell_le (timeMesh P.par) t _ _).1 ?_,trivial⟩
    rw [P.begins 3 Q r t i p]; change bell _ t 0 ≤ u k 3 - S
    rw [show bell (timeMesh P.par) t 0=0 by simp [bell]]; linarith
  have hx: P.issuing t A k=P.shifts 3 (-(0:ℤ)) (P.fullScroll t Q r L):= by
    rw [neg_zero,P.shifts_zero]; change _=_*1; rw [mul_one]; rfl
  obtain ⟨f,g⟩:= P.vread 3 ξ t _ _ L 0 ht he
  have u':P.birthF 3 t (P.issuing t A k):=by rw [hx]; exact f
  refine ⟨u', (P.identical_F 3 ξ t _ _ hx).trans (g.trans ((P.transporting 3 ξ Q r t L 0 ht he).trans ?_))⟩
  let C:= P.charter 3 ξ (T k) ((A).engine P 3 ξ)
  rw [show bell (timeMesh P.par) t 0=0 by simp [bell]]
  change Ε (((u k 3-S)-0).toNNReal) (C Ω)= P.hotRead t x Z s n 0 k
  have hg:u k 3-S-0=(u k 3-0)-S:=by ring
  exact (congrArg (fun z:ℝ=> Ε z.toNNReal (C Ω)) hg).trans (P.charterShift t x Z s n k (u k 3-0) (by linarith only [b]))
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
