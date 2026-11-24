import YM.SU5.Twilight.Directions
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
local notation "π"=> P.pinJoint j
local notation "ω"=> P.colorZero j x
local notation "M"=> timeMesh P.par
local notation "Γ"=> marks M
local notation "N"=> notch M
local notation "ν"=> daylight M
local notation "κ"=> P.voyageF j x
local notation "V" i:max=> ((κ).crew i).play
local notation "Ω"=> P.heaven j x
local notation "ω'"=> P.bank j x
local notation "ϑ"=> P.enter j x
open WeakDual TopologicalSpace
open scoped Pointwise
local notation "Y"=> P.run
local notation "VH"=> P.law
local notation "T"=>P.par
local notation "Z"=>P.history.circuit
local notation "K"=>P.calibration
local notation "Φ" i:max=> P.reflectTest i
local notation "Ξ" i:max=> P.shifts i
local notation "W"=> enclave K
local notation "Γr" t:max=> P.conveying t
local notation "ℓ"=> P.calibration.ℓ
variable (s t:ℕ)
open Tapestry SlabMark
/-!
# Hankel formula of spatial motions on positively (k) separated supports
 Note curvature estimates or any limits from *other choices of characters*
not required. Are allowed to move one argument in all directions except k (provided j acquires acceptable Euclidean thickness). Then the *same support cuts* are enough for canonically continuing in k. No uniform norm-continuity invoked.
-/
local notation "M₁"=>P.ManyF j x
local notation "X"=> P.ColorHil j x
local notation "μ" i:max=> P.birthF i
local notation "ν₁" s:max=> P.viewF j x s
local notation "ν₂" i:max=> P.viewF i (P.otherSpectrum j i x)
open Set TopologicalSpace
variable (k:Trans j)
lemma registered {f:P.Test}(p:P.birthF j s f)(b:ℤ): ((P.voyageF j x).crew k).play (N s b) (P.viewF j x s p)= P.viewF j x s (P.passes j s k.property b p):=by
 rw [P.released]; exact DFunLike.congr_fun (P.meets j x k s b) _ -- check
lemma identical_F {f g:P.Test}(p:P.birthF j s f)(q:P.birthF j s g)(e:f=g): P.viewF j x s p= P.viewF j x s q := by subst g; rfl
lemma moment_isotropic {f g:P.Test}(p:(μ j) s f)(q:(μ j) s g)(r:(μ (k.val)) s ((Φ (k.val)) ((Φ j) f)))(u:(μ (k.val)) s g):
    inner ℂ ((ν₁ s) p) ((ν₁ s) q)=inner ℂ ((ν₂ (k.val)) s r) ((ν₂ (k.val)) s u):=by
  rw [P.released_gram,P.released_gram,P.single_agrees,show (Φ (k.val)) ((Φ (k.val)) ((Φ j) f))=(Φ j) f from aureoleTwice ..]
local notation "U" c:max b:max=> ((κ).crew c).play b

local notation "χ" => P.otherSpectrum j k.val x
local notation "SE"=> P.physicalEnergy k.val (χ)
-- for both positive, advance g by nonnegative amounts on k, at any rung
lemma overture {f g:P.Test}(p:(μ j) s f)(q:(μ j) s g)(r:(μ (k.val)) s ((Φ (k.val)) ((Φ j) f)))(u:(μ (k.val)) s g)(n:ℕ):
    inner ℂ ((ν₁ s) p) ((U k (N s n)) ((ν₁ s) q))=inner ℂ ((ν₂ (k.val)) s r) ((SE).E (whenly M s n) ((ν₂ (k.val)) s u)):=
  calc _ = inner ℂ ((ν₁ s) p) ((ν₁ s) (P.passes _ _ k.property n q)) := by rw [P.registered]
       _ = inner ℂ ((ν₂ (k.val)) s r) ((ν₂ (k.val)) s (P.passesLater _ _ n u)):= P.moment_isotropic j x s k p _ r _ -- parse?
       _ = inner ℂ ((ν₂ (k.val)) s r) ((SE).E (whenly M s n) ((ν₂ (k.val)) s u)) := congrArg (inner ℂ ((ν₂ (k.val)) s r)) (P.releasedLater k.val (χ) s n u)
lemma birthRig (t:ℕ)(ht:s ≤ t){f:P.Test}(q:(μ (k.val)) s ((Φ (k.val)) ((Φ j) f))): (μ (k.val)) t ((Φ (k.val)) ((Φ j) (P.conveying s (t-s) f))):=by
 rw [←P.reflUp,←P.reflUp]; exact P.rig _ _ _ q ht
lemma venture (n:ℕ)(f g:P.Test)(ht:s≤t)(p:(μ j) s f)(q:(μ j) s g)(r:(μ (k.val)) s ((Φ (k.val)) ((Φ j) f)))(u:(μ (k.val)) s g):
    inner ℂ ((ν₁ s) p) ((U k (N t n)) ((ν₁ s) q))=inner ℂ ((ν₂ (k.val)) s r) ((SE).E (whenly M t n) ((ν₂ (k.val)) s u)):=by
 have R₁:=P.birthRig j s k t ht r; have R₂:=P.rig k.val s t r ht
 have hV: P.viewF k.val (χ) t R₂=P.viewF k.val (χ) t R₁:=P.identical_F _ _ _ _ _ (by rw [P.reflUp,P.reflUp])
 have hx: P.viewF k.val (χ) t R₁=_:=hV.symm.trans (P.view_rig k.val (χ) s t r ht)
 have hu:=P.overture j x t k (P.rig j s t p ht) (P.rig j s t q ht) R₁ (P.rig _ s t u ht) n
 refine (congrArg₂ (fun y z:X=>inner ℂ y ((U k (N t n)) z)) (P.view_rig j x s t p ht).symm (P.view_rig j x s t q ht).symm).trans (hu.trans ?_)
 exact congrArg₂ (fun y z:P.ColorHil k.val (χ)=> inner ℂ y ((SE).E (whenly M t n) z)) hx (P.view_rig k.val (χ) s t u ht)
lemma ages (M':Mesh)(a:marks M')(hp:0≤ (a:ℝ)):∃ (t:ℕ)(_:s≤t)(n:ℕ),notch M' t n=a ∧ whenly M' t n=Real.toNNReal (a:ℝ):=by
 obtain ⟨y,d,rfl⟩:=notch_exists M' a; let t:=max y s; have hy:y ≤ t:=le_max_left ..; let w:=castor M' y t d; have hw:notch M' t w=notch M' y d:=notch_up M' y t hy d; have ht:0≤w:=by
    apply (bell_le M' t 0 w).1; change ((↑(notch M' t 0)):ℝ)≤((↑(notch M' t w)):ℝ); rw [hw,notch_zero]; exact hp
 let n:= w.toNat; have hn:notch M' t n=notch M' y d:=by rw [show (n:ℤ)=w from Int.toNat_of_nonneg ht,hw]
 have hx: ((↑(notch M' y d)):ℝ)= ↑(whenly M' t n):=calc
    _ = ((↑(notch M' t n)):ℝ):=congrArg (fun z:marks M'=>z.val) hn.symm
    _ =_ :=natural_time M' t n
 exact ⟨t,le_max_right ..,n,hn,by rw [hx,Real.toNNReal_coe]⟩
lemma advances_cost (a:Γ){f g:P.Test}(p:(μ j) s f)(q:(μ j) s g)(r:(μ (k.val)) s ((Φ (k.val)) ((Φ j) f)))(u:(μ (k.val)) s g)(h:0 ≤ (a:ℝ)):
    inner ℂ ((ν₁ s) p) ((U k a) ((ν₁ s) q))=inner ℂ ((ν₂ (k.val)) s r) ((SE).E (Real.toNNReal (a:ℝ)) ((ν₂ (k.val)) s u)):=by
  let α : Γ→ℂ:=fun a=>inner ℂ ((ν₁ s) p) ((U k a) ((ν₁ s) q))
  let β : ℝ≥0→ℂ:=fun t=>inner ℂ ((ν₂ (k.val)) s r) ((SE).E t ((ν₂ (k.val)) s u))
  have hu:∃ (t:ℕ)(_:s≤t)(n:ℕ),notch M t n=a ∧ whenly M t n=Real.toNNReal (a:ℝ):= ages s M a h
  change α a=β _; obtain ⟨t,ht,n,hn,hw⟩:= hu
  exact (congrArg α hn).symm.trans ((P.venture j x s t k n f g ht p q r u).trans (congrArg β hw))
-- vector-pair certificate
inductive Eats (k:Trans j): P.ColorHil j x→ P.ColorHil j x→Prop where
| chooseF (s:ℕ){f g:P.Test}(p:P.birthF j s f)(q:P.birthF j s g)(r:P.birthF k.val s ((Φ (k.val)) ((Φ j) f)))(u:P.birthF k.val s g)(a:marks (timeMesh P.par))(z:0 < (a:ℝ)): Eats k (P.viewF j x s p) (((P.voyageF j x).crew k).play a (P.viewF j x s q))
namespace Eats
lemma cont {b y:X}(p:P.Eats j x k b y): ContinuousAt (fun a:Γ=>inner ℂ b ((U k a) y)) 0:=by
 cases p with
 | chooseF s p q r u a hp =>
   let v:= (ν₁ s) p; let y:=(ν₁ s) q; let σ:=(ν₂ (k.val)) s r; let β:=(ν₂ (k.val)) s u
   let R (t:Γ):= ((t+a):Γ).val; let G(t:Γ):=inner ℂ σ ((SE).E (Real.toNNReal (R t)) β)
   have he:Continuous R:=by unfold R; fun_prop
   have hg:Continuous G:=continuous_const.inner ((SE).continuousE β|>.comp (continuous_real_toNNReal.comp he))
   apply hg.continuousAt.congr
   have hx:0< R 0:=by simpa [R]
   filter_upwards [he.continuousAt.tendsto.eventually (lt_mem_nhds hx)] with t h
   exact (P.advances_cost j x s k (t+a) p q r u h.le).symm.trans (congrArg (inner ℂ v) (((κ).crew k).paved (X) t a y).symm)
lemma champ (i:Trans j)(w:Γ)(t:i ≠ k){b y:X}(p:P.Eats j x k b y): P.Eats j x k b ((U i w) y):=by
 cases p with
 | chooseF s p q r u a ha =>
   rename_i f g -- inspect
   obtain ⟨d,v,rfl⟩:=notch_exists M w; let n:=max d s; have hy:d≤ n:=le_max_left ..; have hx:s ≤ n:=le_max_right ..; let w:=castor M d n v
   rw [← ContinuousLinearMap.comp_apply, (κ).cCom,ContinuousLinearMap.comp_apply]
   rw [← show N n w=N d v from notch_up M d n hy v, ← P.view_rig j x s n q hx, P.registered, ←P.view_rig j x s n p hx]
   refine Eats.chooseF _ _ _ (P.birthRig j s k n hx r) ?_ a ha -- parse
   exact P.passes k.val n (fun e=> t (Subtype.ext e)) w (P.rig _ _ _ u hx)
end Eats
-- rightward only. can extend by symmetry (left atom champ needs proof then)
structure JointCuts (u w:P.ColorHil j x) (k:Trans j) : Prop where
 survives : ∃ b: Γ, P.Eats j x k ((U k b) u) ((U k b) w)

lemma commutesPlay (a:Trans j)(e v:Γ)(b:X): (U k v) ((U a e) b)=(U a e) ((U k v) b):= DFunLike.congr_fun ((κ).cCom ..) b
lemma cut_holds {a b:X}(p:P.JointCuts j x a b k): ContinuousAt (fun y:Γ=>inner ℂ a ((U k y) b)) 0:=by
 obtain ⟨s,e⟩:= p.survives; apply ContinuousAt.congr (Eats.cont P j x k e) -- parse
 filter_upwards with v
 change inner ℂ ((U k s) a) ((U k v) ((U k s) b))= _; rw [P.commutesPlay j x k k s v, ((κ).crew k).inner_g]
lemma cut_slide (a:Trans j)(t:a≠k)(y:Γ){u w:X}(p:P.JointCuts j x u w k) : P.JointCuts j x u ((U a y) w) k:=by
 obtain ⟨b,e⟩:=p.survives; refine ⟨b,?_⟩; rw [P.commutesPlay]; exact Eats.champ P j x k a y t e
lemma livingH {a b:X}(p:∀ k,P.JointCuts j x a b k): inner ℂ (ω' a) (ω' b) = inner ℂ a b:=by
  let f:= innerSL ℂ a
  let L:= look j
  have t:∀ k: Trans j,(κ).Window b (fun _=>0) f k:= by
    intro i y c; have he(J:List (Trans j×Γ))(t:∀ v∈ J,v.1≠i): P.JointCuts j x a ((κ).band J b) i:=by
       induction J with | nil=> exact p i | cons v J ih=> exact P.cut_slide j x i v.1 (t v (List.mem_cons_self ..)) v.2 (ih (fun j h=> t j (List.Mem.tail _ h)))
    have hv(J:List (Trans j × Γ))(t:Γ) : (U i t) ((κ).band J b)=(κ).band J ((U i t) b):=by
       -- need more general band theorem or induction. here b ok
       induction J with | nil=> rfl| cons z J ih=> change (U i t) ((U z.1 z.2) ((κ).band J b))=(U z.1 z.2) ((κ).band J _); rw [P.commutesPlay,ih]
    apply ContinuousAt.congr (P.cut_holds j x i (he y c)) (Eventually.of_forall fun v=> congrArg f (hv y v))
  have hc:= (κ).covered L b 0 f (fun i _=> t i) (look_one j); have hz:= (κ).faith L b 0 f hc; rw [Alliance.raw_zero] at hz
  let Vv:=P.visitors j x; change inner ℂ (Vv a) (Vv b)=_; rw [← ContinuousLinearMap.adjoint_inner_right]; -- formula orientation? `adjoint_inner_right` rewrites? 
  have h₀: Vv.adjoint=Vv:= (κ).symmetricstack L; rw [h₀,show Vv (Vv b)=Vv b from (κ).grounded L ((κ).planted L b)]; exact hz
-- shift to target all Γ. obtaining genuine equality at this one separation / group
lemma smooth_toDate (y: Trans j→Γ){a b:X}(p:∀ k,P.JointCuts j x a ((κ).raw (look j) y b) k):
   inner ℂ (ω' a) ((P.seasons j x).U (transverse j (fun i=> (y i:ℝ))) (ω' b))= inner ℂ a ((κ).raw (look j) y b):=by rw [P.roll_motion]; exact P.livingH j x p
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.advances_cost
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.smooth_toDate
