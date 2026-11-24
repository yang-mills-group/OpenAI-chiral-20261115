import YM.SU5.Twilight.Hankel
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
local notation "M₁"=>P.ManyF j x
local notation "X"=> P.ColorHil j x
local notation "μ" i:max=> P.birthF i
local notation "ν₁" s:max=> P.viewF j x s
local notation "ν₂" i:max=> P.viewF i (P.otherSpectrum j i x)
open Set TopologicalSpace
variable (k:Trans j)
-- Cut consumption API for labels native room. room Head `H` tracking through shifts lists
local notation "θ"=>P.Test
local notation "A"=> bay K
lemma positiveNotch (s:ℕ)(c:ℤ)(h:0<c): 0 < ((↑(N s c)):ℝ):= by change 0 < (c:ℝ)*_; exact mul_pos (by exact_mod_cast h) (mill_pos M s)
lemma rectangle_cut (d:ℤ){f b:θ} (p:P.birthF j s f)(q:P.birthF j s b)(u:P.birthF k.val s ((Φ (k.val)) ((Φ j) ((Ξ (k.val)) d f))))(a:P.birthF k.val s ((Ξ (k.val)) (d-1) b)) : P.JointCuts j x (P.viewF j x s p) (P.viewF j x s q) k:=by
 let S:=P.passes j s k.property (d-1) q; have hv:(V k) (N s d) ((ν₁ s) q)=(V k) (N s 1) ((ν₁ s) S):=by
   refine (P.registered j x s k q d).trans ?_
   rw [P.registered]; refine P.identical_F _ _ _ _ _ ?_; rw [P.shifts_sum,add_comm,sub_add_cancel];
 refine ⟨N s d,?_⟩; rw [hv,P.registered]; exact Eats.chooseF _ _ S u a (N s 1) (P.positiveNotch s _ zero_lt_one)
-- amenability in terms of actual stencils
lemma canFlip (u:Finset Cover) (b:Axis){f:θ}(p:f∈ bay K u true): P.reflectTest b f ∈ bay K (reflectedBox b 0 u) true:= aureoleBay K u true b 0 f p -- adapt
set_option maxHeartbeats 360000
lemma payable_cut (d:ℤ) (u y:Finset Cover){f b:θ} (p:P.birthF j s f)(q:P.birthF j s b)(f':f∈ A u true)(b':b∈ A y true)(U:∀ i∈ u,i k.val+ruler P.par.block*d ≤ -(ℓ:ℤ))(Vb:∀ i∈ y,(ℓ:ℤ) ≤ i k.val+ruler P.par.block*(d-1)):P.JointCuts j x (P.viewF j x s p) (P.viewF j x s q) k:=by
 have he {f:θ}(p:P.birthF j s f): f∈ enclave K:=by obtain ⟨b,rfl⟩:=p; exact b.property
 let S:= plow K k.val d u
 refine P.rectangle_cut j x s k d p q (P.criteria k.val s (P.canFlip (reflectedBox j 0 S) k.val (P.canFlip S j (P.shifts_support _ _ _ f'))) ?_ (P.mirror_keeps k.val _ (P.mirror_keeps j _ (P.shifts_keep k.val d (he p))))) (P.criteria _ _ (P.shifts_support _ _ _ b') ?_ (P.shifts_keep k.val _ (he q)))
 · intro i h; obtain ⟨z,v,w⟩:= reflect_stays k.val _ _ h; obtain ⟨z1,v1,t⟩:= reflect_stays j _ _ v; obtain ⟨g,r,rfl⟩:=plow_stays K k.val _ _ v1; rw [w,if_pos rfl,t,if_neg k.property,SlabMark.moves,if_pos rfl,mul_zero]; have hx:= U g r; change _+ℓ≤ -((g k.val + ruler P.par.block*d)) + 0; omega -- ℓ coerces
 intro i h; obtain ⟨z,v,rfl⟩:=plow_stays K k.val _ _ h; rw [SlabMark.moves,if_pos rfl,zero_add]; exact Vb z v
-- propagate world-space tests & footprints
section luggage
variable (L:List (Trans j))(e:Trans j→ℤ)
def luggage : θ→ₐ[ℂ]θ:= L.foldr (fun i (p:θ→ₐ[ℂ]θ)=> ((Ξ (i.val)) (e i)).comp p) (AlgHom.id ℂ _)
def border (u:Finset Cover):Finset Cover:= L.foldr (fun i a=> plow K i.val (e i) a) u
def massStep:= (L.map (fun i=> if i=k then e i else 0)).sum
lemma mass_cons(i:Trans j): massStep j k (i::L) e=(if i=k then e i else 0)+massStep j k L e:= List.sum_cons
lemma mass_all: massStep j k (look j) e = e k:= by
 have t(L:List (Trans j))(h:L.Nodup): massStep j k L e= if k∈L then e k else 0:= by
    induction L with| nil=> simp [massStep]| cons i L ih=> obtain ⟨p,q⟩:=List.nodup_cons.mp h; by_cases h:i=k; subst i; rw [mass_cons,ih q]; simp [p]; rw [mass_cons,ih q]; simp [h,Ne.symm h]
 rw [t _ (look_one j),if_pos (look_all j k)]
lemma ship_started (i:Trans j)(t:θ): P.luggage j (i::L) e t= (Ξ (i.val)) (e i) (P.luggage j L e t):= rfl
lemma shipping {u:Finset Cover}{f:θ}(p:f∈ A u true) : P.luggage j L e f ∈ A (P.border j L e u) true:= by induction L with| nil=>exact p| cons i L ih=> rw [show P.border j (i::L) e u= plow K i.val (e i) (P.border j L e u) from rfl, P.ship_started]; exact P.shifts_support i.val (e i) (P.border j L e u) ih
lemma certify {f:θ}(h:P.birthF j s f): P.birthF j s (P.luggage j L e f):=by induction L with|nil=>exact h|cons i L ih=>rw [P.ship_started]; exact P.passes _ s i.property (e i) ih
lemma ship_ideal {f:θ}(p:P.birthF j s f): P.viewF j x s (P.certify j s L e p)= (κ).raw L (fun i=> N s (e i)) (P.viewF j x s p):=by
 induction L with
 | nil=> exact P.identical_F _ _ _ _ _ rfl -- orient
 | cons i L ih=> rw [Alliance.raw_step,ContinuousLinearMap.comp_apply,← ih, P.registered]; exact P.identical_F _ _ _ _ _ rfl
lemma always (u:Finset Cover){x:Cover}(p:x∈ P.border j L e u): ∃ z∈u, x k.val=z k.val+ (ruler P.par.block)*massStep j k L e := by
 induction L generalizing x with
 | nil=> exact ⟨x,p,by simp [massStep]⟩
 | cons i L ih=>
     obtain ⟨y,a,rfl⟩:= plow_stays K i.val (e i) _ p; obtain ⟨z,p,t⟩:= ih a; refine ⟨z,p,?_⟩; by_cases h:i=k
     · subst i; simp only [SlabMark.moves,mass_cons,if_true,t]; change _ + ruler P.par.block*_= _; ring
     rw [SlabMark.moves, if_neg ( (fun g=> h (Subtype.ext (Eq.symm g)))),t,mass_cons,if_neg h,zero_add] -- parse
end luggage
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
