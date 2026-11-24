import YM.SU5.Aria.Piffle
import YM.SU5.Aria.Serves
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
open Aria Set TopologicalSpace Metric Casting
local notation "Λ"=> P.par
local notation "K"=> P.calibration
local notation "H"=> P.large
local notation "Y"=> P.run
local notation "b₀"=>ruler P.par.block
local notation "Φ" => P.colorSpace j x
local notation "ω"=>P.colorZero j x
local notation "X"=> P.ColorHil j x
local notation "Θ" j:max=> P.reflectTest j
local notation "Γ"=> P.VMark
variable (k:Trans j)
namespace Apron
variable (D:P.Apron)
def kiss : P.Apron where
 s:= D.s
 F:=(Θ j) D.F
 S:=Tower.reflectedBox j 0 D.S
 u:=D.u
 pos:=D.pos
 bay:=aureoleBay K _ true j 0 D.F D.bay
 realM:=P.mirror_keeps j _ D.realM
 shelter i:=by
   by_cases h:i=j
   · subst i; have hx: Between K j (2*0-b₀ * (D.u j)) (2*0 - (- b₀* (D.u j))) (Tower.reflectedBox j 0 D.S):= (D.shelter j).mirror K j 0; simpa only [mul_zero,zero_sub,neg_mul,neg_neg] using hx
   intro q y; obtain ⟨q,p,x⟩:=SlabMark.reflect_stays j 0 D.S y; rw [x,if_neg h]; exact D.shelter i q p
lemma kiss_width (j':Axis): (D.kiss P j).realWidth P j'=D.realWidth P j':=rfl
end Apron
local notation "k'"=> k.val
local notation "κ"=> P.calibration
variable (n w:ℕ)
local notation "ϕ" v:max=>P.voxTest j n v
lemma entry_wings (f:P.Card j n w):∃ g:P.Card j n w, (Θ k') (ϕ f.val)=ϕ g.val:=by
 obtain ⟨S,u,d⟩:= f.property; let F:= (Θ k') (ϕ f.val); let T:=reflectedBox k' 0 S
 have hw:F∈ bay K T true:= aureoleBay K S true k.val 0 (ϕ f.val) u; have h:Between K j 0 (b₀*(w:ℤ)) T:= fun i p=>by obtain ⟨i,z,y⟩:= SlabMark.reflect_stays k.val 0 S p; rw [y,if_neg (Ne.symm k.property)]; exact d i z
 exact ⟨(⟨P.positiveVox j n T F hw (fun q z=> (h _ z).1),T,hw,h⟩:P.Card j n w),rfl⟩
lemma crew_flies {z:P.Test}(h:P.birthF j n z): P.birthF j n ((Θ k') z):=by
 let f:=P.emmigrant j n h; obtain ⟨v,pv,g,t⟩:= P.fits j n f.val; obtain ⟨b,hb⟩:= P.entry_wings j k n v g
 have he:ϕ g.val=z:=(congrArg (P.voxTest j n) t).trans (P.documented j n h)
 have hg:ϕ b.val∈enclave K:= hb ▸ P.mirror_keeps k.val 0 (show ϕ g.val∈enclave K from t ▸ f.property)
 rw [←he,hb]; exact P.admitted_view j n b hg
abbrev Partner := Σ n:ℕ, {x:P.Test // P.birthF j n x}
def oneSide (t:P.Partner j): P.ColorHil j x:= P.viewF j x t.1 t.2.property
def turnξ (t:P.Partner j): P.Partner j := ⟨t.1,(Θ k') t.2.val,P.crew_flies j k t.1 t.2.property⟩
local notation "Σq"=> P.Partner j
local notation "σ"=> P.oneSide j x
local notation "ε"=> P.turnξ j k
lemma partner_dense: Dense (Submodule.span ℂ (Set.range (P.oneSide j x)) : Set X):= by
 apply (P.native_dense j x).mono (SetLike.coe_mono (Submodule.span_mono _)); rintro y e; rcases Set.mem_iUnion.mp e with ⟨s,h⟩; rcases h with ⟨v,rfl⟩; have t:P.birthF j s (P.voxTest j s v.val):= ⟨v,rfl⟩; let z: P.Partner j:=⟨s,P.voxTest j s v.val,t⟩; exact ⟨z,P.holdsF j x s t v rfl⟩ -- apply _ generates
lemma ratchet (u v:Σq): inner ℂ (P.oneSide j x (P.turnξ j k u)) (P.oneSide j x (P.turnξ j k v))=star (inner ℂ (P.oneSide j x u) (P.oneSide j x v)):=by
 rcases u with ⟨a,u,hu⟩; rcases v with ⟨b,v,hv⟩; let n:=max a b; have hx:a ≤ n:=le_max_left ..; have he:b ≤ n:=le_max_right ..
 have vs(a:ℕ)(t:a ≤ n)(u:P.Test)(hu:P.birthF j a u): P.viewF j x a (P.crew_flies j k a hu)=P.viewF j x n (P.crew_flies j k n (P.rig j a n hu t)):= (P.view_rig j x a n (P.crew_flies j k a hu) t).symm.trans (P.identical_F j x n _ _ (P.reflUp a n k.val u)) -- ? meta implicit
 let T:= (Θ k')
 let X':=P.conveying a (n-a) u; let Y':=P.conveying b (n-b) v; have hy: (Θ j) (T X')*T Y'=T ((Θ j) X'*Y'):=by rw [show (Θ j) (T X')=T ((Θ j) X') from evenTurn ..]; exact (aureoleProduct ..).symm
 change inner ℂ (P.viewF j x a (P.crew_flies j k a hu)) (P.viewF j x b (P.crew_flies j k b hv))= star (inner ℂ (P.viewF j x a hu) (P.viewF j x b hv)); rw [vs a hx u hu, vs b he v hv,← P.view_rig j x a n hu hx,← P.view_rig j x b n hv he,P.released_gram,P.released_gram]; change P.singleState j n x _=star (P.singleState j n x ((Θ j) X'*Y')); rw [hy]; let z:=(Θ j) X'*Y'
 exact (congrArg (P.chi j x) ((P.star_agrees j k.val n z).symm.trans (P.reading_star j n z).symm)).trans (map_star ..)
lemma anti_world : ∃ U: Muse X,(∀ i,U (σ i)=σ (ε i)) ∧ (∀ b:X,U (U b)=b) ∧ (∀ b:X, ‖U b‖=‖b‖) ∧ (∀ b c:X, inner ℂ (U b) (U c)=star (inner ℂ b c)):= by
 apply Aria.poetry (P.oneSide j x) (P.oneSide j x∘ P.turnξ j k) (P.partner_dense j x) (P.ratchet j x k) (P.turnξ j k) rfl; rintro ⟨n,b,t⟩; exact P.identical_F j x n _ _ (aureoleTwice K k.val 0 b)
noncomputable def blade : Muse (P.ColorHil j x):= (P.anti_world j x k).choose
local notation "B"=> P.blade j x k
lemma blade_view {f:P.Test}(p:P.birthF j n f): B (P.viewF j x n p)= P.viewF j x n (P.crew_flies j k n p):= (P.anti_world j x k).choose_spec.1 ⟨n,f,p⟩
lemma blade_twins (a:X): B (B a)=a:= (P.anti_world ..).choose_spec.2.1 _
lemma blade_norm (a:X): ‖B a‖=‖a‖:= (P.anti_world ..).choose_spec.2.2.1 _
lemma blade_angle (a b:X): inner ℂ (B a) (B b)=star (inner ℂ a b):= (P.anti_world ..).choose_spec.2.2.2 a b
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.anti_world
