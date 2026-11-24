import YM.SatinExist.Poisons
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
set_option maxHeartbeats 340000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open _root_.YM.SatinExist Lancet
namespace Spine
open Six Xara Aria Casting
variable (P:Spine)(x:P.Spectrum0 3)(j:Axis)(s:ℕ)
local notation "K"=> P.calibration
local notation "Y"=> P.run
local notation "H"=> P.large
local notation "Φ"=> P.singleState 3 s x
local notation "Λ"=> P.par
local notation "R"=> P.par.R.L.val
local notation "ℓ"=> P.calibration.ℓ
local notation "M" F:max G:max => P.duoMask s F G
variable (D:P.Test→ₗ[ℂ] ℂ) (h:Comparison P.calibration (P.singleState 3 (s+1) x) D)
abbrev Inordinate (s:ℕ)(X:P.Test→ₗ[ℂ]ℂ)(F G:P.Test):= X (P.duoMask s F G) ≠ P.singleState 3 s x (F*G) ∧ P.singleState 3 s x (F*G)≠0
local notation "sc" x:max=> P.shifts j x
variable (S T:Finset Cover) (F G:P.Test)(k:ℤ){U V:Finset Axis} (p:F∈bay P.calibration S true)(q:G∈bay P.calibration T true)(e:0≤k)(t:Punctus (P:=P) false U k S)(v:Punctus (P:=P) true V k T)(f:P.Inordinate x s D F G)
include h j t v p q f e
lemma welcomeFwd : ∃ᶠ i:ℕ in atTop, P.Inordinate x s D F ((sc (i:ℤ)) G):=by
 let u(i:ℕ):= (sc (i:ℤ)) G; let l(i:ℕ):= D (P.duoMask s F (u i)); let g(i:ℕ):= Φ (F*u i)
 let y:=(P.seasonFwd x j s D h F G k p q e t v); have hg: ChargesX g:=by
    let T:=P.company x j s S T F G p q e t v 1 zero_lt_one; simpa only [one_mul,g] using T
 have hz:l 0 ≠ g 0 ∧ g 0≠0:=by unfold l g u; simp only [Nat.cast_zero,P.shifts_zero]; exact f
 refine ((ChargesX.migrate ((ChargesX.sub (f:=l) y hg).mul hg) (mul_ne_zero (sub_ne_zero.mpr hz.1) hz.2))).mono (fun i hi=>?_)
 exact ⟨sub_ne_zero.mp (left_ne_zero_of_mul hi),right_ne_zero_of_mul hi⟩
lemma welcomeBack : ∃ᶠ i:ℕ in atTop, P.Inordinate x s D ((sc (-(i:ℤ))) F) G:=by
 refine (welcomeFwd P x j s D h S T F G k p q e t v f).mono ?_
 intro i g
 let z:=-(i:ℤ); have ht : Φ ((sc z) F* G) = Φ (F* (sc (-z)) G):=by rw [← P.stamp_title x s j (-z) ((sc z) F*G),map_mul,P.shifts_sum,neg_add_cancel,P.shifts_zero]
 unfold Inordinate; rw [P.seasonTrade x j s D h, ht]; unfold z; rw [neg_neg]; exact g
omit v t j
variable (t':Punctus (P:=P) false ∅ k S)(v':Punctus (P:=P) true ∅ k T)
abbrev clothesM (D:List (Axis×ℤ)) (F:P.Test) :P.Test := D.foldr (fun i X=> P.shifts i.1 i.2 X) F
omit h p q f e
lemma paperC (D:List (Axis×ℤ)) (F:P.Test)(p:F∈bay P.calibration S true): P.clothesM D F ∈ bay K (P.zoneCost S D) true:=by
 induction D with|nil=> exact p|cons i L h=> exact P.shifts_support i.1 i.2 _ h
lemma pureCloth (L:List (Axis×ℤ)) (p:PureMatter K F) : PureMatter K (P.clothesM L F):=by induction L with|nil=> exact p|cons i L h=> exact P.copyIndependent i.1 h i.2
lemma cloth_enc (L: List (Axis×ℤ)) (p:F∈enclave K) : P.clothesM L F∈ enclave K:=by induction L with|nil=> exact p|cons i L h=> exact P.shifts_keep i.1 _ h
include t' v' h p q f e
local notation "D_" L:max m:max=> P.Inordinate x s D (P.clothesM L F) (P.clothesM m G)
lemma transplant : ∃ L L':List (Axis×ℤ), D_ L L' ∧ Punctus (P:=P) true Finset.univ k (P.zoneCost T L') ∧ Punctus (P:=P) false Finset.univ k (P.zoneCost S L):=by
 suffices h:∀ A:Finset Axis, ∃ L L', D_ L L' ∧ Punctus (P:=P) true A k (P.zoneCost T L') ∧ Punctus (P:=P) false A k (P.zoneCost S L) from h _
 intro A; induction A using Finset.induction_on with
 | empty=> exact ⟨[],[],f,v',t'⟩ -- tune
 | @insert i B g ih=>
    obtain ⟨L,Yb,u,Tb,tb⟩:= ih
    obtain ⟨n,t₀,f⟩:= ((P.recoil_area i k tb).and_frequently (P.welcomeBack x i s D h _ _ _ _ k (P.paperC S L F p) (P.paperC T Yb G q) e tb Tb u)).exists
    let L':=(i,-(n:ℤ))::L
    obtain ⟨i₀,x,g'⟩:= ((P.stroll_area i k Tb).and_frequently (P.welcomeFwd x i s D h _ _ _ _ k (P.paperC S L' F p) (P.paperC T Yb G q) e t₀ Tb f)).exists
    exact ⟨L',(i,(i₀:ℤ))::Yb,g',x,t₀⟩
#print axioms transplant
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
