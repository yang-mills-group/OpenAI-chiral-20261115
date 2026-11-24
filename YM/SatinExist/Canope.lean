import YM.SatinExist.Climat
import YM.SatinExist.ExpressP
import YM.SatinExist.Chelo
import YM.SatinExist.Ione
/-!
 # Real stitch payments. Convergence.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3700
set_option maxHeartbeats 460000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry TopologicalSpace
namespace Spine
open Aria Casting
open _root_.YM.CF.Buffered.Afterglow.Hierarchy.Seld LineDeriv
open _root_.YM.Boundary Spectral Poin
local notation "j"=> (3:Axis)
open SatinTails SatinJets Ballad
variable (P:Spine) (x:P.Spectrum0 3) (A:ℕ→P.Apron) 
local notation "ξ"=>P.advocate 3 x j
local notation "CX"=> P.ManyF j (P.advocate 3 x j)
local notation "ν"=> P.seasons j (P.advocate 3 x j)
local notation "λ'"=> P.ColorHil j (P.advocate 3 x j)
local notation "ω"=> P.heaven j (P.advocate 3 x j)
local notation "gtW"=>P.pillar j (P.advocate 3 x j)
local notation "G"=> P.cartage j (P.advocate 3 x j)
local notation "Φ"=> Bench (P.seasons j (P.advocate 3 x j))
local notation "η"=> (P.seasons j (P.advocate 3 x j)).E
local notation "T"=> M (P.seasons j (P.advocate 3 x j))
local notation "K"=> Cache (P.seasons j (P.advocate 3 x j))
local notation "χ" i:max J:max=> (A i).pivot P J
-- moment bill with disordered Eu stamps but same script. absolute normalization
variable {n:ℕ}(B: ℕ→Fin n→P.Apron)(D:Fin n→(P.ManyF 3 (P.advocate 3 x 3)).Op)(r:Fin n→ℕ)
variable (V: ∀ k,P.Concerto x (fun i=> B i k) (r k) (D k))
-- Similar Pay on ℑ₀ product.
section Bills
variable (f:Fin n→Test4)(Ω : Bench (P.seasons 3 (P.advocate 3 x 3)))
abbrev accordC (e:ℝ≥0) (k:ℕ) := SatinJets.accord (P.seasons j (P.advocate 3 x j)) (fun i=> gtW (B k i) (-(e:ℝ)) (e:ℝ) 0) f Ω
abbrev accordsX (e:ℝ≥0) := SatinJets.accord (P.seasons j (P.advocate 3 x j)) (fun i=> plated (ν) (r:=r i) (D i) (e:ℝ)) f Ω
abbrev watchX (i:Fin n):Bench (P.seasons j (P.advocate 3 x j))→ₗ[ℂ] Bench (P.seasons j (P.advocate 3 x j)) :=ℑ (ν) (D i) (f i) (r i)
include V in
lemma goes_thinC (e:ℝ≥0)(d:0<e): pays_to (P.seasons j (P.advocate 3 x j)) atTop (P.accordC x B f Ω e) (P.accordsX x D r f Ω e) := by
 induction n with
 | zero=> exact fun _=> tendsto_const_nhds
 | succ n ih=>
    let X':=(P.seasons j (P.advocate 3 x j)); have he:=(V 0).purchase e d
    obtain ⟨g,z⟩:=he.costs
    let B'(i:ℕ):= Fin.tail (B i); have ht:= SatinJets.purchase X' _ _ he.brakes g z (f 0) (P.accordsX x (Fin.tail D) (Fin.tail r) (Fin.tail f) Ω e) _ (ih B' _ _ (show ∀ i:Fin n,P.Concerto x (fun k=>B' k i) (Fin.tail r i) (Fin.tail D i) from fun i=> V i.succ) (Fin.tail f)) 0
    have hw(a:(CX).Op)(f:Test4):ℑ X' a f 0=ℑ₀ X' a f:=by ext1 y; apply Subtype.ext; have hm:= CF.Buffered.Afterglow.Hierarchy.Seld.native X' a f y 0; rw [CF.Buffered.Afterglow.Hierarchy.Seld.home] at hm; exact hm
    simp_rw [hw] at ht; exact ht
lemma selling_price : (List.ofFn (P.watchX x D r f)).prod Ω= inCourse (ν) r D 0 f Ω:=by
 induction n with
 | zero=> rw [List.ofFn_zero]; rfl
 | succ n ih=> rw [List.ofFn_succ,List.prod_cons]
               let X':=P.watchX x D r f 0; change X' ((List.ofFn (P.watchX x (Fin.tail D) (Fin.tail r) (Fin.tail f))).prod Ω)= stove (ν) 0 (X' _); rw [ih,stove_zero]; rfl
lemma unmuzzle : pays_to (ν) (𝓝[>] (0:ℝ≥0)) (P.accordsX x D r f Ω) ((List.ofFn (P.watchX x D r f)).prod Ω) :=by
 rw [selling_price]; induction n with
 | zero=> exact fun _=> tendsto_const_nhds
 | succ n ih=>
    let f':= Fin.tail f; let D':=Fin.tail D; let r':= Fin.tail r; let Y:= inCourse (ν) r' D' 0 f' Ω; let X:= P.watchX x D r f; let T':= P.accordsX x D' r' f' Ω; let s:= r 0; let u:= 𝓝[>] (0:ℝ≥0); let S:=ν; let C':=D 0; let t:= plated S (r:=s) C';
    have he:pays_to S u (fun i:ℝ≥0=> ℑ₀ S (t i) (f 0) (T' i)) (X 0 Y):= δLimit S s t C' (f 0) Y u id tendsto_id T' (ih _ _ _) (fun e p=> by unfold t plated; simp only [Real.toNNReal_coe]) -- order
    change pays_to S u _ (stove S 0 (X 0 Y)); rw [stove_zero]; exact he
end Bills
variable (W:(Joint n)→L[ℂ] (P.ManyF 3 (P.advocate 3 x 3)).space)
include V
-- represents the ordered moment *distributions* using given CP labels on unheated fields.
structure Origami (Q:P.Ellis 3 x):Prop where
 wave (z:Points n) : AnalyticOnNhd ℂ (P.promisesC x D r z) (OrientedTimes n)
 stamps (p:Points n) (s:Equiv.Perm (Fin n))(a:ℝ)(u:DiningE (3:Axis) p s a): EuGift j (nextSeam p s) a∈ OrientedTimes n ∧ Tendsto (fun m=> P.commonWell 3 x (B m) (Vants p) (Each n)) atTop
    (𝓝 (inner ℂ ω (P.promisesC x (D∘s) (r∘s) (nextSeam p s) (EuGift j (nextSeam p s) a))))
 family (p:Joint n): Tendsto (fun t=> ∫ v:Points n, p v • P.promisesC x D r v (countM j 0 v.ofLp t)) (𝓝[Margins n] (0:Fin n→ℝ≥0)) (𝓝 (W p))
 price (f:Fin n→Test4): W (Joint.materialize n f) = ((List.ofFn (P.watchX x D r f)).prod (P.Asp x j)).val
 warms (f:Fin n→Test4) (i:Bench (ν)) (s:ℝ≥0)(t:0 < s): pays_to (P.seasons j (P.advocate 3 x j)) atTop (P.accordC x B f i s) (P.accordsX x D r f i s)
 lands (f:Fin n→Test4) (i:Bench (P.seasons j (P.advocate 3 x j))) : pays_to (P.seasons j (P.advocate 3 x j)) (𝓝[>] (0:ℝ≥0)) (P.accordsX x D r f i) ((List.ofFn (P.watchX x D r f)).prod i)
-- W.CANONICAL (independence of surveyed reps at standard units) includes detector contrast.price_same
noncomputable def juryW :(Joint n)→L[ℂ] (CX).space:= (boundary_R (ν) ω 0 D (pedestal 0 r)).choose
lemma bound_jury(Q:P.Ellis 3 x):P.Origami x B D r (P.juryW x D r) Q:=by
 let W:=P.juryW x D r; have t:= (boundary_R (ν) ω 0 D (pedestal 0 r)).choose_spec
 have he(z: Fin n → ℝ≥0)(v:z∈Margins n)(p:Points n) : P.promisesC x D r p (countM j 0 p.ofLp z)=regia (ν) ω 0 (slew (ν) (pedestal 0 r) z) D p:= conducts _ _ _ _ _ _ v
 refine ⟨fun p=>wave_h (ν) ω _ _ _, fun p s a h=>⟨EuGift_ready _ _ _ h,P.reading_C x B D r V p s Q a h⟩,?_,?_, P.goes_thinC x B D r V,P.unmuzzle x D r⟩
 · intro N; apply (t N).congr'; filter_upwards [self_mem_nhdsWithin] with z h; simp only [he _ h, wishL_eq,regia_bill]
 intro f; rw [selling_price]; exact computes (ν) (P.Asp x j) (P.transportsK x j) _ _ _ W t
-- certify actual with same W. mixed pose compatibility.
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
