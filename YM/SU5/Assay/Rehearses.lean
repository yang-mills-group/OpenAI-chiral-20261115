import YM.SU5.Assay.CharterCost
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4900
set_option maxHeartbeats 420000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
open Aria Set OS.Semigroup
variable (P:Spine)(j:Axis)(x:P.Spectrum0 j)
local notation "K"=> P.calibration
local notation "H"=> P.ColorHil j x
local notation "B"=> P.ManyF j x
local notation "X"=> (P.ColorHil j x).Op
local notation "Y"=> (P.ManyF j x).Op
local notation "Lag"=>ℝ→ℝ→(P.ManyF j x).Op
local notation "S"=> P.seasons j x
local notation "U"=> P.physicalEnergy j x
local notation "ω"=> (P.seasons j x).wax
local notation "W"=> P.cartage j x
local notation "θ"=> P.tableau j x
local notation "E"=> P.enter j x
local notation "R"=> P.wealth j x
local notation "Vac"=> P.colorZero j x
local notation "Ω"=> P.heaven j x
variable {I:Type*}
/-!
 `Rehearses` : tested on continuous-space inputs **but not compressing
 outputs**, with uniform bound otherwise. Includes adjoints. Thus allows
 compositions directly in price space.
-/
structure Rehearses (a:I→X)(l:Filter I)(T:Y):Prop where
 ceiling: ∃ C:ℝ,0≤C∧∀ᶠ i in l,‖a i‖≤ C
 shows: ∀u:B,Tendsto (fun i=>a i (E u)) l (𝓝 (E (T u)))
 back: ∀u:B,Tendsto (fun i=> star (a i) (E u)) l (𝓝 (E (star T u)))
variable {P j x}{l:Filter I}{a b:I→(P.ColorHil j x).Op}{T M:(P.ManyF j x).Op}
namespace Rehearses
variable (p:P.Rehearses j x a l T)
include p
lemma flanks: BSOT (fun i=> P.reprise j x (a i)) l T:= P.reprise_receipt j x p.ceiling p.shows p.back
lemma unique [NeBot l](q:P.Rehearses j x a l M):T=M:=p.flanks.unique q.flanks
-- Moving v:H, its limit in the subspace
lemma apply' {u:B}{v:I→H}(h:Tendsto v l (𝓝 (E u))):Tendsto (fun i=>a i (v i)) l (𝓝 (E (T u))):=by
 obtain ⟨C,t,z⟩:=p.ceiling; exact firmly a t z (p.shows _) h
lemma dagger : P.Rehearses j x (fun i=>star (a i)) l (star T):=by
 refine ⟨?_,p.back,?_⟩
 · obtain ⟨C,u,v⟩:=p.ceiling; exact ⟨C,u,v.mono fun i t=> (norm_star _).trans_le t⟩
 simp only [star_star]; exact p.shows
lemma congr' (h:a=ᶠ[l] b):P.Rehearses j x b l T:=by
 obtain ⟨C,u,v⟩:=p.ceiling
 exact ⟨⟨C,u,(h.and v).mono fun _ z=>(congrArg norm z.1.symm).trans_le z.2⟩,
  fun i=>(p.shows i).congr' (h.mono fun _ z=> congrArg (fun x:X=>x (E i)) z),
  fun i=>(p.back i).congr' (h.mono fun _ z=>congrArg (fun x:X=>star x (E i)) z)⟩
lemma visit {J:Type*}{k:Filter J}{f:J→I}(h:Tendsto f k l):P.Rehearses j x (fun i=>a (f i)) k T:=by
 obtain ⟨C,u,v⟩:=p.ceiling
 exact ⟨⟨C,u,h.eventually v⟩,fun _=>(p.shows _).comp h,fun _=>(p.back _).comp h⟩
lemma price : Tendsto (fun i=>inner ℂ (Vac) (a i (Vac))) l (𝓝 (inner ℂ Ω (T Ω))):=by
 have u:= P.bank_inner j x Ω (E (T Ω)); rw [P.reprise_empty] at u
 rw [u];exact (tendsto_const_nhds (x:=Vac)).inner (p.shows Ω)
lemma mul (q:P.Rehearses j x b l M):P.Rehearses j x (fun i=>a i*b i) l (T*M):=by
 obtain ⟨C,v,h⟩:= p.ceiling; obtain ⟨D,r,u⟩:= q.ceiling
 refine ⟨⟨C*D,by positivity,(h.and u).mono fun i z=>(norm_mul_le ..).trans (mul_le_mul z.1 z.2 (norm_nonneg _) v)⟩,
   fun i=>p.apply' (q.shows i),?_⟩
 intro i; simp only [star_mul]; exact q.dagger.apply' (p.back i)
lemma add(q:P.Rehearses j x b l M):P.Rehearses j x (fun i=>a i+b i) l (T+M):=by
 obtain ⟨C,v,h⟩:= p.ceiling; obtain ⟨D,r,u⟩:= q.ceiling
 refine ⟨⟨C+D,by positivity,(h.and u).mono fun i z=>(norm_add_le ..).trans (add_le_add z.1 z.2)⟩,
   fun i=>?_,?_⟩
 · rw [add_apply,map_add];exact (p.shows i).add (q.shows i)
 intro i; simp only [star_add,add_apply,map_add]; exact (p.back i).add (q.back i)
omit p in
lemma falls (q:BSOT b l 0):P.Rehearses j x b l 0:=by
 refine ⟨q.ceiling,fun i=>?_,fun i=>?_⟩
 · simpa using q.showAt (E i)
 simpa using q.starAt (E i)
lemma squeeze' {d:I→ℝ}(q: Tendsto d l (𝓝 0))(h:∀ᶠ i in l, ‖b i-a i‖ ≤ d i):P.Rehearses j x b l T:=by
 have ht:BSOT (fun i=>b i-a i) l (0:X):=BSOT.fromNorm (by
    rw [tendsto_iff_norm_sub_tendsto_zero]; simp only [sub_zero]
    exact squeeze_zero' (Eventually.of_forall fun _=>norm_nonneg _) h q)
 have t:= (falls ht).add p;simpa only [sub_add_cancel,zero_add] using t
end Rehearses
-- Through alignment chamber
lemma truck_shows {f:I→P.VMark}{y:Vantage}(p:Tendsto (P.laysM ∘ f) l (𝓝 y)):
 ∀u:B,Tendsto (fun i=>P.truck j x (f i) (E u)) l (𝓝 (E (W y u))):=by
 intro u
 simp only [P.cart_and]
 exact (E).continuous.continuousAt.tendsto.comp ((P.cart_pin' j x p).showAt u)
lemma truck_rehearses {f:I→P.VMark}{y:Vantage}(p:Tendsto (P.laysM ∘ f) l (𝓝 y)):
 P.Rehearses j x (fun i=>P.truck j x (f i)) l (W y):=by
 refine ⟨⟨_,zero_le_one,Eventually.of_forall (fun _=> P.truck_pay ..)⟩,truck_shows p,?_⟩
 simp only [P.truck_dagger,P.cart_star]
 exact truck_shows (f:=fun i=>-f i) p.neg
lemma charter_rehearses {f:I→P.VMark}{y:Vantage}(p:Tendsto (P.laysM ∘ f) l (𝓝 y))
 (q:P.Rehearses j x a l T):P.Rehearses j x (fun i=>P.charter j x (f i) (a i)) l (P.locate j x y T):=by
 simp_rw [P.charter_eq]
 exact ((truck_rehearses p).mul q).mul (truck_rehearses (f:=fun i=> -f i) p.neg)
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
