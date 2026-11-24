import YM.SU5.Aria.Wings
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
local notation "Φ" => P.colorSpace j x
local notation "ω"=>P.colorZero j x
local notation "X"=> P.ColorHil j x
local notation "Χ"=> P.ManyF j x
local notation "ν"=> P.seasons j x
local notation "ψ"=> P.physicalEnergy j x
local notation "Ω"=> P.heaven j x
local notation "E"=> (P.seasons j x).E
local notation "T" r:max=> Real.toNNReal r
local notation "W"=> P.cartage j x
local notation "V"=> P.tableau j x
local notation "ρ"=> P.wealth j x
local notation "κ"=> P.enter j x
variable {I A: Type*}[TopologicalSpace A]
private lemma strongJoint {H : Hilbert}(p:A→H.Op)(q:A→H)(t:Continuous q)(y:∀ x:H, Continuous (fun i=>p i x))(C:ℝ)(c:0≤C)(g:∀ i, ‖p i‖≤C) : Continuous (fun i=>p i (q i)):= continuous_iff_continuousAt.mpr fun x=> firmly p c (Eventually.of_forall g) (y _|>.continuousAt) (t.continuousAt)
lemma caravan (p:A→Vantage)(y:A→Χ)(t:Continuous p)(u:Continuous y): Continuous (fun v=> W (p v) (y v)):= strongJoint (fun i=>W (p i)) y u (fun i=>(P.cart_cont ..).comp t) _ zero_le_one (fun i=> P.cart_pay j x _)
lemma tablets (B:(X).Op)(p:A→Vantage)(y:A→Χ)(t:Continuous p)(u:Continuous y): Continuous (fun i=> V (p i) B (y i)):=by
 let G:=(ρ).comp (B.comp ((κ).toContinuousLinearMap)); have h:Continuous (fun i=>G (W (-p i) (y i))):=G.continuous.comp (P.caravan j x (fun i=>-p i) y t.neg u); exact P.caravan j x p (fun i=>_) t h
variable (B:I→ P.Apron)(p:I→Vantage)(L:List I)
local notation "a" p:max=> P.porchY j B p
local notation "b" p:max=> P.resignY j B p
local notation "Ψ" p:max=> P.memorial j x B L p
lemma follows_real (y:A→I→Vantage)(z:A→ℝ)(H:A→Χ)(u:Continuous y)(h:Continuous z)(v:Continuous H):
    Continuous (fun i=>rector (ν) (P.commuteTight j x B (y i)) (a (y i)) (b (y i)) L (z i) (H i)):=by
 induction L generalizing z with
 | nil=>exact v
 | cons i l ih=>
   let E₀(k:ℝ≥0):=E k; let p'(v:A):= (a (y v)) i; let q(v:A):=(b (y v)) i
   have hp:Continuous (fun v=>y v i):= (continuous_apply i).comp u; have hk: Continuous (fun v=>y v i j):=(continuous_apply j).comp hp
   let g(v:A):= (T (p' v-z v))
   have hv: Continuous g:= continuous_real_toNNReal.comp ((show Continuous p' from hk.sub continuous_const).sub h)
   have ht: Continuous q:= hk.add continuous_const
   let D(v:A):=(rector (ν) (P.commuteTight j x B (y v)) (a (y v)) (b (y v)) l (q v) (H v))
   let S(v:A):=V (y v i) ((B i).engine P j x) (D v)
   exact strongJoint (fun x=> E₀ (g x)) S (P.tablets j x _ _ _ hp (ih q ht)) (fun t=> ((ν).continuousE t).comp hv) 1 zero_le_one (fun _=> (ν).shrinks ..)
lemma full_continuity : Continuous (P.memorial j x B L):=by
 -- start clock 0, equality even in preparatory `e's` unqualified. continuity independent E time ordering. no semantics there!
 let f(y:I→ Vantage):= rector (ν) (P.commuteTight j x B y) (a y) (b y) L 0 Ω; have ht:Continuous f:=P.follows_real j x B L (fun v=>v) (fun _=>0) (fun _ => Ω) continuous_id continuous_const continuous_const; -- syntax
 rw [show P.memorial j x B L=(fun v=> inner ℂ Ω (f v)) from funext fun i=>(rector_view (ν) Ω _ _ _ (P.heaven_hot j x) 0 L).symm]; exact continuous_const.inner ht
lemma order_neighborhood (u:P.Turnstile j B L p): ∀ᶠ s in 𝓝 p,P.Turnstile j B L s:=by
 classical
 obtain ⟨ε,h,t⟩:= P.shelter_frame j B L p u; have g:∀ᶠ x in 𝓝 p,∀i∈ L.toFinset,dist (x i) (p i)<ε:= (L.toFinset.eventually_all).mpr (fun i _=>Metric.tendsto_nhds.mp ((continuous_apply i).tendsto p) ε h) -- args
 exact g.mono (fun i v=> t _ (fun j k=> v j (List.mem_toFinset.mpr k)))
-- Cartesian translation
abbrev settler (x:Vantage)(i:I) : Vantage:=x+p i
lemma settler_time (x:Vantage):∀ i,(a (settler p x)) i=x j+(a p) i∧ (b (settler p x)) i=x j+(b p) i:=fun i=>by simp only [porchY,resignY,Apron.time_panel,Apron.time_edge,settler,Pi.add_apply]; constructor<;>abel
lemma settler_order (t:P.Turnstile j B L p)(v:Vantage):P.Turnstile j B L (settler p v):=by apply t.imp; intro i k h; rw [(P.settler_time j B p v i).2,(P.settler_time j B p v k).1]; linarith
lemma warm_drive (r:Vantage)(t:ℝ≥0)(y:Χ): E t (W r y)= W r (E t y):=by rw [P.uses_cart]; exact DFunLike.congr_fun ((ν).independent ..) y
lemma cart_independent (r s:Vantage)(B:(X).Op)(i:Χ): V (r+s) B (W r i)= W r (V s B i):=by
 unfold tableau; simp only [ContinuousLinearMap.comp_apply,P.cart_paves]; -- perhaps LHS −(r+s) can rewrite
 rw [←ContinuousLinearMap.comp_apply (W (-(r+s))), ← P.cart_paves, show -(r+s)+r= -s by abel]
lemma inner_pay (p:Vantage)(u v:Χ): inner ℂ (W p u) (W p v) = inner ℂ u v:= LinearIsometry.inner_map_map (𝕜:=ℂ) (show (Χ).space →ₗᵢ[ℂ] (Χ).space from { (W p).toLinearMap with norm_map':=P.cart_norm j x p}) u v
lemma settler_rect (z q:ℝ)(r:Vantage)(y:Χ): rector (ν) (P.commuteTight j x B (settler p r)) (a (settler p r)) (b (settler p r)) L (r j+z) (W r y)= W r (rector (ν) (P.commuteTight j x B p) (a p) (b p) L z y):=by
 induction L generalizing z with
 | nil=> rfl
 | cons i L ih=> rw [rector_left,rector_left,(P.settler_time j B p r i).1,(P.settler_time j B p r i).2, add_sub_add_left_eq_sub]; simp only [ContinuousLinearMap.comp_apply,ih,P.warm_drive,commuteTight,settler,P.cart_independent] -- order tactic
lemma settler_def(t:P.Turnstile j B L p)(r:Vantage): Ψ (settler p r)= Ψ p:= by
 let v:= rector (ν) (P.commuteTight j x B (settler p r)) (a (settler p r)) (b (settler p r)) L (r j+0)
 have hz: Ψ (settler p r)=inner ℂ Ω (v Ω):=(rector_view (ν) Ω _ _ _ (P.heaven_hot j x) _ _).symm
 rw [hz]; conv_lhs=> rw [← P.cart_empty j x r]; unfold v; rw [P.settler_rect j x B p L 0 0]
 rw [P.inner_pay,rector_view (ν) Ω _ _ _ (P.heaven_hot j x) 0 L]; rfl

variable (J:P.Ellis j x)
/-- local atlas on all moment domains w/ at least ONE time-rectification of the word. Can report correlators & spatially continuous reconstruction here, though these are time-spreads, not Wightman fields & no claim about points outside these. -/
def Federation : Set (I→ Vantage):= {p | ∃ (y:Axis)(t:List I),L.Perm t∧ P.Turnstile y B t p}
lemma ballots{x:I→ Vantage}: x∈P.Federation B L ↔ ∃ (y:Axis)(t:List I),L.Perm t∧ P.Turnstile y B t x:= Iff.rfl
lemma federation_neighborhoods: IsOpen (P.Federation B L):= by refine isOpen_iff_mem_nhds.mpr fun p h=> ?_; obtain ⟨y,t,a₀,h⟩:=h; refine (P.order_neighborhood y B p t h).mono ?_; intro z b' ; exact ⟨_,_,a₀,b'⟩ -- a notation
-- paste on open supports. Nothing about boundary from this definition.
open scoped Classical
noncomputable def commonWell : ℂ:= if h:p∈P.Federation B L then
 let f:=P.ballots B L|>.1 h; let i:= f.choose; P.memorial i (P.advocate j x i) B f.choose_spec.choose p
 else 0
include J
lemma common_cult {y:Axis}{t:List I}(e:L.Perm t)(v:P.Turnstile y B t p): P.commonWell j x B p L=P.memorial y (P.advocate j x y) B t p:=by
 let h:p∈P.Federation B L:= (P.ballots B L).2 ⟨y,t,e,v⟩; let f:= (P.ballots B L).1 h
 rw [commonWell,dif_pos h]; exact P.unanimous j x B f.choose_spec.choose p f.choose y t f.choose_spec.choose_spec.2 v (f.choose_spec.choose_spec.1.symm.trans e) J
/-- independent of JITTER choice (it only conditioned passage and doesn't appear on RHS). -/
lemma common_cont (v:p∈P.Federation B L): ContinuousAt (fun q=> P.commonWell j x B q L) p:=by
 obtain ⟨y,t,e,s⟩:=v
 apply (P.full_continuity y (P.advocate j x y) B t).continuousAt.congr; filter_upwards [P.order_neighborhood y B p t s] with q u; exact (P.common_cult j x B q L J e u).symm
lemma common_perm {t}(v:p∈P.Federation B L)(f:L.Perm t):p∈P.Federation B t ∧ P.commonWell j x B p L=P.commonWell j x B p t:=by
 obtain ⟨i,k,e,h⟩:=v; exact ⟨⟨i,k,f.symm.trans e,h⟩,(P.common_cult j x _ _ _ J e h).trans (P.common_cult j x _ _ _ J (f.symm.trans e) h).symm⟩
lemma common_shift(p':p∈P.Federation B L)(v:Vantage):settler p v∈P.Federation B L∧ P.commonWell j x B (settler p v) L=P.commonWell j x B p L:=by
 obtain ⟨i,t,e,h⟩:=p'; have hv:=P.settler_order i B p t h v; refine ⟨⟨_,_,e,hv⟩,?_⟩; rw [P.common_cult j x _ _ _ J e h,P.common_cult j x _ _ _ J e hv,P.settler_def i _ B p t h]
lemma common_mirror (y:Axis)(t : p∈ P.Federation B L) : resizeMirror y p∈P.Federation (P.veilMirror B y) L∧
    P.commonWell j x (P.veilMirror B y) (resizeMirror y p) L=star (P.commonWell j x B p L):=by
 obtain ⟨i,v,e,t⟩:=t; rw [P.common_cult j x B p L J e t]; rcases eq_or_ne y i with rfl|h
 · have ht:v.reverse.Perm L:=v.reverse_perm.trans e.symm; have hp:=P.tempestOrder y B p v t; exact ⟨⟨_,_,ht.symm,hp⟩,(P.common_cult j x _ _ _ J ht.symm hp).trans (P.tempest_solution y (P.advocate j x y) B p v t)⟩
 let k:Trans i:=⟨y,h⟩; have hk: P.Turnstile i (P.veilMirror B y) v (resizeMirror y p):=P.wingOrder i k B p v t
 exact ⟨⟨i,v,e,hk⟩,(P.common_cult j x _ _ _ J e hk).trans (P.wing_solution i _ k B p v t)⟩
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.common_mirror
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.common_cont
