import YM.SU5.Registration.Rasp.Several
import YM.SU5.Registration.Heave.BigDrum
/-!
# Managing linear combinations of coherent stencils over every character

Use `ClearScore`, a symbol approximated over ALL γ in operator norm, eventually
for index there after requesting a strictly positive t (and any tolerance).
Requests that estimate on the whole display operator, not each factor
in a Mark product. As in `Rasp.Sponsor`, extends Passport capability.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 400000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open Spine
open CF.Velvet CF.Pannier.Chancel
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel
open SatinNucleus Six DoseTravel Set
open SatinRegistration
namespace Spine
variable (P:Spine)
-- geometry ANY axes
local notation "Χ"=>P.Spectrum0
local notation "Θ"=>P.advocate 3
local notation "E₀"=>P.ColorHil
local notation "H₀"=>P.ManyF
local notation "qz"=>P.wealth
local notation "S₀"=>P.seasons
variable (x:P.Spectrum0 3)(a:Axis)
local notation "ξ"=>Θ x a
local notation "S"=>(P.seasons a (P.advocate 3 x a))
local notation "H"=>(P.ColorHil a (P.advocate 3 x a))
local notation "G"=>(P.ManyF a (P.advocate 3 x a))
local notation "pc"=>P.cartage a (P.advocate 3 x a)
local notation "T₀"=> (S).E
local notation "Ω"=> P.heaven a ξ
local notation "T"=> timeMesh P.par
open Swatch
local notation "τ" p:max=> Real.toNNReal (p:ℝ)
local notation "GOp" x:max=> (P.ManyF a (P.advocate 3 x a)).Op
local notation "Θ'" x:max=> P.seasons a (P.advocate 3 x a)
local notation "Φ"=>P.Spectrum0 3
variable {J:Type*}(K:Set P.Swatch)
open Swatch Aria Casting
local notation "μ"=> P.Stunt
-- symbol corner routines
lemma yearly_cap (A:ℕ→ P.Apron)(u:(ordinary A).WPermit x 3): P.CapReady x A:=by
 refine ⟨fun j=>?_,fun t p=>?_,?_⟩
 · simp_rw [Apron.width_real]; exact NNReal.tendsto_coe.mpr (u.thin j)
 · have h:=u.convergence t p; intro i; simp only [Wstage,ordinary,one_smul] at h; simp_rw [manage,P.honestBridge]; exact h i
 obtain ⟨k,C,e,p⟩:= u.budget; refine ⟨k,C,e,fun t h v=>?_⟩; simp_rw [manage,P.honestBridge]; simpa only [Wstage,ordinary,one_smul] using p t h v
-- Link versions
lemma ordinary_paper (A:ℕ→ P.Apron)(s t:ℝ≥0)(i:ℕ): (ordinary A).Wstage x a s t i=P.stageG a ξ (A i) s t:= one_smul ..
lemma ordinary_kiss (A:ℕ→P.Apron) : (ordinary A).turn a= ordinary (fun i=> (A i).kiss P a):=by unfold Swatch.turn ordinary; rw [funext (f:=fun _ :ℕ => star (1:ℂ)) (g:=fun _=>1) (fun _=>star_one ℂ)] -- check `star_one`

-- heat-stove motion cost
lemma Commission.wander (A:P.Swatch)(p:P.Commission a A)(t:ℝ≥0)(z:0<t){u v:ℕ→ℝ≥0}(e:Tendsto u atTop (𝓝 t))(f:Tendsto v atTop (𝓝 t)): SatinRegistration.Agrees atTop (fun i x=> A.Wstage x a (u i) (v i) i) (fun i x=> A.Wstage x a t t i):=by
 let d:= t/2; have he:d<t:= half_lt_self z; have hd:0<d:= half_pos z; let B(x):=P.seasons a (P.advocate 3 x a); let X(i:ℕ)(x):= A.Wstage x a d d i; let Y(i:ℕ)(x):= (B x).E (t-d);
 let F(i:ℕ)(x):=(B x).E (u i-d); let U(i:ℕ)(x):=(B x).E (v i-d)
 have hb:= p.threshold d hd; have hg:SatinRegistration.Agrees atTop F Y:= same_heat B (tsub_pos_of_lt he) (e.sub_const _); have hZ:SatinRegistration.Agrees atTop U Y:= same_heat B (tsub_pos_of_lt he) (f.sub_const _)
 have hh := (p.being a).eventually (ge_mem_nhds hd); have hT := OnTab.keeps1 B (s:=atTop) (fun i=>u i-d)
 refine (SatinRegistration.of_eq (Y:=F*X*U) (?_)).trans ((((hg.prod (Agrees.refl X) hT hb).prod hZ (hT.prod hb) (OnTab.keeps1 B _))).trans (Agrees.symm (SatinRegistration.of_eq (?_ : _=ᶠ[atTop] Y*X*Y)))) -- unicode notation may coll.
 · filter_upwards [hh,e.eventually (le_mem_nhds he),f.eventually (le_mem_nhds he)] with i h v w; exact funext fun x=> A.Wstage_more x a i h v h w
 filter_upwards [hh] with i h; exact funext fun x=> A.Wstage_more x a i h he.le h he.le

lemma piece_fixed {A B:ℕ→∀ x:P.Spectrum0 3, (GOp x)} (h:SatinRegistration.Agrees atTop A B) (w:ℂ): SatinRegistration.Agrees atTop (fun i x=>w • A i x) (fun i x=> w • B i x):=by
 intro r t; let ε:=r/(‖w‖+1); have ht:0<ε:= by unfold ε; positivity
 filter_upwards [h ε ht] with i p x; rw [dist_eq_norm,← smul_sub,norm_smul,← dist_eq_norm]; exact (mul_le_mul_of_nonneg_left (p x) (norm_nonneg _)).trans (by have hp:ε*(‖w‖+1)=r:= div_mul_cancel₀ r (by positivity); linarith)
lemma piece_sum {l:Finset J}(A B:J→ℕ→∀ x:P.Spectrum0 3,(GOp x))(h:∀ j∈l,SatinRegistration.Agrees atTop (A j) (B j)): SatinRegistration.Agrees atTop (fun i x=> ∑ j∈ l,A j i x) (fun i x=>∑ j∈l,B j i x):=by
 classical
 induction l using Finset.induction_on with
 | empty=> simp only [Finset.sum_empty]; exact Agrees.refl _
 | insert i l v ih=> simp_rw [sum_insert v]; exact (h i (mem_insert_self ..)).plus (ih fun k t=>h k (mem_insert_of_mem t))
lemma spectrum_moves {A B:ℕ→∀ x:P.Spectrum0 3, (GOp x)} {b:GOp x} (h:SatinRegistration.Agrees atTop A B)(v:Flying (fun i=> B i x) b): Flying (fun i=> A i x) b:=by
 apply Flying.by_wages _ v; apply Metric.tendsto_nhds.mpr; intro r t; filter_upwards [h _ (half_pos t)] with i e;
 rw [dist_zero_right,Real.norm_of_nonneg (norm_nonneg _), ←dist_eq_norm]; exact (e x).trans_lt (half_lt_self t)

variable (A:J→P.Swatch)(l:Finset J)(z:J→ℂ)(W:P.Swatch)
-- quotation relation
abbrev ClearScore : Prop := ∀ s:ℝ≥0,0<s→Agrees atTop (fun i x=> W.Wstage x a s s i) (fun i x=> ∑ j∈ l,z j • (A j).Wstage x a s s i)
lemma ClearScore.support (U:P.ClearScore a A l z W)(L:∀ j∈l,A j∈K): P.Sponsor a K W:=by
 intro s h r d e u; let X(i:J):P.Stunt:= ⟨A i,z i,0⟩
 refine ⟨l.toList.map X,?_, (U s h d u).mono (fun i g x=> le_trans ?_ (g x))⟩
 · intro k p; obtain ⟨i,p₁,rfl⟩:=List.mem_map.mp p; exact ⟨L i (Finset.mem_toList.mp p₁),by unfold X; simpa using e, show |(0:ℝ)| < (s:ℝ) from (abs_zero.le).trans_lt h⟩ -- composition equality in `≤ d` above wrong le_trans orientation
 dsimp only; apply le_of_eq; congr 1; unfold VistaSum; rw [List.map_map,←Finset.sum_map_toList]; refine congrArg List.sum (List.map_congr_left (fun i h=>?_)); simp [X,Function.comp_def,Stunt.toner,ticketPlus,ticketMinus] -- finance

variable (V:∀ i, P.Commission a (A i))
lemma ClearScore.supported (Y:Set P.Swatch)(g:Y ⊆ K)(T':P.ClearScore a A l z W)(x:∀ i∈l,A i∈ Y): P.Sponsor a K W:= (T'.support P a Y A l z W x).extending P a Y W g -- `support` parsing might conflict fn
private lemma manifold {H':Hilbert}(l:Finset J)(A:J→ℕ→ H'.Op)(B:J→H'.Op)(h:∀ i∈l,Flying (A i) (B i)) : Flying (fun i=>∑ j∈l,A j i) (∑ j∈l,B j):=by
 classical
 induction l using Finset.induction_on with
 | empty=> simp only [sum_empty]; exact Flying.still _
 | insert i l k ih=> simp_rw [sum_insert k]; exact (h i (mem_insert_self ..)).add' (ih (fun i p=>h i (mem_insert_of_mem p)))
lemma ClearScore.flight (T':P.ClearScore a A l z W) (V:∀ i x,(A i).WPermit x a)(s:ℝ≥0)(h:0<s): Flying (W.Wstage x a s s) (∑ i∈l,z i • (V i x).atHeat s):= spectrum_moves P x a (T' s h) (manifold l _ _ (fun i _=> Flying.scaled (tendsto_const_nhds (x:=z i)) ((V i x).arriving s h)))
lemma ClearScore.all_heat (T':P.ClearScore a A l z W)(V:∀ i x,(A i).WPermit x a)(H':W.WPermit x a)(s:ℝ≥0)(h:0<s): H'.atHeat s=∑ i∈l,z i • (V i x).atHeat s:= (H'.arriving s h).unique (T'.flight P x a A l z W V s h)
lemma ClearScore.WPermit (T':P.ClearScore a A l z W)(V:∀ i x,(A i).WPermit x a)(p:W.Finishes): W.WPermit x a:=by
 refine ⟨p,?_,fun s g => (T'.flight P x a A l z W V s g).Cauchy⟩
 obtain ⟨k,C,b,h⟩:= RisePrice.sum (fun i:J=> (fun s j=> z i • (A i).Wstage x a s s j)) l (fun i=>(V i x).budget.smul (z i)); refine ⟨k,1+C,add_nonneg zero_le_one b,fun t u e=>?_⟩; filter_upwards [T' t u 1 zero_lt_one,h t u e] with i p q
 let S':= ∑ j∈l,z j • (A j).Wstage x a t t i; let D:=W.Wstage x a t t i; have hp: ‖D‖ ≤ 1+ ‖S'‖:= (norm_le_norm_sub_add _ _).trans (add_le_add ((dist_eq_norm D S') ▸ p x) le_rfl)
 apply (mul_le_mul_of_nonneg_left hp (pow_nonneg u.le k)).trans; rw [mul_add,mul_one]; exact add_le_add (pow_le_one₀ (show 0≤(t:ℝ) from u.le) (show (t:ℝ)≤1 from e)) q
lemma ClearScore.funds (T':P.ClearScore a A l z W)(V:∀ i,P.Commission a (A i))(p:W.Finishes): P.Commission a W:= by
 let K:= Set.range A; have he := ClearScore.support P a K A l z W T' (fun i _=> Set.mem_range_self _)
 exact ⟨p, he.threshold P a K _ (fun i p=>by obtain ⟨v,rfl⟩:=p; exact V v), fun x=> T'.WPermit P x a A l z W (fun i x=>(V i).all x) p⟩ -- `WPermit` lemma resolution. tune arguments

universe v
-- all polarities of the charge pass together. not arbitrary product compression.
def StillCurtain (P:Spine)(a:Axis)(K:Set P.Swatch)(A:P.Swatch): Prop:= A∈ Extensions.{v} P a K ∧ A.turn a∈ Extensions.{v} P a K
lemma StillCurtain.card (p:StillCurtain.{v} P a K W): P.Commission a W:= p.1.1
lemma cinematic_issue (W:P.Swatch)(p:P.Commission a W)(J:Set P.Swatch)(u:P.Sponsor a J W)(k:∀ A∈J, StillCurtain.{v} P a K A): StillCurtain.{v} P a K W:=
    ⟨Extensions.admit _ _ _ _ J (fun _ u=> (k _ u).1) p u,
     Extensions.admit _ _ _ _ ((fun x:P.Swatch=>x.turn a) '' J) (fun i p=>by obtain ⟨j,k',rfl⟩:=p; exact (k j k').2) (Commission.turns P a W p) (Sponsor.turns P a J W u)⟩ -- fns binder membership `fun i`: expected implicit. Lean universe param `J` collides J:Type. check.
lemma ClearScore.cinematic (T':P.ClearScore a A l z W)(V:∀ i,StillCurtain.{v} P a K (A i))(p:W.Finishes) : StillCurtain.{v} P a K W:= cinematic_issue P a K W (T'.funds P a A l z W (fun i=>(V i).1.1) p) (Set.range A) (T'.support P a _ A l z W (fun i _=> Set.mem_range_self _)) (fun k p=> by obtain ⟨v,rfl⟩:=p; exact V v)
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms Spine.yearly_cap
#print axioms Spine.ordinary_kiss
#print axioms Spine.piece_sum
#print axioms Spine.spectrum_moves
#print axioms Spine.ClearScore.supported
#print axioms Spine.cinematic_issue
#print axioms Spine.ClearScore.funds
#print axioms Spine.ClearScore.all_heat
#print axioms Spine.Commission.wander
