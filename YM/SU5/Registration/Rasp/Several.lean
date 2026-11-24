import YM.SU5.Registration.Rasp.Warranty
/-!
# Algebra of Sponsors for finite-turn and supplying a coded field set
Sponsor requests a genuine op norm estimate (over all characters); compile local
approximations at arbitrary inner heat cuts. Use to prove transfer when replacing one
field, even to unequal stamps. The approximants are made to buy **sharp Eu point**
questions, not covariance claims. Also see `the construction notes` for link to mean.
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
open Swatch
universe v ν
variable (K:Set P.Swatch)(A B:P.Swatch)
def Extensions : Set P.Swatch:= {A| P.Commission a A ∧ ∀ (I:Type ν) [DecidableEq I],∀ (L:List I)(W:I→P.Swatch)(i:I), i∈L → P.all_desk a W → (∀ B∈K,P.Paper a L (Function.update W i B)) → P.Paper a L (Function.update W i A)}
lemma Extensions.donors (u:A∈K)(g:P.Commission a A): A∈ Extensions.{ν} P a K:=⟨g,fun _ _ _ _ _ _ _ t=> t _ u⟩
lemma Extensions.card (u:A∈Extensions.{ν} P a K):P.Commission a A:=u.1
-- not closure under *arbitrary* finite products. use for names. prove if paid dense K in C, Sponsors from K in C.
lemma Extensions.admit (Y:Set P.Swatch)(T':Y⊆ Extensions.{ν} P a K)(h:P.Commission a A)(g:P.Sponsor a Y A): A∈Extensions.{ν} P a K:=by
 have hz:∀ i∈ Y,i∈Extensions.{ν} P a K:=fun _ q=> T' q
 refine ⟨h,?_⟩; intro I d L W i f t V; let Q:= Function.update W i A; have he:Q i=A:= Function.update_self ..
 refine via_stunts P a L Q i f Y (he.symm ▸ g) (fun i q=>(hz i q).1) (P.all_desk_update a W t i _ h) ?_
 intro B p; unfold Q; rw [Function.update_idem]; exact (hz B p).2 I L W i f t V -- `[DecidableEq I]` etc.

/- co.ext over all lists. Need Ration all occupied, outside also separately, but positions not colored. Use substitution using w∈Extensions.{ν} P a K all. -/
variable {I:Type ν}(L:List I)(W:I→P.Swatch)
-- omitted
lemma Paper.copy {A:I→P.Swatch}(h:P.Paper a L A)(p:P.all_desk a A)(t:P.all_desk a W)(u:∀ i∈L,A i=W i): P.Paper a L W:=by
 classical
 intro g q l k σ r v qk; obtain ⟨f,F',vF⟩:= sews a L q l
 let Ω₁:=fun i=>(p i).all; let Y₁(x:P.Spectrum0 3):= P.ChartPrice x a L (fun i=>(g i x).atHeat) q f F'
 let Y₂(x:P.Spectrum0 3):= P.ChartPrice x a L (fun i=>(Ω₁ i x).atHeat) q f F'
 have he(x:P.Spectrum0 3): P.EuCost x a L (fun i=>(g i x).atHeat) q=Y₁ x:= P.Eu_pays x a L q W _ f F' l vF
 have hc(x:P.Spectrum0 3): P.EuCost x a L (fun i=>(Ω₁ i x).atHeat) q= Y₂ x:= P.Eu_pays x a L q A _ f F' l vF
 let X₁(n:ℕ)(x):= P.RawPrice x a L A (r n) f F' (σ n); let X₂(n:ℕ)(x):= P.RawPrice x a L W (r n) f F' (σ n)
 have hX:X₂=X₁:=by
    funext n x
    have he: P.RawOp x a L A (r n) f F' (σ n) = P.RawOp x a L W (r n) f F' (σ n):=congrArg List.prod (List.map_congr_left (fun i p=>by rw [u i p]))
    unfold X₁ X₂ RawPrice; rw [he]
 have hy:Y₂=Y₁:=by
    funext x; unfold Y₁ Y₂ ChartPrice ChartOp
    let Z(i:I):=Ω₁ i x; let Z'(i:I):= g i x
    let T'(k:I)(B:ℝ≥0→(P.ManyF a (Θ x a)).Op):= P.orbitCut x a B (f k) (F' k) (q k)
    refine congrArg (fun X:List (GOp x)=> inner ℂ (P.heaven a (Θ x a)) (X.prod (P.heaven a (Θ x a)))) (List.map_congr_left (?_)); intro i p; exact congrArg (T' i) (helper P x a (A i) (W i) (u i p) (Z i) (Z' i)) -- where
 let t':= h Ω₁ q l k σ r v qk; have hv: Agrees (b:=fun _=>ℂ) atTop X₁ (fun _ x=> P.EuCost x a L (fun i=>(Ω₁ i x).atHeat) q):=((P.wearing a L q A f F' vF v (fun i _=> (p i).being) qk).symm).trans t'
 simp_rw [hc,hy,← hX] at hv; unfold CoPays; simp_rw [he]; exact (P.wearing a L q W f F' vF v (fun i _=>(t i).being) qk).trans hv
where helper (P:Spine)(x:P.Spectrum0 3)(a:Axis)(A B:P.Swatch)(h:A=B)(f:A.WPermit x a)(g:B.WPermit x a): f.atHeat=g.atHeat:=by subst B; rfl

-- extend any Desks ALL plus any number of replacements. requires nonempty K. General argument on # of not-yet-held K tests.
lemma Paper.all_in (k:K.Nonempty)(t:∀ A∈K,P.Commission a A)(T':∀ (A:I→P.Swatch), (∀ i, A i∈ K) → P.Paper a L A) (p:∀ i,W i∈ Extensions.{ν} P a K) : P.Paper a L W:=by
 classical
 obtain ⟨w,wk⟩:= k; have hw:= t w wk
 suffices ∀ Z:Finset I,(Z ⊆ L.toFinset) → ∀ X:I→ P.Swatch,(∀ i,X i∈Extensions.{ν} P a K) → (∀ i∈ L,i∉ Z → X i∈ K) → P.Paper a L X from this _ (subset_refl L.toFinset) W p (fun i p e=> (e (List.mem_toFinset.mpr p)).elim)
 intro Z; induction Z using Finset.induction_on with
 | empty=>
    intro _ X u v; let B(i:I):= if i∈L then X i else w
    have hb(i:I): B i∈ K:=by unfold B; split_ifs with h; exact v i h (notMem_empty _); exact wk
    exact Paper.copy P a L X (T' B hb) (fun i=> t _ (hb i)) (fun i=>(u i).1) (fun i h=> by unfold B; rw [if_pos h])
 | @insert i z he ih=>
    intro F X u v; have hx:i∈L:= List.mem_toFinset.mp (F (mem_insert_self ..))
    rw [←show Function.update X i (X i)=X from Function.update_eq_self ..]; refine (u i).2 I L X i hx (fun i=>(u i).1) (?_) -- careful rw iter duplicates in goal? tune.
    intro B g; refine ih (subset_trans (subset_insert ..) F) (Function.update X i B) ?_ ?_
    · intro b; by_cases H':b=i; subst b; rw [Function.update_self]; exact Extensions.donors P a K B g (t _ g)
      rw [Function.update_of_ne H']; exact u b
    intro b p e; by_cases H':b=i; subst b; rwa [Function.update_self]; rw [Function.update_of_ne H']; exact v b p (fun y=> (mem_insert.mp y).elim H' e)

-- tape symmetry & turning extensions. Not assuming Parent-closed under arbitrary ribbons,
-- use when also turning the Approx relation carried by new stencils.
lemma Commission.turns (p:P.Commission a A) : P.Commission a (A.turn a) :=by
 refine ⟨p.being,?_,fun x=>(p.all x).reflector x a A⟩; intro s h; obtain ⟨C',t,u⟩:= p.threshold s h; exact ⟨C',t,u.mono (fun i t x=> by dsimp only; rw [Wstage_turn, ContinuousLinearMap.adjoint.norm_map]; exact t x)⟩
abbrev Stunt.twist (k:P.Stunt):P.Stunt:= ⟨k.performer.turn a,star k.wage,-k.jump⟩
lemma twist_stays (k:P.Stunt)(s:ℝ≥0)(t:ℝ)(e:k.floor K s t): (k.twist P a).floor ((fun k:P.Swatch=> k.turn a) '' K) s t:=⟨⟨k.performer,e.1,rfl⟩,(abs_neg k.jump).symm ▸ e.2.1,(abs_neg k.jump).symm ▸ e.2.2⟩ -- argument order? see `turn (l)` variable usage implicit. likely Swatch.turn A a? check
lemma mascot_turn (l:List P.Stunt)(s:ℝ≥0)(i:ℕ): (P.VistaSum x a l s i).adjoint= P.VistaSum x a (l.map (fun k=> k.twist P a)) s i:=by
 induction l with
 | nil=> simp [VistaSum];
 | cons k l ih=>
    let V:= k.toner P x a s i
    have ht: V.adjoint=(k.twist P a).toner P x a s i:= by unfold V Stunt.toner Stunt.twist; rw [ContinuousLinearMap.adjoint.map_smulₛₗ,← Swatch.Wstage_turn, ticketPlus,ticketMinus,ticketPlus,ticketMinus,←sub_eq_add_neg,sub_neg_eq_add]; rfl
    simp only [List.map_cons,VistaSum,List.sum_cons,map_add]; rw [show ((k.toner P x a s i)).adjoint= _ from ht]; exact congrArg (fun x=>_+x) ih
lemma Sponsor.turns (u:P.Sponsor a K A) : P.Sponsor a ((fun k:P.Swatch=> k.turn a) '' K) (A.turn a):=by
 intro s h β ε p t; obtain ⟨l,b₀,c⟩:=u s h β ε p t
 refine ⟨l.map fun k=> k.twist P a,?_ , c.mono (fun i v x=> by dsimp only; rw [Wstage_turn,←P.mascot_turn x a l s i, ContinuousLinearMap.adjoint.dist_map]; exact v x)⟩
 intro k h; obtain ⟨b,V₀,v⟩:=List.mem_map.mp h; -- b collision
 subst k; exact P.twist_stays a K b s β (b₀ b V₀)
 -- collision `b` overwritten! 

end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms Spine.Extensions.admit
#print axioms Spine.Paper.all_in
#print axioms Spine.Sponsor.turns
