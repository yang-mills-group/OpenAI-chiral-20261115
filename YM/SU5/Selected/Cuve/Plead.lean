import YM.SU5.Selected.Cuve.Zen
import YM.SU5.Selected.Lantern.Winter
import YM.SU5.FiniteGaugeData.Pannier.FoyerSeat
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Pannier.Chancel.Cuve
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye RG
open Crest Rail Airy Lantern
open Lantern.Bulb
open Reed (Fine)
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
set_option synthInstance.maxSize 24000
local notation "I"=> Complex.I
local notation "PS" N:max => cutM (Tset N)
/-! # Commercialize terrain. compact before. Notice X,Y stencil translated by *same* u;
every output permit. preserves norm widths and sparse estimate. drag budget ~d².
-/
variable {n k t:ℕ}{N:Side} {M:Tulip.Male}
variable {T:Type}[Fintype T][DecidableEq T](Z:T→ basisRule)
local notation "Ω" N:max=> (1: Pane N)
noncomputable def valée := reservoir.choose
lemma valley_hot:0<valée:= reservoir.choose_spec.1
-- δ may need shrink by extra too. Winter shrinks & combine later; for now require δ=pub. 
lemma vale(t:ℕ): ∀ᶠ i:ℕ in atTop, ∃ γ> (0:ℝ),∀ᶠ N:Side in atTop, Winter 4 valée N γ i ((i:ℝ)⁻¹^t):= reservoir.choose_spec.2 t
-- $exact upper stations on broad budget. for any approximate Route n,N,c$ at finite projected energy. density giant.
variable (W:FaceL)(n t:ℕ)(u: Site N)
def marquee (M:Tulip.Male)(k:ℕ)(K:Finset (Seat N)):= Vo K * hiveY M Z u k
#print marquee
lemma endorse (M:Tulip.Male)(S:Finset (Seat N))(p:Contained (modesIn N S) (rootV Z u k)) :
    PS N* marquee Z u M k S=rootV Z u k:=by unfold marquee; rw [←Matrix.mul_assoc,(cutLane ..).eq,Matrix.mul_assoc, hearty,p] -- rw Commute first Z? name `PS` syntax
lemma root_price (l:ℕ)(h:0<l):∃ C:ℝ,1≤C∧∀ N:Side,∀ (M:Tulip.Male) (u:Site N)(V:Finset (Seat N)),
     ‖hiveX W n t u‖≤C∧ ‖rootV Z u (2*l+2)‖≤C∧ ‖hiveY M Z u (2*l+2)‖≤C∧ ‖marquee Z u M (2*l+2) V‖≤C:=by
 obtain ⟨C,p,v⟩:=breeds (k:=2*l+2) Z (by omega) W n t; refine ⟨max C 1,le_max_right ..,fun N M u V=>?_⟩; obtain ⟨a,b,c⟩:= v N M u; have hg:‖hiveY M Z u (2*l+2)‖≤ max C 1:= (tap_cost ..).trans (c.trans (le_max_left ..)); exact ⟨(tap_cost ..).trans (a.trans (le_max_left ..)),(tap_cost ..).trans (b.trans (le_max_left ..)),hg,bound_shift (cutM_idp _) hg⟩
#print trains
-- station has d choices repeated. Lane forecast success drives upholstery power. Tune d arbitrary >0.
-- Frame abstraction exact upper. ⟨sectionYbound⟩. BootCost output.
structure Loft (W:FaceL)(A: WRect (Fin n) T)(δ γ C:ℝ)(d y l:ℕ) (t:ℕ) (M:Tulip.Male)(N:Side) :Prop where
 permit: IsStarProjection (spar 4 M (1:Pane N)) → ∀ u:Site N, ∀ V S:Finset (Seat N), Contained (modesIn N V) (rootV Z u (2*l+2)) → Lattice.halo (l*d*d) V⊆ S →
    let F:= marquee Z u M (2*l+2) S; let P:=hiveX W n t u; let Y:= rootV Z u (2*l+2)
    ‖F‖≤C∧‖P‖≤C∧‖Y‖≤C ∧ PS N * F=Y ∧ Contained (modesIn N S) F ∧ ‖Pᴴ*F-Screen A‖≤ (d:ℝ)⁻¹^y ∧ ‖(1-spar 4 M (Ω N))*F‖ ≤ (d:ℝ)⁻¹^y -- aero again N binder dependency! PS & Ω use explicit N macros (definition).
#print Loft.mk
abbrev footW(d y:ℕ):= ( (d:ℝ)⁻¹)^y
lemma degree_bill (a A D:ℝ)(y c:ℕ) (p:0<a)(g:y<c): ∀ᶠ d:ℕ in atTop, A*footW d (y+1)*D ≤a*footW d y:=by
 let X:= fun n:ℕ => A*(n:ℝ)⁻¹*D; have h:Tendsto X atTop (𝓝 0):=by simpa only [X, Function.comp, mul_zero,zero_mul] using (((tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul A).mul_const D); -- tune
 filter_upwards [h.eventually (ge_mem_nhds p)] with i v; unfold footW; rw [pow_succ]; apply le_trans _ (mul_le_mul_of_nonneg_right v (show 0≤ (i:ℝ)⁻¹^y by positivity)); unfold X; apply le_of_eq; ring
-- later may override ε profile to fit pressure, just output d^-y. choose l=y+1; winter d^-(l+2), degree integer. Later pick T= d^-5. note Rates n implicit.
variable (A:WRect (Fin n) T){δ:ℝ}
theorem lodge (y:ℕ)(p: Avoriaz δ)(r:0<δ)(a:Rates W A Z (2*(y+1)+2) t) : ∃ C:ℝ,1≤C∧ ∀ᶠ d:ℕ in atTop,∃ γ>(0:ℝ),∀ᶠ U in mounts, let N:= U.2; let M:=U.1; Winter 4 δ N γ d (footW d (y+3)) ∧ (TilePure (N:=N) M→ Loft Z n W A δ γ C d y (y+1) t M N):=by -- arg order tune
 let l:= y+1; have hl:0<l:=by unfold l; omega
 obtain ⟨C,pC,c⟩:=root_price Z W n t l hl; obtain ⟨D,hD,g⟩:= treasury Z l; let B:= ((l:ℝ)^2)*C+D; have ht:= status (k:=2*l+2) W Z (by omega) a
 refine ⟨C,pC,?_⟩; have hc:0<C:=zero_lt_one.trans_le pC; filter_upwards [eventually_gt_atTop 0,(p (y+3)), degree_bill (1/4) C B y l (by norm_num) (by omega)] with d vd p₀ e₀
 let k:= 2*l+2; let b:= (footW d y); let f:=footW d (y+1); let e:= footW d (y+3); have hb:0<b:=by unfold b footW; positivity
 have hf:0< f:=by unfold f footW; positivity
 have hB:0 ≤ B:=by unfold B; positivity
 obtain ⟨γ,hγ,gγ⟩:=p₀; refine ⟨γ,hγ,?_⟩
 filter_upwards [(show Tendsto Prod.snd mounts atTop from tendsto_snd).eventually gγ,Metric.tendsto_nhds.mp ht _ (half_pos hb)] with x u' t'; let N:=x.2; let M:=x.1; refine ⟨u',fun j=> ⟨?_⟩⟩; intro p₁ x V S yV Sb F P Y; change _ ≤ C ∧ _; let T:= hiveY M Z x k; obtain ⟨bP,bY,bF,bA⟩:= c N M x S; have hpS: V⊆ S:= (show V⊆ Lattice.halo (l*d*d) V from (fun i h=>halo_spec.mpr ⟨i,h,(separation_self i).trans_le (Nat.zero_le _)⟩)).trans Sb
 have hv: ‖F-T‖ ≤ B*f:=by
    rw [norm_sub_rev]; refine (busy (C:=C) M _ Y T V yV r.le u' p₁ (show 0 ≤ e by unfold e footW; positivity) bY (hearty ..) (hearty_s M Z x j _) (d*l) S (by rw [Nat.mul_comm d l]; exact Sb) (g N M x j d vd)).trans ?_ -- g args order; hearty
    apply le_of_eq; unfold B f; change ((↑(d*l):ℝ)^2)* (d:ℝ)⁻¹^(y+3) * C+D* (d:ℝ)⁻¹^l=_; unfold l footW; push_cast; rw [show y+3=y+1+2 by omega,pow_add _ (y+1)]; field_simp
 have hA:‖(1-spar 4 M (1: Pane N))*F‖≤ B*f:=by
    rw [show (1-spar 4 M (1: Pane N))*F=(1-spar 4 M (1: Pane N))*(F-T) from ?_]; exact bound_shift p₁.one_sub hv;
    rw [Matrix.mul_sub,Matrix.sub_mul _ _ T,Matrix.one_mul,show spar 4 M (1: Pane N)*T=T from hearty_s M Z x j _,sub_self,sub_zero]
 have he: C*(B*f) ≤ b/4:=by change C*f*B ≤ 1/4*b at e₀; linarith only [e₀]
 refine ⟨bA,bP,bY,endorse Z x M S (yV.grows (modes_monotone hpS)), rising ..,?_, hA.trans ((le_mul_of_one_le_left (mul_nonneg hB hf.le) pC).trans (he.trans (by linarith)))⟩
 rw [show Pᴴ*F-Screen A=Pᴴ*T-Screen A+Pᴴ*(F-T) from ?_]; apply (norm_add_le ..).trans -- tune
 have hg:‖Pᴴ*T-Screen A‖≤ b/2:=by rw [show Pᴴ*T=_ from gramS M Z W x n t k, ←Cuve.tap_sub]; apply (tap_cost _).trans; rw [←dist_eq_norm]; exact t'.le
 exact (add_le_add hg (charge_mul ((Matrix.l2_opNorm_conjTranspose ..).trans_le bP) hv)).trans (by linarith)
 rw [Matrix.mul_sub]; abel
end YM.CF.Pannier.Chancel.Cuve
open YM.CF.Pannier.Chancel.Cuve
#print axioms lodge
#print axioms degree_bill
#print axioms root_price
