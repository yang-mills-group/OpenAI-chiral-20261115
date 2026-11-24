import YM.SU5.FiniteGaugeData.Brique.Bolt
import YM.SU5.FiniteGaugeData.Cuprite.Caesura
set_option autoImplicit false
set_option synthInstance.maxSize 20000
set_option maxHeartbeats 450000
set_option linter.flexible false
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.SU5.FiniteGaugeData.Cuprite.Spirit
open Function NormedSpace Filter Finset MeasureTheory Lattice RG Wilson AnalyticBridge Metric Pressure Galope CF CF.Pastry CF.Py.Rate
open SU Fock Reduction Reduction.Jersey Reduction.Drama Reduction.Drama.Pack Reduction.Hutch Cube Lat Window Presidio Tenant Skye Scree Graph CF.Buffered Window.Brique Next.Rank Branch Nacre -- amb.Supply
open Rush Scroll Peaks Tap Tulip Fir Cascade
open Avenue RouteM Spindle
open scoped Topology ContDiff BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace Kronecker ComplexOrder Classical
attribute [local instance] opCStarAlgebra
variable {n:Side} {ε b v t C c a M u x:ℝ}{r w k j:ℕ} {F:Pane n → Op (Single n)}(Y:Loom n){U:Pane n} (X:Orbit n) {g:Mosquito n}
namespace Pilot
-- define tuning. core face semantics. Weight.: common constants prepared.
private abbrev lostR(V:Pane n)(t:ℝ)(w:ℕ):Finset (Single n):= Finset.univ \ Buffered.modesIn n (coverN V t w (coreN w))
local notation "N" => Fintype.card (Site (More n))
local notation "σ"=> Fintype.card SpinIdx * Fintype.card SU.Slot
local notation "ϕ"=> ((Fintype.card (Ember.coneA SU.Slot):ℕ):ℝ) -- =? check Spin Slot coneA β
local notation "ξ" => discE X.1 t w
private lemma lostH (U:Finset (Site (More n))): (univ \ modesIn n U).card ≤ (univ \ U).card *σ:=by
 let V:=univ\modesIn n U; let F(i:↥V): ↑(univ \ U)× SpinIdx×SU.Slot:=by
    refine (⟨node i.val.1.1, mem_sdiff.mpr ⟨mem_univ _, mt (modes_at ..).mpr (mem_sdiff.mp i.property).2⟩⟩, i.val.1.2,i.val.2)
 change V.card ≤ _; rw [← Fintype.card_coe,← Fintype.card_coe (univ\U), ←Fintype.card_prod, ←Fintype.card_prod]; apply Fintype.card_le_of_injective F; intro i j e; apply Subtype.ext; exact Prod.ext (Prod.ext (needle (congrArg (fun x: ↑(univ \ U)× SpinIdx×SU.Slot=> x.1.val) e)) (congrArg (fun x=>x.2.1) e)) (congrArg (fun x=>x.2.2) e)
abbrev owed(v C:ℝ)(w:ℕ) := ((Fintype.card (Ember.coneA SU.Slot):ℕ):ℝ)* (v^2+ (C+C)^2* (diamC/(w:ℝ)^2))
abbrev once(X:Orbit n)(t:ℝ):ℝ:= (Steve.misses X.1 t).card
abbrev office(C:ℝ)(w:ℕ):= κf w *((Fintype.card (Ember.coneA SU.Slot):ℕ):ℝ)*(C+C)^2
abbrev Ticket(X:Orbit n)(t v C:ℝ)(w:ℕ):ℝ:= owed v C w * N +office C w * once X t
def tollX(t: Mosquito n)(V:Op (Single n)):= twist (tradew n t⁻¹) V
-- pay Cover price
lemma egress(Z:CoversU X Y w t a (M*b) g) (H:Casing n u F c C M)(J:Guard (Y X) u)(e:0≤u)(p:r≤w)(v': 2*tailCost c C r+b*C ≤ v):
 kg (F (Y X)-tollX g (F 1)) ≤ Ticket X t v C w :=by
 let A:= F (Y X); let Q:=F 1; let V:=gauge g (Y X); let G:=F V - Q; have hg:Guard V u:= J.cov g; have hc:‖F V‖ ≤ C:= ambient_value H _ hg; have ht: ‖Q‖≤C:=ambient_value H _ (guard0 e)
 have he: F (Y X) - tollX g Q=tollX g G:=by unfold tollX G; rw [map_sub,H.coloredWT (Y X) J,Mono_tradew,twist_inv] -- H equation lambda.Scope
 have h0:0≤ C:=(norm_nonneg _).trans ht
 let S:= discE X.1 t w; let T:= coverN X.1 t w (coreN w); let W:= modesIn n T; let K:=univ \ W; let L:=tradew n g
 let D(i:Single n):= ‖acts (star G) (basisKet i)‖^2
 have hv(i:Single n):D i ≤ (C+C)^2:= pow_le_pow_left₀ (norm_nonneg _) ((Flare.opy _ _).trans (by simp only [norm_star,show ‖basisKet i‖=(1:ℝ) from by simp [basisKet],mul_one]; exact (norm_sub_le ..).trans (add_le_add hc ht))) 2
 have hl(i:Single n)(e:i∈W):D i ≤ v^2:=by
   obtain ⟨o,hr,hp⟩:= mem_biUnion.mp ((modes_at ..).mp e); let S:= Spindle.patch (coreN w) o; let V':=Spindle.patch (η w) o; let Q:=cutM (modesIn n S); have hm: Lattice.halo r S⊆ V':=by
      intro z p'; obtain ⟨x,y,t⟩:=halo_spec.mp p'; exact Avenue.extend o x z (t.trans p) y
   have hE:‖Q*G‖ ≤ v:= (shape_fee H r V 1 hg (guard0 ‹0≤u›) S V' hm (by rw [profile_trivial]; exact (Z.beds o hr).2.2.2.2)).trans v'
   have ht:star Q=Q:= (cutM_idp _).2; have hh:acts Q (basisKet i)=basisKet i:=by unfold Q; rw [cut_basis,if_pos ((modes_at ..).2 hp)]; -- tune
   change ‖_‖^2≤_; apply pow_le_pow_left₀ (norm_nonneg _) _ 2
   rw [show acts (star G) (basisKet i)= acts (star (Q*G)) (basisKet i) by rw [star_mul,ht,act_mul,hh]]; exact (Flare.opy _ _).trans (by rw [norm_star,show ‖basisKet i‖=(1:ℝ) from by simp [basisKet],mul_one]; exact hE)
 have hz: (K.card:ℝ) ≤ S.card*ϕ:= by rw [Fintype.card_prod]; exact_mod_cast (lostH T)
 have hu: (W.card:ℝ) ≤ (N:ℝ)*ϕ:=by
    apply (Nat.cast_le.mpr (card_le_univ W)).trans; unfold Single; rw [Fintype.card_prod,Fintype.card_prod,Fintype.card_prod SpinIdx SU.Slot,site_card,site_card]; rw [mul_assoc]; push_cast; gcongr; exact_mod_cast (Nat.le_mul_of_pos_right (n.val) two_pos) -- tune
 -- equality and pay.
 rw [show F 1=Q from rfl,he,tollX, Spiny.ktw, ←kgt,kg_I,← Finset.sum_sdiff (s₁:=W) (s₂:=univ) (subset_univ W)] -- tune
 have hm: (S.card:ℝ) ≤ (diamC/(w:ℝ)^2) *N + κf w *once X t := retired _ Z.Intro t
 have hb: (∑ i∈ K,D i) ≤ K.card*(C+C)^2:= (sum_le_sum (g:=fun _=>(C+C)^2) (fun i _=>hv i)).trans_eq (by simp)
 have hk: (∑ i∈ W,D i) ≤ W.card*v^2:= (sum_le_sum hl).trans_eq (by simp) -- hl type?
 unfold Ticket owed office; linarith only [hb,hk,mul_le_mul_of_nonneg_right (hz.trans (mul_le_mul_of_nonneg_right hm (Nat.cast_nonneg (α:=ℝ) (Fintype.card (Ember.coneA SU.Slot))))) (sq_nonneg (C+C)), mul_le_mul_of_nonneg_right hu (sq_nonneg v)]
end Pilot
end YM.SU5.FiniteGaugeData.Cuprite.Spirit
