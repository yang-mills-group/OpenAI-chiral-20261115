import YM.CF.Fief.Crow
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Fief
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Stilo Palot Scion Function Levier Hake Urn Peaks Fock Laic Branch Drapes
open Rush Scroll Paige Vault Phase Acorn Spire Eire
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Jet Lich Corne
open Lich.Muster
attribute [local instance] opCStarAlgebra
local notation "G₅"=> SU.group
open SectorNext.Remainder.Scales
variable {N P B:Side} {F:Patch} {f g h k:ℝ→ℝ} {c a ε K v m:ℝ}{n d:ℕ}
open Vol YM.Push.AbsoluteSums
open ConnectedActivityE6.Raw
namespace sizeK
variable(L:Side)
local notation "q"=> Scales.g G₅ L
lemma yearsK(hp:sizeK L (n+2) f) : sizeK L n fun x=> y G₅ L x*f x:=by
 obtain ⟨C,hp⟩:=hp; refine ⟨C,?_⟩; filter_upwards [hp,(year G₅ L).eventually_gt_atTop 0] with x p v; have he:=yg2 G₅ L v; rw [abs_mul,abs_of_pos v]; rw [pow_add] at p; exact (mul_le_mul_of_nonneg_left p v.le).trans_eq (by rw [←mul_assoc, mul_comm (q x^n),← mul_assoc _ (_^2),he,one_mul])
lemma val_gain(σ:ℝ)(hv:0<σ)(m':ℕ)(hm:0 < m')(n:ℕ): sizeK L n (fun x:ℝ=> tollE σ (Stores.till x/m')):=by
 let P(x:ℝ):ℝ:=↑(Stores.till x/m'); let A(u x:ℝ):ℝ:= tollE u (Stores.till x/m')
 have hp(u:ℝ)(p:0<u):sizeK L 2 (A u):=by
   refine ⟨0,?_⟩; let v:=u/(2* (m'+m':ℕ)); have he:0<v:=by unfold v; positivity
   filter_upwards [tail_delay G₅ L v he,(year G₅ L).eventually_gt_atTop 0,Work.E01.radiusB_tendsto.eventually_ge_atTop (m'*100000*2)] with x t hx h
   let y:= Scales.y G₅ L x; let B:=Stores.till x; have hz:B/m' > 0:=by unfold B Stores.till; apply Nat.div_pos _ hm; omega
   have ht : B≤(m'+m')*(B/m'):=by have hv:= Nat.mod_add_div B m'; have hp:=Nat.mod_lt B hm; rw [Nat.add_mul]; nlinarith
   have hh:=yg2 G₅ L hx; rw [pow_zero,mul_one,abs_of_pos (Real.exp_pos _)]
   apply le_trans (Real.exp_le_exp.mpr (_ : -(u/2)*(P x)≤ -v*B)) (t.trans_eq (by change (Scales.y G₅ L x)⁻¹= _; field_simp; linarith))
   rw [neg_mul,neg_mul,neg_le_neg_iff]; unfold v P; have ht : (↑B:ℝ)≤ (m'+m':ℕ)*(B/m':ℕ):=by exact_mod_cast ht
   field_simp; nlinarith
 have hq := Nat.zero_lt_succ n
 let v':=σ/(n+1:ℕ); have hv':0<v':=by unfold v'; positivity
 refine (((hp _ hv').square (n+1)).low (k:=n) (by omega)).cost_d (Eventually.of_forall fun x=>Eq.le ?_)
 apply congrArg abs; unfold A tollE; rw [← Real.exp_nat_mul]; congr 1; unfold v'; push_cast; field_simp
lemma tempo :sizeK L 1 temp:=by
 apply (((main L).tint (height L)).scale 2).cost_d
 filter_upwards [Work.E07.temp_coarse_le G₅ L, eventually_gt_atTop (0:ℝ)] with x h v; have he:= Work.E09.temp_pos v; rw [abs_of_pos he]; rw [fi] at h; exact h.trans (le_abs_self _)
lemma fierce:sizeK L 1 fun x=>fiery G₅ x L:=by simp_rw [fi]; exact (main L).tint (height L)
-- justify transversal caps pay
variable {c f:Side} in
lemma profileG (G:Ratio c f){F H:ℝ→ℝ}(k r:ℕ)(p:sizeK L n F)(a b u:ℝ)(h:sizeK L d H): sizeK L (n+d) fun x=> payN G k (radiusB x) r a b (F x) (H x) u:=by
 let V(x):ℝ:= Footprint.spread (G.count.val^4) (Paths.originFee k (radiusB x)); have hh:sizeK L 0 V:=by
    dsimp only [V,Footprint.spread,Paths.originFee,Animals.ballCost]; push_cast
    let C:= (((Bcash L).scale k).accrue (mild L 1)); exact (((C.accrue C).accrue (mild L 1)).powC 4).scale _ -- tune ball
 let Q₀:= (G.count.val^4); let μ':= Paths.baseFee (d:=r) G k; let W:= Footprint.payment Q₀ 0 0 b 1 1 a μ'; let Q':=Real.exp (a*μ') * (b⁻¹^(4+0) * ((4+0:ℕ).factorial:ℝ) * Real.exp b)*(1-Real.exp (-b))⁻¹
 apply ((((p.tint h).tint hh).scale Q')).cost_d; filter_upwards with x; apply Eq.le; apply congrArg abs; unfold payN Footprint.payment Footprint.degreeIncome Q' μ' V; ring
lemma rollP {c f:Side} (G:Ratio c f)(k r v:ℕ)(t:ℝ)(h:0<t) (B C D A W:ℝ)(a:ℝ)(p:0<v) (σ':ℝ→ℝ)(hv:sizeK L 1 σ') : sizeK L 3 fun x:ℝ=> worthK G k (radiusB x) (Stores.till x/v) (2*y G₅ L x+D) A B C t a W (σ' x) :=by
 have he:= (val_gain L t h v p 5); let V(n:ℕ)(x:ℝ):=C * σ' x^n; let T (u x:ℝ):=tollE t (Stores.till x/v)*u; let Q(n:ℕ)(b x:ℝ):= payN G k (radiusB x) n A a (V n x) (T b x) t
 have ht(u:ℝ):sizeK L 5 (T u) := he.tint (mild L u)
 have hu(n:ℕ)(i:ℝ): sizeK L 5 fun x=> Q n i x:=profileG L G k n (sizeK.scale (hv.low (Nat.zero_le _) |>.powC _) _) A a t (ht _)
 let F(x):=payN G k (radiusB x) 2 A a C (T (Stationary.gramCost G₅ B) x) t+(Q 3 B x+Q 4 B x); have hp:sizeK L 5 F:= (profileG L G k 2 (mild L _) _ _ _ (ht _)).accrue ((hu 3 B).accrue (hu 4 B)) -- tune
 refine sizeK.accrue (?_ : sizeK L 3 fun x=> (2*y G₅ L x+D)*F x) ((hu 2 W).low (by omega)); refine sizeK.cost_d (((yearsK (n:=3) L hp).scale 2).accrue ((hp.low (k:=3) (by omega)).scale D)) (Eventually.of_forall fun x=> Eq.le (congrArg abs (by ring)))
lemma rollA {c f:Side} (G:Ratio c f)(k:ℕ) (D A B C t a W:ℝ)(σ':ℝ→ℝ)(h:sizeK L 1 σ') : sizeK L 3 fun x:ℝ=> worthH G k (radiusB x) D A B C t a W (σ' x):=by
 exact ((profileG L G k 3 ((h.square 3).scale C) A a t (mild L _)).accrue ((profileG L G k 4 ((h.square 4).scale C) A a t (mild L _)).low (by omega))).scale D
end sizeK
end YM.CF.Fief
