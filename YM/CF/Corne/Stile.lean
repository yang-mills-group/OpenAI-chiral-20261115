import YM.CF.Corne.Spun
import YM.CF.Corne.Falls
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Corne
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace Matrix Kronecker
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Push.Uniform (curve Slope tint partSpace meetVar)
open AnalyticBridge.Annulus1AD AnalyticBridge.SectorAffine Oriented Esti Vol Bloch Exterior Jet
open RG Forge Cay Slate Rel
open Arena Tarn Reine
local notation "G₅"=> SU.group
variable {c f:Side}{S:StepData c f}{T:Tube SU.group S}{F:Forest S.ratio}{q:Chi}{s:Signed}{l n:ℕ}{x d β C D σ m:ℝ}{P:Tab S}{V:Config SU.group c}
open Cube
variable {r j:ℕ}{u v W a b w s':ℝ}{i:Site c}{F:Tab S}{K:Teller G₅}{P': Tab S}
open Lat Rush Cour Scroll Laic Kennel Paige Spire Branch Broc Pec Facet Peaks
variable {n' B Mx X: Side}{T: Roam Mx X B}(G: Ratio (CSide Mx B) (CSide X B))(F:Tube G₅ T)
variable {C V R Z η e:ℝ}(Q: Msca Mx X B G e){Φ:nomA Mx X B→ ℂ}
local notation "pG"=> CSide Mx B
local notation "pF"=> CSide X B
local notation "D₀"=> More pG
local notation "D₁"=> More pF
variable (x d u:ℝ)(q:Chi)(l:ℕ)(S: Monk G₅ T)(A:Rent0 G e)(β:ℝ)(t:0 < e)
section
local notation "Y"=> mSeal X B
open Hest
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open Fock Tulip Urn Vault Proa
variable (H:Haze Mx X B G e)
attribute [local instance] opCStarAlgebra
local notation "Ĉ"=> composeCost n
abbrev dataC (n:ℕ)(K:ℝ):= (Fintype.card SU.Slot:ℝ)^2*K
lemma chairP(g:Site (More c)→SU.E)(E:Type)[NormedAddCommGroup E][NormedSpace ℝ E](X:E→Op (Single c))(x:E)(i j:Single c)(p:∀ v w:SU.Slot, Allows n (fun y=> X y (i.1,v) (j.1,w)) x C): Allows n (fun y=>ActZ g (X y) i j) x (dataC n C):=by
 let A:= (SU.matter (g (terse i.1))); let B:= SU.matter (g (terse j.1)); let Xv(v w:SU.Slot)(y:E):=(A.val i.2 v * star B.val w j.2)* X y (i.1,v) (j.1,w)
 have hx(v w):Allows n (Xv v w) x C:=by
    let V:= A.val i.2 v * star B.val w j.2; let R:= V • ContinuousLinearMap.id ℂ ℂ; have ht: ‖V‖ ≤1:=by rw [norm_mul]; refine mul_le_one₀ ((norm_entry ..).trans (CStarRing.norm_of_mem_unitary A.property).le) (by positivity) ((norm_entry ..).trans (CStarRing.norm_of_mem_unitary (show star (B.val:Op _) ∈ unitary (Op SU.Slot) from (B⁻¹).property)).le)
    refine (((p v w).linear (R.restrictScalars ℝ) (K:=1) (ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun i=>by change ‖V*i‖≤_; rw [norm_mul,one_mul]; exact mul_le_of_le_one_left (norm_nonneg _) ht)).mono (one_mul _).le) -- tune
 apply (((summed univ (fun v y=>∑ w,Xv v w y) (fun v _=>summed univ _ (fun i _=>hx v i))).mono ?_).germ ?_)
 · unfold dataC; rw [card_univ]; exact le_of_eq (by ring)
 filter_upwards with y; rw [show ActZ g (X y) i j= ni i.1 j.1 (twist _ (X y)) i.2 j.2 from rfl, twistW]; simp_rw [Matrix.mul_apply,sum_mul]; unfold Xv A B ni; rw [sum_comm]; apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; dsimp only [Matrix.of_apply]; ring -- tune
structure DegreeP (u:ℝ)(P:Tab T)(b:ℝ):Prop where
 X(y:Mast G₅ D₀): ‖y‖<1→ ‖Souk.flute P.1 (sol T F P.2 x P.1 l) u y‖< η
 T0(y:Mast G₅ D₀)(hp:‖y‖<1)(i j:Single pG): Allows n (fun y:Mast G₅ D₀=> shelfH G H t x (teen P.1 F x P.2 l u y) i j) y (b*u^3)
-- derivative sup.Seat. Requires actual germ near (β param fixed, S flags). Compatible enough with all paths.
variable{L: nomA Mx X B→ Op (Single (CSide Mx B))}
lemma forkY (i j':Single pG)(h:T.ratio=ratio G)(p:K.Funds T F)(he:Ready F x)(hk:1000 ≤radiusB x)(g:Site D₀→ SU.E)(v: Directions G₅ D₀→ Mast G₅ D₀)(hp:Slate.Far.Lamp F u x S (place_x i) g v j n)(v':ℝ)(ht:DegreeP G F x l t H u (S.park,S.k) v' (n:=n) (η:=η))(hv:∀ y:Mast G₅ D₀,‖y‖<1→ Fire F x S.park S.k l u n C y)(U:Directions G₅ D₀→Rent0 G e)(hV:∀ᶠ t in 𝓝 0,Bride G F x d q l (rough (S.atop t x) 0) (U t) β (radiusB x+1) (place_x i))(hz:l+76≤ j)(hy:Hest.Ind G H a C D n L)(hq:Fleck G t S.park η D n):Allows n (fun t=> led G x H (U t) i j') 0 (dataC n (composeCost n (v'*u^3) (1/2))):=by
 let W(z:Mast G₅ D₀):= shelfH G H t x (teen S.park F x S.k l u z); have ht':‖v 0‖<1:=hp.stage.value.trans_lt (by norm_num)
 apply (chairP g⁻¹ (Directions G₅ D₀) (W ∘ v) 0 i j' (fun j k=>(ht.T0 (v 0) ht' (i.1,j) (j'.1,k)).comp hp.stage)).germ
 filter_upwards [hV,hp.reads,hp.stage.smooth.continuousAt.eventually (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr ht'))] with y H0 hp' hu; let S':= rough (S.atop y x) 0; let J:= S.park; have hk':= mem_ball_zero_iff.mp hu; have hg:Tarn.drift G₅ (place_x i) (horn x l) (Lattice.gauge g S'.V) (satU G₅ u (v y)):= fun x t=>hp' _ (t.trans (Nat.mul_le_mul_right _ hz))
 have hS: Tarn.drift G₅ (place_x i) (horn x l) S'.V (Lattice.gauge g⁻¹ (satU G₅ u (v y))):=by have he:=hg.via g⁻¹; rwa [Tarn.dyadic,inv_mul_cancel,fix_s] at he
 exact (swingS G F x d q l S' (U y) β t H i j' h H0 hy p he hk rfl _ u (v y) (hv _ hk') hq (ht.X _ hk') hS (fun v=> hp.sanda (farther (Nat.mul_le_mul_right _ (by omega)) (show place_x i∈ S.key.dome (horn x l) from v)))).symm
end
end YM.CF.Corne
