import YM.CF.Wray.Shop
import YM.Next.RANK.Stretch
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Wray
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}
variable {d e η t z g b c A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
open Yaw Pig
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Iva Eire Trees Font
-- long Bore labels with thermo halo and ads mounted. lift support by 21 before any stamp. No K suppression requested.
local notation "Nx"=> Domain N B
local notation "Fx"=> Domain P B
local notation "v₀"=> ((l+90)*radiusB x)
local notation "x'"=> (radiusB x)
variable {γ σ Hz:ℝ}{I: Stake.Isle} (Q:Pail.Payment R σ) (F:Pilot){H:Muster G S x d T}(M:Bit (Site (Domain N B))→ ℝ)(M':Bit (Site (Domain N B))→ℝ) (Z_:mSeal P B→ℝ)(V':mSeal P B→Toll (Single (mid N B))) {Φ:nomA N P B→ℂ}{θ:nomA N P B→ Op (Single (mid N B))}
variable (B0:Pail.Payment.BondL Q I M F H M' k j) (U_: Fief.Scute H I.fine I.fine (Q.q₁ x) (Q.q₂ x) I.pay I.oath (k+2) (l+90) I.s I.song σ Φ θ Z_ V')
variable (o:Site (Domain N B))(hz:1000≤radiusB x)
include U_ B0 hz
local notation "Lo"=> Palot.leaf (Site (Domain N B))
local notation "VO"=>Toll (Single (mid N B))
def OpC (L':Palot.leaf (Site (Domain N B)))(_i:ℝ): Raid (LeanV (Single (mid N B))) := Iva.cull k (Fief.potQ (x:=x) (S:=S) V' v₀ L') (Kplan k (M L')+ M' L'+ Fief.potR (S:=S) (x:=x) Z_ v₀ L') -- i phantom
local notation "E"=> ((Q.k₁ x))
local notation "T'"=> (Branch.ledgerV)
local notation "C_"=> (fun i=> OpC (l:=l) (k:=k) (S:=S) (x:=x) M M' Z_ V' i 0)
abbrev legE (h:ℝ)(k:ℕ)(x:ℝ):=steel k (Kplan k (Q.k₁ x)+ Q.k₂ x+ Q.q₁ x)+h^2* steel k (Q.q₂ x)
lemma tallyX(h:ℝ) : 0 ≤ C_ ∧ (∑ i:Palot.leaf (Site (Domain N B)),tallyL o i σ (radiusB x)* Hake.joinV (stake h) (C_ i))≤ legE Q h k x :=by
 obtain ⟨p,v⟩:=B0.plan o; let zq:= U_.fare o; let zp:= U_.fuel o
 constructor
 · let X: Monk SU.group S:=⟨bareStores S, Classical.choice (Tree.select S.ratio S.patch.odd_side),Classical.arbitrary _,1,1,0⟩ ; have hv:Chir X x:= (PhysicalNext.JointLoad.Heir.noFlags ..).symm -- uses hx x≥0? threshold.P.Temp maybe noFlags assumption. inspect
   let hq:= B0.earns X hv; have ht: ‖X.z‖ ≤ F.hat R x:=norm_zero.le.trans (mul_nonneg F.high.le (Scales.pos ..).le); have hn:= hq.2 ht ℝ 0 (fun i=>?_ ) (norm_zero.le.trans zero_le_one); swap; · simp [axl]; first|rfl|ext; simp [axl]; try split <;>rfl
   intro i; exact cull_p _ _ (fun l t=> sum_nonneg (fun j _=> (U_.clanV j).pos l t)) (add_nonneg (add_nonneg (plan_nn k (hq.1 i).nonneg) (hn.1.pays i).nonneg) (sum_nonneg (fun j _=> mul_nonneg (by norm_num) (U_.mote j).pos)))
 simp_rw [OpC,stars]; let xK:= fun y:ℝ=>Kplan k y; let a:ℝ:=(k+1); let L':= fun i:Lo=>Fief.tallyL o i σ (radiusB x)
 let vR(i:Lo):=potR (S:=S) (x:=x) Z_ v₀ i; let g(i:Lo):= potQ (S:=S) (x:=x) V' v₀ i
 have hu:0≤a:=by unfold a; positivity
 let b':=Kplan k 1; have hb:0 ≤ b':= plan_nn k zero_le_one
 have hs(x:ℝ): Kplan k x=b'*x:=by unfold b' Kplan Jet.composeCost; ring
 change ∑ i:Lo, L' i*(a*(Kplan k (M i)+ M' i+ vR i)+ h^2*(a*T' (g i))) ≤ a*(Kplan k E + Q.k₂ x+ Q.q₁ x) +h^2*(a*Q.q₂ x) -- tune T' inference
 simp_rw [mul_add, sum_add_distrib,mul_left_comm (L' _) (h^2),mul_left_comm (L' _) a, hs,mul_left_comm (L' _) b',←mul_sum] -- tune simp order
 exact add_le_add (add_le_add (add_le_add (by gcongr) (by gcongr)) (by exact mul_le_mul_of_nonneg_left zq hu)) (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left zp hu) (by positivity))
omit hz U_ B0
lemma expanse {D:ℕ}(P:Palot.leaf (Site (Domain N B))): (vast (k:=D) H (.inr (.inr P))).val ⊆ halo 21 P.val:=by
 change halo 20 (halo 1 _) ⊆ _; intro x h; obtain ⟨i,v,g⟩:= halo_spec.mp h; obtain ⟨j,w,k⟩:= halo_spec.mp v; exact halo_spec.mpr ⟨_,w,(separation_triangle j i x).trans (by omega)⟩
include hz
section
variable {ι:Type}[Fintype ι][LinearOrder ι]
set_option maxHeartbeats 500000 in
lemma bears (A_:Lo→Raid ι)(ht:∀ i:Lo,0 ≤ A_ i) (K:Lo→ Support (Domain N B))(hpV:∀ i:Lo,K i ⊆ halo 21 i.val) (h:ℝ)(z:0 ≤ σ)(u:0 ≤ h)(U:ℝ)(hv:∀ o:Site (Domain N B),(∑ i:Lo,tallyL o i σ x'*joinV (stake h) (A_ i))≤ U)(p:U≤1)(a:ℝ)(v:0≤a)(y:a*100000≤σ)(g:Lo→ Site (Domain N B))(hk:∀ i:Lo,g i∈i.val):(∑ i:Lo with g i=o,Trees.currency (radiusB x) a (K i) * joinV (stake h) (Rue.saber (A_ i) 1))≤ Real.exp (a*100000)*Real.exp 1*U:=by
 let V(i:Lo):=joinV (stake h) (A_ i)
 have hh(i:Lo): 0 ≤ V i:= sum_nonneg (fun a _=>mul_nonneg ((stokes (X:=ι) u).fee a) (ht i a))
 have hg(o: Site (Domain N B))(i:Lo):0 ≤ tallyL o i σ (radiusB x)*V i:=by unfold tallyL; split; exact mul_nonneg (Real.exp_pos _).le (hh _); rw [zero_mul]
 have hd(i:Lo): V i≤ U:=by
    obtain ⟨i',v⟩:= i.property; apply le_trans _ (le_trans (single_le_sum (f:=fun l=>tallyL i' l σ (radiusB x)*V l) (fun l _=>hg ..) (mem_univ i)) (hv i')); exact le_mul_of_one_le_left (hh _) (by rw [tallyL,if_pos v]; exact Real.one_le_exp (mul_nonneg z (by positivity)))
 let W:= (Real.exp (a * 100000)*Real.exp 1); have hw:0 ≤ W:=mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le; apply le_trans _ (mul_le_mul_of_nonneg_left (hv o) hw)
 change (∑ i:Lo with g i=o,_) ≤ W * ∑ i:Lo,tallyL o i σ (radiusB x)*V i; rw [sum_filter,mul_sum]; apply sum_le_sum; intro i _; by_cases hb:g i=o; swap; · rw [if_neg hb]; exact mul_nonneg hw (hg o i)
 let M':= coverNumber x' i.val; let C:= coverNumber x' (K i); have h':(x':ℕ)*C ≤ 100000*(x'+x'* M'):= (Nat.mul_le_mul_left _ (Corona.cover_mono (hpV i) _)).trans (YM.Next.Rank.Thirst.widen x' x' 21 (by omega) le_rfl (by omega) _); have he:C ≤ 100000*(1+M'):= Nat.le_of_mul_le_mul_left (h'.trans_eq (by ring)) (by omega : x'>0)
 have ht':Trees.currency (radiusB x) a (K i) ≤ Real.exp (a*100000)* tallyL o i σ (radiusB x):=by
    rw [Trees.currency,tallyL,if_pos (hb ▸ hk i),← Real.exp_add]; apply Real.exp_monotone; have hx:(C:ℝ) ≤ 100000*(1+M':ℝ):=by exact_mod_cast he
    apply (mul_le_mul_of_nonneg_left hx v).trans; change _ ≤ a*100000+σ*M'; nlinarith only [mul_le_mul_of_nonneg_right y (Nat.cast_nonneg (α:=ℝ) M')]
 rw [if_pos hb]; have hx:= Rue.peony 1 (ht i) (stokes (X:=ι) u); rw [pow_one] at hx
 let Rv:= Trees.currency x' a (K i)
 refine (mul_le_mul_of_nonneg_left hx (show 0 ≤ Rv from (Real.exp_pos _).le)).trans ?_; change Rv*(Real.exp (V i)* V i)≤ W*_; apply le_trans (mul_le_mul_of_nonneg_right ht' (mul_nonneg (Real.exp_pos _).le (hh i))); apply le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (Real.exp_monotone ((hd i).trans p)) (hh i)) ((Real.exp_pos _).le.trans ht')); unfold W; simp only [mul_comm,mul_left_comm,mul_assoc,le_refl] -- ambiguous exp ht'
end
include hz U_ B0
lemma bearsE (h:ℝ)(z:0 ≤ σ)(u:0 ≤ h)(p:legE Q h k x≤1)(a:ℝ)(v:0 ≤ a)(y:a*100000≤σ) (b:ℕ)(g:Lo→ Site (Domain N B))(hk:∀ i: Lo,g i∈i.val) : (∑ i: Palot.leaf (Site (Domain N B)) with g i=o,Trees.currency (radiusB x) a (vast (k:=b) H (.inr (.inr i))).val * joinV (stake h) (leoV (S:=S) x Z_ V' k v₀ i (M i) (M' i)))≤ Real.exp (a*100000)* Real.exp 1* legE Q h k x:=by
 exact bears o hz C_ (tallyX Q F M M' Z_ V' B0 U_ o hz h).1 _ (fun i=> expanse i) _ z u _ (fun i=>(tallyX Q F M M' Z_ V' B0 U_ i hz h).2) p a v y g hk

omit hz U_ B0
lemma legX(h:ℝ)(a:ℝ): sizeK R.L 3 fun x=> Real.exp (a*100000)*Real.exp 1*legE Q h k x:=by unfold legE steel; exact ((((((rates.arm _ _ _ Q.p1).accrue Q.p2).accrue Q.r1).scale _).accrue ((Q.r2.scale _).scale _)).scale _)
end YM.CF.Wray
