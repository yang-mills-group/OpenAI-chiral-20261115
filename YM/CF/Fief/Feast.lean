import YM.CF.Fief.Dell
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
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Stilo Palot Scion Function Levier Hake Urn Peaks Fock Laic Branch Drapes
open Rush Scroll Paige Vault Phase Acorn Spire Eire
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Jet Lich Corne
open Jet Push.AbsoluteSums
local notation "G₅"=> SU.group
variable {c f n N X B:Side}{S:StepData (Domain N B) (Domain X B)}{G:Ratio (mid N B) (mid X B)}{a b e C H D:ℝ}{k l j:ℕ}
open Lich.Muster Font
attribute [local instance] opCStarAlgebra
local notation "η"=> Domain N B
local notation "mX"=>Domain X B
variable (k) {M:Male} {K D v x:ℝ}
-- induced F Ledger at free histories any epoch. size capacity I(kernel). patches.D
variable (h:0<radiusB x)
def mintB(F:mSeal X B→ℝ)(Y:Bit (Site (Domain N B))) := ∑ i∈ Lich.Muster.queen (S:=S) (x:=x) k Y,F i
section
variable {F:mSeal X B→ℝ}
local notation "W" => Lich.Muster.Tee (x:=x) (P:=X) (B:=B)
include h
private abbrev coverG(i:mSeal X B) := Lattice.halo k (hatY S i)
abbrev price_g (L:Side)(σ ε v:ℝ)(k:ℕ)(x:ℝ):ℝ:= ((k*radiusB x+k*radiusB x+1)^4*L.val^4:ℕ) * (tollE σ (Stores.till x)*(Real.exp (ε*tileN k)*v))
lemma mass_h(t v:ℝ)(P:F=F)(g:0<t)(p:0 ≤ v)(hk:2*v*tileN k ≤t/2*S.patch.L.val*radiusB x)(Q:∀ i,0 ≤ F i)(hq:∀ i,F i≠ 0→Grove (terr _) i)(b:ℝ)(hp:0≤b)(he:∀ i,hitE t F i ≤ b)(u:Site (Domain N B)) :
 (∑ L:Bit (Site (Domain N B)),tallyL u L v (radiusB x)*mintB (S:=S) (x:=x) (k*radiusB x) F L) ≤ price_g S.patch.L t v b k x:=by
 let r:=k*radiusB x; let X'(i:mSeal X B):= coverG (S:=S) r i
 refine Eq.trans_le ?_ (venture S.ratio _ _ h t v g p hk Q hq (Lich.Muster.Tee (P:=X) (B:=B) (x:=x)) (Stores.till x) (fun i v=> by apply le_of_lt; simpa [Lich.Muster.Tee,Hest.portA] using v) he hp u)
 unfold mintB queen; simp_rw [mul_sum,sum_filter]; rw [sum_comm]; apply sum_congr rfl; intro i p; let f:=X' i; have hh:(Stores.till x)< i.card:=by simpa [Tee,Hest.portA] using p
 have heZ:f.Nonempty:= ((card_pos.mp (show 0 < i.card from Nat.lt_of_le_of_lt (Nat.zero_le _) hh)).image (S.ratio.parent)).mono (halo_subset ..); let L:= (⟨f,heZ⟩:Bit (Site (Domain N B)))
 rw [sum_eq_single L]; dsimp only [tallyL]; split
 next y=> change (if u∈ f then Real.exp (v* ↑(coverNumber (radiusB x) f)) else 0)*F i=if u∈ f then F i*Real.exp (v* ↑(coverNumber (radiusB x) f)) else 0; split <;> first| apply mul_comm | rw [zero_mul]
 next y=> exact False.elim (y rfl)
 · intro b _ t; rw [if_neg (fun p=>t (Subtype.ext p.symm))] -- tune orientation branch
 simp
variable{W':mSeal X B→ℝ}{P:mSeal X B→ Toll (Single (mid N B))}
variable{F':Haze N X B G e}{Z:mSeal X B→Rent0 G e→ℂ}
local notation "ρ"=> k*radiusB x
lemma tallA {C s' b v:ℝ}{r:ℕ}(h0:Odd G.count.val)(hR:S.ratio=ratio G)(P':∀ i: mSeal X B,Filer G i (P i) C r (F' i))(H:Ledger v P b)(ht:0 < v)(hz:0 ≤ s') (hk:2*s'*tileN k ≤ v/2/2*S.patch.L.val*radiusB x)(u:Site (Domain N B)) :
 let V:= lampQ v*b; (∑ L:Bit (Site (Domain N B)),tallyL u L s' (radiusB x)*ledgerV (potQ (x:=x) (S:=S) P ρ L)) ≤ price_g S.patch.L (v/2) s' V k x:=by
 intro V; let Q(i):= ledgerV (P i); have hp:0 ≤ V:=by unfold V lampQ; apply mul_nonneg (tsum_nonneg _) H.posP; intro i; unfold Tenant.quota; positivity
 rw [show (∑ L:Bit _,_) = ∑ L: Bit (Site (Domain N B)), tallyL u L s' (radiusB x)*mintB (S:=S) (x:=x) ρ Q L from ?_]
 swap
 · apply sum_congr rfl; intro L _; congr 1; change ∑ i: Single (mid N B),∑ j,∑ x'∈_, P x' i j=_; simp_rw [sum_comm (f:=fun j x=> P x _ j)]; rw [sum_comm]; rfl -- tune
 refine mass_h k h _ _ (F:=fun x=>ledgerV (P x)) rfl (half_pos ht) hz hk (fun i=>sum_nonneg (fun j _=>sum_nonneg (fun l _=>(P' i).pos j l))) ?_ V hp (cap_l G r h0 P' H ht) u
 intro i t; obtain ⟨u,hq,t⟩:= Finset.exists_ne_zero_of_sum_ne_zero t; obtain ⟨j,k,h⟩:= Finset.exists_ne_zero_of_sum_ne_zero t; exact ((P' i).root u j h).1 -- tune sum syntax
lemma tallS {r:ℕ}(p:∀ i,Flash (dressL G e) (LineE r G C e) r i (Z i) (W' i))(hP:∀ i,hitE a W' i≤ b)(hv:0 ≤ b)(hp:0<a)(ht:0 ≤v)(hk: 2*v*tileN k≤ a/2*S.patch.L.val*radiusB x)(u:Site (Domain N B)): (∑ L:Bit (Site (Domain N B)), tallyL u L v (radiusB x)*potR (x:=x) (S:=S) W' ρ L)≤2*price_g S.patch.L a v b k x:=by
 let M:=mintB (S:=S) (x:=x) ρ W'; have he(X):potR (x:=x) (S:=S) W' ρ X=2*M X:=by unfold M potR mintB; rw [mul_sum]
 apply le_trans _ (mul_le_mul_of_nonneg_left (mass_h k h a v (F:=W') rfl hp ht hk (fun i=>(p i).pos) (fun i=> (p i).travel) b hv hP u) (by norm_num:0≤(2:ℝ))); apply Eq.le; simp_rw [he]; rw [mul_sum]; apply sum_congr rfl; intro i v; change _=2*(_ * M i); ring
end
lemma invest_g {v:ℝ}(n:ℕ)(hp:0<a)(Z:Side) : sizeK Z n (price_g Z a b v k):=by
 unfold price_g; push_cast
 let K:= ((sizeK.Bcash Z).scale k); let P:= (((K.accrue K).accrue (sizeK.mild Z 1)).powC 4).tint (sizeK.mild Z ((Z.val:ℝ)^4)); have hv :sizeK Z n (fun x=> tollE a (Stores.till x)):= by simpa only [Nat.div_one] using sizeK.val_gain Z a hp 1 (by norm_num) n
 rw [←Nat.zero_add n]; exact P.tint (hv.tint (sizeK.mild Z _))
end YM.CF.Fief
