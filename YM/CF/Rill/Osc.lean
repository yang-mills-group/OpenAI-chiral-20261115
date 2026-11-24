import YM.CF.Rill.Peer
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Rill
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD Ac Esti
variable {c f:Side}{S:StepData c f}{r v l:ℕ}{w x β d:ℝ}{q:Chi}
open CF.Forge
open AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Matrix
local notation "G"=>SU.group
open Err
variable {M N:Monk G S}{e b w K t:ℝ} {U V:Config G c}{E F:Support c} {T:Tube G S}
open Jet
section shake
variable {E F L:Type*}[NormedAddCommGroup E][NormedSpace ℝ E] [NormedAddCommGroup F][NormedSpace ℝ F][NormedAddCommGroup L][NormedSpace ℝ L]{f g:E→ F}{X:E}{d b:ℝ}{k l n:ℕ}
structure Shake (f:E→F)(X:E)(b:ℝ)(n:ℕ):Prop where
 price:0≤b
 smooth: ContDiffAt ℝ (↑n) f X
 bill(k:ℕ):0<k→k≤n→ ‖iteratedFDeriv ℝ k f X‖ ≤ b
namespace Shake
lemma pick(p: Allows n f X b):Shake f X b n :=⟨p.nonneg,p.smooth,fun i _=>p.norm_le i⟩
lemma paid (p:Shake f X b n)(h:‖f X‖≤d): Allows n f X (max b d):=by
 refine ⟨p.smooth,fun i v=>?_⟩; cases i; rw [norm_iteratedFDeriv_zero]; exact h.trans (le_max_right ..); exact (p.bill _ (Nat.zero_lt_succ _) v).trans (le_max_left ..) -- tune
lemma same (p: Shake f X b n)(h:f=ᶠ[𝓝 X] g):Shake g X b n:=⟨p.price,p.smooth.congr_of_eventuallyEq h.symm,fun i t v=>by rw [← (h.iteratedFDeriv ℝ i).self_of_nhds]; exact p.bill i t v⟩
lemma holds(F:F): Shake (fun _:E=>F) X 0 n:=⟨le_rfl,contDiffAt_const,fun k v _=>by rw [iteratedFDeriv_const_of_ne (Nat.ne_of_gt v),Pi.zero_apply,norm_zero]⟩
lemma bag(p:Shake f X b n)(h:b≤d):Shake f X d n:=⟨p.price.trans h,p.smooth,fun i v w=>(p.bill i v w).trans h⟩
lemma team(p: Shake f X b n){v:E→ L}(h: Shake v X b n):Shake (fun i=>(f i,v i)) X b n:=by refine ⟨p.price,p.smooth.prodMk h.smooth,fun i u j=>?_⟩; rw [iteratedFDeriv_prodMk p.smooth h.smooth (Nat.cast_le.mpr j), ContinuousMultilinearMap.opNorm_prod]; exact max_le (p.bill i u j) (h.bill i u j)
def quota(k:ℕ):ℝ:= ∑ i:Fin (k+1),(Fintype.card (OrderedFinpartition i):ℝ)
lemma quake(n:ℕ):0≤ quota n:=by unfold quota; positivity
lemma order(k:ℕ)(l:ℕ)(v:k≤l):(Fintype.card (OrderedFinpartition k):ℝ) ≤ quota l:=by let j:Fin (l+1):=⟨k,Nat.lt_succ_of_le v⟩; exact single_le_sum (f:=fun j:Fin (l+1)=>(Fintype.card (OrderedFinpartition j):ℝ)) (fun i _=>by positivity) (mem_univ j)
lemma thorn(p:Shake f X b n){g:F→ L}(h:Shake g (f X) d n)(hp:b≤1): Shake (g ∘ f) X (quota n*(d*b)) n:=by
 have ht:=p.price; have hx:=h.price; refine ⟨by have hu:=quake n; positivity,h.smooth.comp X p.smooth,fun i u v=>?_⟩
 rw [iteratedFDeriv_comp h.smooth p.smooth (Nat.cast_le.mpr v)]; refine (norm_sum_le ..).trans ((sum_le_sum (g:=fun _:OrderedFinpartition i=>d*b) fun j _=> ?_).trans ?_)
 · have hl:0<j.length:= j.length_pos u -- tune
   have hv:=j.norm_compAlongOrderedFinpartition_le (iteratedFDeriv ℝ j.length g (f X)) (fun k=>iteratedFDeriv ℝ (j.partSize k) f X); refine hv.trans (mul_le_mul (h.bill _ hl (j.length_le.trans v)) ?_ (by positivity) hx); refine le_trans (Finset.prod_le_prod (g:=fun _=>b) (fun i p=>by positivity) (fun k _=>p.bill _ (j.partSize_pos k) ((j.partSize_le k).trans v))) ?_; simp only [prod_const,card_univ,Fintype.card_fin]; exact (pow_le_pow_of_le_one ht hp (show 1≤j.length from hl)).trans_eq (pow_one _)
 simp_rw [sum_const,nsmul_eq_mul,card_univ]; gcongr; apply order i n v
end Shake
end shake
end YM.CF.Rill
