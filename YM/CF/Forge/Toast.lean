import YM.CF.Forge.Dawn
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Forge
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD Ac Esti
variable {G:Gauge}{c f:Side}{S:StepData c f}{r v l:ℕ}{w x β d:ℝ}{q:Chi}{T:Tube G S}
open AnalyticBridge.SectorAffine Oriented
local notation "G"=>SU.group
variable {M N:Monk G S}{T:Tube G S}{K:Stores S}{J:ChartRatio G}{s:ℝ}
section axe
variable {X:Support c}(h:Beat M N X)(hr:Ready T x)(hp:1000≤radiusB x){l:ℕ}
local notation "b"=>radiusB x
include hr h hp
lemma rimP {a:Prices SU.group (M.zoo x)}{c':Prices SU.group (N.zoo x)}(i:Rows.Receipt SU.group S)(u:Beat.shadows (o:=down S i) X (15*b)) (H:∀ j j',PatchReads.lift («G»:=G) (x:=x) (A:=M.key) (F:=M.park) j=PatchReads.lift (x:=x) (A:=N.key) (F:=N.park) j' →separation (down S i) (front M.key M.park j) ≤ b→a j=c' j') : axle M.key M.park T x M.k q d (M.bush x) a M.V i = axle N.key N.park T x N.k q d (N.bush x) c' N.V i :=by
 let r:= span S.patch x; have ht:=hr.inputs; change r ≤ b/50 at ht
 have he := h.scope (x:=x) (r:=2*r) (by omega) u
 unfold axle; simp only [Pi.add_apply, Matrix.mulVec,dotProduct, plinth (i:=i) hr.rules he q d]; congr 1
 apply PatchReads.sum_eq (he.lower (r':=r) (by omega)) (fun j hj=>?_ ) (fun j hj=> ?_) (fun j j' k l=>?_ )
 · rw [move_range hr.rules hj,zero_mul]
 · rw [move_range hr.rules hj,zero_mul]
 rw [move_eq hr.rules (he.lower (r':=r) (by omega)) l,H j j' l (by omega)]
lemma axles {a:Prices SU.group (M.zoo x)}{c':Prices SU.group (N.zoo x)}(s':Signed)(u: K.dome (r+(l+65)*b) ⊆ X)(H:∀ j j',PatchReads.lift («G»:=G) (x:=x) (A:=M.key) (F:=M.park) j=PatchReads.lift (x:=x) (A:=N.key) (F:=N.park) j' →Beat.shadows (o:=front M.key M.park j) X ((l+62)*b)→a j=c' j') : columnP s' (wheel M.key M.park T x M.k q d (M.bush x) a M.V) (anchorage (turnStore s' K) r) = columnP s' (wheel N.key N.park T x N.k q d (N.bush x) c' N.V) (anchorage (turnStore s' K) r):=by
 let Y:=wheel M.key M.park T x M.k q d (M.bush x) a M.V; let W:=wheel N.key N.park T x N.k q d (N.bush x) c' N.V; have hv(i:Slots S)(p:∀ j:SU.group.ColorIndex, down S (i,j) ∈ K.dome r): Y i=W i:=by
    ext j; have hp':=foster (p j) u (show r+(l+65)*b ≤ _ from le_rfl); refine rimP (q:=q) (d:=d) h hr hp (i,j) (aroundBk X hp' (by simp_rw [separation_self,Nat.add_mul]; omega)) (fun u v t w=> H _ _ t (aroundBk X hp' (by simp_rw [Nat.add_mul]; omega)))
 unfold columnP; refine congrArg₂ (·+·) (sum_congr rfl fun i j=>sum_congr rfl fun l _=>?_ ) (sum_congr rfl fun i p=>?_ )
 · unfold media; rw [show wheel M.key M.park T x M.k q d (M.bush x) a M.V (s',.inl (i,l))= _ from hv _ (fun j'=> (dome_turn s' K r _).mp ((mem_filter.mp j).2))]
 unfold media; rw [show wheel M.key M.park T x M.k q d (M.bush x) a M.V (s',.inr i)= _ from hv _ (fun j=>(dome_turn s' K r _).mp ((mem_filter.mp p).2))]
end axe
variable {X:Support c}(h:Duo G S M N X)(hr:Ready T x)(hp:1000≤radiusB x)(hz:shovel S.patch+10≤ radiusB x)(l':spanO T x){l:ℕ}
include h hr hp hz l'
lemma pepr (g:K.dome ((r+187+l)*radiusB x) ⊆ X): M.pep x T s K q d l β w J r=N.pep x T s K q d l β w J r:=by
 unfold Monk.pep; rw [paysS h hr hp hz g,crest_l h hp g hr]; congr 2; unfold Monk.tin Esti.σ pist; dsimp only; refine congrArg (_ * ·) (congrArg averaged (funext fun i=>?_ ))
 have ht:K.dome (r*radiusB x+(l+65)*radiusB x) ⊆ X:= Subset.trans (farther (by simp_rw [Nat.add_mul]; omega)) g
 refine congrArg₂ (·+·) (congrArg₂ (·-·) ?_ (axles (q:=q) (d:=d) h.toBeat hr hp i ht (fun j j' l u=>h.toBeat.reaction (q:=q) (d:=d) (β:=β) hr hp l u))) ?_
 · exact vixen (q:=q) (d:=d) (β:=β) (l:=l) i h hr hp hz s K (r*radiusB x) l' (Subset.trans (farther (by simp_rw [Nat.add_mul]; omega)) g)
 refine axles (q:=q) (d:=d) h.toBeat hr hp i ht (fun j j' p u=>?_); exact liftN_read hr (h.toBeat.scope (r:=(l+41)*radiusB x) (by simp_rw [Nat.add_mul]; omega) u) p
end YM.CF.Forge
