import YM.CF.Forge.Cigar
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
namespace Monk
local notation "G"=>SU.group
variable (x:ℝ)(T:Tube SU.group S)(s:ℝ)(M:Monk G S)(K: Stores S)(q:Chi)(d:ℝ)(l:ℕ)(β w:ℝ)(J:ChartRatio G)(r:ℕ)
def silver:=dawnP T M.key K M.park M.V x M.k q d (M.bush x) l (M.bell x) β r s w
def copper:= beamE T M.key K M.park M.V x M.k q d (M.bush x) l (M.bell x) β J r
def tin:=Esti.σ T M.key K M.park x M.k q d (M.bush x) l (M.bell x) β r s (fun _:ℝ=> M.V) 0
def pep:=M.silver x T s K q d l β w r*M.copper x T K q d l β J r*Real.exp (M.tin x T s K q d l β r) -- tune dot order
end Monk
lemma foster {X:Support c} {i:Site c}{A:Stores S}{m:ℕ} (p:i∈A.dome r)(h:A.dome v⊆X)(q:r+m ≤ v) : Beat.shadows (o:=i) X m:=by intro j hp; obtain ⟨z,hg,hp⟩:=halo_spec.mp hp; rw [mem_singleton.mp hg] at hp; obtain ⟨t,p,u⟩:=halo_spec.mp p; exact h (halo_spec.mpr ⟨t,p,(separation_triangle t i j).trans (by omega)⟩)
section
local notation "G"=> SU.group
variable {K:Stores S}{J:ChartRatio G}{s:ℝ}{l:ℕ}{T:Tube SU.group S}{X:Support c}{M N:Monk G S}(h:Duo G S M N X)(hr:Ready T x)(hp:1000≤radiusB x)(hz:shovel S.patch+10≤ radiusB x)
local notation "b"=>radiusB x
local notation "Ms"=>M.sent x T q d l β
local notation "Ns"=>N.sent x T q d l β
include h hr hp hz
lemma paysS (u:K.dome ((r+187+l)*b)⊆ X) : M.silver x T s K q d l β w r = N.silver x T s K q d l β w r:=by
 let L:= obv x r 100 K; let H:= obv x r 110 K; have hb : cohoT M.key x w s q M.V Ms M.k L H=cohoT N.key x w s q N.V Ns N.k L H:=by
    unfold cohoT Esti.total; have he(i)(v:i∈L):Beat.shadows (o:=i) X ((l+70)*b):=foster (show i∈ K.dome ((r+100)*b) from v) u (by simp_rw [Nat.add_mul]; omega)
    have hh(i)(z:i∈nearNoise L): Beat.shadows (o:=i.1) X ((l+68)*b):=by
       obtain ⟨j,p,k⟩:=Finset.not_disjoint_iff.mp ((mem_filter.mp z).2); exact aroundBk X (he j k) ((Nat.add_le_add_right (price_pin i p (mem_insert_self ..)) _).trans (by simp_rw [Nat.add_mul]; omega))
    refine congrArg₂ (· * ·) (congrArg₂ (· * ·) (prod_congr rfl fun i k=> ?_) (prod_congr rfl fun i k=> h.ebb_p hr hp hz i (hh _ k) s)) (congrArg₂ (· * ·) (prod_congr rfl fun i k=>h.frameR hr hp hz i (aroundBk X (he i k) (by simp_rw [separation_self,Nat.add_mul]; omega))) (prod_congr rfl fun i k=> (h.turnI hr hp hz i s (hh i k)).2))
    obtain ⟨j,p,k⟩:= Finset.not_disjoint_iff.mp ((mem_filter.mp k).2); have ht :Beat.shadows (o:=j) X ((l+71)*b):=foster (show j ∈ K.dome ((r+110)*b) from k) u (by simp_rw [Nat.add_mul]; omega)
    refine h.biri hr hp i (aroundBk X ht ?_); obtain ⟨e,t,rfl⟩:=mem_image.mp p; have h:= Work.E04.parent_separation S.ratio i.1 e; have hp:=Work.E01.sep_touched i _ t; rw [separation_comm (S.ratio.parent e)]; simp_rw [Nat.add_mul]; omega
 exact hb
omit h hr hp hz
private lemma sees_u {M:Monk G S}(A:Stores S)(w':ℕ){i:Active M.key x M.park}(h:i∈locals M.key A x M.park w'):S.ratio.parent i.val.val.1 ∈ A.dome (w'+1):=by
 rcases (mem_filter.mp h).2 with p|p; exact farther (Nat.le_succ _) p
 obtain ⟨j,w,p⟩:=halo_spec.mp p; let k:=i.val.val; let z':=S.ratio.parent k.1
 exact halo_spec.mpr ⟨j,w,(separation_triangle j (S.ratio.parent (k.1+step k.2)) z').trans (Nat.add_le_add p ((separation_comm ..).trans_le (Work.E03.parent_step S k.1 k.2)))⟩
include h hp
lemma crest_u(u:K.dome ((r+187+l)*b)⊆ X)(z:SU.group.Color→ℝ) (hr:Ready T x): ∏ i∈locals M.key K x M.park ((r+104)*b),z (M.rich x T q d l β i) = ∏ i∈locals N.key K x N.park ((r+104)*b),z (N.rich x T q d l β i):=by
 let a:= (r+104)*b; let g:= locals M.key K x M.park a; let f:= locals N.key K x N.park a
 have hh{A: Monk G S}(i:Active A.key x A.park)(p:i∈locals A.key K x A.park a):Beat.shadows (o:=S.ratio.parent i.val.val.1) X ((l+62)*b):=foster (sees_u (M:=A) K a p) u (by unfold a; simp_rw [Nat.add_mul]; omega)
 have ht{M N:Monk G S}(h:Beat M N X)(i:Active M.key x M.park)(p:i∈locals M.key K x M.park a):∃ j:Active N.key x N.park,j∈locals N.key K x N.park a ∧ i.val.val=j.val.val:=by
    obtain ⟨j,v⟩:=(h.scope (r:=0) (by simp_rw [Nat.add_mul]; omega) (hh i p)).switch i (by simp)
    refine ⟨j,mem_filter.mpr ⟨mem_univ _,?_⟩,v⟩; exact v ▸ (show witnesses K a _ from (mem_filter.mp p).2)
 choose G' hG hG' using fun i p=>ht h.toBeat i p; refine prod_bij G' hG (fun x p y t v=> ?_) (fun x p=>?_) (fun i p=>congrArg z (h.toBeat.reflected hr hp (hG' _ p) (hh _ p)))
 · exact Subtype.ext (Subtype.ext ((hG' x p).trans ((congrArg (fun i:Active N.key _ N.park=>i.val.val) v).trans (hG' y t).symm)))
 obtain ⟨i,t,w⟩:= ht h.toBeat.sym x p; exact ⟨i,t,Subtype.ext (Subtype.ext ((hG' _ t).symm.trans w.symm))⟩ -- injection eq tune orientation
lemma crest_l(u:K.dome ((r+187+l)*b)⊆ X) (hr:Ready T x): M.copper x T K q d l β J r=N.copper x T K q d l β J r:=congrArg₂ (·*·) (crest_u (q:=q) (d:=d) (β:=β) h hp u (extended q J d) hr) (crest_u (q:=q) (d:=d) (β:=β) h hp u (broad q d) hr)
end
end YM.CF.Forge
