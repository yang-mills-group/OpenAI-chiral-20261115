import YM.CF.Scion.Emp
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
abbrev fJ(y:Rent0 G e)(i:Site D₀):= ∑ j∈ univ.filter (fun j:Y=> j.card≤Stores.till x), turtle (ratio G) j i • Q j y
structure Bride (j:ℕ)(i:Site D₀):Prop where
 feat (k:Bond D₀): separation i k.1 ≤ j→ A.val.2 k= S.V k
 pear (k:Bond D₁): separation i (T.ratio.parent k.1) ≤ j→ A.val.1 k=S.sent x F q d l β k
local notation "k₀"=>(S.park,S.k)
lemma studio (h:Thu F x u l Q t K n η C a Z V R Φ)(i:Site D₀)(hp:i∉ S.key.dome (Cay.horn x l))(p:Taurus u S (Cay.horn x l) i)(hk:Bride G F x d q l S A β (radiusB x+1) i)(hs:S.z=0): Facet.plain F x q d u l Q t k₀ i S.V=fJ G Q x A i:=by
 obtain ⟨g,y,t',hz⟩:= p.found; let U:= hornY F q x d l k₀ y; have he:= firm F x q d u l Q t h.funds h.ready (h.tall (S.park,S.k)) h.pay (h.ears _) h.sizes y t'
 have hF:=firn F x q d u l Q t h.funds h.ready (h.tall (S.park,S.k)) h.pay (h.ears _) h.sizes (i:=i) g y he
 rw [honor _ _ _ _ _ _ _ _ h.funds h.ready (h.tall _) h.pay (h.ears _) h.sizes h.fine _ t' hz,← hF.2]; obtain ⟨N,H,K⟩:=h.pay.members
 unfold turf fJ; refine Finset.sum_congr rfl fun j v=>?_ ; unfold Facet.test; rw [pear_even G t hF.1]; by_cases p:N j=0; · simp only [show Q j=0 from funext fun i=> norm_le_zero_iff.mp ((H j).sumline i|>.trans_eq p), Pi.zero_apply]
 by_cases t0:i∈ Facet.mount (ratio G) j; swap; · simp [Facet.turtle,t0]
 apply congrArg (turtle (ratio G) j i • ·)
 let D:=Cay.horn x l; have ht':= h.fine; have hy'(v':Site D₁)(hv:v'∈ j):separation i (T.ratio.parent v') ≤ radiusB x+1:=by rw [h.sizes]; apply (thigh (ratio G) ((H j).travel p) t0 _ hv).trans; exact Nat.add_le_add_right (((mem_filter.mp v).2).trans (Nat.div_le_self _ _)) _
 let V':=Lattice.gauge g y; let S': Monk G₅ T:={faint S with V:=V'}; let Z':=bunk T (S.park,S.k) V'
 let H₁:Beat (faint S) S' (pavilion (Cay.horn x l) i):= ⟨fun _ _=>Iff.rfl,fun _ _=>rfl,fun _ _=>rfl,fun _ _=>Iff.rfl,fun i h' _=>(hz i ((theatre ..).mp h')).symm,fun _ _=>rfl,fun _ _=>rfl⟩
 let A':Rent0 G e:=⟨_,hF.1⟩; have he:Q j A'=Q j A:=by
    apply (H j).reads A' A; constructor
    · intro e u v; change Z'.sent x F q d l 0 e=A.val.1 e; rw [hk.pear e (hy' _ u), show S.sent _ _ _ _ _ _ e=_ from ((show Beat S S' (pavilion D i) from { H₁ with road:=(aura hp).road })).backF h.ready h.fine e ?_,flatR F x q d l β S' hs]
      swap; exact aroundBk (pavilion (Cay.horn x l) i) (Subset.refl _) (by have hp:= hy' _ u; unfold Cay.horn; simp_rw [Nat.add_mul]; omega)
      have he: S'.sent x F q d l 0= Z'.sent x F q d l 0:=by
        change landed x S'.key S'.park S'.V (S'.bush x) (S'.fuel x F q d l 0)=landed x S'.key S'.park S'.V (Z'.bush x) (Z'.fuel x F q d l 0); rw [oasisN _ _ _ _ _ (M:=S') hs,oasisN _ _ _ _ _ (M:=Z') rfl,show S'.bush x=Z'.bush x from funext fun i=> False.elim ((notChilled _ _ _ i.val) i.property)]
      rw [he]
    intro e u v; have ht':= hy' _ (mem_filter.mp u).2; rw [h.sizes,Ratio.embed_parent] at ht'; change Lattice.gauge g y e=A.val.2 e; rw [hk.feat _ ht', hz e (by change separation _ _≤ _; unfold Cay.horn; simp_rw [Nat.add_mul]; omega)] -- tune V' beta
 exact he
end
end YM.CF.Corne
