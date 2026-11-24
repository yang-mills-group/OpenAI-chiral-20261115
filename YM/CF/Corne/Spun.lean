import YM.CF.Corne.Pink
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
-- read by anchor i = place_x SINGLE harmonic pair
section
variable (i j:Single (CSide Mx B))
local notation "k₀"=> (S.park,S.k)
def led (A:Rent0 G e): Op (Single (CSide Mx B)):= ∑ q∈ Hest.portA (Stores.till x), H q A
lemma themeX (ht:T.ratio=ratio G)(hp:i=i)(ha:Bride G F x d q l S A β (radiusB x+1) (place_x i))(A₀:Hest.Haze Mx X B G e){Xr:nomA Mx X B→Op (Single (CSide Mx B))}(hv:Hest.Ind G H a C D n Xr)(hx: Ready F x)(hB:1000≤ radiusB x)(hb:place_x i∉ S.key.dome (Cay.horn x l))(u:Config G₅ D₀)(hz:Tarn.drift G₅ (place_x i) (Cay.horn x l) S.V u)(g:S.z=0)(hr: hornY F q x d l k₀ u∈ Rent0 G e):
 led G x H A i j=shelfH G H t x (hornY F q x d l k₀ u) i j:=by
 obtain ⟨S',p,H'⟩:=hv.port; let Q:= faint S; let Z:Monk G₅ T:={Q with V:=u}; let W:= bunk T (S.park,S.k) u; let P:= place_x i; let A':Rent0 G e:=⟨_,hr⟩
 unfold led shelfH; rw [Matrix.sum_apply,Matrix.sum_apply,pear_even G t hr]; refine Finset.sum_congr rfl fun l' a=> ?_ ; let V:= p l'; by_cases h:S' l' i j=0
 · exact (norm_le_zero_iff.mp ((V.gate i j _).trans_eq h)).trans (norm_le_zero_iff.mp ((V.gate i j A').trans_eq h)).symm
 obtain ⟨hp,hP,_⟩:= V.root i j h; have he:P∈ Facet.mount (ratio G) l':=mem_image.mpr ⟨_,(mem_filter.mp hP).2,(ratio G).embed_parent _⟩; apply congrArg (fun y:Op (Single (CSide Mx B))=> y i j) (V.reads A A' ?_); constructor
 · intro e v w; have h: separation P (T.ratio.parent e.1) ≤ radiusB x+1:= by rw [ht]; exact (thigh _ hp he _ v).trans (Nat.add_le_add_right (((mem_filter.mp a).2).trans (Nat.div_le_self _ _)) _)
   have hp:Beat S Z (pavilion (Cay.horn x l) P):= ⟨(aura hb).road,fun _ _=>rfl,fun _ _=>rfl,fun _ _=>Iff.rfl,fun i v _=>hz _ ((theatre ..).mp v),fun _ _=>rfl,fun _ _=>rfl⟩; change A.val.1 _ = W.sent x F q d l 0 e; rw [ha.pear _ h, hp.backF hx hB e (aroundBk _ (Subset.refl _) (by unfold Cay.horn; simp_rw [Nat.add_mul]; omega)),flatR F x q d l β Z g]
   have hZ:Z.sent x F q d l 0=W.sent x F q d l 0:=by
        change landed x Z.key Z.park Z.V (Z.bush x) (Z.fuel x F q d l 0)=landed x Z.key Z.park Z.V (W.bush x) (W.fuel x F q d l 0); rw [oasisN _ _ _ _ _ (M:=Z) g,oasisN _ _ _ _ _ (M:=W) rfl,show Z.bush x=W.bush x from funext fun i=> False.elim ((notChilled _ _ _ i.val) i.property)]
   rw [hZ]
 intro e v w; have he':= (thigh _ hp he _ (mem_filter.mp v).2).trans (Nat.add_le_add_right (((mem_filter.mp a).2).trans (Nat.div_le_self _ _)) _) -- tune implicit till
 rw [Ratio.embed_parent] at he'; exact (ha.feat _ he').trans (hz e (by unfold P at he'; unfold Cay.horn; simp_rw [Nat.add_mul]; omega))
variable {Xr:nomA Mx X B→Op (Single (CSide Mx B))}
local notation "P'"=>place_x i
lemma swingS (ht:T.ratio=ratio G)(ha:Bride G F x d q l S A β (radiusB x+1) (place_x i))(h: Hest.Ind G H a C D n Xr)(hx: K.Funds T F)(hp:Ready F x)(hg:1000 ≤ radiusB x)(hv:S.z=0)(m:Site D₀→ SU.E)(u:ℝ)(v:Mast G₅ D₀)(hy:Fire F x S.park S.k l u n R v)(hw:Fleck G t S.park η D n)(ht':‖Souk.flute S.park (sol T F S.k x S.park l) u v‖<η)(hc:Tarn.drift G₅ P' (Cay.horn x l) S.V (Lattice.gauge m (satU G₅ u v)))(hf:P'∉ S.key.dome (Cay.horn x l)) :
 led G x H A i j=ActZ m (shelfH G H t x (teen S.park F x S.k l u v)) i j:=by
 let U:= satU G₅ u v; let S':= Souk.flute S.park (sol T F S.k x S.park l) u v; let V':= Lattice.gauge m U; have hv': (hornY F q x d l k₀ U)∈ Rent0 G e:=(wreath F q x d l k₀ v hy).symm ▸ hw.onP _ ht'
 let H₀:= constantGauge m T.ratio; let Z:= shelfH G H t x; let P₀:Rent0 G e:=⟨_,hv'⟩
 have hF:hornY F q x d l k₀ V'= Peaks.july G H₀ P₀.val:= candle F q x d l ht _ _ m hx; have hz:hornY F q x d l k₀ V'∈Rent0 G e:= hF.symm ▸ Peaks.joint_g G _ hv' H₀
 rw [themeX G F x d q l S A β t H i j ht rfl ha H h hp hg hf _ hc hv hz]; apply congrArg (fun k:Op (Single (CSide Mx B))=> k i j) ; change shelfH G H t x (hornY F q x d l k₀ V') = _ -- tune need show equality op
 obtain ⟨W,p,K⟩:=h.port; unfold shelfH; rw [show teen S.park F x S.k l u v=hornY F q x d l k₀ U from (wreath F q x d l k₀ v hy).symm]; rw [pear_even G t hz,pear_even G t hv']; unfold ActZ; rw [map_sum]; apply sum_congr rfl; intro i h; have he:scaleG G H₀=m:=by unfold scaleG H₀; funext i; simp only [Function.comp_apply,constantGauge,ht,Ratio.embed_parent]
 let X:Rent0 G e:=⟨_,hz⟩; change H i X=ActZ m (H i P₀); rw [show X=(dressL G e).dress H₀ P₀ from Subtype.ext hF,(p i).gauge,he]
end
end
end YM.CF.Corne
