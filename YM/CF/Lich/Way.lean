import YM.CF.Lich.Line
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Lich
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Stilo Palot Scion Function Levier Hake Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire Eire
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
-- separate path ledger Φ.M.Target.S.P
variable {N P B:Side}(G:Ratio (mid N B) (mid P B))(S:StepData (Domain N B) (Domain P B))(x e:ℝ)(T:Tube SU.group S)
variable{r n j d:ℕ}
namespace Muster
variable{G S x e T}
variable(A:Muster G S x e T)
variable(U: Monk SU.group S)(V W:Rent0 G e) -- V true W at ζ=0
local notation "θ"=> A.room
local notation "j"=> A.loft
local notation "β"=> A.beta
local notation "q"=> A.trot
local notation "α"=> A.ang
local notation "γ"=> A.fee
local notation "l"=> A.post
local notation "F"=> U.sent x T q θ l β
local notation "Y"=> (U.park,U.k)
local notation "K"=> U.key.dome (j*radiusB x)
local notation "Q'"=> A.LawQ
local notation "YY"=> A.Beds
-- account per site
-- far components plus interior.Optional momentum.
open Corne
open Matrix Further.CurvedGaussianJets.Tracks PhysicalNext.OrderedAffine2B.SymFare
local notation "N₀"=> kist U
-- group totals: EACH path says cost at root.Can enlarge inside blockProof local growth
local notation "A'"=> emptyA T x U.k U.key U.park U.V
local notation "B'"=> perZ T x U.k U.key U.park U.V
def vent (u:Run (U.zoo x) (n+1)):= -(1/2:ℝ)*barP A' B' u
-- param
variable(T)
def paveB (w:LinkS S n)(M:Monk SU.group S):ℝ := if h:∃ u: Run (M.zoo x) (n+1),stave u=w then vent (T:=T) M h.choose else 0 -- x implicit fails
lemma stationB(u:Run (U.zoo x) (n+1)): paveB (x:=x) T (stave u) U= vent (T:=T) U u:=by
 let h:∃ v:Run (U.zoo x) (n+1), stave v=stave u:= ⟨_,rfl⟩; unfold paveB; rw [dif_pos h,stave_inj h.choose_spec]
variable{H : Support (Domain N B)}{M' : Monk SU.group S}(w:LinkS S n)
section
variable{U}
lemma stampP {u:Run (U.zoo x) (n+1)} {v:Run (M'.zoo x) (n+1)}(hr:Ready T x)(hp:1000 ≤ radiusB x)(p:stave u=stave v)(h: Beat U M' H)(hh:∀ i,Beat.shadows (o:= S.ratio.parent (stave u i).1) H ((l+58)*radiusB x)):vent (T:=T) U u=vent (T:=T) M' v:=by
 let r:=radiusB x; have he: ∀ i,(u i).val.val=(v i).val.val:=congrFun p
 have hx(i):= h.scope (x:=x) (r:=(l+46)*r + r) (by unfold r; simp_rw [Nat.add_mul]; omega) (hh i) -- uses Y,K
 have hv:=Sample.less («Y»:=U.bush x) (Y':=M'.bush x) (basic_sr hr hp (k:=U.k) (k':=M'.k) (V:=U.V) (W:=M'.V)) stone_s; have ht:4*r≤(l+46)*r:= Nat.mul_le_mul_right _ (by omega)
 unfold vent; rw [familiar (p:=u) (w:=v) (hv.more (by unfold r at *; omega : radiusB x/10 ≤ (l+46)*r)) (fun i=>(perPt i hr hp).more (by omega)) (Names.less ((basic_n hr hp).under (by unfold r; omega)) (lanes_one _)) (Names.less ((basic_n hr hp).under (by unfold r; omega)) (lanes_one _)) he hx]
-- names reading
lemma stencil(p:Ready T x)(hp:1000 ≤ radiusB x)(h:∀ i, Beat.shadows (o:=S.ratio.parent (w i).1) H ((l+58)*radiusB x)): Virt S (paveB (x:=x) T w) H :=by
 intro M N u
 have he(a b:Monk SU.group S)(u:Beat a b H)(g:∃ v:Run (a.zoo x) (n+1), stave v=w):∃ v:Run (b.zoo x) (n+1),stave v=w:=by
    obtain ⟨v,rfl⟩:=g; have hk(i:Fin (n+2)):= (u.scope (r:=0) (by simp_rw [Nat.add_mul]; omega) (h i)).switch (v i) (by change separation _ _ ≤ 0; dsimp only [Tarn.stave]; rw [separation_self]); choose W hW using hk; exact ⟨W,funext fun i=>(hW i).symm⟩
 unfold paveB; by_cases hv:∃ v:Run (M.zoo x) (n+1), stave v=w
 · have hp':=he _ _ u hv; rw [dif_pos hv,dif_pos hp']; exact stampP T A p hp (hv.choose_spec.trans hp'.choose_spec.symm) u (by rw [hv.choose_spec]; exact h) -- need rw under binder
 simp only [dif_neg hv,dif_neg (show ¬∃ v:Run (N.zoo x) (n+1),Tarn.stave v=w from mt (he _ _ u.sym) hv)]
lemma hideB(p:Ready T x)(hp:1000≤radiusB x)(h:¬CodeZ S x w): paveB (x:=x) T w U=0:=by
 unfold paveB; split; next v=>
    have hu:¬ Speaks S v.choose := fun t=> h (v.choose_spec ▸ ((code_x v.choose).mpr t)); unfold vent; rw [muzzled hp (Names.less ((basic_n p hp).under (by omega)) (lanes_one _)) (fun i=>(perN i).under (by omega)) v.choose hu,mul_zero]
 next=>rfl
end
lemma spitB(i:Site (Domain N B))(p:Ready T x)(hp:1000 ≤ radiusB x): tit T x U i n= ∑ w∈ finW i S x n, plant S i w*paveB (x:=x) T w U:=by
 let V(w: LinkS S n):= plant S i w*paveB (x:=x) T w U; have he: ∑ w,V w = ∑ w∈finW i S x n,V w:=by
    unfold finW; rw [sum_filter]; refine sum_congr rfl fun k _=>?_ ; split
    next => rfl
    next f=> unfold V; by_cases hv:i∈Tarn.grove S (k 0); rw [hideB T k p hp (fun t=>f ⟨hv,t⟩),mul_zero]; simp [plant,hv]
 change _=∑ w∈_,V w; rw [←he]; apply Finset.sum_of_injOn stave stave_inj.injOn (fun v _=> mem_univ _) ?_ ?_
 · intro j' u v; unfold V; rw [show paveB (x:=x) T j' U=0 from (dif_neg (fun ⟨u,k⟩=> v ⟨u,mem_univ _,k⟩)),mul_zero]
 intro u _; unfold V; rw [stationB]; rfl
variable{T}
lemma Beat_k {H:Support (Domain N B)}(p:Beat U M' H):Beat (kist U) (kist M') H:= ⟨fun _ _=>Iff.rfl,p.fr,p.fe,p.trunks,fun _ _ _=>rfl,fun _ _=>rfl,fun _ _=>rfl⟩
end Muster
end YM.CF.Lich
