import YM.CF.Tarn.Nail
import YM.CF.Arena.Pearl
import YM.CF.Neige.Morse
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Tarn
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace Matrix Kronecker
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Push.Uniform (curve Slope tint partSpace meetVar)
open AnalyticBridge.Annulus1AD AnalyticBridge.SectorAffine Oriented Esti Vol Bloch Exterior Jet
open RG Forge Cay Slate Rel
open Arena
local notation "G"=> SU.group
variable {c f:Side}{S:StepData c f}{T:Tube SU.group S}{F:Forest S.ratio}{q:Chi}{s:Signed}{l n:ℕ}{x d β C D σ m:ℝ}{P:Tab S}{V:Config SU.group c}
open Cube
open Matrix Further.CurvedGaussianJets.Tracks PhysicalNext.OrderedAffine2B.SymFare
variable {H:Support c}{M N:Monk G S}{j:ℕ}
-- ambient tickets
abbrev LinkS (S:StepData c f)(n:ℕ):= Run (Bond f) (n+1)
def stave{x:ℝ}{M:Monk G S}(w:Run (M.zoo x) (j+1)):LinkS S j:=fun i=>(w i).val.val
lemma stave_inj: Function.Injective (stave (M:=M) (x:=x) (j:=j)):= fun _ _ h=>funext fun i=> Subtype.ext (Subtype.ext (congrFun h i))
def CodeZ(S:StepData c f)(x:ℝ){j:ℕ}(w:LinkS S j): Prop := w 0=w (Fin.last _) ∧∀ i:Fin (j+1), Miles S (3*radiusB x) (w i.castSucc) (w i.succ)
lemma code_x(w:Run (M.zoo x) (j+1)): CodeZ S x (stave w)↔ Speaks S w:= and_congr ⟨fun h=>Subtype.ext (Subtype.ext h),fun h=>congrArg (fun i:M.zoo x=>i.val.val) h⟩ Iff.rfl
variable (T:Tube G S)(x:ℝ)(q:Chi)(d:ℝ)(l:ℕ)
def pes (M:Monk G S)(w:Run (M.zoo x) (j+1)):ℝ:=
 -(1/2:ℝ)*barP (emptyA T x M.k M.key M.park M.V) (perZ T x M.k M.key M.park M.V) w+(1/2:ℝ)*barP (neo T x M.k M.key M.park M.V) (fun _=>1) w+barP (acc T x M.k M.key M.park q d (M.bush x) l M.V) (fun _=>1) w
lemma stun (w:Run (M.zoo x) (j+1))(hr:Ready T x)(p:1000 ≤ radiusB x)(hx:¬Speaks S w): pes T x q d l M w=0:=by
 let Q:Neige.Shelf (Rows.In x M.key M.park ( «G»:=SU.group)):=1; unfold pes
 have ht : Neige.Names (emptyA T x M.k M.key M.park M.V) (radiusB x):= Names.less ((basic_n hr p).under (by omega)) (lanes_one _)
 rw [muzzled p ht (fun i=>(perN i).under (by omega)) w hx, muzzled p (neoN hr p) (fun i=>lanes_one _) w hx,muzzled p (accN hr p) (fun i=>lanes_one _) w hx]; simp
lemma folic{w:Run (M.zoo x) (j+1)}{u:Run (N.zoo x) (j+1)}(hr:Ready T x)(hp:1000 ≤ radiusB x)(p:stave w=stave u)(hx:∀ i,Scan S x (S.ratio.parent (stave w i).1) ((l+47)*radiusB x) M.key N.key M.park N.park M.k N.k M.V N.V (M.bush x) (N.bush x)): pes T x q d l M w=pes T x q d l N u:=by
 have he: ∀ i, (w i).val.val=(u i).val.val:=congrFun p; let r:=radiusB x
 have hu:4*r≤(l+46)*r:= Nat.mul_le_mul_right _ (by omega); have hz:r+r≤4*r:=by omega
 have hv:=Sample.less (Y:=M.bush x) (Y':=N.bush x) (basic_sr hr hp (k:=M.k) (k':=N.k) (V:=M.V) (W:=N.V)) stone_s
 have hL:∀ i,Scan S x (S.ratio.parent (stave w i).1) ((l+46)*r+r) M.key N.key M.park N.park M.k N.k M.V N.V (M.bush x) (N.bush x):=fun i=>(hx i).lower (by unfold r; simp_rw [Nat.add_mul]; omega)
 unfold pes
 rw [familiar (p:=w) (w:=u) (hv.more (by unfold r at *; omega : radiusB x/10 ≤ (l+46)*r)) (fun i=>(perPt i hr hp).more (by omega)) (Names.less ((basic_n hr hp).under (by unfold r; omega)) (lanes_one _)) (Names.less ((basic_n hr hp).under (by unfold r; omega)) (lanes_one _)) he hL, familiar ((neo_pt hr hp).more hu) (fun i=>stone_s) (neoN hr hp) (neoN hr hp) he hL,familiar (accPt hr hp (l:=l) (D:=d)) (fun i=>stone_s) (accN hr hp) (accN hr hp) he hL] -- implicit
-- by path
def pave (w:LinkS S j)(M:Monk G S):ℝ:= if h:∃ u:Run (M.zoo x) (j+1),stave u=w then pes T x q d l M h.choose else 0
lemma paved(w:Run (M.zoo x) (j+1)): pave T x q d l (stave w) M=pes T x q d l M w:=by
 let h:∃ u:Run (M.zoo x) (j+1), stave u=stave w:=⟨_,rfl⟩; unfold pave; rw [dif_pos h,stave_inj h.choose_spec] -- let Prop let vs have
lemma hideS(w:LinkS S j)(hr:Ready T x)(hp:1000 ≤ radiusB x)(hx:¬CodeZ S x w): pave T x q d l w M=0:=by
 unfold pave; split
 next h=> exact stun T x q d l _ hr hp (fun t=> hx (h.choose_spec ▸ ((code_x _).mpr t)))
 next=>rfl
lemma payV (w:LinkS S j)(hr:Ready T x)(hp:1000 ≤ radiusB x)(hx:∀ i,Beat.shadows (o:=S.ratio.parent (w i).1) H ((l+58)*radiusB x)):Virt S (pave T x q d l w) H:=by
 intro M N h; let L:= (l+47)*radiusB x
 have he(a b:Monk G S)(h:Beat a b H)(p:∃ u:Run (a.zoo x) (j+1), stave u=w):∃ u:Run (b.zoo x) (j+1),stave u=w:=by
    obtain ⟨u,rfl⟩:=p
    let o(i):= S.ratio.parent (stave u i).1; have hp(i:Fin (j+2)):= (h.scope (r:=0) (hx i|> (fun _=> by simp_rw [Nat.add_mul]; omega)) (hx i)).switch (u i) (by change separation (o i) (o i) ≤ 0; rw [separation_self]) -- tune
    choose v H using hp; exact ⟨v,funext fun i=>(H i).symm⟩
 unfold pave; by_cases hu:∃ u:Run (M.zoo x) (j+1),stave u=w
 · have hv:=he M N h hu; rw [dif_pos hu,dif_pos hv]; refine folic T x q d l hr hp (hu.choose_spec.trans hv.choose_spec.symm) ?_; intro i; rw [hu.choose_spec]; exact h.scope (by simp_rw [Nat.add_mul]; omega) (hx i)
 simp only [dif_neg hu,dif_neg (show ¬∃ u:Run (N.zoo x) _, stave u=w from mt (he _ _ h.sym) hu)]
end YM.CF.Tarn
