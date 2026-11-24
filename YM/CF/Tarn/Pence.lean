import YM.CF.Tarn.Tuck
import YM.CF.Souk.Rayon
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
open AnalyticBridge.RelativeLogdet
lemma walkP (t a v b X:ℝ)(u:Mast G c)(h:Medal T x C m v a b n l t P.1 P.2 u)(hp:C ≤ X)(hz:tipPay v x ≤ 1)(hv:tipPay b x ≤1)(ht:a*t ≤X)(hX:0 ≤ C) (w:LinkS S j) : let U(y):=bunk S P (satU G t y); let V:= (Fintype.card SU.group.ColorIndex:ℝ)^(j+1+1)*(2^n*X*(2^n*X)^j)
 Allows n (fun y=>pave T x q d l w (U y)) u (V+V+V):=by
 intro U V; have he:0 ≤ X:=hX.trans hp; have he'(i:Mast G c): (U i).bush x=1:=rfl
 by_cases hy:∃ y:Run ((U u).zoo x) (j+1), stave y=w
 · obtain ⟨y,rfl⟩:=hy; have hp' := h.headX.cheaper hp ((mul_le_of_le_one_right hX hz).trans hp); have ha:C*tipPay b x ≤ X:=(mul_le_of_le_one_right hX hv).trans hp
   have ht':=bar_t hp' y
   have hv':=bar_t (h.stepX.cheaper ha ha) y
   have hp':=bar_t ((h.spend q d).cheaper ht ht) y
   have hz':0 ≤ V:= ht'.nonneg; refine (((((ht'.smul (-(1/2:ℝ))).mono (mul_le_of_le_one_left hz' (by norm_num))).add ((hv'.smul (1/2:ℝ)).mono (mul_le_of_le_one_left hz' (by norm_num)))).add hp').germ ?_)
   filter_upwards with i; change _= pave T x q d l (stave y) (U i); rw [show stave y=stave (j:=j) (M:=U i) (x:=x) y from rfl,paved]; rfl -- tune
 apply Allows.germ (f:=fun _:Mast G c=>(0:ℝ)) (allows_const u (by rw [norm_zero]; unfold V; positivity)); filter_upwards with i; rw [pave,dif_neg (show ¬∃ y: Run ((U i).zoo x) _,stave y=w from hy)]
lemma Quill_r (i:Site c)(p:Ready T x)(hp:1000 ≤ radiusB x)(h:Beat.shadows (o:=i) H ((l+68)*radiusB x)):Virt S (fun M=> Quill T x q d l M i) H:=by
 intro M N hv; unfold Quill; refine sum_congr rfl fun j (hi:j∈_)=>?_ ; rw [bedsX _ _ _ _ _ _ _ _ p hp,bedsX _ _ _ _ _ _ _ _ p hp]; refine sum_congr rfl fun w he=>?_ ; congr 1 -- tune dep
 have hz:= mem_filter.mp he; refine payV _ _ _ _ _ w p hp (fun t y u=>h ?_) hv
 have hy:= latticeFieldEstimatesC hz.2.2 hz.2.1 t; have he: t.val* (3*radiusB x) ≤3*(3*radiusB x):=Nat.mul_le_mul_right _ (by have hw:= (Finset.mem_range.mp hi); omega); apply (theatre ..).mpr; apply (separation_triangle i (S.ratio.parent (w t).1) y).trans; have hs:= (theatre ..).mp u; simp_rw [Nat.add_mul] at *; omega -- tune implicit
abbrev gems (L:Side)(i:ℕ)(n j:ℕ)(V:ℝ):ℝ:=
 let E:=10*i; let r:=Fintype.card Axis*L.val^4*(E+E+1)^4; let X:= (Fintype.card SU.group.ColorIndex:ℝ)^(j+1+1)*(2^n*V*(2^n*V)^j); (r^(j+2):ℕ)*(X+X+X)
def Gems (L:Side)(i:ℕ)(n:ℕ)(V:ℝ):ℝ:= ∑ j∈Finset.range 3,gems L i n j V
lemma Quill_c(o:Site c)(t a v b X:ℝ)(u:Mast G c)(h:Medal T x C m v a b n l t P.1 P.2 u)(p:Ready T x)(hB:1000 ≤radiusB x) (hp:C ≤ X)(hz:tipPay v x ≤ 1)(hv:tipPay b x ≤1)(ht:a*t ≤X)(hX:0 ≤ C) : Allows n (fun y=>Quill T x q d l (bunk S P (satU G t y)) o) u (Gems S.patch.L (radiusB x) n X):=by
 let K(y):=bunk S P (satU G t y); unfold Quill; simp_rw [bedsX T x q d l _ _ o p hB]
 refine Jet.allows_sum (f:=fun j y=>∑ w∈finW o S x j, plant S o w * pave T x q d l w (K y)) ?_
 intro j he; let V:= (Fintype.card SU.group.ColorIndex:ℝ)^(j+1+1)*(2^n*X*(2^n*X)^j); let Z:=V+V+V; let I:=finW o S x j; let W(w:LinkS S j)(y):= plant S o w * pave T x q d l w (K y)
 have hx: 0 ≤ Z:=by unfold Z V; have he:=hX.trans hp; positivity
 apply (summed I W (fun w _ => ((walkP t a v b X u h hp hz hv ht hX w).smul (plant S o w)).mono (mul_le_of_le_one_left hx plant_v))).mono; refine mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (packed o _ ?_)) hx
 have hv: (j+1)*(3*radiusB x) ≤ 3*(3*radiusB x):=Nat.mul_le_mul_right _ (mem_range.mp he); omega
open Stationary Push.Loops
lemma jewels (V:ℝ)(p:0 ≤ V)(n:ℕ)(L:Side): nib (fun i=>Gems L i n V):=by
 let H(i:ℕ):=(Fintype.card Axis*(L.val)^4*(10*i+10*i+1)^4:ℕ); let U(i:ℕ):=(H i:ℝ); have hv:nib U:=by
    unfold U H; push_cast; let S(v:ℕ):ℕ:=10*v; have ht:CapY S:=CapY.lives.scal 10; convert (nib_const ((Fintype.card Axis:ℝ)*(L.val:ℝ)^4) (by positivity)).mul (plot_n ht) using 1; ext v; unfold plot S; push_cast; rfl -- tune
 let Q(j:ℕ):=(Fintype.card SU.group.ColorIndex:ℝ)^(j+1+1)*(2^n*V*(2^n*V)^j); let A(j:ℕ):=Q j+Q j+Q j; change nib _; let W(j i:ℕ):=gems L i n j V; change nib (fun i=>∑ j∈ Finset.range 3,W j i)
 have he(j): nib (W j):=by
    rw [show W j=(fun i=> (U i)^(j+2)*A j) from funext fun i=> by unfold U; norm_cast] -- tune
    exact (hv.pow (j+2)).mul (nib_const _ (by unfold A Q; positivity))
 simp only [← Fin.sum_univ_eq_sum_range]; exact nib.sumV (fun j:Fin 3=>W j.val) (fun i=>he _)
end YM.CF.Tarn
