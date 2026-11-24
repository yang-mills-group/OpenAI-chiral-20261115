import YM.CF.Skye.Hark
import YM.AnalyticBridge.GAUSSIAN_FIELD_ALIGNMENT.Locations
set_option autoImplicit false
noncomputable section
namespace YM.CF.Skye
open Function Filter Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory Mesa ProbabilityTheory Peaks Drapes Rush Precision Tree Push.SectorMeasure Next.SectorChange Tulip AnalyticBridge.GaussianFieldAlignment
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
variable {n m:Side}{u d e a:ℝ}{r:ℕ}(G:Ratio n m)(q:Chi)(d:ℝ)
lemma brake(F:Forest (ratio G))(p:0<d)(t:2*d<firstRadius group):Continuous (uncurry (seine G F q d)):=by
 let P:=ratio G; have ht:Continuous (Precision.replica (G:=group) P):=by apply continuous_pi; intro i; unfold Precision.replica; split <;> fun_prop
 have hh(i:Seat m):Continuous (fun V:Pane m× Pane n=> F.foldAt V.1 i):=(F.folds i).comp continuous_fst
 have hj(x:reach m): Continuous (fun V:Pane m×Pane n=> portU G F q d V.1 V.2 x):=by
    let f(V:Pane m×Pane n):=Precision.replica P V.2 x; let Z(V:Pane m×Pane n):= gauge (F.foldAt V.1) V.1 x; have hy:Continuous f:= (continuous_apply x).comp (ht.comp continuous_snd); have hz:Continuous Z:=((hh x.1).mul ((continuous_apply x).comp continuous_fst)).mul (hh (x.1+step x.2)).inv
    exact (group.lieExp_cont.comp ((patched_continuous q p t).comp (hz.mul hy.inv))).mul hy
 apply continuous_pi; intro i; exact ((hh i.1).inv.mul (hj i)).mul ((hh (i.1+step i.2)).inv.inv)
lemma brake_g(F:Forest (ratio G))(p:Odd G.count.val)(W:Pane m)(V:Pane n)(g: Seat m→E) : seine G F q d (gauge g W) (gauge (scaleG G g) V)=gauge g (seine G F q d W V):=by
 set a := F.foldAt W; let y:=constantGauge (scaleG G g) (ratio G); have hp: F.foldAt (gauge g W)= y*a*g⁻¹:=by
    funext i; unfold Forest.foldAt; rw [travel_gauge,F.hike_root]; change (g i*_* (y i)⁻¹)⁻¹=y i *(travel W _ _)⁻¹*(g i)⁻¹; group
 let Z:= portU G F q d W V; have he: portU G F q d (gauge g W) (gauge (scaleG G g) V) = gauge y Z:=by
    unfold portU; rw [hp, ←copied (ratio G) p]; change (fun i=>knit _ _ (Lattice.gauge (y*a*g⁻¹) (gauge g W) i) (gauge y _ i))= _; rw [gauge_sq,mul_assoc (y*a), inv_mul_cancel,mul_one,←gauge_sq]; funext i; exact knitted q d (y _) _ _ _
 rw [seine,seine,hp,he,gauge_sq,gauge_sq]; congr 1; group; rfl
section
variable (T:RG.StepData (More n) (More m))(p:T.ratio=ratio G)
abbrev toForest(F:Forest (ratio G)):Forest T.ratio:= p.symm ▸ F
def moveTree (F:Forest (ratio G))(s:Sweep n): Forest (ratio G):= p ▸ Locations.forest s.s ((assembly n).embed s.b) (toForest G T p F)
def reSweep (s:Sweep n):Sweep m:=⟨s.s,G.embed s.b,s.charge⟩
lemma reA(s:Sweep n): (ratio G).embed ((assembly n).embed s.b)=(assembly m).embed (G.embed s.b):=by
 generalize hv:s.b=x; rw [← wrap_lift x]; rw [Ratio.embed_wrap,Ratio.embed_wrap,Ratio.embed_wrap,Ratio.embed_wrap]; change wrap (More m) (G.count.val • 2 • Lattice.lift x)=wrap _ ((2:ℕ) • G.count.val • Lattice.lift x); rw [smul_comm] -- tune
private lemma move_props (D: Ratio (More n) (More m))(T:RG.StepData (More n) (More m))(p:T.ratio=D)(F:Forest D)(s:Signed)(b: Seat n): let P:Forest T.ratio := p.symm ▸ F; let F':Forest D:=p▸ Locations.forest s b P; ∀ i:Seat m,(Forest.hike F' i).map (fun a=>a.rotate s)=F.hike (affine s (D.embed b) i):=by
 subst D; dsimp only; set Z:=(Locations.forest s b F)
 intro i; induction i using Forest.hike.induct Z with
 | case1 i l ih=>
    rw [Forest.hike,dif_pos l,List.map_cons]; conv_rhs=>rw [Forest.hike, dif_pos ((Locations.leaves (S:=T) s b i).2 l)]
    change List.cons _ _=_; congr 1; change ((F.up _).rotate s⁻¹).rotate s=_; rw [Step.rotate_mul,mul_inv_cancel,Step.rotate_one]; rw [ih]; have hk:=Locations.climbs s b F i; exact congrArg (Forest.hike F) hk
 | case2 i hi=> rw [Forest.hike,dif_neg hi]; conv_rhs =>rw [Forest.hike,dif_neg (fun l=>hi ((Locations.leaves (S:=T) s b i).1 l))]
                simp
lemma move_h (F:Forest (ratio G))(s:Sweep n)(i) : List.map (fun a:Step=>a.rotate s.s) ((moveTree G T p F s).hike i)= F.hike (boxA (reSweep G s) i):=by simp only [sitA, show (reSweep G s).b=G.embed s.b from rfl]; rw [show _ = _ from (reA G s).symm]; exact move_props ..
lemma foldR (F:Forest (ratio G))(s: Sweep n)(V:Pane m): (moveTree G T p F s).foldAt (flashA (reSweep G s) V) = fun i=> polarT s.charge (F.foldAt V (boxA (reSweep G s) i)):=by funext i; unfold Forest.foldAt; rw [flashA,levity]; change (polarT _ (travel V (boxA _ _) (List.map (fun i:Step=>i.rotate s.s) _)))⁻¹=_; rw [move_h]; exact (map_inv ..).symm
-- need remove broad proof param with unused p in reA (p not used; check)
include p
lemma toneR (s:Sweep n)(V:Pane n): Precision.replica (ratio G) (flashA s V)= flashA (reSweep G s) (Precision.replica (ratio G) V):=by
 rw [revoke,revoke]; have hp(U:Pane n): Precision.replica (ratio G) (polarT s.charge ∘ U)=polarT s.charge ∘ Precision.replica (ratio G) U:=by
    funext i; simp only [Precision.replica,Function.comp_apply]; split_ifs; exact (map_one (polarT s.charge)).symm; rfl
 rw [hp,← p,Locations.replica_move,p,reA]; rfl
lemma port_mv(F:Forest (ratio G))(s:Sweep n)(V:Pane n)(W:Pane m): portU G (moveTree G T p F s) q d (flashA (reSweep G s) W) (flashA s V)= flashA (reSweep G s) (portU G F q d W V):=by
 funext i; rw [flash,portU,foldR,toneR G T p]; rw [←show flashA (reSweep G s) (gauge (F.foldAt W) W)=Lattice.gauge (fun i=> polarT s.charge (F.foldAt W (boxA (reSweep G s) i))) (flashA (reSweep G s) W) from revG (reSweep G s) W _,flash,flash]; split; · rw [knitC,knitV]; rfl
 rw [knitC]; rfl
lemma seine_mv(F:Forest (ratio G))(s:Sweep n)(V:Pane n)(W:Pane m): seine G (moveTree G T p F s) q d (flashA (reSweep G s) W) (flashA s V)= flashA (reSweep G s) (seine G F q d W V):=by rw [seine,seine,foldR,port_mv,revG]; congr 1; funext i; simp [reSweep] -- tune
end
end YM.CF.Skye
