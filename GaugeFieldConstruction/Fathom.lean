import GaugeFieldConstruction.Cata
/-!
# Cover spin probe effects.
-/
set_option autoImplicit false
set_option maxHeartbeats 60000
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.TableF
open Function Filter Metric Lattice Wilson Finset MeasureTheory RG Precision Tree
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open FlightFlux Fluxim
open Fock Tulip Lat Spire Phase Cube
attribute [local instance] opCStarAlgebra
open AnalyticBridge VerifiedReset Taxi
open Lenten
open Stationary Vault Font
open Bank Laurent Bloch Tap Hove Spire
open Haro Peaks Rush Fir Next.Free Thorn
open Planned.PrimaryIntegral295 Carrier
namespace Boom
variable {f c:Side} {M:Male}{G: Ratio c f}{A:Site f}{M':Male}
variable (p:Momentum)(b:Bool)
abbrev multiY (p:Momentum)(i j o:Kt):ℂ:=0 -- tune
abbrev bootstrap (M:Male)(b:Bool)(t:Momentum):= if b then boot 4 M t else 1-boot 4 M t
abbrev InputC (M':Male)(b:Bool)(p:Momentum) := bootstrap M' b p * baseF b
abbrev blockX (M:Male)(b:Bool)(L:Side)(l:Site L)(p:Momentum): Pal:=arm b 4 L M.val l p ⊗ₖ (1:Op SU.Slot)
lemma αLay {i:Site G.count}(t:Cover):
 mode p (loft G A t)*mode (aliasAt p i) (lift (hid G A t))=mode (aliasAt p i) (t+lift (PatchLoc G A)) :=by
 have he:=mode_shift (aliasAt p i) (lift (hid G A t)) (G.count.val • loft G A t); rw [← mode_scale,alias_scale,mode_phase,mode_periodic,mul_one] at he -- left expression tune
 exact (mul_comm ..).trans (he.symm.trans (congrArg (mode (aliasAt p i)) (balance _ _).symm)) -- tune
variable (v:p∈baseCube)(e:Odd G.count.val)(A:Site f)
include v e
lemma prismH (x:Cover) (i j:Kt): (∑' t:Cover, mode p t *ware G A M b [] x i (t,j))=∑ l:Site G.count,(mode (aliasAt p l) (dockLoc G A x) * Next.Free.toll G.count 2) * blockX M b G.count l p i j:=by -- tune TollH
 let H:=loft G A x; let Z:=hid G A x; let F:= Hed b 4 G.count M.val Z i.1 j.1 []; let g(l : Site G.count):=blockX M b _ l p i j; let K(y:Cover):=mode p y *ware G A M b [] x i (y,j); -- tune shadow use x -> h'
 have h:mode p=(fun t=> mode p t):= rfl
 have hz:∑' t,K t=(mode p H * (1:Op SU.Slot) i.2 j.2)*Laurent.read F p:=by
    rw [← (Equiv.addRight H).tsum_eq]; unfold Laurent.read; rw [← tsum_mul_left]; refine tsum_congr fun z=>?_ ; change K (z+H)=_; unfold K ware; rw [mode_shift,show z+H- loft G A x=z from add_sub_cancel_right ..]; unfold F Z; simp only [smul_eq_mul]; ring
 rw [show (∑' t,K t)=_ from hz, show Laurent.read F p= _ from shiny b 4 _ M.val e M.property [] (by decide) p v Z i.1 j.1]; -- binder tune
 unfold Fir.paint; rw [Matrix.sum_apply,mul_sum]; refine sum_congr rfl fun l _=> ?_; rw [blockX, Matrix.kronecker_apply, dockLoc,← show mode p H *mode _ _= _ from αLay (i:=l) (G:=G) (A:=A) p x]; -- order
 simp only [Matrix.smul_apply, smul_eq_mul,listChip, List.map_nil,List.prod_nil,one_mul]; unfold H Z; ring
variable {V σ:ℝ}(h:Honed G.count M b V σ)(t:0< V)(z:0<σ)
include h t z
lemma ontoH (X:Cover)(i j:Kt) (M':Male): let B:Pal:= InputC M' b p
 (∑' y:Mill, mode p y.1 * ware G A M b [] X i y * B y.2 j) =∑ l:Site G.count, (mode (aliasAt p l) (dockLoc G A X)* Next.Free.toll G.count 2)*(blockX M b G.count l p *B) i j:=by
 intro B; let C (y:Mill):= ware G A M b [] X i y; let Y(x:Cover)(j:Kt):= C (x,j)
 have he: Summable fun y=>‖C y‖:=by have he:=(gene_budget (A:=A) h t z X i [] (by simp) 0).2.1; simp_rw [wl0,one_mul] at he; exact he
 let K(y:Mill):=mode p y.1*C y*B y.2 j
 have hk:Summable K:=by
    apply Summable.of_norm; let D:=Equiv.prodComm Kt Cover; apply D.summable_iff.mp; apply (summable_prod_of_nonneg (f:=fun q: Kt×Cover=> ‖K (D q)‖) (fun _=>norm_nonneg _)).2 ⟨fun k=>?_,(hasSum_fintype _).summable⟩
    change Summable fun x=> ‖mode p x * Y x k * B k j‖; simp_rw [norm_mul, mode_real _ _ v.1,one_mul]; exact (he.prod_symm.prod_factor k).mul_right _
 change (∑' y,K y)= _; rw [show tsum K=_ from ((Equiv.prodComm Kt Cover).tsum_eq K).symm.trans ((hk.prod_symm).tsum_prod),tsum_fintype]; -- tune tsum_prod'
 let X'(l:Site G.count):= mode (aliasAt p l) (dockLoc G A X)*Next.Free.toll G.count 2
 have hp (k:Kt): (∑' x: Cover,K (x,k))=∑ l: Site G.count,X' l*(blockX M b G.count l p i k* B k j):=by
    change (∑' x:Cover, mode p x * C (x,k)*B k j)=_; rw [tsum_mul_right, show (∑' t:Cover, mode p t* C (t,k)) = _ from prismH p b v e A X i k, sum_mul]; exact sum_congr rfl fun w _=> mul_assoc ..
 change ∑ x:Kt,∑' y: Cover,K (y,x)=_; simp_rw [hp]; rw [sum_comm]; apply sum_congr rfl; intro l _; rw [Matrix.mul_apply,mul_sum]
lemma ontoF (X:Cover)(i m:Kt)(M':Male) : let B:= InputC M' b p
 (∑' y:Mill, mode p y.1*Sister M G b A X i y*B y.2 m) = ∑ l:Site G.count, (mode (aliasAt p l) (dockLoc G A X)* Next.Free.toll G.count 2)*(bootstrap M b (aliasAt p l) * (blockX M b G.count l p*B)) i m:=by
 intro B; let T (y:Lane)(x:Mill):= journey M b (sill M G b A) X i y x; let W(y:Mill):= mode p y.1*B y.2 m; let F(z:Lane)(t:Mill):=T z t * W t
 have ht:Summable (fun z: Lane ×Mill=>‖T z.1 z.2‖) := sum_coin M b _ X i 3 (SpringB h t z A X i 3); let C:=∑ l:Kt,‖B l m‖
 have he(y:Mill):‖W y‖≤ C:=by unfold W; rw [norm_mul,mode_real _ _ v.1,one_mul]; exact single_le_sum (f:=fun i:Kt=> ‖B i m‖) (fun _ _=> norm_nonneg _) (mem_univ y.2)
 have hv:Summable (uncurry F):=Summable.of_norm_bounded (ht.mul_right C) fun v=> by change ‖T v.1 v.2*W v.2‖≤ _; rw [norm_mul]; exact mul_le_mul_of_nonneg_left (he _) (norm_nonneg _)
 let D(l:Site G.count):=blockX M b G.count l p*B; let q(l:Site G.count):=aliasAt p l
 let L (l t):= mode (q l) t*Next.Free.toll G.count 2
 let Φ(x:Mill):=mode p x.1*Sister M G b A X i x*B x.2 m
 have hx(x):Φ x=∑' z:Lane,F z x:=by unfold Φ Sister streamsW F; rw [tsum_mul_right]; unfold W; ring -- tune T
 let f(j:Kt)(y:Cover)(l:Site G.count):= L l (dockLoc G A X) * (mode (q l) y*Paw 4 M b y i j) * D l j m
 have hs(j:Kt)(y:Cover): ∑' z:Mill,F (j,y) z= ∑ l:Site G.count, f j y l:=by
    unfold F T journey; let Y:= Paw 4 M b y i j
    rw [show (∑' z:Mill,(Y*sill M G b A j (X+y) z)*W z)= Y * ∑' z:Mill, mode p z.1*ware G A M b [] (X+y) j z *B z.2 m from ?_, ontoH p b v e A h t z _ _ _ M',mul_sum]; -- tune
    · apply sum_congr rfl; intro l _; unfold f Y L q; rw [show dockLoc G A (X+y)=dockLoc G A X + y from (by unfold dockLoc; abel),mode_shift]; unfold D; ring
    rw [← tsum_mul_left]; refine tsum_congr fun z=> ?_; unfold W sill Ytab; ring
 have hg(l:Site G.count)(j:Kt): Summable fun x:Cover=> mode (q l) x * Paw 4 M b x i j:=by
    apply Summable.of_norm; simp_rw [norm_mul,mode_real (q l) _ (alias_base v l e).1,one_mul]; exact (hel_pawn 4 (by decide) M b).sumK i j
 have hy: Summable (fun y:Lane=>∑' z:Mill, F y z):=hv.prod
 change ∑' y:Mill, Φ y = _; simp_rw [hx]; rw [hv.tsum_comm, show ∑' y:Lane,∑' z:Mill,F y z=_ from hy.tsum_prod,tsum_fintype]; -- tune
 simp_rw [hs]
 have hh(j:Kt): ∑' y:Cover,∑ l: Site G.count,f j y l=∑ l:Site G.count,L l (dockLoc G A X)*((bootstrap M b (q l)) i j*D l j m):= by
    rw [Summable.tsum_finsetSum (fun l _=> ((hg l j).mul_left (L l (dockLoc G A X))).mul_right (D l j m))]; apply sum_congr rfl; intro l _; rw [tsum_mul_right,tsum_mul_left]; rw [show (∑' y: Cover,mode (q l) y *Paw 4 M b y i j)= _ from (hel_pawn 4 (by decide) M b).readK (q l) (alias_base v _ e) i j]; exact mul_assoc ..
 simp_rw [hh]; rw [sum_comm]; refine sum_congr rfl fun l _=>?_ ; rw [Matrix.mul_apply,mul_sum]
end Boom
end YM.CF.TableF
end
