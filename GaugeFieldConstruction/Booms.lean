import GaugeFieldConstruction.Clockup
import GaugeFieldConstruction.Loons
import YM.CF.Hove.Out
set_option autoImplicit false
set_option maxHeartbeats 50000
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
variable {c f: Side}(G:Ratio c f)(p:Odd G.count.val)(A: Site f)(M:Male)(T:Script Male)(e:Use 4 G.count T)
def deckLoc:= ((isle G).symm A).1
abbrev PatchLoc:= ((isle G).symm A).2
def endLoc(y:Cover):= deckLoc G A+wrap c y
def dockLoc(x:Cover):= x + lift (PatchLoc G A)
abbrev loft(x:Cover):=cellar G.count (dockLoc G A x)
abbrev ParkV(x:Cover):= A + wrap f x
abbrev hid(x:Cover):= wrap G.count (dockLoc G A x)
lemma seal_o:A=isle G (deckLoc G A,PatchLoc G A):=by unfold deckLoc PatchLoc; rw [Prod.mk.eta,Equiv.apply_symm_apply]
lemma park_pay(x: Cover): ParkV A x=isle G (endLoc G A (loft G A x), hid G A x):=by
 let r:=PatchLoc G A; let B:=deckLoc G A; let X:= loft G A x; let Y:=hid G A x; have hp: x+lift r= lift Y + G.count.val • X:=balance G.count _ -- exact
 unfold ParkV; nth_rw 1 [seal_o G A]; change isle G (B,r)+_=isle G (B+ wrap c X,Y)
 rw [isle_apply,isle_apply,← Ratio.root_embed, ← Ratio.root_embed G, map_add, G.root_embed, G.root_embed,G.embed_wrap]; -- tune method
 have hh:=congrArg (wrap f) hp; simp only [map_add] at hh; linear_combination (norm:=abel) hh
include p
lemma omega_loc(x:Cover): Rush.wind A x= Rush.wind (deckLoc G A) (loft G A x):=by
 unfold Rush.wind; apply congrArg Rush.fee
 let X:= periods f (natural A+x); let Y:= periods c (natural (deckLoc G A)+loft G A x)
 have he:= carrying f (natural A+x); change natural (wrap f (natural A+x))+ f.val • X=natural A+x at he; rw [map_add,nat_true, show A+wrap f x= _ from park_pay G _ x, data_isle G p, show natural A= _ from (congrArg natural (seal_o G A)).trans (data_isle G p _ _)] at he -- rewrites RHS X occurrence problem
 have hp:= carrying c (natural (deckLoc G A)+loft G A x); rw [map_add,nat_true] at hp; let K:=loft G A x; let D:=deckLoc G A; let r:=PatchLoc G A; let V:=natural (isle G (D,r))
 have ht: x+lift r= lift (hid G A x)+ G.count.val • K:=balance G.count _
 apply nsmul_right_injective f.property.ne'
 change f.val • X=f.val • Y
 have hi:G.count.val • (natural (endLoc G A K)) + f.val • Y= G.count.val • natural D+ G.count.val • K:=by
    rw [G.exact_size, mul_comm c.val, mul_smul,←smul_add,←smul_add]; exact congrArg (fun x:Cover=> G.count.val • x) hp; -- tune
 change G.count.val • natural (endLoc G A K)+ lift (hid G A x)+offset G.count+ f.val • X= G.count.val • natural D + lift r+offset G.count+x at he
 linear_combination (norm:=abel) he-hi+ht -- plan
-- true Y (unit tested all indices)
omit p
abbrev Mill := Cover×Kt
def ware (b:Bool)(D:List Axis)(x:Cover)(i:Kt)(y:Mill):ℂ:= Hed b 4 G.count M.val (hid G A x) i.1 y.2.1 D (y.1-loft G A x) * (1:Op SU.Slot) i.2 y.2.2
lemma Y_blank (b:Bool)(D:List Axis)(x:Cover)(i:Kt)(y:Mill)(h:i.2≠y.2.2): ware G A M b D x i y=0:=by simp only [ware,Matrix.one_apply_ne h,mul_zero] -- tune
include p e
lemma merry₄ (b:Bool) : Tap.merry G p T 4 b M []= Rush.cart c (tub (coverlet b 4 G.count M.val [])) ⊗ₖ (1:Op SU.Slot):=by rw [merry,sticks 4 G.count p (by decide) (by decide) T e G rfl M]; exact pine_stencil 4 G.count p (by decide) (by decide) T e G rfl M b [] (by decide)
lemma φ_W (b:Bool)(x:Cover)(i j:Kt)(m:Site c): Tap.fan G p T 4 b M [] (plot (stickW A i) x) (stickW m j)= Rush.cart c (tub (coverlet b 4 G.count M.val [])) (endLoc G A (loft G A x),hid G A x,i.1) (m,0,j.1)*(1:Op SU.Slot) i.2 j.2:=by
 rw [show plot (stickW A i) x=switchG G ((endLoc G A (loft G A x),(hid G A x,i.1)),i.2) from ?_]; unfold Tap.fan; rw [merry₄ G p M T e, arch,Matrix.of_apply,Equiv.symm_apply_apply]; rfl -- tune binder order
 unfold Tap.plot; rw [show A+wrap f x=isle G (endLoc G A (loft G A x), hid G A x) from park_pay G A x]; rfl
lemma parchment (b:Bool)(x:Cover)(i:Kt)(z:Single c): toneT G p T 4 b M A i [] x z=∑' y:Cover, (if endLoc G A y=z.1.1 then Rush.wind (deckLoc G A) y*ware G A M b [] x i (y,portB z) else 0) :=by
 let L:=G.count; let K:=tub (coverlet b 4 L M.val []); let V:= loft G A x; let H:= hid G A x; let B:= deckLoc G A; let J:=z.1.1; let k:= Hove.portB z; -- tune
 unfold toneT pax; rw [show Tap.fan G p T 4 b M [] (plot (stickW A i) x) z=_ from φ_W G p A M T e b x i k J]
 rw [← (Equiv.addRight V).tsum_eq]; rw [Rush.cart,Matrix.of_apply, ← tsum_mul_right,← tsum_mul_left]; apply tsum_congr; intro y
 let Q:=endLoc G A V; rw [wagon_app]; change Rush.wind A x * ((if Q+wrap c y=J then Rush.wind Q y*K y (H,i.1) (0,k.1) else 0) * (1:Op SU.Slot) i.2 k.2)= if endLoc G A (y+V)=J then Rush.wind B (y+V)*ware _ _ _ _ _ _ _ _ else _
 have hh:endLoc G A (y+V)=Q+wrap c y:=by unfold Q endLoc; rw [map_add]; abel
 by_cases g:Q+wrap c y=J
 · rw [hh,if_pos g,if_pos g]; change _= Rush.wind B (y+V)* (K ((y+V)-loft G A x) (H,i.1) (0,k.1)* (1:Op SU.Slot) i.2 k.2); rw [show (y+V)-loft G A x=y from add_sub_cancel_right .., show Rush.wind B (y+V)= Rush.wind A x*Rush.wind Q y from ?_]; unfold K; ring -- tune opacity k
   rw [add_comm y,Hove.route_H,omega_loc G p A x]; rfl
 rw [hh,if_neg g,if_neg g,zero_mul,mul_zero]
-- moving output one sign at period
omit e
lemma Ydiff_loc (d:List Axis)(x:Cover)(b:Bool)(i: Kt)(j:Axis)(y:Mill)(k:d.length ≤ 2): ware G A M b (j::d) x i y= ware G A M b d (x+Lattice.step j) i y-ware G A M b d x i y:=by
 let V:= x+step j; let Z:=lift (PatchLoc G A); have he: dockLoc G A (x+step j)=dockLoc G A x + step j:=by unfold dockLoc; abel
 let K:=loft G A x; let H:=hid G A x; have hp:loft G A (x+step j)=K+carryStep j H:=by unfold loft; rw [he,Trellis.cellar_step p]; -- tune
 have hf:hid G A (x+step j)=H+step j:=by unfold hid; rw [he,map_add,wrap_step]; -- tune
 unfold ware; rw [hp,hf, shine_move b 4 _ _ p M.property (hid G A x) i.1 y.2.1 j d (by simp; omega), sub_mul, sub_add_eq_sub_sub]; -- tune
lemma X_one (u:Bool)(z:List Axis)(i:Kt)(t:Mill)(v:z.length≤3): loom z (fun x=> ware G A M u [] x i t)= fun x=>ware G A M u z x i t:=by
 induction z with
 | nil=> rfl
 | cons a z ih=> rw [loom_cons, ih (by simp at v; omega)]; funext x; exact (Ydiff_loc G p A M z x u i a t (by simp at v; omega)).symm
end Boom
end YM.CF.TableF
end
