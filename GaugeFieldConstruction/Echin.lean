import GaugeFieldConstruction.Eases
import GaugeFieldConstruction.Pleb
set_option autoImplicit false
set_option maxHeartbeats 60000
noncomputable section
namespace YM.GaugeFieldConstruction.Wick.Yacht
open StressFHeat MeasureTheory Analysis Function Filter Metric Maxwell Finset Gap Complex Cauchy Row Phys Flux.One
open Lattice CF.XGarden.MastTin.ArtCart.Violets CF.Py.Rate.LocalLimit.Papal
open scoped Topology ContDiff BigOperators Classical
open HopeC
-- Perturbed fields real offsets & coordinates
abbrev pinF (x:Wφ):FW:=debtF x.2.1 x.2.2
abbrev pinG (x:Wα):PW:=debtG x.2.1 x.2.2
def Fuse (x:Cover)(i:Wφ): HopeC E4:=diagram SpecW (off x) (off i.1) 2
def Glint (x:Cover)(i:Wα): HopeC E4:=diagram (addQ (Foliants i.2.1) SpecW) (off x) (off i.1) 1
abbrev Freight (x:Cover)(i:Wφ)(b:Bool)(m:ℕ)(r:ℝ):=Wane (stride b) (pinF i) (Fuse x i) m r
abbrev Gauke (x:Cover)(i:Wα)(m:ℕ)(r:ℝ):= Wane lace (pinG i) (Glint x i) m r
local notation "ξ" =>(yarn false)
abbrev NaR (t:ℝ)(x y:Cover):= t • (off y-off x)
lemma F_put (x y:Cover)(i j:Wφ)(K:Set E4)(h:0∉K)(t:ℝ)(v:0<t)(f:PathsZ (Fuse x i) (Fuse y j) K (NaR t x y) t): κF i j= (t:ℂ)^3* (∫ z:E4×E4,port ξ (NaR t x y+t • (z.2-z.1)) (pinF i) (pinF j) ∂(pairs (Fuse x i) (Fuse y j)).μ):=by
 have hp:=drill SpecW SpecW (off i.1) (off j.1) (off x) (off y) 2 t (blend i.2.1 j.2.1) 3 (Foulard v i.2.1 j.2.1) K h f v.le
 unfold κF; by_cases e:i.2.2=j.2.2
 · have he: ξ (pinF i) (pinF j)=blend i.2.1 j.2.1:= (portF i.2.1 j.2.1 i.2.2 j.2.2 false).trans ((if_pos e).trans (thread_un ..))
   rw [if_pos e.symm,Marne i.1 j.1 i.2.1 j.2.1 hp.1]; simp_rw [show ∀ u:E4,port ξ u (pinF i) (pinF j)=eye u (blend i.2.1 j.2.1) from fun u => congrArg (eye u) he]; exact hp.2
 rw [if_neg (Ne.symm e)]; simp_rw [show ∀ u:E4,port ξ u (pinF i) (pinF j)=0 from fun _=>(by change eye _ (ξ _ _)= _; rw [pinF,pinF,portF,if_neg e,map_zero]),integral_zero,mul_zero]
lemma G_put (x y:Cover)(i j:Wα)(K:Set E4)(h:0∉K)(t:ℝ)(v:0<t)(f:PathsZ (Glint x i) (Glint y j) K (NaR t x y) t): κg i j= (t:ℂ)^4* (∫ z:E4×E4,port ge (NaR t x y+t • (z.2-z.1)) (pinG i) (pinG j) ∂(pairs (Glint x i) (Glint y j)).μ):=by
 let T:=curl i.2.1.val.1 i.2.1.val.2 j.2.1.val.1 j.2.1.val.2; let P:=brackC (LensO i) (LensO j); have hp:=drill (addQ (Foliants i.2.1) SpecW) (addQ (Foliants j.2.1) SpecW) (off i.1) (off j.1) (off x) (off y) 1 t T 4 (Scarf v _ _ _ _) K h f v.le
 unfold κg; by_cases e:i.2.2=j.2.2
 · rw [if_pos e,greenCar (LensO i) (LensO j) hp.1]
   change (∫ x,T.val x ∂P.μ)=(t:ℂ)^4*(∫ z:E4×E4,eye (NaR t x y+t • (z.2-z.1)) (ge (pinG i) (pinG j)) ∂(pairs _ _).μ)
   simp_rw [show ge (pinG i) (pinG j)=T from (inlet ..).trans (if_pos e)]
   have hh:=hp.2; simp only [one_smul] at hh; exact hh
 rw [if_neg e]; simp_rw [show ∀ u:E4,port ge u (pinG i) (pinG j)=0 from fun _=>(by change eye _ (ge _ _)=_; rw [pinG,pinG,inlet,if_neg e,map_zero]), integral_zero,mul_zero]
-- relative offsets. doubled matter.Press
abbrev zF (x:Cover)(i:Wφ):Wφ:= (2*i.1-x,i.2) -- 2 multiplication integer array; OK?
abbrev zG (x:Cover)(i:Wα):Wα:=(i.1-x,i.2)
def Garn (i:Wφ):HopeC E4:= HopeC.lift SpecW (fun f:E4=> off i.1+(2:ℝ) • f) (by fun_prop)
lemma G_near (x:Cover)(i:Wα):Glint x i=Glint 0 (zG x i):=by
 have he: billMark (off x) (off i.1) 1=billMark (off 0) (off (i.1-x)) 1:=by funext u; unfold billMark; rw [off_sub]; simp only [one_smul]; rw [show off 0=0 from by ext k; simp [off],sub_zero]; abel
 unfold Glint diagram; congr 1 -- tune
lemma F_near (x:Cover)(i:Wφ): Fuse x i=Garn (zF x i):=by
 have he: off (zF x i).1=(2:ℝ) • off i.1-off x:=by ext k; simp [zF,off] -- tune
 unfold Fuse Garn diagram; congr 1; funext v; unfold billMark; rw [he]; module
end YM.GaugeFieldConstruction.Wick.Yacht
end
