import Merino.JadeEye.Pith
import Merino.JadeEye.Ripe
import Merino.JadeEye.Arc
import Merino.Rind

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.JadeEye
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Swell

variable {n:Side}{P:BudgetPoint}
open Cuff -- Room and glint collision?
variable {o:Seat n} {v R:ℝ}

def lime (P:BudgetPoint)(R:ℝ):=R*(4*(P.threshold*(1+P.B)))
lemma low (P:BudgetPoint)(p:1≤R): P.threshold ≤ lime P R:=by
 have l:= P.threshold_pos
 unfold lime
 apply le_trans _ (le_mul_of_one_le_left (by positivity) p)
 rw [mul_add,mul_one]
 nlinarith only [l,mul_nonneg l.le (Nat.cast_nonneg (α:=ℝ) P.B)]

lemma hedge (h:Lip group v R)(b0:lime P R≤v)
   (b:2≤P.B)(l:2*(P.B/10+1)<(More n).val)
   (V:Pane n)(p:V∈pass P o):
  ∃ (g:Seat n→E) (X:Bows n),‖X‖≤lime P R ∧
    Agrees (purse (P.B/10) o) (gauge g V) (dyeB n X) := by
 have t:=P.threshold_pos.le
 have hn := t.trans (low P h.cost)
 obtain ⟨g,r⟩:=Planned.AtomRegular.Foliage.Cube.anchored o (ping_le p)
   t (Corona.halo_mono (by omega) (le_refl _)) l


 let U:=gauge g V
 let k:=P.B/10
 have y : ∀ (i: Edge (Seat n)),i.1∈purse k o →
    group.lieExp (group.plog (group.mat (U i)))=U i ∧
    ‖group.plog (group.mat (U i))‖≤lime P R:=by
   intro i hx; obtain ⟨a,w,q⟩:=halo_spec.mp hx
   rw [Finset.mem_singleton] at w;subst a
   have e:group.chord (U i)≤4*(P.threshold*(1+P.B)):= by
     apply le_trans (r _ q)
     exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (add_le_add le_rfl
        (Nat.cast_le.mpr (q.trans (Nat.div_le_self ..)))) t) (by norm_num)
   have a:= h.read (U i) ((e.trans (le_mul_of_one_le_left (by positivity) h.cost)).trans b0)
   exact ⟨a.1,a.2.trans (mul_le_mul_of_nonneg_left e (zero_le_one.trans h.cost))⟩
 let X:Bows n:=fun i=>if i.1∈purse k o then group.plog (group.mat (U i)) else 0
 refine ⟨g,X,(pi_norm_le_iff_of_nonneg hn).mpr ?_,?_⟩
 · intro i; unfold X; split; exact (y _ (by assumption)).2
   rwa [norm_zero]
 intro i hx _
 change U i=group.lieExp (X i)*1
 rw [mul_one]
 have p:X i=_:= if_pos hx
 rw [p,(y i hx).1]


def tux (g:Seat n→E):Bows n→L[ℝ]Bows n:=
 ContinuousLinearMap.pi fun i=>(group.adjoint (g i.1)).toContinuousLinearMap ∘L ContinuousLinearMap.proj i

lemma overcoat (g:Seat n→E):‖tux g‖≤1:= by
 apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one; intro i
 rw [one_mul]
 apply (pi_norm_le_iff_of_nonneg (norm_nonneg i)).mpr
 intro j
 change ‖group.adjoint _ (i j)‖≤‖i‖
 rw [group.norm_adjoint]
 exact norm_le_pi_norm i j

lemma acc (V:Pane n)(g:Seat n→E)(X:Bows n): gauge g (increment V X)=
   increment (gauge g V) (tux g X):=by
 funext i
 change g i.1 * (group.lieExp _ * _) * _ =
    group.lieExp (group.adjoint (g i.1) (X i)) * (g i.1 * _ * _)
 have q:group.lieExp (group.adjoint (g i.1) (X i)) = (g i.1)*group.lieExp (X i)*(g i.1)⁻¹:=by
    apply group.mat_injective; simp [Gauge.mat_lieExp,Gauge.mat_adjoint,Gauge.exp_conjugate];rfl
 rw [q]
 simp only [mul_assoc,inv_mul_cancel_left]


variable {K:Scree.Loom n}{F:SOp n}{d a c C r:ℝ}
structure Potion (P:BudgetPoint)(n:Side)(d v r C R:ℝ):Prop where
  sail:Lip group v R
  ride:Room d r C
  logx:lime P R≤v
  expo:lime P R<r
  cheap:lime P R≤1
  high:2≤P.B
  wide:2*(P.B/10+1)<(More n).val

theorem spend (p:Potion P n d v r C R) (t:Skylit P d K)
   (j:Trunk o F (P.B/10) a c d)(ha:0≤a)
   (V:Pane n)(q:V∈pass P o)(T:Bows n→L[ℝ]Bows n)(u:‖T‖≤P.threshold) :
  Jet.Allows 6 (fun y=> (masked K P o F (increment V (T y))).trace) 0
      (‖(F (profile 1)).trace‖+c*C*lime P R^2):=by
 obtain ⟨g,X,H,A⟩:= hedge p.sail p.logx p.high p.wide V q
 let L:Bows n→L[ℝ]Duo n:=
    (ContinuousLinearMap.inr ..).comp ((tux g).comp T)
 have hr:=low P p.sail.cost
 have hn:=P.threshold_pos.le.trans hr
 have hl:‖L‖≤lime P R:=by
    apply L.opNorm_le_bound hn; intro y
    change max ‖(0:Bows n)‖ ‖tux g (T y)‖≤_
    rw [norm_zero]


    refine max_le (by positivity) ?_
    apply le_trans ((tux g).le_opNorm (T y))
    rw [←one_mul (lime P R * ‖y‖)]
    exact mul_le_mul (overcoat g) ((T.le_opNorm y).trans (mul_le_mul_of_nonneg_right (u.trans hr) (norm_nonneg y))) (norm_nonneg _) zero_le_one
 let z:Duo n:=(X,0)
 have m:‖z‖≤lime P R:=max_le H (by rw [norm_zero]; exact hn)

 let J:= glint (filer d F)
 have e : Jet.Allows 6 (fun y=>J (z+L y)) 0 (‖J 0‖+c*C*lime P R^2):=
    ferment hn p.cheap (fun _ q=>age j.pay p.ride ha (q.trans p.expo.le)) (young j.pay p.ride ha) z m L hl
 have he:J 0=(F (profile 1)).trace:=by
   have f:=p.ride.get (0:Duo n) (by rw [norm_zero]; exact p.ride.haveR.le)
   unfold J glint
   rw [Jet.equalizer,dif_pos f]
   have hz: du n 0=1:=by
      change increment (increment 1 (0:Bows n)) 0=1
      simp only [AnalyticBridge.Merino.at_zero]
   change (F (profile _)).trace=_
   rw [hz]
 rw [he] at e
 refine e.germ ?_


 have hw: ∀ᶠ y in 𝓝 (0:Bows n), ‖z+L y‖<r:=
    ((continuous_const.add L.continuous).norm.continuousAt.eventually
      (gt_mem_nhds (by simpa [z] using m.trans_lt p.expo)))
 have hc:Continuous (increment V):=by unfold increment; fun_prop
 have hb: ∀ᶠ y in 𝓝 (0:Bows n), increment V (T y) ∈ pass P o:=
    (hc.comp T.continuous).continuousAt.eventually (ping_o.mem_nhds
      (by rw [Function.comp_apply,map_zero,AnalyticBridge.Merino.at_zero]; exact q))
 filter_upwards [hw,hb] with y hy ey
 let U:=increment V (T y)
 let W:=du n (z+L y)
 change J (z+L y)=(masked K P o F U).trace
 rw [←trace_twist (tradew n g) (masked K P o F U),←mask_gauge t ha j]
 have d': profile W∈Openc (More n) d:=p.ride.get _ hy.le
 rw [mask_extension t ha j (show gauge g U ∈pass P o from (pingB U g).mpr ey) d']
 · unfold J glint
   rw [Jet.equalizer,dif_pos d']
 unfold U
 rw [acc]
 change Agrees _ _ (increment (increment 1 (X+0)) (0+tux g (T y)))
 rw [add_zero,zero_add]
 intro i s₁ s₂
 exact congrArg (_ * ·) (A i s₁ s₂)

