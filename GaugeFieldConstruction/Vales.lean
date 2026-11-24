import GaugeFieldConstruction.Ivorine
import YM.CF.Roots.Seat
import SatinThinPiers
import YM.CF.Mica.Sleet
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 30000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.TableF
open Function Filter Metric Lattice Wilson Finset MeasureTheory RG Precision Tree
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open FlightFlux Fluxim
open Fock Tulip Lat Spire Phase Cube
attribute [local instance] opCStarAlgebra
open AnalyticBridge VerifiedReset Taxi
local notation "GS"=> SU.group
variable {n:Side}{p: BudgetPoint}{Q: InkD n}{o:Skye.Seat n}{X:Scree.Hub n}{h c:ℝ}
namespace Lenten
open Bank Laurent Bloch Tap Hove Spire
open Haro Hove Moto Tap
namespace Layout
open scoped YM.CF.Mew
open HushP ModuleB Pastry Flot
namespace Fren
open Skye Levier Scroll Spire Ione
open Lattice
open ProjectorNext.Equivariance (bonds pull_increment roll pulledDirection)
-- Point root always moves by pull. x at old.
variable (s:Sweep n)(R:Signed)
open Rush
-- anchor costs on this chart.
def Nwall (n:Side):Prop:=300<n.val
lemma delta_o (v:Site n)(u:10*separation (node v) o < (More n).val)(g:100<n.val): 8*separation (AnchorN o) v< n.val:=by
 have he: separation o (node (AnchorN o))≤4:=by
    have ht: 2*lateral (siteOffset o)< (More n).val:=by change _<n.val*2; have hf:=rent_z o; omega
    rw [separation_comm]; change spread (stem o (node (AnchorN o))) ≤_; rw [show stem o (node (AnchorN o))= siteOffset o from lift_path (by rw [anchor_E]; abel) ht]; exact Finset.sup_le fun i _=> (height_l _ _).trans (rent_z o)
 have hx:= separation_triangle (node v) o (node (AnchorN o)); rw [Hove.ζdist, separation_comm v] at hx; change 10*_<n.val*2 at u
 omega
private lemma carryAB (z w:Cover)(o:Site n) : Rush.wind o z*Rush.wind (o+wrap _ z) w= Rush.wind o (z+w):=by
 let T:= o+wrap n z; let V:=infT o z; let X:=infT T w; let Y:=infT o (z+w); let P:= periods n (natural o+z); let K:= periods n (natural T+w); let D:= periods n (natural o+(z+w));
 have hp:P+K=D:=by
    apply nsmul_right_injective (M:=Cover) n.property.ne'; change n.val • (P+K)=n.val • D; rw [smul_add]; unfold P K D; rw [show o+wrap n (z+w)=T+wrap _ w from (by unfold T; rw [map_add, ←add_assoc])] at Y; unfold T at *; linear_combination (norm:=abel) V+X-Y
 unfold Rush.wind; rw [←dues]; exact congrArg fee hp
lemma gold_F (o:Skye.Seat n)(i j:Site n)(f:8*separation (AnchorN o) i < n.val)(u:8*separation (AnchorN o) j<n.val):
 Caller o i*Caller o j= Rush.wind i (stem i j):=by
 let x:=AnchorN o; let V:=stem x i; let W:=stem x j; have he: stem i j=W-V:=by
    apply lift_eq_iff.mpr; refine ⟨?_,fun a=>?_⟩
    · rw [map_sub,show wrap n W=j-x from wrap_lift _,show wrap n V=i-x from wrap_lift _]; abel
    have hv:=component_le (j-x) a; have hx:=component_le (i-x) a; rw [separation_comm] at f u; unfold V W x at *; unfold separation stem at *; simp only [Pi.sub_apply]; omega
 have hp:= carryAB V (stem i j) x; rw [he, show x+wrap n V=i from (by rw [show wrap n V=_ from (show wrap n V=i-x from wrap_lift _)]; abel),show V+(W-V)=W from (by abel)] at hp
 rw [he]; change Rush.wind _ _* Rush.wind x W=_; rw [←hp,←mul_assoc,show Rush.wind x V* Rush.wind x V=1 from fee_one _,one_mul] -- tune
-- pair in movement instance. let mill = s sites
abbrev bookx (v:Site n):= (castX s).mills n v
lemma pays_E (i:Site n):node (bookx s i)=boxA s (node i):= (castX s).nodex i
lemma stir_gap (x: Site n): separation (node (bookx s x)) o=separation (node x) (sh s o):=by rw [pays_E]; nth_rw 1 [← show boxA s (sh s o)=o from Equiv.apply_symm_apply ..]; rw [sitT]
lemma stir_IO(i j:Site n) : separation (bookx s i) (bookx s j)=separation i j:=by unfold bookx; rw [Scroll.Shape.mills,Scroll.Shape.mills,affine,affine,separation_translate,separation_signed] -- tune namespace
variable (o) {s}
-- when supporting. for moving X old puts Z inputs. use Nonwrapping at h (older path sufficiently late). budgets constant independent n
lemma fee_c (s:Sweep n)(x y:Site n)(p:10*separation (node (bookx s x)) o < (More n).val)(e:10*separation (node (bookx s y)) o < (More n).val)(K:100<n.val): let a:=castX s
 Caller o (bookx s x)* Caller o (bookx s y)= a.payA x*a.payA y * (Caller (sh s o) x*Caller (sh s o) y):=by
 intro a; let X:=bookx s x; let Y:=bookx s y; let Z:= AnchorN (sh s o); have hp : 8*separation Z x < n.val:= delta_o x ((stir_gap ..) ▸ p) K -- scope
 have hx : 8 * separation Z y<n.val:=delta_o y ((stir_gap ..) ▸ e) K
 rw [gold_F o _ _ (delta_o _ p K) (delta_o _ e K), gold_F (sh s o) _ _ hp hx]
 have he: stem X Y=a.s.act (stem x y):=by
    have h1:2*separation y x < n.val:=by have ht:=separation_triangle y Z x; rw [separation_comm y Z] at ht; omega
    apply lift_eq_iff.mpr; let V:=stem x y; refine ⟨?_,fun i=>?_⟩
    · rw [←wrap_signed]; unfold stem; rw [wrap_lift]; unfold Y X bookx Scroll.Shape.mills affine; rw [Signed.act_sub, add_sub_add_right_eq_sub] -- tune
    obtain ⟨j,rfl⟩:= a.s.perm.surjective i; rw [Signed.act_at]; have ht:= component_le (y-x) j; unfold separation at h1; unfold stem; split <;> omega
 let v:=stem x y; change Rush.wind X (stem X Y)= _; have hd:x+wrap n v=y:=by rw [show wrap n v=y-x from wrap_lift _]; abel
 rw [he]; let H:ℂ:=Rush.wind X (a.s.act v); let w:=Rush.wind x v; have h':= footFee a x v; rw [hd] at h'; change _*H= w*a.payA y at h'; change H=_*w; linear_combination a.payA x*h'-H*a.reflex x
variable (s)
abbrev night(g:Bool):ℝ:= if g then -1 else 1
def κcad (R:Signed)(g:Bool): Plane→L[ℝ]Plane:=by
 refine LinearMap.toContinuousLinearMap ⟨⟨fun i=> night g • R.act i,?_⟩,?_⟩
 · intro a b; rw [R.act_add,smul_add]
 intro u i; change night g • R.act (u • i) = u • (night g • R.act i); rw [show R.act (u • i)=u • R.act i from ?_,smul_comm]
 ext j; obtain ⟨j,rfl⟩:= R.perm.surjective j; simp only [Pi.smul_apply,R.act_at]; split <;> simp
lemma rom_d (R:Signed)(b:Bool)(v:Cover)(x:Plane): rom (R.act v) (κcad R b x)=night b*rom v x:=by
 rw [rom_p,rom_p,← Equiv.sum_comp R.perm,Finset.mul_sum]; apply sum_congr rfl; intro i _; change (↑(_:ℤ):ℝ)*( (night b • R.act x) (R.perm i))= _; rw [Pi.smul_apply]; change _*(night b*R.act x _)=_; rw [R.act_at,R.act_at]; split <;> push_cast <;> ring
abbrev candT (R:Signed)(g:Bool): Views→L[ℝ]Views:= ContinuousLinearMap.prodMap (κcad R g) (κcad R g)
lemma angle_κ(R:Signed)(g:Bool)(p:Plane): Lenten.angle (κcad R g p)= Scroll.cadence R g (Lenten.angle p):=by
 funext i; obtain ⟨j,rfl⟩:= R.perm.surjective i
 change (((night g • R.act p) (R.perm j):ℝ):ℂ)= _; cases g <;> cases h:R.flip j <;> simp [night,angle,Scroll.cadence,h]
variable {o}
lemma pose_C (x:Site n)(t:10*separation (node (bookx s x)) o < (More n).val)(a:Plane)(b:Bool): pointF o (bookx s x) (κcad s.s b a)= night b*pointF (sh s o) x a:=by
 unfold pointF; rw [pays_E,stem_S s (node x) (pays_E s x ▸ t)]; simp only [_root_.smul_apply,smul_eq_mul]; rw [rom_d]; ring -- tune orientation
lemma φ_e (x y:Site n)(u:10*separation (node (bookx s x)) o < (More n).val)(v:10*separation (node (bookx s y)) o < (More n).val)(a:Views)(b:Bool) : κviews o (bookx s x) (bookx s y) (candT s.s b a)= night b* κviews (sh s o) x y a:=by
 change -(pointF o _ (κcad s.s b _)) + pointF o _ (κcad _ b _)= night b*((- (pointF _ _ a.1))+ pointF _ _ a.2); rw [pose_C s x u, pose_C s y v]; rw [mul_add,mul_neg]; rfl
lemma PhaseV (x y:Site n)(u:10*separation (node (bookx s x)) o < (More n).val)(v:10*separation (node (bookx s y)) o < (More n).val)(a:Views)(b:Bool) : PayS (κviews o (bookx s x) (bookx s y)) (candT s.s b a)= cSignX b (PayS (κviews (sh s o) x y) a):=by
 unfold PayS; rw [φ_e s x y u v a b]; cases b; · rw [show night false=1 from rfl,one_mul]; rfl
 let X:ℝ:=κviews (sh s o) x y a
 rw [show night true= -1 from rfl,neg_one_mul]; change Complex.exp (Complex.I*(↑(-X)))= (starRingEnd ℂ) (Complex.exp (Complex.I*↑X)); rw [← Complex.exp_conj,map_mul]; simp
end Fren
end Layout
end Lenten
end YM.CF.TableF
end
