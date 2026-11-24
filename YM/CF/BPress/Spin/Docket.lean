import YM.CF.BPress.Spin.Pledge
import YM.CF.BPress.Spin.Touches
/-! Actual spaces for Spin stages. Invitations here accept sums of chords; `AtW/OpenW` evaluate
 the expenditures needed on product with additional data, on any domain including Borel subdomains.
 `symbolHere` supplies the schedule thresholds before choosing Guard itself.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Spin
open Function Filter Finset Lattice Fock SU Lat Cube Tenant Branch Tulip Scroll Dial Pledge Drapes
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra

variable {N:Side}{a d:ℝ} {D:Type}
abbrev home (N:Side)(i:Single N):Site (More N):= node i.1.1
structure Form (N:Side)(D:Type) where
 eval: Support (More N)→D→D→ℝ
 pos(S : Support (More N))(x y): 0≤eval S x y
 mono{S T : Support (More N)}: S⊆T→∀x y, eval S x y≤eval T x y
namespace Form
def stage (F:Form N D): Stage (Site (More N)) (Single N) D Empty:= ⟨terr _,home _,fun i=> Empty.elim i, F.eval,F.pos,F.mono⟩ -- tune
abbrev Comes (F:Form N D)[TopologicalSpace D](P:Pledge)(f:Raw D (Single N)):= P.Costs F.stage f
lemma full (F:Form N D):Capacity F.stage quota:=by obtain ⟨A,B,C⟩:= Tulip.meterQ N 1; exact ⟨A,B,C⟩
lemma paid:0≤quota:=le_trans (by norm_num : (0:ℝ)≤16) quota_bound
def init (U:D→Bkg (More N)):Form N D:= ⟨fun S x y=> invitation S (U x) (U y),fun _ _ _=> invitation.positive,fun s _ _=> invitation.mono s⟩
-- plug paths and reindex
lemma pulls {D' : Type}[TopologicalSpace D'][TopologicalSpace D]{F:Form N D}{F':Form N D'}{A : Raw D (Single N)}{P:Pledge}(p:F.Comes P A)(f:D'→D)(u:Continuous f)(v:∀ S x y,F.eval S (f x) (f y)≤ F'.eval S x y) : F'.Comes P (A ∘ f):= Costs.pulls p f u rfl rfl v
end Form

abbrev OpenW (N:Side) (d:ℝ):= {x:Bkg (More N)// Cube.Guard x d}
abbrev AtW (N:Side)(d:ℝ): Form N (OpenW N d):= .init Subtype.val
variable {f:Raw (Bkg (More N)) (Single N)} {M:Jill.Male}
structure Shelf (N:Side)(d:ℝ)(j:ℕ)(P:Pledge) : Prop where
 entries (M:Jill.Male) : Form.Comes (AtW N d) P (spar j M ∘ Subtype.val)
 proj (M:Jill.Male)(x:OpenW N d) : IsStarProjection (spar j M x.val)
 tag (M:Jill.Male)(x: OpenW N d)(g) : spar j M (gauge g x.val)= twist (tradew N g) (spar j M x.val)

variable (j:ℕ)
theorem symbolHere (h:1≤j) : ∃ (e:ℝ) (v:ℕ) (P:Pledge), 0<e∧∀N:Side,v≤ N.val→∀ d≤e,Shelf N d j P:=by
 obtain ⟨A,r,e,pA,pr,hx,v,H⟩:= funde_s _ h; obtain ⟨C,hC,n,L⟩:= funde_q _ h; let Y:Pledge:=⟨A,r,pA,pr⟩; let U:=sphereRate; have hU:=sphereRate_cost
 refine ⟨min e C,max v n,Y.scales (U/e),lt_min hx hC,fun N w d g=>?_⟩
 have hp (M):= Drapes.Crown.lib (H M N ((le_max_left ..).trans w)); let ψ(x : OpenW N d):Openc (More N) e:= ⟨profile x.val,⟨x.val,x.property.shrink (g.trans (min_le_left ..)),by simpa⟩⟩
 constructor
 · intro M; refine Costs.morph (P:=Y) (hp M) ψ (Continuous.subtype_mk (Dial.profile_c.comp continuous_subtype_val) _) rfl rfl (div_pos hU.positive hx).le ?_
   intro S x y; change fare S (profile x.val) (profile y.val)/|e|≤U/e*invitation S x.val y.val; rw [abs_of_pos hx]; exact (div_le_div_of_nonneg_right (invitation.forum_compare hU) hx.le).trans_eq (by unfold U; ring)
 · intro M x; exact L M N ((le_max_right ..).trans w) x.val (x.property.shrink (g.trans (min_le_right ..)))
 intro M x g; unfold spar; rw [profile_g, twist_formula]; exact (hp M).tiesK.frame g (ψ x)
end YM.CF.BPress.Spin
