import YM.CF.Haro.Celt
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Haro
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Stationary Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Fock Tulip Font Spire Nacre Ember Pec
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker MatrixOrder Classical
attribute [local instance] opCStarAlgebra
open Tap Hake Urn Yaw Levier Proa Rill
variable {c f:Side}(j m:ℕ)(e:Even j)(h:2 ≤ j)
variable (G:Ratio c f)(ho:Odd G.count.val)
open Branch Laic
variable {t:ℝ}(Y: cro G t)(W: Meter TailB G t)(V: Meter Grave G t)
open Skye Precision
open Jet
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{z:E}
-- value at rotated ALL. Fine fields read near stock literal. 
open Lat
variable {x ε τ τ' s d b K R:ℝ}{l:ℕ}
def diverge(k:Side)(B:Support (More k))(A:Pane k)(v:ℝ):Prop:=∀ i:Pressure.Bond (More k), ends i⊆ B → ‖brand (A i)-1‖ ≤ v
lemma diverged{u:Side}(Z:Support (More u))(A:Pane u)(v:ℝ)(h:0 ≤ v)(p:diverge u Z A v):NearS u Z A v:=by
 intro i y; apply (pi_norm_le_iff_of_nonneg h).mpr; intro b; cases b; change ‖star _ -(1:Tulip.Twig)‖≤_; rw [← star_one (R:=Tulip.Twig),←star_sub,norm_star]; exact p i y; exact p i y
lemma breeze(F Q: Pane f)(g:Site (More f)→SU.E)(i: Pressure.Bond (More f))(x:SU.E)(p:F i*(Q i)⁻¹=x):‖brand (Lattice.gauge g F i)-brand (Lattice.gauge g Q i)‖=‖brand x-1‖:=by
 unfold Lattice.gauge; simp_rw [brand_mul,brand_inv,← sub_mul,←mul_sub]; rw [brand_rig,brand_lef]; rw [←p,brand_mul,brand_inv]
 rw [show brand _* star (brand _)-1=(brand (F i)-brand (Q i))*star (brand (Q i)) from by rw [sub_mul,show _*star (brand _)=1 from (brand_unit (Q i)).2],brand_rig] -- tune
lemma δ_L(a:ℝ)(p:0<a):∃ b:ℝ,0<b ∧∀ i:SU.group.Color,‖i‖ < b → ‖brand (SU.group.lieExp i)-1‖≤ a:=by
 let f:=brand ∘ SU.group.lieExp; have ht:Continuous f:= Dial.spinD.comp SU.group.lieExp_cont; have hv:= Metric.mem_nhds_iff.mp (ht.continuousAt.eventually (Metric.ball_mem_nhds (f 0) p)); obtain ⟨c,h,x⟩:= hv; refine ⟨c,h,fun i p=>?_⟩; have hx:‖f i-f 0‖<a:=mem_ball_iff_norm.mp (@x i (mem_ball_zero_iff.mpr p)); rw [show f 0=1 from by simp [f,brand_one]] at hx; exact hx.le
-- ANY transferred g. fully physical.H
open RG Tree Pressure -- tune
open PhysicalNext.JointLoad
variable {S: StepData (More c) (More f)}(fK:S.ratio=ratio G)(T: Arch G t) (M:Forge.Monk SU.group S)
variable {g:Seat c→SU.E}(D:Support (More f))(U:Support (More c))
def herb (U:Seat f→SU.E)(A:Rill.Arch G t): Rill.Arch G t:= ⟨(july G U A.val.1, Lattice.gauge U A.val.2),joint_g G _ A.property.1 U,A.property.2.cov _⟩
variable (f' W':Pane f) {o:Seat c}{P:BudgetPoint}{n:ℕ}
include fK ho
lemma helix_l (hF:Agrees D f' T.val.1.1)(hz:f'= T.val.2)(h: Rill.PaneL M U x ε τ W') (p: Heir.Canvas P o l M.V g n K)(pK:0 ≤ K)(v: Agrees D W' f')(w:Agrees (cloudG G D) M.V T.val.1.2)(hp: (∀ i∈ D,(ratio G).parent i∈U))
 (hs:∀ i∈ D, (ratio G).parent i ∉ M.key.dome (20*radiusB x))(hv:∀ i∈D,separation o ((ratio G).parent i) ≤ l) (hb:0 ≤ b)(ht:∀ i:SU.group.Color,‖i‖< τ → ‖brand (SU.group.lieExp i)-1‖≤ b/2)(ha: K*P.threshold*(1+(l:ℝ)) < τ) : let A:= herb G (g ∘ (ratio G).parent) T; NearS f D A.val.1.1 b∧NearS c (cloudG G D) A.val.1.2 b∧NearS f D A.val.2 b:=by
 intro A; let P':= Precision.replica (ratio G) M.V; let Q:= gauge g M.V; have he: scaleG G (g ∘ (ratio G).parent)=g:=funext fun i=>by simp [Peaks.scaleG,Ratio.embed_parent] -- tune M.V unfold
 have hc(i:Bond (More c))(z:separation o i.1 ≤ l): ‖brand (Q i)-1‖≤ b/2:=by
    rw [show Q i= group.lieExp _ from Siete.lift_q p i z]; refine ht _ ((p.size i z).trans_lt (lt_of_le_of_lt ?_ ha)); have hy:= P.threshold_pos; gcongr -- tune gauge group
 have hj:NearS c (cloudG G D) (gauge g T.val.1.2) b:=by
    apply diverged _ _ _ hb; intro i z
    obtain ⟨x,y⟩:=insert_subset_iff.mp z; have hl: Agrees (cloudG G D) Q (gauge g T.val.1.2):=tied _ _ _ g g w (fun _ _=>rfl); rw [←hl i x (singleton_subset_iff.mp y)]
    exact (hc i (by have h:= hv _ (mem_filter.mp x).2; rw [Ratio.embed_parent] at h; exact h)).trans (half_le_self hb)
 have hk:NearS f D (gauge (g ∘ (ratio G).parent) f') b:=by
    apply diverged _ _ _ hb; intro i z; obtain ⟨y,u⟩:=insert_subset_iff.mp z
    rw [←tied D W' f' (g ∘ (ratio G).parent) (g ∘ (ratio G).parent) v (fun _ _=>rfl) _ y (singleton_subset_iff.mp u)]; refine (norm_sub_le_norm_sub_add_norm_sub _ (brand (Lattice.gauge (g ∘ (ratio G).parent) P' i)) _).trans ?_
    have hx:‖brand (gauge (g ∘ (ratio G).parent) P' i)-1‖≤ b/2:=by
       unfold P'; rw [show Lattice.gauge (g ∘ (ratio G).parent) (Precision.replica (ratio G) M.V)=Precision.replica (ratio G) (gauge g M.V) from copied (ratio G) ho _ _]; unfold Precision.replica; split; · simp [brand_one]; positivity
       exact hc _ (hv i.1 y)
    obtain ⟨z,k,p⟩:= h.farF i (by rw [fK]; exact hp _ y) (by rw [fK]; exact hs _ y); rw [fK] at p; rw [breeze W' P' (g ∘ (ratio G).parent) i _ p.symm]; exact (add_le_add (ht _ (mem_ball_zero_iff.mp k)) hx).trans_eq (by ring)
 change NearS _ _ (gauge _ T.val.1.1) _ ∧ NearS _ _ (gauge _ _) _ ∧ NearS _ _ (gauge _ _) _
 rw [←hz,he]; refine ⟨?_,hj,hk⟩
 intro i w; obtain ⟨d,u⟩:= insert_subset_iff.mp w; let K:=g ∘ (ratio G).parent; let e:= gauge K T.val.1.1; have ht: (Tulip.profile e i)= Tulip.profile (gauge K f') i:= by
    ext1 y; unfold profile e; rw [←Skye.tied D _ _ K K hF (fun _ _=>rfl) i d (singleton_subset_iff.mp u)]
 rw [show Tulip.profile _ i= _ from ht]; exact hk i w
end YM.CF.Haro
