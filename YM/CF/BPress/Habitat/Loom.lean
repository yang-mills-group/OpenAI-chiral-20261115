import YM.CF.BPress.Habitat.Race
/-! Lantern Plain(screw fields) on all arguments. file.Pose Ambient topology and measurable conventions. don't store flags/clamp here. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Habitat
open Function Finset NormedSpace MeasureTheory Filter Metric Lattice Wilson Branch Fock Spin SpinSign Spin.Pledge Cube Lat SU Spin.Paint Nacre Laic Font Tulip Tenant Dial Scroll Thera Meadow Topology Upled
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace ContDiff Classical YM.CF.BPress.Vesper
attribute [local instance] opCStarAlgebra
abbrev Lamp(s:Side):=Site s → Upled Slot
abbrev Fate(N:Side):=Site N→ Bool
abbrev Plain(N:Side):=Bkg (More N) × Stun N × Fate N × Lamp (More N) × Lamp (More N)
variable {N:Side}
namespace Plain
abbrev G(x:Plain N): Bkg (More N):=x.1
abbrev X(x: Plain N):Stun N:=x.2.1
abbrev stars(x:Plain N): Fate N:= x.2.2.1
abbrev H0(x:Plain N): Lamp (More N):= x.2.2.2.1
abbrev H1(x:Plain N):Lamp (More N):=x.2.2.2.2
def lamp(x:Plain N)(t:Bool): Lamp (More N):= if t then x.H1 else x.H0
def spin(x:Plain N)(t:Bool)(v:ℝ):Paint (More N):= fun i=> Upled.decode (x.lamp t i) v
def key(x:Plain N): Support N:= univ.filter fun i=> x.stars i
scoped instance Bore_l {s:Side} : BorelSpace (Lamp s) :=by haveI : SecondCountableTopology (Upled Slot):=inferInstance; infer_instance -- maybe self ref
scoped instance bore_p : BorelSpace (Plain N):= by haveI : SecondCountableTopology (Upled Slot):=inferInstance; haveI : SecondCountableTopology (Lamp (More N)):=inferInstance; haveI : BorelSpace (Fate N):= inferInstance; haveI : BorelSpace (Lamp (More N) × Lamp (More N)):=inferInstance; haveI : BorelSpace (Fate N × Lamp (More N) × Lamp (More N)):= Prod.borelSpace; haveI : BorelSpace (Stun N):=inferInstance; apply Prod.borelSpace
@[fun_prop] lemma cont_G : Continuous (Plain.G (N:=N)):= continuous_fst
@[fun_prop] lemma cont_X : Continuous (Plain.X (N:=N)):=continuous_fst.comp continuous_snd
@[fun_prop] lemma cont_star :Continuous (Plain.stars (N:=N)):= continuous_fst.comp (continuous_snd.comp continuous_snd)
@[fun_prop] lemma cont_lamp (t:Bool) :Continuous (fun i:Plain N=> i.lamp t):=by cases t; exact continuous_fst.comp (continuous_snd.comp (continuous_snd.comp continuous_snd)); exact continuous_snd.comp (continuous_snd.comp (continuous_snd.comp continuous_snd))
@[fun_prop] lemma cont_spin (t:Bool):Continuous (fun i:Plain N ×ℝ=> i.1.spin t i.2):= continuous_pi fun j=> decode_c.comp ((((continuous_apply j).comp (cont_lamp t)).comp continuous_fst).prodMk continuous_snd)
variable (S:Support (More N))(x y:Plain N)
abbrev FateTick (x y:Bool):ℝ:= if x=y then 0 else 1
lemma tickc (x y: Bool): 0≤ FateTick x y:=by unfold FateTick; split <;> norm_num
def turnTick := ∑ i: Site N with node i∈ S,FateTick (x.stars i) (y.stars i)
def sun (i:Site (More N)):= dist (x.X i) (y.X i) + δFee (x.H0 i) (y.H0 i)+δFee (x.H1 i) (y.H1 i)
lemma sun_pos (i:Site (More N)): 0≤ sun x y i:=add_nonneg (add_nonneg dist_nonneg dist_nonneg) dist_nonneg
def meetP := ∑ i∈ S,sun x y i + 0 -- tune parentheses parse `,sun i+0` maybe drops
-- eval sum metric
abbrev evalC := invitation S x.G y.G+turnTick S x y+meetP S x y
lemma tick_h : 0≤ turnTick S x y:=sum_nonneg fun i _=>tickc ..
lemma meet_h :0≤ meetP S x y:=by simp only [meetP,add_zero]; exact sum_nonneg fun i _=>sun_pos ..
lemma pos_eval : 0≤ evalC S x y:= add_nonneg (add_nonneg invitation.positive (tick_h S x y)) (meet_h S x y)
lemma mono_tick {Q:Support (More N)}(u:S⊆Q): turnTick S x y ≤ turnTick Q x y:= sum_le_sum_of_subset_of_nonneg (fun i h=> mem_filter.mpr ⟨mem_univ _,u ((mem_filter.mp h).2)⟩) (fun _ _ _=>tickc ..) -- tune
lemma mono_τ {Q:Support (More N)}(u:S⊆Q) : evalC S x y≤ evalC Q x y:=add_le_add (add_le_add (invitation.mono u) (mono_tick S x y u)) (by simp only [meetP,add_zero]; exact sum_le_sum_of_subset_of_nonneg u fun _ _ _=>sun_pos ..)
lemma ticketS: invitation S x.G y.G≤ evalC S x y:=(le_add_of_nonneg_right (tick_h S x y)).trans (le_add_of_nonneg_right (meet_h S x y))
lemma ticketT: turnTick S x y≤ evalC S x y:= (le_add_of_nonneg_left invitation.positive).trans (le_add_of_nonneg_right (meet_h S x y))
lemma ticketU(i:Site (More N))(h:i∈S): sun x y i≤ evalC S x y:= by unfold evalC; refine le_trans ?_ (le_add_of_nonneg_left (add_nonneg invitation.positive (tick_h S x y))); unfold meetP; rw [add_zero]; exact single_le_sum (fun i _=>sun_pos x y i) h -- tune plus
lemma spins (v:ℝ) (h:v∈Set.Icc (0:ℝ) 2)(i)(k:i∈ S)(t:Bool): ‖x.spin t v i-y.spin t v i‖≤evalC S x y:=by
 apply le_trans ?_ (ticketU S x y i k); cases t; · exact (supPrice ..|>.1 le_rfl) v h|>.trans ((le_add_of_nonneg_left dist_nonneg).trans (le_add_of_nonneg_right dist_nonneg)) -- tune elaboration
 exact (supPrice ..|>.1 le_rfl) v h|>.trans (le_add_of_nonneg_left (add_nonneg dist_nonneg dist_nonneg)) -- tune
end Plain
end YM.CF.BPress.Habitat
