import YM.CF.Cour.Hue
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.Cour
open Function NormedSpace Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Laic Tenant Proa Broc Jet Pec MeasureTheory
open scoped Matrix.Norms.L2Operator Topology BigOperators NNReal Classical ContDiff InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{n m B:Side}{u a C K:ℝ}{k:ℕ}
abbrev BaseV(n:Side):= Signed× Site n× Ok n× Ok n
def vood(x:BaseV n):Site (More n):= (incX x.1).anon n (node x.2.1)
def eyes(v:Signed)(x:Site n)(i:Ok n):=traceP ((incX v).anon n (node x)) (Moire.rayW (incX v) (boot (node x) i))
def home(v:BaseV n):=eyes v.1 v.2.1 v.2.2.1 ∪ eyes v.1 v.2.1 v.2.2.2
abbrev earY(v:BaseV n):= contour (node v.2.1) v.2.2.1 v.2.2.2
lemma home_p(v:BaseV n):Grove (terr _) (home v)∧ vood v∈ home v:= ⟨(trace_g ..).unite (trace_g ..) (trace_source ..) (trace_source ..), mem_union_left _ (trace_source ..)⟩
lemma home_l(v:BaseV n):(↑(home v).card:ℝ) ≤ 8* earY v+18:=by
 have hp(i): (eyes v.1 v.2.1 i).card ≤ 8*(dial (node v.2.1) i+1)+1:= by unfold eyes; apply (trace_k ..).trans; rw [Moire.ray_L]; exact Nat.add_le_add_right (leanB ..) _
 have he := (card_union_le (eyes v.1 v.2.1 v.2.2.1) (eyes v.1 v.2.1 v.2.2.2)).trans (Nat.add_le_add (hp _) (hp _)); unfold home earY contour
 apply (show (↑(eyes v.1 v.2.1 v.2.2.1 ∪ eyes v.1 v.2.1 v.2.2.2).card:ℝ)≤↑((8*(dial (node v.2.1) v.2.2.1+1)+1)+(8*(dial (node v.2.1) v.2.2.2+1)+1)) from Nat.cast_le.mpr he).trans; push_cast; exact le_of_eq (by ring)
abbrev clipW(v:Signed)(x:Site n)(i:Ok n)(U: Post n):SU.group.Color:=silt (node x) i (Yg (incX v) U)
lemma chip(x:Signed)(v:Site n)(i:Ok n)(F F':Post n)(p:Agrees (eyes x v i) F F'): clipW x v i F=clipW x v i F':=by
 unfold clipW silt; simp_rw [← Moire.ray_t]; congr 1; exact travel_local _ _ _ _ (fun i hi ht=> p i (List.mem_toFinset.mpr hi) (List.mem_toFinset.mpr ht)) -- tune
lemma sugar(x:Signed)(v:Site n)(i:Ok n): Continuous (clipW x v i):= (siltC ..).comp (f:=Yg (incX x)) (by rw [show Yg (n:=n) (incX x)= Lattice.pull x 0 from funext fun i=> Ywin x i]; exact Wilson.continuous_pull ..) -- tune
abbrev oil(W:Pride n)(v:BaseV n):ℂ:= W v.2.1 v.2.2.1 v.2.2.2
def bead(W:Pride n)(v:BaseV n)(U:Post n): ℂ:=let f:=clipW v.1 v.2.1; ((Fintype.card Signed:ℝ)⁻¹ * inner ℝ (f v.2.2.1 U) (f v.2.2.2 U)) • (pays v.1 (oil W v))
lemma shore_P(W:Pride n)(U:Post n):pigment W U=∑ v:BaseV n,bead W v U:=by
 unfold pigment lexn zinger Pec.tag BaseV; simp_rw [Fintype.sum_prod_type,map_sum, Finset.smul_sum,map_smul,smul_smul]; rfl
lemma brimC(W:Pride n)(x:BaseV n):Continuous (bead W x):=by unfold bead; exact (continuous_const.mul ((sugar x.1 x.2.1 x.2.2.1).inner (𝕜:=ℝ) (sugar x.1 x.2.1 x.2.2.2))).smul continuous_const
lemma pays_nN(s:Signed)(x:ℂ): ‖Pec.pays s x‖=‖x‖:=by cases v:detX s<;> simp [Pec.pays,v]
lemma wagon (h:0 ≤ u)(t:0<a)(k:ℕ):∃ A:ℝ,1 ≤ A∧ ∀ {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{n:Side}(V:Pride n)(w:BaseV n)(q:E→ Post n)(p:E), Jet.TransK k q p u→ Allows k (bead V w ∘ q) p (A*Real.exp (a*earY w)*‖oil V w‖):=by
 obtain ⟨c,v,H⟩:= yolk u h t k
 let f:=((Fintype.card Signed:ℝ)⁻¹); let M:= innerSL ℝ (E:=SU.group.Color); let X:=2^k*‖M‖; let D:=f*(X*c*c)
 refine ⟨max 1 D,le_max_left ..,@fun E _ _ n V w q p u=>?_⟩; let W(i):= H p q u (incX w.1) (node w.2.1) i; let L:= pays w.1 (oil V w); let P:= (ContinuousLinearMap.id ℝ ℝ).smulRight L
 have he: ‖P‖ ≤ ‖oil V w‖:=by unfold P L; rw [ContinuousLinearMap.norm_smulRight_apply,pays_nN]; simp -- tune
 let i:=w.2.2.1; let j:=w.2.2.2; let y(k:Ok n):= c*Real.exp (a*dial (node w.2.1) k); have hv :Jet.Allows k (fun y=> f* inner ℝ (clipW w.1 w.2.1 i (q y)) (clipW w.1 w.2.1 j (q y))) p (|f| * (X*y i *y j)):= ((W i).bilinear M (W j) le_rfl).smul f
 apply ((hv.linear P he).mono ?_); apply le_trans _ (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right 1 D) (Real.exp_pos ..|>.le)) (norm_nonneg _)); rw [abs_of_nonneg (show 0≤f by unfold f; positivity)]; apply le_of_eq; unfold D earY contour y i j; rw [mul_add a,Real.exp_add]; ring
lemma brassA (k:ℕ)(p:1 ≤u)(ht:0<a):∃ A:ℝ,1≤A ∧∀ e:ℝ,∀ (m B: Side)(W:Pride (CSide m B))(v: BaseV (CSide m B)), Flash (Spire.soar m B e) (aether k u e m B) k (home v) (bead W v ∘ Subtype.val) (A*Real.exp (a*earY v)*‖oil W v‖):=by
 obtain ⟨A,h,H⟩:= wagon (zero_le_one.trans p) ht k
 refine ⟨A,h,fun e m B W v=> ⟨⟨mul_nonneg (mul_nonneg (zero_le_one.trans h) (Real.exp_pos ..|>.le)) (norm_nonneg _),fun _=>(home_p v).1,(brimC ..).comp continuous_subtype_val,fun x=> ?_,fun x y p=>?_,fun x y=>?_⟩,fun E _ _ _ V t f p x hx=>H _ _ _ _ (p x hx)⟩⟩
 · let U(z:ℝ):=x.val; exact (H W v U 0 (fun i=> allows_const _ ((show ‖fund (x.val i)‖=1 from CStarRing.norm_of_mem_unitary (firstF _).property).trans_le p))).value -- tune
 · dsimp only [bead,Function.comp_apply]; rw [chip _ _ _ x.val y.val (fun i o h=>p i (mem_union_left _ o) (mem_union_left _ h)),chip v.1 v.2.1 v.2.2.2 x.val y.val (fun i o h=> p i (mem_union_right _ o) (mem_union_right _ h))]
 dsimp only [Function.comp_apply,bead]; unfold Spire.soar; simp only [clipW,van,silt_g, StressFlux.inner_adjoint]
end YM.CF.Cour
